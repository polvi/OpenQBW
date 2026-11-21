//! Tables and rows of a company file, read through the exact page cipher.
//!
//! [`TableReader`] removes the page cipher (the `cipher` module), reads the
//! SQL Anywhere catalog (`ISYSTAB`, `ISYSTABCOL`) and decodes the rows of any
//! table by its column list.
//!
//! # Page
//!
//! A table page starts with a 28-byte header: its own page number (`u32`),
//! the page type at byte 6 (`'e'` or `'E'`), `04` at byte 16 and a kind byte
//! below 16 at byte 17, the live row count at 18, the slot count at 22 and
//! the table id at 24. The slot directory follows at byte 28, one `u16` per
//! slot; a slot of 0 is free. A row starts 28 bytes after its slot value.
//!
//! # Row
//!
//! ```text
//! [length u16] [flags u8] [presence bitmap] [values in column order]
//! ```
//!
//! The bitmap has one bit for each nullable column, most significant bit
//! first; a clear bit means NULL and the column takes no bytes.
//!
//! # Values
//!
//! Integers and floats are little-endian. A date is minutes since
//! 1600-02-29 (`u32`); a timestamp adds microseconds within the minute
//! (`u32`). A numeric is `[k] [ctrl] [k base-100 digits, least significant
//! first]`. A string or binary value starts with one byte: below `0x80` it is
//! the length of the value that follows; `0xFF` is followed by a big-endian
//! `u16` length; anything else is `0x80 | n`, then `n` prefix bytes, a flag
//! byte, the size (`u32`), a page (`u32`), two bytes and a slot (`u16`) that
//! locate the value outside the row. Such a value is a chain of rows
//! `[length u16] [flags u8] [body]`; flag bit 2 means the body starts with
//! the page (`u32`) and slot (`u16`) of the next piece.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;

use crate::cipher::PlainImage;
use crate::error::{Error, Result};
use crate::scan::ReadOptions;

/// Bytes before the slot directory; row offsets count from here.
const HEADER: usize = 28;
/// First byte past the row area (the CRC follows).
const ROW_END: usize = 0xFFC;
/// Table id of `ISYSTAB`.
const SYSTAB: u32 = 1;
/// Table id of `ISYSTABCOL`.
const SYSTABCOL: u32 = 2;
/// Days from 1970-01-01 back to 1600-02-29, the zero of stored dates.
const EPOCH_DAYS: i64 = -135_081;
/// Pieces followed before a chained value is given up as a loop.
const MAX_CHAIN: usize = 1 << 16;

/// A decoded column value.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Value {
    /// SQL NULL.
    Null,
    /// A signed integer, a tinyint or a bit.
    Int(i64),
    /// An unsigned 64-bit integer.
    UInt(u64),
    /// A float or a double.
    Float(f64),
    /// A character value. Bytes that are not UTF-8 are read as Latin-1.
    Text(String),
    /// A binary value.
    Bytes(Vec<u8>),
    /// A numeric, as an exact decimal string.
    Decimal(String),
    /// A date, `YYYY-MM-DD`.
    Date(String),
    /// A timestamp, `YYYY-MM-DD HH:MM:SS.ffffff`.
    Timestamp(String),
}

/// One column of a table, from `ISYSTABCOL`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Column {
    /// Column id; rows store values in this order.
    pub id: u32,
    /// Column name.
    pub name: String,
    /// SQL Anywhere domain id (2 integer, 3 numeric, 9 varchar, ...).
    pub domain: u16,
    /// Whether the column can be NULL.
    pub nullable: bool,
    /// Declared width.
    pub width: u32,
    /// Declared scale.
    pub scale: u16,
}

/// One table, from `ISYSTAB`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Table {
    /// Table id.
    pub id: u32,
    /// Table name.
    pub name: String,
    /// Columns in row order.
    pub columns: Vec<Column>,
    /// Column ids missing from the catalog below the highest one found.
    /// Rows of a table with gaps do not decode past the first gap.
    pub missing_columns: Vec<u32>,
    /// Table pages that belong to it.
    pub page_count: usize,
}

/// One row of a table.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct Row {
    /// Page the row is on.
    pub page: u64,
    /// Slot of the row on its page.
    pub slot: u16,
    /// One value per column of the table. Columns after a decode error are
    /// [`Value::Null`].
    pub values: Vec<Value>,
    /// Why decoding stopped early, when it did.
    pub error: Option<String>,
    /// Row bytes that were not decoded; empty for a clean row.
    pub raw_tail: Vec<u8>,
}

/// Reads tables and rows from a company file.
pub struct TableReader {
    image: PlainImage,
    tables: Vec<Table>,
    pages: BTreeMap<u32, Vec<u64>>,
}

impl TableReader {
    /// Open a `.qbw` company file or a zlib-compressed QBB backup.
    ///
    /// # Errors
    ///
    /// The errors of [`Reader::open`](crate::Reader::open) for a file that
    /// cannot be read or is not a supported company file, and
    /// [`Error::KeystreamMismatch`] when fewer than half of the written
    /// pages name their own page number after decoding, which means the
    /// page cipher constants do not fit this file.
    pub fn open(path: impl AsRef<Path>, options: &ReadOptions) -> Result<Self> {
        let path = path.as_ref();
        let mut file = File::open(path)?;
        if crate::qbb::has_signature(&mut file)? {
            return Self::from_bytes(
                crate::qbb::company_bytes(file, options.max_backup_bytes)?,
                options,
            );
        }
        drop(file);
        let mut bytes = Vec::new();
        File::open(path)?.read_to_end(&mut bytes)?;
        Self::from_bytes(bytes, options)
    }

    /// As [`TableReader::open`], over the bytes of a company file already in
    /// memory.
    pub fn from_bytes(bytes: Vec<u8>, _options: &ReadOptions) -> Result<Self> {
        let store = crate::open::store_from_bytes(bytes)?;
        let mut stored = Vec::with_capacity(store.size_bytes() as usize);
        for pn in 0..store.page_count() {
            let page = store.page(pn).map_err(|e| Error::from_store(e, Some(pn)))?;
            stored.extend_from_slice(page.bytes());
        }
        drop(store);
        Self::from_stored(&stored)
    }

    fn from_stored(stored: &[u8]) -> Result<Self> {
        let image = PlainImage::decode(stored);
        if image.live_pages() * 2 < image.written_pages() {
            return Err(Error::KeystreamMismatch {
                validated: image.live_pages(),
                pages: image.written_pages(),
            });
        }
        let mut pages: BTreeMap<u32, Vec<u64>> = BTreeMap::new();
        for pn in 1..image.page_count() {
            if let Some(tid) = image.page(pn).and_then(table_page) {
                pages.entry(tid).or_default().push(pn);
            }
        }
        let mut reader = Self {
            image,
            tables: Vec::new(),
            pages,
        };
        reader.tables = reader.read_catalog();
        Ok(reader)
    }

    /// Pages in the file, the superblock included.
    pub fn page_count(&self) -> u64 {
        self.image.page_count()
    }

    /// Written pages whose header names their own page number.
    pub fn live_pages(&self) -> u64 {
        self.image.live_pages()
    }

    /// Written pages that name another page: the checkpoint log at the end
    /// of the file, which holds earlier images of pages. They are not read.
    pub fn stale_pages(&self) -> u64 {
        self.image.written_pages() - self.image.live_pages()
    }

    /// Every table the catalog names that has columns, ordered by id.
    pub fn tables(&self) -> &[Table] {
        &self.tables
    }

    /// The table called `name`, compared without regard to ASCII case.
    pub fn table(&self, name: &str) -> Option<&Table> {
        self.tables
            .iter()
            .find(|t| t.name.eq_ignore_ascii_case(name))
    }

    /// Decode every row of `table`, in page and slot order.
    pub fn rows(&self, table: &Table) -> Vec<Row> {
        let nullable = table.columns.iter().filter(|c| c.nullable).count();
        let mut out = Vec::new();
        for (page, slot, raw) in self.raw_rows(table.id) {
            out.push(self.decode_row(table, nullable, page, slot, raw));
        }
        out
    }

    /// `(page, slot, row bytes)` of every row on the pages of table `tid`.
    fn raw_rows(&self, tid: u32) -> impl Iterator<Item = (u64, u16, &[u8])> {
        self.pages
            .get(&tid)
            .into_iter()
            .flatten()
            .filter_map(|&pn| self.image.page(pn).map(|pg| (pn, pg)))
            .flat_map(|(pn, pg)| {
                (0..slot_count(pg))
                    .filter_map(move |slot| row_at(pg, slot).map(|row| (pn, slot as u16, row)))
            })
    }

    fn read_catalog(&self) -> Vec<Table> {
        let mut names: BTreeMap<u32, String> = BTreeMap::new();
        for (_, _, row) in self.raw_rows(SYSTAB) {
            let Some(tid) = le32(row, 4) else { continue };
            if let Some(name) = counted_name(row, 44..60, 3, false) {
                names.insert(tid, name);
            }
        }
        let mut columns: BTreeMap<u32, BTreeMap<u32, Column>> = BTreeMap::new();
        for (_, _, row) in self.raw_rows(SYSTABCOL) {
            if row.len() < 40 {
                continue;
            }
            let (Some(tid), Some(id), Some(width)) = (le32(row, 4), le32(row, 8), le32(row, 16))
            else {
                continue;
            };
            if id >= 2000 {
                continue;
            }
            let Some(name) = counted_name(row, 30..44, 1, true) else {
                continue;
            };
            columns.entry(tid).or_default().insert(
                id,
                Column {
                    id,
                    name,
                    domain: u16::from_le_bytes([row[12], row[13]]),
                    nullable: row[14] == 1 && row[15] == b'Y',
                    width,
                    scale: u16::from_le_bytes([row[20], row[21]]),
                },
            );
        }
        let mut tables = Vec::new();
        for (id, name) in names {
            let Some(cols) = columns.remove(&id) else {
                continue;
            };
            let highest = cols.keys().next_back().copied().unwrap_or(0);
            let missing_columns = (1..=highest).filter(|i| !cols.contains_key(i)).collect();
            tables.push(Table {
                id,
                name,
                columns: cols.into_values().collect(),
                missing_columns,
                page_count: self.pages.get(&id).map_or(0, Vec::len),
            });
        }
        tables
    }

    fn decode_row(&self, table: &Table, nullable: usize, page: u64, slot: u16, raw: &[u8]) -> Row {
        let bitmap_len = nullable.div_ceil(8);
        let mut values = vec![Value::Null; table.columns.len()];
        let mut at = 3 + bitmap_len;
        let mut error = None;
        let mut seen = 0usize;
        for (i, col) in table.columns.iter().enumerate() {
            if col.nullable {
                let present = raw
                    .get(3 + seen / 8)
                    .is_some_and(|b| b >> (7 - seen % 8) & 1 == 1);
                seen += 1;
                if !present {
                    continue;
                }
            }
            match self.decode_value(col.domain, raw, at) {
                Ok((v, next)) => {
                    values[i] = v;
                    at = next;
                }
                Err(why) => {
                    error = Some(format!("{why} at column {}", col.name));
                    break;
                }
            }
        }
        let at = at.min(raw.len());
        // A row is at least 9 bytes; a shorter one is padded with zeros.
        let padding = raw.len() == 9 && raw[at..].iter().all(|&b| b == 0);
        if error.is_none() && at < raw.len() && !padding {
            error = Some(format!("{} bytes after the last column", raw.len() - at));
        }
        let raw_tail = if error.is_some() {
            raw[at..].to_vec()
        } else {
            Vec::new()
        };
        Row {
            page,
            slot,
            values,
            error,
            raw_tail,
        }
    }

    /// Decode one value of `domain` at `at`; returns it and the offset after it.
    fn decode_value(
        &self,
        domain: u16,
        raw: &[u8],
        at: usize,
    ) -> std::result::Result<(Value, usize), &'static str> {
        const SHORT: &str = "row ends inside the value";
        let take = |n: usize| raw.get(at..at + n).ok_or(SHORT);
        Ok(match domain {
            2 => (Value::Int(i32::from_le_bytes(arr(take(4)?)).into()), at + 4),
            21 => (Value::Int(u32::from_le_bytes(arr(take(4)?)).into()), at + 4),
            1 => (Value::Int(i16::from_le_bytes(arr(take(2)?)).into()), at + 2),
            22 => (Value::Int(u16::from_le_bytes(arr(take(2)?)).into()), at + 2),
            19 | 24 => (Value::Int(take(1)?[0].into()), at + 1),
            20 => (Value::Int(i64::from_le_bytes(arr(take(8)?))), at + 8),
            23 => (Value::UInt(u64::from_le_bytes(arr(take(8)?))), at + 8),
            4 => (
                Value::Float(f32::from_le_bytes(arr(take(4)?)).into()),
                at + 4,
            ),
            5 => (Value::Float(f64::from_le_bytes(arr(take(8)?))), at + 8),
            6 => {
                let minutes = u32::from_le_bytes(arr(take(4)?));
                (Value::Date(date(minutes)), at + 4)
            }
            13 | 14 => {
                let b = take(8)?;
                let minutes = u32::from_le_bytes(arr(&b[..4]));
                let micros = u32::from_le_bytes(arr(&b[4..]));
                (Value::Timestamp(timestamp(minutes, micros)), at + 8)
            }
            3 | 27 => {
                let (text, next) = numeric(raw, at)?;
                (Value::Decimal(text), next)
            }
            7..=12 | 28 | 31 | 32 | 36 => {
                let (bytes, next) = self.counted(raw, at)?;
                let v = if matches!(domain, 11 | 12 | 28 | 31) {
                    Value::Bytes(bytes)
                } else {
                    Value::Text(text(bytes))
                };
                (v, next)
            }
            _ => return Err("unsupported column type"),
        })
    }

    /// A string or binary value at `at`, inline or stored outside the row.
    fn counted(
        &self,
        raw: &[u8],
        at: usize,
    ) -> std::result::Result<(Vec<u8>, usize), &'static str> {
        const SHORT: &str = "row ends inside the value";
        let first = *raw.get(at).ok_or(SHORT)?;
        if first < 0x80 {
            let end = at + 1 + first as usize;
            return Ok((raw.get(at + 1..end).ok_or(SHORT)?.to_vec(), end));
        }
        if first == 0xFF {
            let len = raw.get(at + 1..at + 3).ok_or(SHORT)?;
            let start = at + 3;
            let end = start + u16::from_be_bytes([len[0], len[1]]) as usize;
            return Ok((raw.get(start..end).ok_or(SHORT)?.to_vec(), end));
        }
        let r = at + 1 + (first & 0x7F) as usize;
        let locator = raw.get(r..r + 13).ok_or(SHORT)?;
        let size = u32::from_le_bytes(arr(&locator[1..5])) as usize;
        let page = u32::from_le_bytes(arr(&locator[5..9]));
        let slot = u16::from_le_bytes(arr(&locator[11..13]));
        let value = self
            .chained(page.into(), slot.into(), size)
            .ok_or("value stored outside the row cannot be followed")?;
        Ok((value, r + 13))
    }

    /// Follow a chain of pieces from (`page`, `slot`) until `size` bytes.
    fn chained(&self, mut page: u64, mut slot: usize, size: usize) -> Option<Vec<u8>> {
        let mut out = Vec::new();
        for _ in 0..MAX_CHAIN {
            let pg = self.image.page(page)?;
            if slot >= slot_count(pg) {
                return None;
            }
            let start = slot_offset(pg, slot) + HEADER;
            let head = pg.get(start..start + 3)?;
            let len = u16::from_le_bytes([head[0], head[1]]) as usize;
            if len < 3 || start + len > ROW_END {
                return None;
            }
            let mut body = &pg[start + 3..start + len];
            let more = head[2] & 4 != 0;
            if more {
                page = u32::from_le_bytes(arr(body.get(..4)?)).into();
                slot = u16::from_le_bytes(arr(body.get(4..6)?)).into();
                body = &body[6..];
            }
            out.extend_from_slice(body);
            if out.len() >= size {
                out.truncate(size);
                return Some(out);
            }
            if !more {
                return None;
            }
        }
        None
    }
}

/// The table id of a table page, `None` for any other page.
fn table_page(pg: &[u8]) -> Option<u32> {
    let is_table = matches!(pg[6], b'e' | b'E')
        && pg[16] == 4
        && pg[17] < 16
        && u16::from_le_bytes([pg[18], pg[19]]) <= u16::from_le_bytes([pg[22], pg[23]]);
    is_table.then(|| u32::from_le_bytes(arr(&pg[24..28])))
}

fn slot_count(pg: &[u8]) -> usize {
    let n = u16::from_le_bytes([pg[22], pg[23]]) as usize;
    // More slots than fit before the row area is not a slot directory.
    if HEADER + 2 * n > ROW_END { 0 } else { n }
}

fn slot_offset(pg: &[u8], slot: usize) -> usize {
    (u16::from_le_bytes([pg[HEADER + 2 * slot], pg[HEADER + 2 * slot + 1]]) & 0xFFF) as usize
}

/// The row in `slot`, `None` for a free slot or a length that does not fit.
fn row_at(pg: &[u8], slot: usize) -> Option<&[u8]> {
    let off = slot_offset(pg, slot);
    if off == 0 {
        return None;
    }
    let start = off + HEADER;
    let len = u16::from_le_bytes([*pg.get(start)?, *pg.get(start + 1)?]) as usize;
    if len < 4 || start + len > ROW_END {
        return None;
    }
    Some(&pg[start..start + len])
}

fn le32(row: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(arr(row.get(at..at + 4)?)))
}

/// Copy a slice whose length the caller has already fixed.
fn arr<const N: usize>(b: &[u8]) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&b[..N]);
    out
}

/// The first length-prefixed identifier whose length byte lies in `window`.
///
/// The catalog rows are read at fixed offsets up to their name; the columns
/// between vary in width by a few bytes across versions of the row.
fn counted_name(
    row: &[u8],
    window: std::ops::Range<usize>,
    min: usize,
    spaces: bool,
) -> Option<String> {
    for at in window {
        let len = *row.get(at)? as usize;
        if len < min || len > 64 {
            continue;
        }
        let Some(name) = row.get(at + 1..at + 1 + len) else {
            continue;
        };
        let head = name[0].is_ascii_alphabetic() || name[0] == b'_';
        let rest = name
            .iter()
            .all(|&b| b.is_ascii_alphanumeric() || b == b'_' || (spaces && b == b' '));
        if head && rest {
            return Some(String::from_utf8_lossy(name).into_owned());
        }
    }
    None
}

/// Bytes as text: UTF-8 when valid, otherwise Latin-1.
fn text(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes)
        .unwrap_or_else(|e| e.into_bytes().into_iter().map(char::from).collect())
}

/// `[k] [ctrl] [k base-100 digits]` as an exact decimal string.
fn numeric(raw: &[u8], at: usize) -> std::result::Result<(String, usize), &'static str> {
    let head = raw.get(at..at + 2).ok_or("row ends inside the value")?;
    let (k, ctrl) = (head[0] as usize, head[1]);
    if k == 0 {
        return Ok(("0".into(), at + 2));
    }
    if k > 20 {
        return Err("numeric digit count above 20");
    }
    let digits = raw
        .get(at + 2..at + 2 + k)
        .ok_or("row ends inside the value")?;
    if digits.iter().any(|&d| d > 99) {
        return Err("numeric digit above 99");
    }
    let mut whole: String = digits.iter().rev().map(|d| format!("{d:02}")).collect();
    let exponent = 2 * (i32::from(ctrl & 0x7F) - 64);
    let mut out = if exponent >= 0 {
        whole.push_str(&"0".repeat(exponent as usize));
        whole.trim_start_matches('0').to_owned()
    } else {
        let frac = exponent.unsigned_abs() as usize;
        if whole.len() <= frac {
            whole.insert_str(0, &"0".repeat(frac - whole.len() + 1));
        }
        let (int, dec) = whole.split_at(whole.len() - frac);
        let int = int.trim_start_matches('0');
        let dec = dec.trim_end_matches('0');
        let int = if int.is_empty() { "0" } else { int };
        if dec.is_empty() {
            int.to_owned()
        } else {
            format!("{int}.{dec}")
        }
    };
    if out.is_empty() {
        out.push('0');
    }
    if ctrl & 0x80 != 0 && out != "0" {
        out.insert(0, '-');
    }
    Ok((out, at + 2 + k))
}

/// `(year, month, day)` of a day count from 1970-01-01 (proleptic Gregorian).
fn civil(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (yoe + era * 400 + i64::from(month <= 2), month, day)
}

fn date(minutes: u32) -> String {
    let (y, m, d) = civil(EPOCH_DAYS + i64::from(minutes / 1440));
    format!("{y:04}-{m:02}-{d:02}")
}

fn timestamp(minutes: u32, micros: u32) -> String {
    // The second field counts microseconds past the minute and can run past
    // one minute; carry it rather than print a 61st second.
    let total = u64::from(minutes) * 60_000_000 + u64::from(micros);
    let day = total / 86_400_000_000;
    let rest = total % 86_400_000_000;
    let (y, mo, d) = civil(EPOCH_DAYS + day as i64);
    let secs = rest / 1_000_000;
    format!(
        "{y:04}-{mo:02}-{d:02} {:02}:{:02}:{:02}.{:06}",
        secs / 3600,
        secs / 60 % 60,
        secs % 60,
        rest % 1_000_000
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipher::PAGE;
    use crate::cipher::tests::encode_page;

    /// A plain page: header for `tid` with `kind` at byte 17, rows packed
    /// from the end of the row area, one slot each.
    fn page(pn: u32, tid: u32, kind: u8, rows: &[Vec<u8>]) -> Vec<u8> {
        let mut pg = vec![0u8; PAGE];
        pg[..4].copy_from_slice(&pn.to_le_bytes());
        pg[6] = b'e';
        pg[16] = 4;
        pg[17] = kind;
        let n = rows.len() as u16;
        pg[18..20].copy_from_slice(&n.to_le_bytes());
        pg[22..24].copy_from_slice(&n.to_le_bytes());
        pg[24..28].copy_from_slice(&tid.to_le_bytes());
        let mut end = ROW_END;
        for (i, row) in rows.iter().enumerate() {
            end -= row.len();
            pg[end..end + row.len()].copy_from_slice(row);
            let off = (end - HEADER) as u16;
            pg[HEADER + 2 * i..HEADER + 2 * i + 2].copy_from_slice(&off.to_le_bytes());
        }
        pg
    }

    /// `[length] [flags] body`.
    fn row(flags: u8, body: &[u8]) -> Vec<u8> {
        let mut r = ((body.len() + 3) as u16).to_le_bytes().to_vec();
        r.push(flags);
        r.extend_from_slice(body);
        r
    }

    fn systab_row(tid: u32, name: &str) -> Vec<u8> {
        let mut body = vec![0xC0];
        body.extend_from_slice(&tid.to_le_bytes());
        body.resize(50, 0);
        body.push(name.len() as u8);
        body.extend_from_slice(name.as_bytes());
        row(0, &body)
    }

    fn systabcol_row(tid: u32, id: u32, domain: u16, nullable: bool, name: &str) -> Vec<u8> {
        let mut body = vec![0u8];
        body.extend_from_slice(&tid.to_le_bytes());
        body.extend_from_slice(&id.to_le_bytes());
        body.extend_from_slice(&domain.to_le_bytes());
        body.push(1);
        body.push(if nullable { b'Y' } else { b'N' });
        body.extend_from_slice(&4u32.to_le_bytes());
        body.extend_from_slice(&0u16.to_le_bytes());
        body.resize(35, 0);
        body.push(name.len() as u8);
        body.extend_from_slice(name.as_bytes());
        row(0, &body)
    }

    /// Encode plain pages 1.. into a stored file with an empty superblock.
    fn stored(pages: &[Vec<u8>]) -> Vec<u8> {
        let mut file = vec![0u8; PAGE];
        for (i, pg) in pages.iter().enumerate() {
            file.extend(encode_page(
                pg,
                i as u64 + 1,
                &crate::cipher::Phase::Fixed(false),
            ));
        }
        file
    }

    const T: u32 = 3000;

    fn sample() -> TableReader {
        let catalog = page(1, SYSTAB, 4, &[systab_row(T, "ledger")]);
        let cols = page(
            2,
            SYSTABCOL,
            4,
            &[
                systabcol_row(T, 1, 2, false, "id"),
                systabcol_row(T, 2, 6, true, "posted"),
                systabcol_row(T, 3, 3, true, "amount"),
                systabcol_row(T, 4, 9, true, "memo"),
                systabcol_row(T, 5, 24, false, "cleared"),
                systabcol_row(T, 6, 12, true, "attachment"),
            ],
        );
        // Row 1: every column present; the attachment is chained over two
        // pieces on pages 4 and 5.
        let mut full = vec![0xF0];
        full.extend_from_slice(&7i32.to_le_bytes());
        full.extend_from_slice(&(150_786u32 * 1440).to_le_bytes());
        full.extend_from_slice(&[0x02, 0xBF, 0x2D, 0x22]);
        full.extend_from_slice(b"\x05hello");
        full.push(1);
        full.extend_from_slice(&[0x82, b'a', b'b', 0x80]);
        full.extend_from_slice(&10u32.to_le_bytes());
        full.extend_from_slice(&4u32.to_le_bytes());
        full.extend_from_slice(&[0, 0]);
        full.extend_from_slice(&0u16.to_le_bytes());
        // Row 2: only the NOT NULL columns.
        let mut sparse = vec![0x00];
        sparse.extend_from_slice(&(-3i32).to_le_bytes());
        sparse.push(0);
        // Row 3: memo of 200 bytes, the long inline form.
        let mut long = vec![0x20];
        long.extend_from_slice(&9i32.to_le_bytes());
        long.extend_from_slice(&[0xFF, 0x00, 200]);
        long.extend(std::iter::repeat_n(b'x', 200));
        long.push(0);
        let data = page(3, T, 3, &[row(0, &full), row(0, &sparse), row(0, &long)]);
        let mut first = 5u32.to_le_bytes().to_vec();
        first.extend_from_slice(&0u16.to_le_bytes());
        first.extend_from_slice(b"abcdef");
        let lob1 = page(4, T, 20, &[row(4, &first)]);
        let lob2 = page(5, T, 20, &[row(0, b"ghij")]);
        TableReader::from_stored(&stored(&[catalog, cols, data, lob1, lob2])).unwrap()
    }

    #[test]
    fn catalog_lists_the_table_and_its_columns() {
        let r = sample();
        assert_eq!(r.page_count(), 6);
        assert_eq!(r.live_pages(), 5);
        assert_eq!(r.stale_pages(), 0);
        let t = r
            .table("LEDGER")
            .expect("table found without regard to case");
        assert_eq!((t.id, t.name.as_str(), t.page_count), (T, "ledger", 1));
        let names: Vec<_> = t.columns.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(
            names,
            ["id", "posted", "amount", "memo", "cleared", "attachment"]
        );
        assert!(t.missing_columns.is_empty());
        assert!(!t.columns[0].nullable && t.columns[1].nullable);
    }

    #[test]
    fn rows_decode_by_the_presence_bitmap() {
        let r = sample();
        let rows = r.rows(r.table("ledger").unwrap());
        assert_eq!(rows.len(), 3);
        assert!(
            rows.iter()
                .all(|row| row.error.is_none() && row.raw_tail.is_empty())
        );
        assert_eq!(
            rows[0].values,
            [
                Value::Int(7),
                Value::Date("2012-12-31".into()),
                Value::Decimal("-34.45".into()),
                Value::Text("hello".into()),
                Value::Int(1),
                Value::Bytes(b"abcdefghij".to_vec()),
            ]
        );
        assert_eq!(
            rows[1].values,
            [
                Value::Int(-3),
                Value::Null,
                Value::Null,
                Value::Null,
                Value::Int(0),
                Value::Null,
            ]
        );
        assert_eq!(rows[2].values[3], Value::Text("x".repeat(200)));
        assert_eq!((rows[0].page, rows[0].slot, rows[2].slot), (3, 0, 2));
    }

    #[test]
    fn a_row_that_runs_out_reports_where() {
        let catalog = page(1, SYSTAB, 4, &[systab_row(T, "ledger")]);
        let cols = page(
            2,
            SYSTABCOL,
            4,
            &[
                systabcol_row(T, 1, 2, false, "id"),
                systabcol_row(T, 2, 9, false, "memo"),
            ],
        );
        let mut cut = Vec::new();
        cut.extend_from_slice(&1i32.to_le_bytes());
        cut.extend_from_slice(b"\x09short");
        let mut extra = Vec::new();
        extra.extend_from_slice(&2i32.to_le_bytes());
        extra.extend_from_slice(b"\x02ok\xAA\xBB");
        let data = page(3, T, 3, &[row(0, &cut), row(0, &extra)]);
        let r = TableReader::from_stored(&stored(&[catalog, cols, data])).unwrap();
        let rows = r.rows(r.table("ledger").unwrap());
        assert_eq!(rows[0].values, [Value::Int(1), Value::Null]);
        assert_eq!(
            rows[0].error.as_deref(),
            Some("row ends inside the value at column memo")
        );
        assert_eq!(rows[0].raw_tail, b"\x09short");
        assert_eq!(rows[1].values[1], Value::Text("ok".into()));
        assert_eq!(
            rows[1].error.as_deref(),
            Some("2 bytes after the last column")
        );
        assert_eq!(rows[1].raw_tail, [0xAA, 0xBB]);
    }

    #[test]
    fn free_slots_and_missing_columns() {
        let catalog = page(1, SYSTAB, 4, &[systab_row(T, "ledger")]);
        let cols = page(2, SYSTABCOL, 4, &[systabcol_row(T, 3, 2, false, "third")]);
        let mut data = page(3, T, 3, &[row(0, &[0; 6]), row(0, &[0; 6])]);
        data[HEADER..HEADER + 2].copy_from_slice(&[0, 0]);
        data[18] = 1;
        let r = TableReader::from_stored(&stored(&[catalog, cols, data])).unwrap();
        let t = r.table("ledger").unwrap();
        assert_eq!(t.missing_columns, [1, 2]);
        assert_eq!(r.rows(t).len(), 1, "the freed slot is skipped");
    }

    #[test]
    fn a_file_the_constants_do_not_fit_is_an_error() {
        let mut file = vec![0u8; PAGE * 9];
        for (i, b) in file[PAGE..].iter_mut().enumerate() {
            *b = (i as u32).wrapping_mul(2_654_435_761).to_le_bytes()[3];
        }
        let Err(e) = TableReader::from_stored(&file) else {
            panic!("random pages must not open");
        };
        assert!(matches!(
            e,
            Error::KeystreamMismatch {
                validated: 0,
                pages: 8
            }
        ));
    }

    #[test]
    fn numeric_layout() {
        let n = |b: &[u8]| numeric(b, 0).unwrap().0;
        assert_eq!(n(&[0x02, 0x40, 0x08, 0x02]), "208");
        assert_eq!(n(&[0x01, 0x41, 0x03]), "300");
        assert_eq!(n(&[0x02, 0x3F, 0x2F, 0x4B]), "75.47");
        assert_eq!(n(&[0x02, 0xBF, 0x2D, 0x22]), "-34.45");
        assert_eq!(n(&[0x03, 0x3F, 0x39, 0x56, 0x2F]), "4786.57");
        assert_eq!(n(&[0x02, 0xC0, 0x3C, 0x09]), "-960");
        assert_eq!(n(&[0x03, 0xBF, 0x32, 0x31, 0x03]), "-349.5");
        assert_eq!(n(&[0x01, 0x3E, 0x05]), "0.0005");
        assert_eq!(n(&[0x00, 0x81]), "0");
        assert_eq!(n(&[0x01, 0xC0, 0x00]), "0");
        assert!(numeric(&[0x01, 0x40, 100], 0).is_err());
        assert!(numeric(&[0x02, 0x40, 1], 0).is_err());
    }

    #[test]
    fn dates_count_minutes_from_1600_02_29() {
        assert_eq!(date(0), "1600-02-29");
        assert_eq!(date(1439), "1600-02-29");
        assert_eq!(date(1440), "1600-03-01");
        assert_eq!(date(150_786 * 1440), "2012-12-31");
        assert_eq!(
            timestamp(150_786 * 1440 + 61, 1_500_000),
            "2012-12-31 01:01:01.500000"
        );
        assert_eq!(timestamp(1439, 60_000_000), "1600-03-01 00:00:00.000000");
    }

    #[test]
    fn text_falls_back_to_latin_1() {
        assert_eq!(text(b"caf\xC3\xA9".to_vec()), "caf\u{e9}");
        assert_eq!(text(b"caf\xE9 \xB7".to_vec()), "caf\u{e9} \u{b7}");
    }
}
