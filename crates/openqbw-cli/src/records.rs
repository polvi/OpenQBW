//! Decoders for the application records QuickBooks keeps as binary values
//! in `I_GENERAL`, `I_SPECIAL` and `I_RECONCILIATION_DISCREPANCY_TRACKER`
//! (SPECIFICATION.md section 8c.8).
//!
//! Two self-describing encodings cover the structured records and are
//! rendered as JSON into `_decoded_records`. A handful of records with a
//! known meaning are also written as tables of their own.

use std::collections::HashMap;
use std::fmt::Write as _;

use anyhow::Result;
use rusqlite::types::Value as Sql;
use rusqlite::{Transaction, params};

fn u16_at(d: &[u8], i: usize) -> Option<u16> {
    Some(u16::from_le_bytes(d.get(i..i + 2)?.try_into().ok()?))
}

fn u32_at(d: &[u8], i: usize) -> Option<u32> {
    Some(u32::from_le_bytes(d.get(i..i + 4)?.try_into().ok()?))
}

fn printable(b: &[u8]) -> bool {
    b.iter()
        .all(|&x| (32..127).contains(&x) || matches!(x, 9 | 10 | 13))
}

/// `b` as text when it is printable bytes closed by one NUL.
fn c_text(b: &[u8]) -> Option<String> {
    let (last, body) = b.split_last()?;
    (*last == 0 && printable(body)).then(|| body.iter().map(|&c| c as char).collect())
}

/// NUL-terminated text at `off` in a fixed layout.
fn text_at(d: &[u8], off: usize) -> Option<String> {
    let tail = d.get(off..)?;
    let end = tail.iter().position(|&c| c == 0)?;
    (end > 0 && printable(&tail[..end])).then(|| tail[..end].iter().map(|&c| c as char).collect())
}

/// A date stored as day, month, year (`u16`).
fn dmy(d: &[u8]) -> Option<String> {
    let (day, month, year) = (*d.first()?, *d.get(1)?, u16_at(d, 2)?);
    ((1..=31).contains(&day) && (1..=12).contains(&month) && (1900..2200).contains(&year))
        .then(|| format!("{year:04}-{month:02}-{day:02}"))
}

fn unix_time(secs: u32) -> String {
    let (days, rest) = (i64::from(secs / 86400), secs % 86400);
    format!(
        "{} {:02}:{:02}:{:02}",
        super::iso_date_from_unix_days(days),
        rest / 3600,
        rest % 3600 / 60,
        rest % 60
    )
}

fn hex(b: &[u8]) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// A value of the tagged encoding: `[tag u8][type u8][value]`, where the
/// type is `(size - 1) << 3` for a fixed value of 1 to 4 bytes, `0x20` for a
/// `u8` length and `0x28` for a `u16` length.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Tagged {
    Fixed(Vec<u8>),
    Text(String),
    /// A 19-byte date and time; empty when unset.
    Time(String),
    Bytes(Vec<u8>),
    Fields(Vec<(u8, Tagged)>),
}

impl Tagged {
    fn int(&self) -> Option<i64> {
        match self {
            Tagged::Fixed(b) => Some(b.iter().rev().fold(0i64, |n, &x| n << 8 | i64::from(x))),
            _ => None,
        }
    }

    /// Text, including a fixed value that holds short text.
    fn text(&self) -> Option<String> {
        match self {
            Tagged::Text(s) => Some(s.clone()),
            Tagged::Fixed(b) => c_text(b),
            _ => None,
        }
    }

    fn get(&self, tag: u8) -> Option<&Tagged> {
        match self {
            Tagged::Fields(f) => f.iter().find(|(t, _)| *t == tag).map(|(_, v)| v),
            _ => None,
        }
    }

    fn json(&self, out: &mut String) {
        match self {
            Tagged::Fixed(b) => {
                match c_text(b).filter(|s| b.len() >= 3 && s.len() + 1 == b.len()) {
                    Some(s) => json_str(&s, out),
                    None => {
                        let _ = write!(out, "{}", self.int().unwrap_or(0));
                    }
                }
            }
            Tagged::Text(s) => json_str(s, out),
            Tagged::Time(s) => {
                out.push_str("{\"time\":");
                json_str(s, out);
                out.push('}');
            }
            Tagged::Bytes(b) => {
                let _ = write!(out, "{{\"hex\":\"{}\"}}", hex(b));
            }
            Tagged::Fields(f) => {
                out.push('[');
                for (i, (tag, v)) in f.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    let _ = write!(out, "[{tag},");
                    v.json(out);
                    out.push(']');
                }
                out.push(']');
            }
        }
    }
}

/// The 19-byte date and time of the tagged encoding: `03 00`, year `u16`,
/// month, day, hour, minute, second.
fn tagged_time(v: &[u8]) -> Option<String> {
    if v.len() != 19 || v[..2] != [3, 0] {
        return None;
    }
    if v[2..13].iter().all(|&x| x == 0) {
        return Some(String::new());
    }
    let year = u16_at(v, 2)?;
    let (mo, d, h, mi, s) = (v[4], v[5], v[6], v[7], v[8]);
    ((1..=12).contains(&mo) && (1..=31).contains(&d) && h < 24 && mi < 60 && s < 61)
        .then(|| format!("{year:04}-{mo:02}-{d:02} {h:02}:{mi:02}:{s:02}"))
}

/// Parse `d` as a list of tagged fields that fills it exactly.
pub(crate) fn tagged(d: &[u8]) -> Option<Tagged> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < d.len() {
        let (tag, ty) = (d[i], *d.get(i + 1)?);
        i += 2;
        let fixed = matches!(ty, 0x00 | 0x08 | 0x10 | 0x18);
        let n = match ty {
            _ if fixed => usize::from(ty >> 3) + 1,
            0x20 => {
                i += 1;
                usize::from(*d.get(i - 1)?)
            }
            0x28 => {
                i += 2;
                usize::from(u16_at(d, i - 2)?)
            }
            _ => return None,
        };
        let v = d.get(i..i + n)?;
        i += n;
        let value = if fixed {
            Tagged::Fixed(v.to_vec())
        } else if let Some(s) = c_text(v) {
            Tagged::Text(s)
        } else if let Some(t) = tagged_time(v) {
            Tagged::Time(t)
        } else if let Some(sub) = (v.len() >= 2).then(|| tagged(v)).flatten() {
            sub
        } else {
            Tagged::Bytes(v.to_vec())
        };
        out.push((tag, value));
    }
    Some(Tagged::Fields(out))
}

/// An item of the block encoding. A container is
/// `05 01 0a 00 [version u16][length u16][id u16]` followed by its items,
/// the length counting the header; a field is
/// `05 07 [tag u16][length u16][extra u16][value]`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Block {
    Container {
        id: u16,
        version: u16,
        items: Vec<Block>,
    },
    Field {
        tag: u16,
        extra: u16,
        value: BlockValue,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BlockValue {
    Items(Vec<Block>),
    Text(String),
    Bytes(Vec<u8>),
}

/// Parse `d` as block items that fill it exactly.
pub(crate) fn block(d: &[u8]) -> Option<Vec<Block>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < d.len() {
        match (d[i], *d.get(i + 1)?) {
            (5, 1) => {
                if u16_at(d, i + 2)? != 10 {
                    return None;
                }
                let n = usize::from(u16_at(d, i + 6)?);
                if n < 10 {
                    return None;
                }
                out.push(Block::Container {
                    id: u16_at(d, i + 8)?,
                    version: u16_at(d, i + 4)?,
                    items: block(d.get(i + 10..i + n)?)?,
                });
                i += n;
            }
            (5, 7) => {
                let n = usize::from(u16_at(d, i + 4)?);
                let v = d.get(i + 8..i + 8 + n)?;
                let nested = if v.starts_with(&[5, 1]) {
                    block(v)
                } else {
                    None
                };
                out.push(Block::Field {
                    tag: u16_at(d, i + 2)?,
                    extra: u16_at(d, i + 6)?,
                    value: match (nested, c_text(v)) {
                        (Some(items), _) => BlockValue::Items(items),
                        (None, Some(s)) => BlockValue::Text(s),
                        (None, None) => BlockValue::Bytes(v.to_vec()),
                    },
                });
                i += 8 + n;
            }
            _ => return None,
        }
    }
    Some(out)
}

fn block_json(items: &[Block], out: &mut String) {
    out.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        match item {
            Block::Container { id, version, items } => {
                let _ = write!(out, "{{\"id\":{id},\"version\":{version},\"items\":");
                block_json(items, out);
                out.push('}');
            }
            Block::Field { tag, extra, value } => {
                let _ = write!(out, "[{tag},{extra},");
                match value {
                    BlockValue::Items(items) => block_json(items, out),
                    BlockValue::Text(s) => json_str(s, out),
                    BlockValue::Bytes(b) => {
                        let _ = write!(out, "{{\"hex\":\"{}\"}}", hex(b));
                    }
                }
                out.push(']');
            }
        }
    }
    out.push(']');
}

/// The first field with `tag` anywhere under `items`, as raw bytes.
fn block_bytes(items: &[Block], tag: u16) -> Option<&[u8]> {
    items.iter().find_map(|item| match item {
        Block::Container { items, .. } => block_bytes(items, tag),
        Block::Field {
            tag: t,
            value: BlockValue::Bytes(b),
            ..
        } if *t == tag => Some(b.as_slice()),
        Block::Field {
            value: BlockValue::Items(items),
            ..
        } => block_bytes(items, tag),
        Block::Field { .. } => None,
    })
}

/// The format name and JSON of a record in one of the two encodings.
pub(crate) fn decode_json(d: &[u8]) -> Option<(&'static str, String)> {
    let mut out = String::new();
    if d.len() > 6 && d[0] == 0x64 {
        tagged(d)?.json(&mut out);
        Some(("tagged", out))
    } else if d.starts_with(&[5, 1]) {
        block_json(&block(d)?, &mut out);
        Some(("block", out))
    } else {
        None
    }
}

/// Company information: the fixed layout in field 1002 of the `I_GENERAL`
/// record with key 22.
pub(crate) fn company_info(d: &[u8]) -> Vec<(&'static str, String)> {
    let Some(items) = block(d) else {
        return Vec::new();
    };
    let Some(b) = block_bytes(&items, 1002).filter(|b| b.len() >= 2082) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (name, off) in [
        ("company_name", 4),
        ("legal_name", 64),
        ("address_1", 124),
        ("address_2", 166),
        ("city", 208),
        ("postal_code", 242),
        ("country", 258),
        ("industry", 1570),
    ] {
        if let Some(s) = text_at(b, off) {
            out.push((name, s));
        }
    }
    if let Some(date) = dmy(&b[2078..2082]) {
        out.push(("created_date", date));
    }
    out
}

/// Statement dates of an account's reconciliations, newest first: 4-byte
/// dates up to offset 480 of the `I_GENERAL` record with key 43, then the
/// count, the account id and a time.
pub(crate) fn recon_dates(d: &[u8], account: i64) -> Vec<String> {
    if d.len() != 492 || u32_at(d, 484).map(i64::from) != Some(account) {
        return Vec::new();
    }
    d[..480].chunks(4).map_while(dmy).collect()
}

/// A row of `I_RECONCILIATION_DISCREPANCY_TRACKER`.
#[derive(Debug, Default, PartialEq)]
pub(crate) struct Discrepancy {
    pub change_code: Option<i64>,
    pub target_id: Option<i64>,
    pub transaction_id: Option<i64>,
    pub account_id: Option<i64>,
    pub statement_date: Option<String>,
    pub amount: Option<String>,
    pub transaction_date: Option<String>,
    /// Keys of the name, document number, memo and the two user names in
    /// the string records (`I_GENERAL` key 14).
    pub name: Option<i64>,
    pub doc_num: Option<i64>,
    pub memo: Option<i64>,
    pub entered_by: Option<i64>,
    pub changed_at: Option<String>,
    pub changed_by: Option<i64>,
    pub view_type: Option<i64>,
}

/// A 9-byte amount: a byte below the scale, a 6-byte count of 1/100000,
/// a byte, then a byte whose top bit is set on a positive amount.
fn amount(v: &[u8]) -> Option<String> {
    if v.len() != 9 || v[0] != 0 {
        return None;
    }
    let units = v[1..7]
        .iter()
        .rev()
        .fold(0u64, |n, &x| n << 8 | u64::from(x));
    let mut s = format!("{}.{:05}", units / 100_000, units % 100_000);
    while s.ends_with('0') {
        s.pop();
    }
    if s.ends_with('.') {
        s.pop();
    }
    if v[8] & 0x80 == 0 && units != 0 {
        s.insert(0, '-');
    }
    Some(s)
}

/// One byte, then `[tag u16][value]` fields closed by tag `0xFFFF`.
pub(crate) fn discrepancy(d: &[u8]) -> Option<Discrepancy> {
    let mut r = Discrepancy::default();
    let mut i = 1;
    loop {
        let tag = u16_at(d, i)?;
        i += 2;
        let n = match tag {
            0xFFFF => return (i == d.len()).then_some(r),
            5 => 9,
            0x0D => 2,
            0..=0x0C => 4,
            _ => return None,
        };
        let v = d.get(i..i + n)?;
        i += n;
        let int = || Some(v.iter().rev().fold(0i64, |n, &x| n << 8 | i64::from(x)));
        match tag {
            0 => r.change_code = int(),
            1 => r.target_id = int(),
            2 => r.transaction_id = int(),
            3 => r.account_id = int(),
            4 => r.statement_date = dmy(v),
            5 => r.amount = amount(v),
            6 => r.transaction_date = dmy(v),
            7 => r.name = int(),
            8 => r.doc_num = int(),
            9 => r.memo = int(),
            0x0A => r.entered_by = int(),
            0x0B => r.changed_at = u32_at(v, 0).map(unix_time),
            0x0C => r.changed_by = int(),
            _ => r.view_type = int(),
        }
    }
}

/// A release line of the file's version history, such as
/// `V23.0D R6 07/09/2013`: version, release and ISO date.
pub(crate) fn version_line(line: &str) -> Option<(String, String, String)> {
    let mut parts = line.split_whitespace();
    let (version, release, date) = (parts.next()?, parts.next()?, parts.next()?);
    let mut mdy = date.split('/');
    let (m, d, y) = (mdy.next()?, mdy.next()?, mdy.next()?);
    let ok = version.starts_with('V')
        && release.starts_with('R')
        && m.len() == 2
        && d.len() == 2
        && y.len() == 4
        && [m, d, y]
            .iter()
            .all(|p| p.bytes().all(|c| c.is_ascii_digit()));
    ok.then(|| {
        (
            version.to_string(),
            release.to_string(),
            format!("{y}-{m}-{d}"),
        )
    })
}

fn has(tx: &Transaction, table: &str, columns: &[&str]) -> Result<bool> {
    for c in columns {
        let n: i64 = tx.query_row(
            "SELECT count(*) FROM pragma_table_info(?) WHERE name = ?",
            params![table, c],
            |r| r.get(0),
        )?;
        if n == 0 {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Clean rows of a key, record number and value table, in order.
fn records(tx: &Transaction, table: &str) -> Result<Vec<(Sql, i64, Vec<u8>)>> {
    if !has(tx, table, &["key_fld", "rec_num", "data_fld"])? {
        return Ok(Vec::new());
    }
    let mut q = tx.prepare(&format!(
        "SELECT key_fld, rec_num, data_fld FROM {}
         WHERE _decode_error IS NULL AND typeof(rec_num) = 'integer'
           AND typeof(data_fld) = 'blob'
         ORDER BY key_fld, rec_num",
        super::sql_ident(table)
    ))?;
    let rows = q.query_map([], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)))?;
    Ok(rows.collect::<rusqlite::Result<_>>()?)
}

/// Add `_decoded_records` and the tables read from single records:
/// `company_info`, `file_versions`, `recon_history`, `recon_discrepancies`,
/// `bank_feed_accounts` and `bank_feed_institutions`. All are created, and
/// stay empty when the file has no matching record. Returns the number of
/// rows in `_decoded_records`.
pub(crate) fn add_decoded_records(tx: &Transaction) -> Result<u64> {
    tx.execute_batch(
        "CREATE TABLE _decoded_records (
            source  TEXT NOT NULL,
            key_fld,
            rec_num INTEGER NOT NULL,
            -- tagged or block.
            format  TEXT NOT NULL,
            json    TEXT NOT NULL
        );
        CREATE TABLE company_info (field TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE file_versions (
            seq INTEGER PRIMARY KEY, version TEXT NOT NULL, release TEXT NOT NULL,
            release_date TEXT NOT NULL
        );
        CREATE TABLE recon_history (
            account_id INTEGER NOT NULL, account_name TEXT,
            statement_date TEXT NOT NULL,
            PRIMARY KEY (account_id, statement_date)
        );
        CREATE TABLE recon_discrepancies (
            account_id INTEGER, account_name TEXT, statement_date TEXT,
            target_id INTEGER, transaction_id INTEGER, transaction_date TEXT,
            amount TEXT, name TEXT, doc_num TEXT, memo TEXT, entered_by TEXT,
            changed_at TEXT, changed_by TEXT, transaction_view_type INTEGER,
            change_code INTEGER
        );
        CREATE TABLE bank_feed_accounts (
            account_id INTEGER PRIMARY KEY, account_name TEXT, nickname TEXT,
            institution TEXT, institution_id INTEGER
        );
        CREATE TABLE bank_feed_institutions (
            institution_id INTEGER PRIMARY KEY, name TEXT, address TEXT,
            city TEXT, state TEXT, postal_code TEXT, country TEXT, phone TEXT,
            connection TEXT, url TEXT
        );",
    )?;
    let names = has(tx, "abmc_account_user", &["account_id", "name"])?;
    let account_name = |id: i64| -> Option<String> {
        if !names {
            return None;
        }
        tx.query_row(
            "SELECT name FROM abmc_account_user WHERE account_id = ?",
            [id],
            |r| r.get(0),
        )
        .ok()
    };
    let general = records(tx, "I_GENERAL")?;
    let special = records(tx, "I_SPECIAL")?;
    let mut decoded = 0u64;
    for (source, rows) in [("I_GENERAL", &general), ("I_SPECIAL", &special)] {
        for (key, rec, data) in rows {
            if let Some((format, json)) = decode_json(data) {
                tx.execute(
                    "INSERT INTO _decoded_records VALUES (?,?,?,?,?)",
                    params![source, key, rec, format, json],
                )?;
                decoded += 1;
            }
        }
    }
    // The discrepancy rows name their text by key into the string records.
    let mut strings: HashMap<i64, String> = HashMap::new();
    for (key, rec, data) in &general {
        let Sql::Integer(key) = key else { continue };
        match key {
            14 => {
                if let Some(s) = data.strip_prefix(&[0xFF, 0xFF]).and_then(c_text) {
                    strings.insert(*rec, s);
                }
            }
            22 => {
                for (field, value) in company_info(data) {
                    tx.execute(
                        "INSERT OR IGNORE INTO company_info VALUES (?,?)",
                        params![field, value],
                    )?;
                }
            }
            43 => {
                for date in recon_dates(data, *rec) {
                    tx.execute(
                        "INSERT OR IGNORE INTO recon_history VALUES (?,?,?)",
                        params![rec, account_name(*rec), date],
                    )?;
                }
            }
            301 | 315 => {
                let Some(top) = tagged(data) else { continue };
                let (Some(id), Some(body)) = (top.get(100).and_then(Tagged::int), top.get(103))
                else {
                    continue;
                };
                let text = |v: &Tagged, tag: u8| v.get(tag).and_then(Tagged::text);
                if *key == 301 {
                    tx.execute(
                        "INSERT OR IGNORE INTO bank_feed_accounts VALUES (?,?,?,?,?)",
                        params![
                            id,
                            account_name(id),
                            text(body, 101),
                            text(body, 102),
                            body.get(122).and_then(Tagged::int)
                        ],
                    )?;
                } else if let Some(f) = body.get(1) {
                    tx.execute(
                        "INSERT OR IGNORE INTO bank_feed_institutions
                         VALUES (?,?,?,?,?,?,?,?,?,?)",
                        params![
                            id,
                            text(f, 4),
                            text(f, 5),
                            text(f, 8),
                            text(f, 9),
                            text(f, 10),
                            text(f, 11),
                            text(f, 12),
                            text(f, 15),
                            text(f, 38)
                        ],
                    )?;
                }
            }
            _ => {}
        }
    }
    for (_, rec, data) in &special {
        if *rec != 6 {
            continue;
        }
        let end = data.iter().position(|&c| c == 0).unwrap_or(data.len());
        let text: String = data[..end].iter().map(|&c| c as char).collect();
        for (seq, (version, release, date)) in text.lines().filter_map(version_line).enumerate() {
            tx.execute(
                "INSERT INTO file_versions VALUES (?,?,?,?)",
                params![seq as i64 + 1, version, release, date],
            )?;
        }
    }
    for (_, _, data) in records(tx, "I_RECONCILIATION_DISCREPANCY_TRACKER")? {
        let Some(r) = discrepancy(&data) else {
            continue;
        };
        let s = |key: Option<i64>| key.and_then(|k| strings.get(&k).cloned());
        tx.execute(
            "INSERT INTO recon_discrepancies VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            params![
                r.account_id,
                r.account_id.and_then(&account_name),
                r.statement_date,
                r.target_id,
                r.transaction_id,
                r.transaction_date,
                r.amount,
                s(r.name),
                s(r.doc_num),
                s(r.memo),
                s(r.entered_by),
                r.changed_at,
                s(r.changed_by),
                r.view_type,
                r.change_code
            ],
        )?;
    }
    Ok(decoded)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn json(d: &[u8]) -> String {
        decode_json(d).unwrap().1
    }

    /// A tagged record: id, name, body size and body.
    fn tagged_record(id: u32, body: &[u8]) -> Vec<u8> {
        let mut d = vec![0x64, 0x18];
        d.extend_from_slice(&id.to_le_bytes());
        d.extend_from_slice(&[0x65, 0x18, b'd', b'u', b'm', 0, 0x66, 0x18]);
        d.extend_from_slice(&(body.len() as u32).to_le_bytes());
        d.extend_from_slice(&[0x67, 0x20, body.len() as u8]);
        d.extend_from_slice(body);
        d
    }

    #[test]
    fn tagged_values_of_every_type() {
        let mut body = vec![1, 0x00, 7, 2, 0x08, 0x34, 0x12, 3, 0x10, b'O', b'N', 0];
        body.extend_from_slice(&[4, 0x20, 3, b'h', b'i', 0]);
        body.extend_from_slice(&[5, 0x20, 2, 0xAA, 0xBB]);
        let mut time = vec![3, 0, 0xE8, 0x07, 5, 23, 14, 9, 21];
        time.extend_from_slice(&[0, 0, 0, 0, b'*', b'*', b'*', 0, 0, 0x6E]);
        body.extend_from_slice(&[6, 0x20, 19]);
        body.extend_from_slice(&time);
        assert_eq!(
            json(&tagged_record(16939, &body)),
            "[[100,16939],[101,\"dum\"],[102,45],[103,[[1,7],[2,4660],[3,\"ON\"],\
             [4,\"hi\"],[5,{\"hex\":\"aabb\"}],[6,{\"time\":\"2024-05-23 14:09:21\"}]]]]"
        );
    }

    #[test]
    fn tagged_lists_nest_and_long_values_take_a_u16_length() {
        let inner = [1, 0x00, 1, 5, 0x20, 2, b'x', 0];
        let mut body = vec![9, 0x28, inner.len() as u8, 0];
        body.extend_from_slice(&inner);
        assert_eq!(
            json(&tagged_record(1, &body)),
            "[[100,1],[101,\"dum\"],[102,12],[103,[[9,[[1,1],[5,\"x\"]]]]]]"
        );
    }

    #[test]
    fn a_truncated_tagged_record_is_not_decoded() {
        let d = tagged_record(1, &[4, 0x20, 3, b'h', b'i', 0]);
        assert!(decode_json(&d[..d.len() - 1]).is_none());
    }

    fn field(tag: u16, extra: u16, value: &[u8]) -> Vec<u8> {
        let mut d = vec![5, 7];
        d.extend_from_slice(&tag.to_le_bytes());
        d.extend_from_slice(&(value.len() as u16).to_le_bytes());
        d.extend_from_slice(&extra.to_le_bytes());
        d.extend_from_slice(value);
        d
    }

    fn container(id: u16, items: &[u8]) -> Vec<u8> {
        let mut d = vec![5, 1, 10, 0, 1, 0];
        d.extend_from_slice(&(items.len() as u16 + 10).to_le_bytes());
        d.extend_from_slice(&id.to_le_bytes());
        d.extend_from_slice(items);
        d
    }

    #[test]
    fn blocks_nest_through_fields() {
        let inner = container(2, &field(1, 0, b"Home\0"));
        let mut items = field(6, 1, &[0x95, 0x13]);
        items.extend_from_slice(&field(3, 0, &inner));
        assert_eq!(
            json(&container(168, &items)),
            "[{\"id\":168,\"version\":1,\"items\":[[6,1,{\"hex\":\"9513\"}],\
             [3,0,[{\"id\":2,\"version\":1,\"items\":[[1,0,\"Home\"]]}]]]}]"
        );
    }

    #[test]
    fn company_fields_are_read_at_their_offsets() {
        let mut b = vec![0u8; 2408];
        for (off, s) in [(4, "Example Co"), (208, "Springfield"), (242, "00000")] {
            b[off..off + s.len()].copy_from_slice(s.as_bytes());
        }
        b[2078..2082].copy_from_slice(&[9, 7, 0xDD, 0x07]);
        let d = container(1, &field(1002, 0, &b));
        assert_eq!(
            company_info(&d),
            [
                ("company_name", "Example Co".to_string()),
                ("city", "Springfield".to_string()),
                ("postal_code", "00000".to_string()),
                ("created_date", "2013-07-09".to_string()),
            ]
        );
    }

    #[test]
    fn recon_dates_stop_at_the_first_empty_slot() {
        let mut d = vec![0u8; 492];
        d[..8].copy_from_slice(&[30, 11, 0xE2, 0x07, 2, 10, 0xE2, 0x07]);
        d[480..488].copy_from_slice(&[2, 0, 0, 0, 28, 0, 0, 0]);
        assert_eq!(recon_dates(&d, 28), ["2018-11-30", "2018-10-02"]);
        assert!(recon_dates(&d, 29).is_empty());
    }

    #[test]
    fn a_discrepancy_row_is_read_field_by_field() {
        let mut d = vec![0, 1, 0, 0xED, 0x27, 0, 0, 3, 0, 0x27, 0, 0, 0];
        d.extend_from_slice(&[4, 0, 28, 2, 0xDF, 0x07]);
        d.extend_from_slice(&[5, 0, 0, 0x50, 0x05, 0x3D, 0x80, 0x01, 0, 0x20, 0x31]);
        d.extend_from_slice(&[0x0B, 0, 0x57, 0xEF, 0x83, 0x67, 0x0D, 0, 26, 0, 0xFF, 0xFF]);
        let r = discrepancy(&d).unwrap();
        assert_eq!(r.target_id, Some(10221));
        assert_eq!(r.account_id, Some(39));
        assert_eq!(r.statement_date.as_deref(), Some("2015-02-28"));
        assert_eq!(r.amount.as_deref(), Some("-64464.5"));
        assert_eq!(r.changed_at.as_deref(), Some("2025-01-12 16:35:35"));
        assert_eq!(r.view_type, Some(26));
        assert!(discrepancy(&d[..d.len() - 2]).is_none());
    }

    #[test]
    fn amounts_are_counts_of_a_hundred_thousandth() {
        assert_eq!(
            amount(&[0, 0x40, 0x32, 0x59, 0x02, 0, 0, 0x20, 0xB1]).unwrap(),
            "394"
        );
        assert_eq!(amount(&[0, 0, 0, 0, 0, 0, 0, 0x20, 0x31]).unwrap(), "0");
    }

    #[test]
    fn version_lines() {
        assert_eq!(
            version_line("V23.0D R6 07/09/2013").unwrap(),
            ("V23.0D".into(), "R6".into(), "2013-07-09".into())
        );
        assert!(version_line("build has").is_none());
    }
}
