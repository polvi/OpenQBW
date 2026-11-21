//! Closed-form page cipher of a QuickBooks company file.
//!
//! Every page after the superblock is stored as eight 512-byte sectors (the
//! last one holds 496 payload bytes and the 16-byte trailer). Each sector is
//! transformed on its own:
//!
//! ```text
//! q     = 103 - si - pn + 2*(pn & 1) + 32*(pn >> 4)
//! rot   = 149 + ((q - (q & 1)) mod 256) + 2*phase*(q & 1)
//! slope = 5 + 2*(q >> 9) - 4*((pn >> 9) & !8)            (mod 256)
//! step  = slope * rot^-1                                  (mod 256)
//! base  = (pn ^ 0xF1) + si + 167                          (mod 256)
//! stored[(t + rot) mod 512] = plain[t] + base + ((t + rot) mod 512) * step
//! ```
//!
//! `pn` is the page number and `si` the sector index. `phase` is one bit per
//! group of eight pages; it is not derived here, it is recovered from the page
//! number that every page carries in its first four bytes (see
//! [`phase_map`]).
//!
//! The cipher walks a sector with stride `rot`. In the last sector the walk
//! skips the 16 trailer slots, which adds `slope` to the keystream once for
//! each slot still ahead of a position and moves the bytes that would have
//! landed on a trailer slot one more stride along (see [`last_sector`]).
//!
//! After the sectors are restored, 12 bytes of the page header and the 12
//! trailer bytes before the CRC trade places (see [`decode_page`]).
//!
//! The constants come from one QuickBooks 2024 company file, where the page
//! number check passes on every live page. A file they do not fit is
//! reported as [`Error::KeystreamMismatch`](crate::Error::KeystreamMismatch),
//! never decoded on a guess.

/// Bytes in a page.
pub(crate) const PAGE: usize = 4096;
/// Bytes in a sector.
const SECTOR: usize = 512;
/// Payload bytes in the last sector; the trailer takes the other 16.
const LAST: usize = 496;
/// Sectors in a page.
const SECTORS: usize = PAGE / SECTOR;
/// Offset of the 12 trailer bytes that trade places with header bytes.
const TRAILER: usize = 0xFF0;
/// Offset of the CRC, stored as it is.
const CRC: usize = 0xFFC;

/// Keystream parameters of one sector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SectorKey {
    /// Keystream byte at stored offset 0.
    pub(crate) base: u8,
    /// Keystream increment per stored byte.
    pub(crate) step: u8,
    /// Rotation of the plaintext within the sector, and the walk stride.
    pub(crate) rot: usize,
    /// `step * rot` mod 256; the keystream increment per walk step.
    pub(crate) slope: u8,
}

/// Inverse of an odd `x` modulo `2^bits` (`bits` at most 16).
fn inverse(x: u32, bits: u32) -> u32 {
    let mask = (1u32 << bits) - 1;
    // Newton iteration doubles the number of correct low bits each round;
    // an odd x is its own inverse modulo 8.
    let mut y = x & mask;
    for _ in 0..4 {
        y = y.wrapping_mul(2u32.wrapping_sub(x.wrapping_mul(y))) & mask;
    }
    y
}

/// The key of sector `si` of page `pn` under pairing phase `phase`.
pub(crate) fn sector_key(pn: u64, si: usize, phase: bool) -> SectorKey {
    let p = i64::try_from(pn).unwrap_or(i64::MAX);
    let q = 103 - si as i64 - p + 2 * (p & 1) + 32 * (p >> 4);
    let odd = q & 1;
    let rot = 149 + (q - odd).rem_euclid(256) + if phase { 2 * odd } else { 0 };
    let slope = (5 + 2 * (q >> 9) - 4 * ((p >> 9) & !8)).rem_euclid(256) as u8;
    let step = slope.wrapping_mul(inverse(rot as u32, 8) as u8);
    let base = ((p ^ 0xF1) + si as i64 + 167).rem_euclid(256) as u8;
    SectorKey {
        base,
        step,
        rot: rot as usize,
        slope,
    }
}

/// Layout of the last sector for one rotation.
struct LastSector {
    /// Trailer slots still ahead of each stored position in the walk.
    ahead: [u8; LAST],
    /// Stored position of each plaintext offset.
    stored_at: [u16; LAST],
}

/// The walk visits stored positions `rot, 2*rot, ...` modulo 512 and ends on
/// position 0. Positions 496..512 belong to the trailer and are skipped.
fn last_sector(rot: usize) -> LastSector {
    let inv = inverse(rot as u32, 9) as usize;
    let visit = |pos: usize| if pos == 0 { SECTOR } else { pos * inv % SECTOR };
    let mut holes = [0usize; SECTOR - LAST];
    for (j, h) in holes.iter_mut().enumerate() {
        *h = visit(LAST + j);
    }
    let mut ahead = [0u8; LAST];
    for (pos, a) in ahead.iter_mut().enumerate() {
        let k = visit(pos);
        *a = holes.iter().filter(|&&h| h >= k).count() as u8;
    }
    let mut stored_at = [0u16; LAST];
    for (t, s) in stored_at.iter_mut().enumerate() {
        let mut pos = (t + rot) % SECTOR;
        while pos >= LAST {
            pos = (pos + rot) % SECTOR;
        }
        *s = pos as u16;
    }
    LastSector { ahead, stored_at }
}

/// Keystream byte at stored offset `i` of a full sector.
#[inline]
fn stream(key: SectorKey, i: usize) -> u8 {
    key.base.wrapping_add((i as u8).wrapping_mul(key.step))
}

/// Restore one stored page to the SQL Anywhere page it holds.
///
/// A page of zeros was never written and is returned as it is.
pub(crate) fn decode_page(raw: &[u8], pn: u64, phase: bool) -> Vec<u8> {
    let mut out = vec![0u8; PAGE];
    if raw.len() != PAGE || raw.iter().all(|&b| b == 0) {
        out[..raw.len().min(PAGE)].copy_from_slice(&raw[..raw.len().min(PAGE)]);
        return out;
    }
    for si in 0..SECTORS - 1 {
        let key = sector_key(pn, si, phase);
        let a = si * SECTOR;
        for t in 0..SECTOR {
            let i = (t + key.rot) % SECTOR;
            out[a + t] = raw[a + i].wrapping_sub(stream(key, i));
        }
    }
    let key = sector_key(pn, SECTORS - 1, phase);
    let last = last_sector(key.rot);
    let a = (SECTORS - 1) * SECTOR;
    for t in 0..LAST {
        let i = last.stored_at[t] as usize;
        let ks = stream(key, i).wrapping_add(key.slope.wrapping_mul(last.ahead[i]));
        out[a + t] = raw[a + i].wrapping_sub(ks);
    }
    // Header bytes 18..20 and 6..16 hold the last 12 payload bytes of the
    // page; the stored trailer holds the header fields they displaced.
    let mut head = [0u8; 28];
    head.copy_from_slice(&out[..28]);
    out[18..20].copy_from_slice(&raw[TRAILER..TRAILER + 2]);
    out[6..16].copy_from_slice(&raw[TRAILER + 2..CRC]);
    out[TRAILER..TRAILER + 2].copy_from_slice(&head[18..20]);
    out[TRAILER + 2..CRC].copy_from_slice(&head[6..16]);
    out[CRC..].copy_from_slice(&raw[CRC..]);
    out
}

/// `true` when the first four plaintext bytes of the page, read with
/// `phase`, are its own page number.
fn names_itself(raw: &[u8], pn: u64, phase: bool) -> bool {
    let key = sector_key(pn, 0, phase);
    let mut head = [0u8; 4];
    for (t, h) in head.iter_mut().enumerate() {
        let i = (t + key.rot) % SECTOR;
        *h = raw[i].wrapping_sub(stream(key, i));
    }
    u64::from(u32::from_le_bytes(head)) == pn
}

/// Pairing phase of each group of eight pages.
///
/// The phase changes the first sector of an even page, so an even page whose
/// header names its own page number under exactly one phase decides its
/// group. A group with no such page takes the phase of the nearest decided
/// group before it, or after it when there is none before.
pub(crate) fn phase_map(pages: &[u8]) -> Vec<bool> {
    let count = pages.len() / PAGE;
    let groups = count.div_ceil(8);
    let mut votes = vec![(0u32, 0u32); groups];
    for pn in (2..count).step_by(2) {
        let raw = &pages[pn * PAGE..pn * PAGE + SECTOR];
        if raw.iter().all(|&b| b == 0) {
            continue;
        }
        let off = names_itself(raw, pn as u64, false);
        let on = names_itself(raw, pn as u64, true);
        if off != on {
            let v = &mut votes[pn >> 3];
            if on {
                v.1 += 1;
            } else {
                v.0 += 1;
            }
        }
    }
    let mut phase: Vec<Option<bool>> = votes
        .iter()
        .map(|&(off, on)| (off != on).then_some(on > off))
        .collect();
    let mut seen = None;
    for p in &mut phase {
        match *p {
            Some(v) => seen = Some(v),
            None => *p = seen,
        }
    }
    let mut seen = None;
    for p in phase.iter_mut().rev() {
        match *p {
            Some(v) => seen = Some(v),
            None => *p = seen,
        }
    }
    phase.into_iter().map(|p| p.unwrap_or(false)).collect()
}

/// A company file with the page cipher removed.
pub(crate) struct PlainImage {
    bytes: Vec<u8>,
    live: Vec<bool>,
    written: u64,
}

impl PlainImage {
    /// Decode every page of `stored`, the whole file.
    pub(crate) fn decode(stored: &[u8]) -> Self {
        let count = stored.len() / PAGE;
        let phase = phase_map(stored);
        let mut bytes = Vec::with_capacity(count * PAGE);
        let mut live = vec![false; count];
        let mut written = 0;
        bytes.extend_from_slice(&stored[..PAGE.min(stored.len())]);
        for pn in 1..count {
            let raw = &stored[pn * PAGE..(pn + 1) * PAGE];
            let page = decode_page(raw, pn as u64, phase[pn >> 3]);
            if raw.iter().any(|&b| b != 0) {
                written += 1;
                live[pn] = u32::from_le_bytes([page[0], page[1], page[2], page[3]]) as usize == pn;
            }
            bytes.extend_from_slice(&page);
        }
        Self {
            bytes,
            live,
            written,
        }
    }

    /// Pages in the file, the superblock included.
    pub(crate) fn page_count(&self) -> u64 {
        self.live.len() as u64
    }

    /// Pages that hold data (not all zeros), the superblock excluded.
    pub(crate) fn written_pages(&self) -> u64 {
        self.written
    }

    /// Pages whose header names their own page number.
    pub(crate) fn live_pages(&self) -> u64 {
        self.live.iter().filter(|&&l| l).count() as u64
    }

    /// The decoded page `pn`, when its header names its own page number.
    ///
    /// The pages that do not are the checkpoint log at the end of the file,
    /// which holds earlier images of other pages.
    pub(crate) fn page(&self, pn: u64) -> Option<&[u8]> {
        let i = usize::try_from(pn).ok()?;
        if !*self.live.get(i)? {
            return None;
        }
        self.bytes.get(i * PAGE..(i + 1) * PAGE)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Inverse of [`decode_page`], for building test files.
    pub(crate) fn encode_page(plain: &[u8], pn: u64, phase: bool) -> Vec<u8> {
        let mut work = plain.to_vec();
        let mut raw = vec![0u8; PAGE];
        raw[TRAILER..TRAILER + 2].copy_from_slice(&plain[18..20]);
        raw[TRAILER + 2..CRC].copy_from_slice(&plain[6..16]);
        work[18..20].copy_from_slice(&plain[TRAILER..TRAILER + 2]);
        work[6..16].copy_from_slice(&plain[TRAILER + 2..CRC]);
        raw[CRC..].copy_from_slice(&plain[CRC..]);
        for si in 0..SECTORS - 1 {
            let key = sector_key(pn, si, phase);
            let a = si * SECTOR;
            for t in 0..SECTOR {
                let i = (t + key.rot) % SECTOR;
                raw[a + i] = work[a + t].wrapping_add(stream(key, i));
            }
        }
        let key = sector_key(pn, SECTORS - 1, phase);
        let last = last_sector(key.rot);
        let a = (SECTORS - 1) * SECTOR;
        for t in 0..LAST {
            let i = last.stored_at[t] as usize;
            let ks = stream(key, i).wrapping_add(key.slope.wrapping_mul(last.ahead[i]));
            raw[a + i] = work[a + t].wrapping_add(ks);
        }
        raw
    }

    /// A page of pseudo-random bytes that names `pn` in its header.
    pub(crate) fn noise_page(pn: u64) -> Vec<u8> {
        let mut x = 0x9E37_79B9u32 ^ pn as u32;
        let mut page: Vec<u8> = (0..PAGE)
            .map(|_| {
                x = x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                (x >> 24) as u8
            })
            .collect();
        page[..4].copy_from_slice(&(pn as u32).to_le_bytes());
        page
    }

    #[test]
    fn inverse_is_exact_for_every_odd_residue() {
        for x in (1u32..512).step_by(2) {
            assert_eq!(x * inverse(x, 9) % 512, 1, "mod 512, x = {x}");
            assert_eq!((x & 255) * inverse(x, 8) % 256, 1, "mod 256, x = {x}");
        }
    }

    #[test]
    fn step_times_rotation_is_the_slope() {
        for pn in [
            1u64, 2, 255, 256, 425, 511, 512, 4095, 4096, 8191, 8192, 31_000,
        ] {
            for si in 0..SECTORS {
                for phase in [false, true] {
                    let k = sector_key(pn, si, phase);
                    assert_eq!(k.rot % 2, 1);
                    assert!((149..=405).contains(&k.rot));
                    assert_eq!(k.step.wrapping_mul(k.rot as u8), k.slope);
                }
            }
        }
    }

    #[test]
    fn known_sector_keys() {
        // Page 1, sector 0, phase on: q = 103 - 1 + 2 = 104.
        assert_eq!(
            sector_key(1, 0, true),
            SectorKey {
                base: 0xF0u8.wrapping_add(167),
                step: 5u8.wrapping_mul(inverse(253, 8) as u8),
                rot: 253,
                slope: 5,
            }
        );
        // The phase moves only sectors whose q is odd.
        assert_eq!(sector_key(1, 0, false), sector_key(1, 0, true));
        assert_eq!(sector_key(2, 0, false).rot + 2, sector_key(2, 0, true).rot);
    }

    #[test]
    fn last_sector_layout_is_a_permutation() {
        for rot in (149usize..=405).step_by(2) {
            let l = last_sector(rot);
            let mut seen = [false; LAST];
            for &p in &l.stored_at {
                assert!(!seen[p as usize], "rot {rot}: position {p} used twice");
                seen[p as usize] = true;
            }
            assert_eq!(l.ahead[0], 0, "the walk ends on position 0");
            assert!(l.ahead.iter().all(|&a| a <= 16));
        }
    }

    #[test]
    fn decode_inverts_encode() {
        for pn in [
            1u64, 2, 3, 168, 169, 425, 680, 1536, 1957, 4097, 20_304, 31_348,
        ] {
            for phase in [false, true] {
                let plain = noise_page(pn);
                let raw = encode_page(&plain, pn, phase);
                assert_eq!(
                    decode_page(&raw, pn, phase),
                    plain,
                    "page {pn}, phase {phase}"
                );
            }
        }
    }

    #[test]
    fn unwritten_page_stays_zero() {
        assert!(decode_page(&[0u8; PAGE], 7, false).iter().all(|&b| b == 0));
    }

    #[test]
    fn phase_is_recovered_per_group_and_fills_gaps() {
        // Groups 0 and 1 phase on, group 2 unwritten, group 3 phase off.
        let mut file = vec![0u8; PAGE * 32];
        for pn in 1u64..32 {
            let phase = match pn >> 3 {
                0 | 1 => true,
                2 => continue,
                _ => false,
            };
            let raw = encode_page(&noise_page(pn), pn, phase);
            file[pn as usize * PAGE..(pn as usize + 1) * PAGE].copy_from_slice(&raw);
        }
        assert_eq!(phase_map(&file), [true, true, true, false]);
        let image = PlainImage::decode(&file);
        assert_eq!(image.page_count(), 32);
        assert_eq!(image.written_pages(), 23);
        assert_eq!(image.live_pages(), 23);
        assert_eq!(image.page(9).unwrap(), &noise_page(9)[..]);
        assert!(image.page(16).is_none(), "unwritten page");
    }

    #[test]
    fn a_page_that_names_another_page_is_not_live() {
        // A checkpoint-log page: an image of page 5 stored at position 9.
        let mut file = vec![0u8; PAGE * 16];
        for pn in 1u64..16 {
            let plain = if pn == 9 {
                noise_page(5)
            } else {
                noise_page(pn)
            };
            let raw = encode_page(&plain, pn, false);
            file[pn as usize * PAGE..(pn as usize + 1) * PAGE].copy_from_slice(&raw);
        }
        let image = PlainImage::decode(&file);
        assert!(image.page(9).is_none());
        assert_eq!(image.live_pages(), 14);
        assert_eq!(image.written_pages(), 15);
    }
}
