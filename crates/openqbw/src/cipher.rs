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
//! (`pn >> 9`, `q >> 9`); it only matters where `q` is odd. It is not derived
//! here, it is recovered from the page number that every page carries in its
//! first four bytes (see [`Phase::learn`]).
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

use std::collections::BTreeMap;

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

/// `q` of sector `si` of page `pn`; the key is a function of it and of `pn`.
fn q_of(pn: u64, si: usize) -> i64 {
    let p = i64::try_from(pn).unwrap_or(i64::MAX);
    103 - si as i64 - p + 2 * (p & 1) + 32 * (p >> 4)
}

/// The phase bit of the page cipher.
///
/// No rule for it is known. On the file it was derived from it is constant
/// over each (`pn >> 9`, `q >> 9`): it changes at page numbers 1536, 2048,
/// 4096 and 8192 and, inside page 1956, where `q` passes 2048.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Phase {
    /// The same bit everywhere.
    #[cfg_attr(not(test), allow(dead_code))]
    Fixed(bool),
    /// One bit per (`pn >> 9`, `q >> 9`), as learned from a file.
    Learned(BTreeMap<(i64, i64), bool>),
}

impl Phase {
    /// The bit for a sector of page `pn` whose `q` is `q`.
    ///
    /// A pair the file gave no evidence for takes the bit of the nearest
    /// `pn >> 9` with the same `(q >> 9) - (pn >> 9)`, then of any pair with
    /// the same `pn >> 9`, then 0.
    fn at(&self, pn: u64, q: i64) -> bool {
        let map = match self {
            Self::Fixed(bit) => return *bit,
            Self::Learned(map) => map,
        };
        let n = i64::try_from(pn >> 9).unwrap_or(i64::MAX);
        let c = q >> 9;
        if let Some(&bit) = map.get(&(n, c)) {
            return bit;
        }
        let span = map.keys().next_back().map_or(0, |k| k.0.max(n)) + 1;
        for d in 1..=span {
            for other in [n - d, n + d] {
                if let Some(&bit) = map.get(&(other, other + c - n)) {
                    return bit;
                }
            }
        }
        map.range((n, i64::MIN)..=(n, i64::MAX))
            .next()
            .is_some_and(|(_, &bit)| bit)
    }

    /// Learn the bit from the even pages of `pages`, the whole stored file.
    ///
    /// Sector 0 of an even page has odd `q`, so its key depends on the bit;
    /// a page whose header names its own page number under exactly one
    /// value of the bit votes for it.
    pub(crate) fn learn(pages: &[u8]) -> Self {
        let mut votes: BTreeMap<(i64, i64), (u32, u32)> = BTreeMap::new();
        for pn in (2..pages.len() / PAGE).step_by(2) {
            let raw = &pages[pn * PAGE..pn * PAGE + SECTOR];
            if raw.iter().all(|&b| b == 0) {
                continue;
            }
            let pn = pn as u64;
            let off = names_itself(raw, pn, false);
            let on = names_itself(raw, pn, true);
            if off != on {
                let v = votes
                    .entry(((pn >> 9) as i64, q_of(pn, 0) >> 9))
                    .or_default();
                if on {
                    v.1 += 1;
                } else {
                    v.0 += 1;
                }
            }
        }
        Self::Learned(
            votes
                .into_iter()
                .filter(|&(_, (off, on))| off != on)
                .map(|(k, (off, on))| (k, on > off))
                .collect(),
        )
    }
}

/// The key of sector `si` of page `pn`.
pub(crate) fn sector_key(pn: u64, si: usize, phase: &Phase) -> SectorKey {
    let p = i64::try_from(pn).unwrap_or(i64::MAX);
    let q = q_of(pn, si);
    let odd = q & 1;
    let lift = if odd == 1 && phase.at(pn, q) { 2 } else { 0 };
    let rot = 149 + (q - odd).rem_euclid(256) + lift;
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
pub(crate) fn decode_page(raw: &[u8], pn: u64, phase: &Phase) -> Vec<u8> {
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

/// `true` when the first four plaintext bytes of the page, read with the
/// phase bit `bit`, are its own page number.
fn names_itself(raw: &[u8], pn: u64, bit: bool) -> bool {
    let key = sector_key(pn, 0, &Phase::Fixed(bit));
    let mut head = [0u8; 4];
    for (t, h) in head.iter_mut().enumerate() {
        let i = (t + key.rot) % SECTOR;
        *h = raw[i].wrapping_sub(stream(key, i));
    }
    u64::from(u32::from_le_bytes(head)) == pn
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
        let phase = Phase::learn(stored);
        let mut bytes = Vec::with_capacity(count * PAGE);
        let mut live = vec![false; count];
        let mut written = 0;
        bytes.extend_from_slice(&stored[..PAGE.min(stored.len())]);
        for pn in 1..count {
            let raw = &stored[pn * PAGE..(pn + 1) * PAGE];
            let page = decode_page(raw, pn as u64, &phase);
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

    const ON: Phase = Phase::Fixed(true);
    const OFF: Phase = Phase::Fixed(false);

    /// Inverse of [`decode_page`], for building test files.
    pub(crate) fn encode_page(plain: &[u8], pn: u64, phase: &Phase) -> Vec<u8> {
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
                    let k = sector_key(pn, si, &Phase::Fixed(phase));
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
            sector_key(1, 0, &ON),
            SectorKey {
                base: 0xF0u8.wrapping_add(167),
                step: 5u8.wrapping_mul(inverse(253, 8) as u8),
                rot: 253,
                slope: 5,
            }
        );
        // The phase moves only sectors whose q is odd.
        assert_eq!(sector_key(1, 0, &OFF), sector_key(1, 0, &ON));
        assert_eq!(sector_key(2, 0, &OFF).rot + 2, sector_key(2, 0, &ON).rot);
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
                let phase = Phase::Fixed(phase);
                let plain = noise_page(pn);
                let raw = encode_page(&plain, pn, &phase);
                assert_eq!(decode_page(&raw, pn, &phase), plain, "page {pn}, {phase:?}");
            }
        }
    }

    #[test]
    fn unwritten_page_stays_zero() {
        assert!(decode_page(&[0u8; PAGE], 7, &OFF).iter().all(|&b| b == 0));
    }

    /// The bit as it lies on the file the cipher was derived from, for the
    /// pairs the tests touch.
    fn sample_phase() -> Phase {
        Phase::Learned(BTreeMap::from([
            ((0, 0), true),
            ((1, 1), true),
            ((3, 3), false),
            ((3, 4), true),
            ((4, 4), false),
        ]))
    }

    #[test]
    fn phase_can_change_inside_a_page() {
        // Page 1956: q runs 2051 down to 2044, so sectors 0 and 2 (q 2051,
        // 2049) lie in pair (3, 4) and sectors 4 and 6 (q 2047, 2045) in
        // pair (3, 3).
        let phase = sample_phase();
        let rot = |si, p: &Phase| sector_key(1956, si, p).rot;
        assert_eq!(rot(0, &phase), rot(0, &ON));
        assert_eq!(rot(2, &phase), rot(2, &ON));
        assert_eq!(rot(4, &phase), rot(4, &OFF));
        assert_eq!(rot(6, &phase), rot(6, &OFF));
        assert_ne!(rot(4, &ON), rot(4, &OFF));
        let plain = noise_page(1956);
        let raw = encode_page(&plain, 1956, &phase);
        assert_eq!(decode_page(&raw, 1956, &phase), plain);
        assert_ne!(decode_page(&raw, 1956, &ON), plain);
        assert_ne!(decode_page(&raw, 1956, &OFF), plain);
    }

    #[test]
    fn phase_is_learned_from_even_pages() {
        let truth = sample_phase();
        let mut file = vec![0u8; PAGE * 2060];
        // One even page in each pair, and page 1957 to decode afterwards.
        for pn in [2u64, 600, 1540, 1956, 1957, 1962, 2050] {
            let raw = encode_page(&noise_page(pn), pn, &truth);
            file[pn as usize * PAGE..(pn as usize + 1) * PAGE].copy_from_slice(&raw);
        }
        assert_eq!(Phase::learn(&file), truth);
        let image = PlainImage::decode(&file);
        assert_eq!(image.page_count(), 2060);
        assert_eq!(image.written_pages(), 7);
        assert_eq!(image.live_pages(), 7);
        assert_eq!(image.page(1956).unwrap(), &noise_page(1956)[..]);
        assert_eq!(image.page(1957).unwrap(), &noise_page(1957)[..]);
        assert!(image.page(16).is_none(), "unwritten page");
    }

    #[test]
    fn unseen_pairs_take_the_nearest_evidence() {
        let phase = sample_phase();
        // Seen.
        assert!(phase.at(1956, 2051));
        assert!(!phase.at(1956, 2047));
        // (2, 2) is unseen: nearest page superblock with q in the same one.
        assert!(phase.at(1100, 1100));
        // (5, 5): nearest is (4, 4).
        assert!(!phase.at(2600, 2600));
        // (4, 5): the nearest with q one superblock ahead is (3, 4).
        assert!(phase.at(2500, 2600));
        // Nothing learned at all.
        assert!(!Phase::Learned(BTreeMap::new()).at(10, 100));
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
            let raw = encode_page(&plain, pn, &OFF);
            file[pn as usize * PAGE..(pn as usize + 1) * PAGE].copy_from_slice(&raw);
        }
        let image = PlainImage::decode(&file);
        assert!(image.page(9).is_none());
        assert_eq!(image.live_pages(), 14);
        assert_eq!(image.written_pages(), 15);
    }
}
