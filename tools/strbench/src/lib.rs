//! Harness for comparing unit-cost Levenshtein implementations on identical inputs.
//!
//! Every tool is exposed through [`Answer`]-returning adapters:
//!
//! * [`edlib`] wraps Edlib's global (NW) distance mode, reached through the C shim in
//!   `csrc/shim.cpp`. It takes byte strings, so it only accepts symbols below 256.
//! * [`wfa`] wraps WFA2-lib in `edit` (Levenshtein) mode with heuristics disabled and
//!   score-only computation. It also takes byte strings.
//! * [`rapidfuzz`] wraps the `rapidfuzz` crate's Levenshtein distance with uniform
//!   weights (1, 1, 1). It accepts any hashable slice, including sparse `u32` symbols.
//! * [`difffold`] calls difffold's kernel from `src/levenshtein.rs`, compiled from the
//!   repository. It accepts any `Eq` token type, so sparse `u32` ids are supported.
//!
//! The oracles here are independent of all three libraries. [`oracle_full`] is the
//! two-row Wagner-Fischer dynamic program and [`oracle_bounded`] is a banded version
//! that is exact for every distance up to its bound.

use std::cmp::min;

use rapidfuzz::distance::levenshtein;

#[cfg(not(strbench_no_externals))]
mod ffi {
    extern "C" {
        pub fn sb_edlib(a: *const u8, an: usize, b: *const u8, bn: usize, k: i64) -> i64;
        pub fn sb_wfa(a: *const u8, an: usize, b: *const u8, bn: usize, max_steps: i64) -> i64;
    }
}

/// Result of a Levenshtein query: the exact distance, or a report that it exceeds the bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answer {
    Dist(usize),
    Exceeds,
}

/// Exact distance with no bound.
#[cfg(not(strbench_no_externals))]
pub fn edlib(a: &[u8], b: &[u8], k: Option<usize>) -> Answer {
    let bound = k.map_or(-1, |k| i64::try_from(k).expect("bound fits in i64"));
    // SAFETY: slices are valid for their lengths for the duration of the call, and the
    // shim does not retain the pointers.
    let r = unsafe { ffi::sb_edlib(a.as_ptr(), a.len(), b.as_ptr(), b.len(), bound) };
    decode("edlib", r)
}

/// WFA2-lib in edit mode, score only, heuristics off. `k` caps the wavefront steps.
#[cfg(not(strbench_no_externals))]
pub fn wfa(a: &[u8], b: &[u8], k: Option<usize>) -> Answer {
    let bound = k.map_or(-1, |k| i64::try_from(k).expect("bound fits in i64"));
    // SAFETY: as in `edlib`.
    let r = unsafe { ffi::sb_wfa(a.as_ptr(), a.len(), b.as_ptr(), b.len(), bound) };
    decode("wfa", r)
}

/// Stub used when the external sources are absent. The bench never calls it, since it reports the
/// tool as `not-built` first.
#[cfg(strbench_no_externals)]
pub fn edlib(_a: &[u8], _b: &[u8], _k: Option<usize>) -> Answer {
    panic!("edlib is not built in this run (STRBENCH_EXT was not set)")
}

/// Stub used when the external sources are absent. See [`edlib`].
#[cfg(strbench_no_externals)]
pub fn wfa(_a: &[u8], _b: &[u8], _k: Option<usize>) -> Answer {
    panic!("wfa is not built in this run (STRBENCH_EXT was not set)")
}

/// RapidFuzz Levenshtein distance with uniform weights.
pub fn rapidfuzz(a: &[u32], b: &[u32], k: Option<usize>) -> Answer {
    match k {
        None => Answer::Dist(levenshtein::distance(a, b)),
        Some(k) => {
            let args = levenshtein::Args::default().score_cutoff(k);
            match levenshtein::distance_with_args(a, b, &args) {
                Some(d) => Answer::Dist(d),
                None => Answer::Exceeds,
            }
        }
    }
}

/// The difffold kernel, included from the repository source so the harness times the same code.
#[path = "../../../src/levenshtein.rs"]
pub mod difffold_levenshtein;

/// difffold exact distance, found by threshold doubling inside the kernel.
pub fn difffold(a: &[u32], b: &[u32], k: Option<usize>) -> Answer {
    match k {
        None => Answer::Dist(difffold_levenshtein::levenshtein(a, b) as usize),
        Some(k) => {
            let limit = u32::try_from(k).expect("bound fits in u32");
            match difffold_levenshtein::levenshtein_within_u32(a, b, limit) {
                Some(d) => Answer::Dist(d as usize),
                None => Answer::Exceeds,
            }
        }
    }
}

/// Byte values WFA2-lib can use for symbols. Its ASCII kernels use `'!'` and `'?'` as the
/// pattern and text end sentinels, so a symbol equal to the other side's sentinel makes
/// extension run past the end and return wrong results. Both bytes are excluded.
const WFA_SAFE_BYTES: [u8; 253] = {
    let mut out = [0u8; 253];
    let mut i = 0;
    let mut v: u16 = 1;
    while i < 253 {
        if v != b'!' as u16 && v != b'?' as u16 {
            out[i] = v as u8;
            i += 1;
        }
        v += 1;
    }
    out
};

/// Maps dense symbol ids to the byte values Edlib reads. Ids must be below 256, and the map is the identity.
pub fn edlib_bytes(symbols: &[u32]) -> Option<Vec<u8>> {
    symbols.iter().map(|&x| u8::try_from(x).ok()).collect()
}

/// Maps dense symbol ids to bytes WFA2-lib can read without hitting its sentinels. The map is
/// injective, so equality between symbols is preserved. Returns `None` for ids outside
/// `0..253`, which covers dense 256-symbol alphabets and sparse ids.
pub fn wfa_bytes(symbols: &[u32]) -> Option<Vec<u8>> {
    symbols
        .iter()
        .map(|&x| WFA_SAFE_BYTES.get(usize::try_from(x).ok()?).copied())
        .collect()
}

#[cfg(not(strbench_no_externals))]
fn decode(tool: &str, r: i64) -> Answer {
    match r {
        -1 => Answer::Exceeds,
        -2 => panic!("{tool} reported an internal error"),
        d if d >= 0 => Answer::Dist(usize::try_from(d).expect("non-negative")),
        other => panic!("{tool} returned unexpected code {other}"),
    }
}

/// Full Wagner-Fischer dynamic program with two rows. Quadratic, used for small pairs.
pub fn oracle_full(a: &[u32], b: &[u32]) -> usize {
    let m = b.len();
    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for (i, &ca) in a.iter().enumerate() {
        cur[0] = i + 1;
        for j in 1..=m {
            let sub = prev[j - 1] + usize::from(ca != b[j - 1]);
            cur[j] = min(sub, min(prev[j] + 1, cur[j - 1] + 1));
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

const INF: usize = usize::MAX / 4;

/// Banded dynamic program restricted to diagonals `|i - j| <= k`.
///
/// Any alignment of cost at most `k` stays inside that band, so the banded value is the
/// exact distance whenever it is at most `k`. Otherwise the true distance exceeds `k`.
/// Cost is `O(n * k)` time and `O(m)` memory.
pub fn oracle_bounded(a: &[u32], b: &[u32], k: usize) -> Answer {
    let (n, m) = (a.len(), b.len());
    if n.abs_diff(m) > k {
        return Answer::Exceeds;
    }
    if n == 0 {
        return if m <= k {
            Answer::Dist(m)
        } else {
            Answer::Exceeds
        };
    }
    if m == 0 {
        return if n <= k {
            Answer::Dist(n)
        } else {
            Answer::Exceeds
        };
    }
    let mut prev = vec![INF; m + 1];
    let mut cur = vec![INF; m + 1];
    for (j, slot) in prev.iter_mut().enumerate().take(min(m, k) + 1) {
        *slot = j;
    }
    for i in 1..=n {
        let lo = i.saturating_sub(k);
        let hi = min(m, i + k);
        // The previous row was valid only up to `min(m, i - 1 + k)`. Any cell past that point
        // must read as unreachable.
        if hi > min(m, i - 1 + k) {
            prev[hi] = INF;
        }
        for j in lo..=hi {
            if j == 0 {
                cur[0] = i;
                continue;
            }
            let sub = prev[j - 1] + usize::from(a[i - 1] != b[j - 1]);
            let mut best = min(sub, prev[j] + 1);
            if j > lo {
                best = min(best, cur[j - 1] + 1);
            }
            cur[j] = best;
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    let d = prev[m];
    if d <= k {
        Answer::Dist(d)
    } else {
        Answer::Exceeds
    }
}

/// Exact distance by bound doubling over [`oracle_bounded`].
///
/// Returns `None` when the work would exceed `budget` cell updates, so callers can fall back
/// to cross-tool consensus instead of spending quadratic time.
pub fn oracle_exact(a: &[u32], b: &[u32], budget: u64) -> Option<usize> {
    let (n, m) = (a.len(), b.len());
    if (n as u64 + 1) * (m as u64 + 1) <= 4_000_000 {
        return Some(oracle_full(a, b));
    }
    let mut k = n.abs_diff(m).max(1);
    loop {
        let cells = (n as u64) * (2 * k as u64 + 1);
        if cells > budget {
            return None;
        }
        if let Answer::Dist(d) = oracle_bounded(a, b, k) {
            return Some(d);
        }
        if k >= n.max(m) {
            return Some(oracle_full(a, b));
        }
        k = k.saturating_mul(2);
    }
}

/// Small deterministic PRNG (SplitMix64). Avoids a `rand` dependency.
#[derive(Clone)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform value in `0..n`. `n` must be non-zero.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// Symbol table: dense ids `0..sigma`, or `sparse` random `u32` ids that are all at least 256.
pub fn alphabet(rng: &mut Rng, sigma: usize, sparse: bool) -> Vec<u32> {
    if !sparse {
        return (0..sigma as u32).collect();
    }
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(sigma);
    while out.len() < sigma {
        let v = (rng.next_u64() as u32) | 0x100;
        if seen.insert(v) {
            out.push(v);
        }
    }
    out
}

pub fn random_seq(rng: &mut Rng, len: usize, symbols: &[u32]) -> Vec<u32> {
    (0..len)
        .map(|_| symbols[rng.below(symbols.len())])
        .collect()
}

/// Applies `edits` random unit edits (substitution, insertion or deletion) to `seq`, with
/// positions drawn from `lo..hi` of the current sequence.
pub fn mutate(
    rng: &mut Rng,
    seq: &[u32],
    edits: usize,
    symbols: &[u32],
    lo: usize,
    hi: usize,
) -> Vec<u32> {
    let mut s = seq.to_vec();
    for _ in 0..edits {
        let hi_now = hi.min(s.len());
        let lo_now = lo.min(hi_now);
        let pos = lo_now + rng.below((hi_now - lo_now).max(1));
        match rng.below(3) {
            0 if pos < s.len() => s[pos] = symbols[rng.below(symbols.len())],
            1 => s.insert(pos.min(s.len()), symbols[rng.below(symbols.len())]),
            _ if pos < s.len() => {
                s.remove(pos);
            }
            _ => s.push(symbols[rng.below(symbols.len())]),
        }
    }
    s
}

/// Pair regimes used by the bench matrix. The designed edit count is the target; the
/// realized distance can be smaller when random edits cancel out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Regime {
    /// Designed distance `k / 2`, so `d < k`.
    Below,
    /// Designed distance `k`.
    Equal,
    /// Designed distance `k + 1`.
    AboveOne,
    /// Designed distance `8k` (capped at `n / 2`), so `d >> k`.
    Far,
    /// Two edits in the middle third, leaving long identical prefix and suffix.
    Tiny,
    /// Two independent random sequences.
    Unrelated,
    /// Sixteen edits anywhere in the sequence. Used by the exact-distance job, where no bound applies.
    Mid16,
}

impl Regime {
    pub fn name(self) -> &'static str {
        match self {
            Regime::Below => "d<k",
            Regime::Equal => "d==k",
            Regime::AboveOne => "d==k+1",
            Regime::Far => "d>>k",
            Regime::Tiny => "tiny-prefix-suffix",
            Regime::Unrelated => "unrelated",
            Regime::Mid16 => "d=16",
        }
    }

    /// Designed edit count for the bounded job at bound `k` and length `n`.
    pub fn designed_d(self, n: usize, k: usize) -> Option<usize> {
        match self {
            Regime::Below => Some(k / 2),
            Regime::Equal => Some(k),
            Regime::AboveOne => Some(k + 1),
            Regime::Far => {
                let d = (8 * k).min(n / 2);
                (d >= 2 * k).then_some(d)
            }
            Regime::Tiny => Some(2),
            Regime::Unrelated => None,
            Regime::Mid16 => Some(16),
        }
    }
}

/// Builds one `(a, b)` pair for a regime. `designed` is the edit count to apply.
pub fn make_pair(
    rng: &mut Rng,
    regime: Regime,
    n: usize,
    designed: usize,
    symbols: &[u32],
) -> (Vec<u32>, Vec<u32>) {
    let a = random_seq(rng, n, symbols);
    let b = match regime {
        Regime::Unrelated => random_seq(rng, n, symbols),
        Regime::Tiny => {
            let lo = n / 3;
            let hi = (2 * n) / 3;
            mutate(rng, &a, designed, symbols, lo, hi.max(lo + 1))
        }
        _ => mutate(rng, &a, designed, symbols, 0, n),
    };
    (a, b)
}
