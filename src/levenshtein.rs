//! Exact bounded unit-cost Levenshtein distance over arbitrary token sequences.
//!
//! The objective here is the classical Levenshtein distance: insert, delete and substitute each cost
//! one. It is deliberately not the indel (LCS) distance of [`crate::lines`], where a substitution
//! costs two, so `[a]` versus `[b]` has distance 2 there. The two distances agree only when no
//! substitution can help. `tests/levenshtein.rs` pins a case where they differ.
//!
//! The entry points are:
//!
//! * [`levenshtein_within`]: the exact distance if it is at most a limit, else `None`.
//! * [`levenshtein`]: the exact distance, found by threshold doubling so the cost follows the distance.
//! * [`levenshtein_within_u32`]: the same as [`levenshtein_within`] for integer token ids.
//!
//! Algorithms (all exact):
//!
//! * a rolling band (Ukkonen's cutoff) of width `2k + 1`, which costs `O(n k)` time and `O(k)` memory;
//! * a full dynamic program, kept as [`levenshtein_full_dp`] and used only as the test oracle.
//!
//! Correctness of the band rests on three facts. First, the distance is at most `max(n, m)`, so a
//! limit above that is clipped to it without changing the answer. Second, cell values are capped at
//! `k + 1`: a true value above `k` stays above `k` under the capped recurrence, and a true value at most
//! `k` has an optimal path whose every prefix cost is at most `k`, so it is computed exactly. Third,
//! `|n - m| <= k` is necessary, because every edit changes the length by at most 1.
//!
//! Common prefix and suffix trimming is valid for unit-cost Levenshtein: for equal first tokens,
//! `lev(xA, xB) = lev(A, B)`, and symmetrically for suffixes. This holds because an optimal alignment
//! can always match a pair of equal first tokens, and the same argument applies to the last tokens. The
//! trimming does not extend to one-sided token elimination, which is not valid: a token absent from the
//! other side can still be substituted for a cost of 1, not 2.

/// Exact unit-cost Levenshtein distance if it is at most `limit`, else `None`.
///
/// Runs in `O(min(n, m) * limit)` time and `O(limit)` space in the worst case, and `O(n + m)` when
/// the lengths differ by more than `limit`. A limit larger than the input lengths costs the same as
/// the full dynamic program. The limit is a `u32`, so the returned distance always fits a `u32`.
pub fn levenshtein_within<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    within_usize(a, b, limit_to_usize(limit)).map(distance_to_u32)
}

/// Exact unit-cost Levenshtein distance.
///
/// Doubles the threshold `1, 2, 4, ...` until the bounded search succeeds, so the cost grows with the
/// distance rather than with the input lengths. The threshold never exceeds `max(n, m)`, where the
/// search is guaranteed to succeed.
///
/// # Panics
///
/// Panics if the distance does not fit in a `u32`. That requires an input longer than `u32::MAX`
/// tokens. Use [`levenshtein_within`] for bounded queries, which never panics on length.
pub fn levenshtein<T: Eq>(a: &[T], b: &[T]) -> u32 {
    let cap = a.len().max(b.len());
    let mut k: usize = 1;
    loop {
        let kk = k.min(cap);
        if let Some(d) = within_usize(a, b, kk) {
            return distance_to_u32(d);
        }
        assert!(kk < cap, "distance is at most the longer input length");
        k = k.saturating_mul(2);
    }
}

/// Full `O(n m)` dynamic program. The reference oracle for the tests, not a fast path.
#[doc(hidden)]
pub fn levenshtein_full_dp<T: Eq>(a: &[T], b: &[T]) -> usize {
    let m = b.len();
    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for (i, ai) in a.iter().enumerate() {
        cur[0] = i + 1;
        for j in 1..=m {
            let sub = prev[j - 1] + usize::from(*ai != b[j - 1]);
            cur[j] = sub.min(prev[j] + 1).min(cur[j - 1] + 1);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

/// The rolling band alone, with the same contract as [`levenshtein_within`]. Exposed for the test
/// suite and the benchmark; use [`levenshtein_within`] in production code.
#[doc(hidden)]
pub fn levenshtein_within_band<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    let (a, b) = trim(a, b);
    let k = limit_to_usize(limit);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return within_usize(a, b, k).map(distance_to_u32);
    }
    band(a, b, k.min(a.len().max(b.len()))).map(distance_to_u32)
}

/// Converts a `u32` limit to `usize`. A limit that a `usize` cannot hold is larger than every
/// representable length, so clamping it to `usize::MAX` preserves the answer.
fn limit_to_usize(limit: u32) -> usize {
    usize::try_from(limit).unwrap_or(usize::MAX)
}

/// Converts a distance that is known to be at most a `u32` limit. Only the top-level callers hold that
/// guarantee, so a failure is a logic error and not a runtime condition.
fn distance_to_u32(d: usize) -> u32 {
    u32::try_from(d).expect("distance is at most the u32 limit or the longer input length")
}

/// Strips the common prefix and suffix. Valid for unit-cost Levenshtein; see the module docs.
fn trim<'a, T: Eq>(a: &'a [T], b: &'a [T]) -> (&'a [T], &'a [T]) {
    let p = a.iter().zip(b).take_while(|(x, y)| x == y).count();
    let (a, b) = (&a[p..], &b[p..]);
    let s = a
        .iter()
        .rev()
        .zip(b.iter().rev())
        .take_while(|(x, y)| x == y)
        .count();
    (&a[..a.len() - s], &b[..b.len() - s])
}

/// Ukkonen's rolling band over the trimmed inputs.
///
/// Row `i` holds `D[i][j]` for `j` in `[i - k, i + k]`, stored at index `c = j - i + k` in a buffer of
/// width `2k + 1`. Two rows are kept, so the memory is `O(k)`. Every stored value is capped at `k + 1`,
/// which stands for "more than `k`". Cells outside the band or the matrix hold the cap. Each row is
/// filled only over the columns `j` in `[0, m]`, so the inner loop has no range checks; the cells
/// outside that range are written with the cap.
fn band<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<usize> {
    match band_rows(a, b, k, usize::MAX) {
        Band::Exact(d) => d,
        Band::Unfinished => unreachable!("an unbounded band always finishes"),
    }
}

/// The result of a band run that may stop early.
enum Band {
    /// The band finished. The distance is `Some(d)` if it is at most `k`.
    Exact(Option<usize>),
    /// The row budget ran out before the band finished.
    Unfinished,
}

/// The band with at most `row_budget` rows. Dissimilar inputs usually empty the band after a few
/// rows, so a small budget often settles them.
fn band_rows<T: Eq>(a: &[T], b: &[T], k: usize, row_budget: usize) -> Band {
    let (n, m) = (a.len(), b.len());
    debug_assert!(n >= 1 && m >= 1 && n.abs_diff(m) <= k && k <= n.max(m));
    let w = 2 * k + 1;
    let cap = k + 1;
    // One extra sentinel cell at index `w` stays at the cap, so `prev[c + 1]` never needs a check.
    let mut prev = vec![cap; w + 1];
    let mut cur = vec![cap; w + 1];
    // Row 0: `D[0][j] = j`, stored at `c = j + k` for `j` in `[0, min(k, m)]`.
    for j in 0..=k.min(m) {
        prev[j + k] = j;
    }
    for i in 1..=n {
        if i > row_budget {
            return Band::Unfinished;
        }
        let ai = &a[i - 1];
        // Columns with `0 <= j <= m` sit at `c` in `[lo, hi]`, where `j = i + c - k`.
        let lo = k.saturating_sub(i);
        let hi = (m + k - i).min(w - 1);
        cur[..lo].fill(cap);
        let mut row_min = cap;
        let mut start = lo;
        if i <= k {
            // `j = 0`: the first column of the matrix, `D[i][0] = i`.
            cur[lo] = i.min(cap);
            row_min = cur[lo];
            start = lo + 1;
        }
        // `left` carries `D[i][j - 1] + 1`. Before the band it is the cap, since that cell is out.
        let mut left = if start == 0 { cap } else { cur[start - 1] + 1 };
        for c in start..=hi {
            let j = i + c - k;
            let sub = prev[c] + usize::from(*ai != b[j - 1]);
            let up = prev[c + 1] + 1;
            let v = sub.min(up).min(left).min(cap);
            cur[c] = v;
            left = v + 1;
            row_min = row_min.min(v);
        }
        cur[hi + 1..=w].fill(cap);
        if row_min >= cap {
            // Every path through this row costs more than `k`, and costs never decrease along a path.
            return Band::Exact(None);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    // After the last swap `prev` is row `n`; `j = m` sits at `c = m + k - n`.
    let d = prev[m + k - n];
    Band::Exact((d <= k).then_some(d))
}

/// Bounded search on `usize` thresholds: `Some(d)` if the distance `d` is at most `k`.
///
/// Dispatches between the rolling band and the bit-parallel kernel by the cost model in
/// [`bit_parallel_pays`]. A pattern whose match table would exceed [`MAX_MASK_WORDS`] words, or whose
/// class lookups would cost more than the band, goes to the band instead. Both kernels are exact, so the
/// choice never changes the answer.
fn within_usize<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<usize> {
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(a.len() + b.len());
    }
    let (p, t) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let k = k.min(t.len());
    let width = 2 * k + 1;
    let blocks = p.len().div_ceil(WORD_BITS);
    // Each class beyond the band width would make the linear class scan cost more than the band.
    if !bit_parallel_pays(blocks, 0, width) {
        return band(a, b, k);
    }
    let max_classes = (MAX_MASK_WORDS / blocks).saturating_sub(1).min(width);
    if let Some((cls, reps)) = classify_scan(p, max_classes) {
        let classes = reps.len();
        let lookup = classes.saturating_mul(LOOKUP_COST);
        if bit_parallel_pays(blocks, lookup, width) {
            let rows = probe_rows(t.len(), blocks, lookup, width);
            if let Band::Exact(d) = band_rows(a, b, k, rows) {
                return d;
            }
            let masks = Masks::new(&cls, classes);
            let class = |x: &T| reps.iter().position(|&r| p[r] == *x).unwrap_or(classes);
            return run_kernel(&masks, p.len(), t, class, k);
        }
    }
    band(a, b, k)
}

/// Rows the band may spend before the bit-parallel kernel is preferred. The budget is a quarter of the
/// bit-parallel work, so a probe that fails costs at most a quarter of the kernel it precedes.
fn probe_rows(text_len: usize, blocks: usize, lookup_cost: usize, width: usize) -> usize {
    let work = text_len.saturating_mul(
        blocks
            .saturating_mul(BLOCK_COST)
            .saturating_add(lookup_cost),
    );
    (work / (4 * width * CELL_COST)).max(1)
}

/// The cost model choosing the bit-parallel kernel over the band, per text token, in quarter-cell units.
///
/// The band spends `width` cell updates of `CELL_COST` units each. The bit-parallel kernel spends
/// `BLOCK_COST` units per 64-bit block plus the `lookup_cost` of the class lookup.
fn bit_parallel_pays(blocks: usize, lookup_cost: usize, width: usize) -> bool {
    blocks
        .saturating_mul(BLOCK_COST)
        .saturating_add(lookup_cost)
        < width.saturating_mul(CELL_COST)
}

const WORD_BITS: usize = 64;
/// Cost of one band cell update, in quarter-cell units. Measured at about 4 ns per cell.
const CELL_COST: usize = 4;
/// Cost of one 64-bit block step. Measured at about 3 ns per block.
const BLOCK_COST: usize = 3;
/// Cost of one class comparison in the generic linear scan. Measured at about 0.6 ns per comparison.
const LOOKUP_COST: usize = 1;
/// Cost of mapping one text token to its class on the integer-id path, dense or sorted.
const U32_LOOKUP_COST: usize = 2;
/// Bound on the match-mask table, in 64-bit words (16 MiB). The table holds `(classes + 1) * blocks`
/// words, so its size is bounded by the pattern length squared over 64, never by the alphabet.
const MAX_MASK_WORDS: usize = 1 << 21;
const HIGH: u64 = 1 << 63;

/// Match masks of a pattern: for each class `c`, the bit `i` of block `b` is set when pattern token `i`
/// (of block `b`) belongs to class `c`. The last class, `classes`, is all zero and serves tokens that
/// occur nowhere in the pattern.
struct Masks {
    blocks: usize,
    rows: Vec<u64>,
}

impl Masks {
    /// Builds the masks from the class of each pattern position. `cls` must be non-empty and every
    /// class must be below `classes`.
    fn new(cls: &[usize], classes: usize) -> Self {
        let blocks = cls.len().div_ceil(WORD_BITS);
        let mut rows = vec![0u64; (classes + 1) * blocks];
        for (i, &c) in cls.iter().enumerate() {
            rows[c * blocks + i / WORD_BITS] |= 1u64 << (i % WORD_BITS);
        }
        Masks { blocks, rows }
    }
}

/// Assigns each pattern position a class by linear scan over one representative per class. Works for
/// any `Eq` token, but a lookup costs one comparison per class. Returns `None` once more than
/// `max_classes` distinct tokens are seen, so the caller can fall back without a full scan.
fn classify_scan<T: Eq>(p: &[T], max_classes: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    let mut reps: Vec<usize> = Vec::new();
    let mut cls = Vec::with_capacity(p.len());
    for (i, x) in p.iter().enumerate() {
        match reps.iter().position(|&r| p[r] == *x) {
            Some(c) => cls.push(c),
            None => {
                if reps.len() >= max_classes {
                    return None;
                }
                cls.push(reps.len());
                reps.push(i);
            }
        }
    }
    Some((cls, reps))
}

/// Runs the single-word kernel when the pattern fits one block, else the multiword kernel.
fn run_kernel<T>(
    masks: &Masks,
    m: usize,
    t: &[T],
    class: impl Fn(&T) -> usize,
    k: usize,
) -> Option<usize> {
    if masks.blocks == 1 {
        myers_single(masks, m, t, class, k)
    } else {
        myers_multi(masks, m, t, class, k)
    }
}

/// Bit-parallel Levenshtein for a pattern of at most 64 tokens (Myers 1999, global form with the
/// top-row horizontal delta fixed to `+1`, as in Hyyro's 2003 formulation).
///
/// Bit `i` of the vertical vectors is the vertical delta of pattern row `i + 1`. The score tracks
/// `D[m][j]`, the bottom cell of column `j`.
fn myers_single<T>(
    masks: &Masks,
    m: usize,
    t: &[T],
    class: impl Fn(&T) -> usize,
    k: usize,
) -> Option<usize> {
    debug_assert!(masks.blocks == 1 && (1..=WORD_BITS).contains(&m));
    let high = 1u64 << (m - 1);
    let (mut pv, mut mv) = (!0u64, 0u64);
    let mut score = m;
    let n = t.len();
    for (j, x) in t.iter().enumerate() {
        let eq = masks.rows[class(x)];
        let xv = eq | mv;
        let xh = (((eq & pv).wrapping_add(pv)) ^ pv) | eq;
        let ph = mv | !(xh | pv);
        let mh = pv & xh;
        if ph & high != 0 {
            score += 1;
        } else if mh & high != 0 {
            score -= 1;
        }
        let ph = (ph << 1) | 1;
        let mh = mh << 1;
        pv = mh | !(xv | ph);
        mv = ph & xv;
        // The bottom cell falls by at most 1 per remaining text token.
        if score.saturating_sub(n - j - 1) > k {
            return None;
        }
    }
    (score <= k).then_some(score)
}

/// Bit-parallel Levenshtein over `masks.blocks` 64-bit blocks (Myers 1999 section 4, Hyyro's block
/// carries). Each block takes the horizontal delta of the block above as its carry-in.
fn myers_multi<T>(
    masks: &Masks,
    m: usize,
    t: &[T],
    class: impl Fn(&T) -> usize,
    k: usize,
) -> Option<usize> {
    let blocks = masks.blocks;
    let last_high = 1u64 << ((m - 1) % WORD_BITS);
    let mut pv = vec![!0u64; blocks];
    let mut mv = vec![0u64; blocks];
    let mut score = m;
    let n = t.len();
    for (j, x) in t.iter().enumerate() {
        let row = class(x) * blocks;
        // The top row has `D[0][j] = j`, so its horizontal delta into block 0 is `+1`.
        let mut carry: i8 = 1;
        let mut delta: i8 = 0;
        for b in 0..blocks {
            let hbit = if b + 1 == blocks { last_high } else { HIGH };
            let (np, nm, cout, d) = block_step(masks.rows[row + b], pv[b], mv[b], carry, hbit);
            pv[b] = np;
            mv[b] = nm;
            carry = cout;
            delta = d;
        }
        match delta {
            1 => score += 1,
            -1 => score -= 1,
            _ => {}
        }
        if score.saturating_sub(n - j - 1) > k {
            return None;
        }
    }
    (score <= k).then_some(score)
}

/// One block of the Myers recurrence. `hin` is the horizontal delta entering the block from above
/// (`-1`, `0` or `+1`). Returns the new vertical vectors, the horizontal delta leaving the block's top
/// bit (`HIGH`, the carry for the next block), and the delta at `hbit` (the bottom row of the matrix
/// when `hbit` is that row).
fn block_step(eq: u64, pv: u64, mv: u64, hin: i8, hbit: u64) -> (u64, u64, i8, i8) {
    let xv = eq | mv;
    let eq = if hin < 0 { eq | 1 } else { eq };
    let xh = (((eq & pv).wrapping_add(pv)) ^ pv) | eq;
    let ph = mv | !(xh | pv);
    let mh = pv & xh;
    let carry = sign_at(ph, mh, HIGH);
    let delta = sign_at(ph, mh, hbit);
    let mut ph = ph << 1;
    let mut mh = mh << 1;
    if hin < 0 {
        mh |= 1;
    } else if hin > 0 {
        ph |= 1;
    }
    let pv = mh | !(xv | ph);
    let mv = ph & xv;
    (pv, mv, carry, delta)
}

/// The horizontal delta at `bit` (`+1`, `0` or `-1`), read from the plus and minus vectors.
fn sign_at(ph: u64, mh: u64, bit: u64) -> i8 {
    if ph & bit != 0 {
        1
    } else if mh & bit != 0 {
        -1
    } else {
        0
    }
}

/// Bit-parallel kernel alone, single-word path, with the contract of [`levenshtein_within`]. The
/// shorter side after trimming is the pattern. A pattern longer than 64 tokens is routed to the
/// multiword kernel. Exposed for the test suite and the benchmark.
#[doc(hidden)]
pub fn levenshtein_within_myers_single<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    bit_parallel_entry(a, b, limit_to_usize(limit))
}

/// Bit-parallel kernel alone, multiword path, with the contract of [`levenshtein_within`]. Exposed for
/// the test suite and the benchmark.
#[doc(hidden)]
pub fn levenshtein_within_myers_multi<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    let k = limit_to_usize(limit);
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let (p, t) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let k = k.min(t.len());
    // No class cap: the table is bounded by the pattern length, which the caller already holds.
    let (cls, reps) =
        classify_scan(p, usize::MAX).expect("classification without a class cap cannot be refused");
    let masks = Masks::new(&cls, reps.len());
    let class = |x: &T| reps.iter().position(|&r| p[r] == *x).unwrap_or(reps.len());
    myers_multi(&masks, p.len(), t, class, k).map(distance_to_u32)
}

fn bit_parallel_entry<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<u32> {
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let (p, t) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let k = k.min(t.len());
    let (cls, reps) =
        classify_scan(p, usize::MAX).expect("classification without a class cap cannot be refused");
    let masks = Masks::new(&cls, reps.len());
    let class = |x: &T| reps.iter().position(|&r| p[r] == *x).unwrap_or(reps.len());
    run_kernel(&masks, p.len(), t, class, k).map(distance_to_u32)
}

/// Bounded search for integer token ids, with the contract of [`levenshtein_within`].
///
/// The classes are the distinct ids of the pattern. Each text token is mapped to its class by a dense
/// table when the ids are small relative to the pattern, and by binary search otherwise. Both lookups
/// are cheaper than the generic class scan, so this path stays bit-parallel for more limits.
pub fn levenshtein_within_u32(a: &[u32], b: &[u32], limit: u32) -> Option<u32> {
    let k = limit_to_usize(limit);
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let (p, t) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let k = k.min(t.len());
    let width = 2 * k + 1;
    let blocks = p.len().div_ceil(WORD_BITS);
    if !bit_parallel_pays(blocks, U32_LOOKUP_COST, width) {
        return band(a, b, k).map(distance_to_u32);
    }
    let rows = probe_rows(t.len(), blocks, U32_LOOKUP_COST, width);
    if let Band::Exact(d) = band_rows(a, b, k, rows) {
        return d.map(distance_to_u32);
    }
    let mut keys = p.to_vec();
    keys.sort_unstable();
    keys.dedup();
    if keys.len() > (MAX_MASK_WORDS / blocks).saturating_sub(1) {
        return band(a, b, k).map(distance_to_u32);
    }
    let classes = keys.len();
    let cls: Vec<usize> = p
        .iter()
        .map(|x| keys.binary_search(x).expect("every pattern id is a key"))
        .collect();
    let masks = Masks::new(&cls, classes);
    let max_key = keys[classes - 1];
    let found = if (max_key as usize) < 4 * p.len() + 256 {
        let mut table = vec![classes; max_key as usize + 1];
        for (c, &key) in keys.iter().enumerate() {
            table[key as usize] = c;
        }
        let class = |x: &u32| table.get(*x as usize).copied().unwrap_or(classes);
        run_kernel(&masks, p.len(), t, class, k)
    } else {
        let class = |x: &u32| keys.binary_search(x).unwrap_or(classes);
        run_kernel(&masks, p.len(), t, class, k)
    };
    found.map(distance_to_u32)
}
