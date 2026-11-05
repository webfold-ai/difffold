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
//! * [`levenshtein_within_u32`]: the same as [`levenshtein_within`] for integer token ids, with a symbol
//!   count lower bound that rejects unrelated inputs before any kernel runs.
//!
//! Kernels (all exact):
//!
//! * a furthest-reaching wavefront over diagonals, which costs `O((k + 1)^2)` diagonal steps plus match
//!   extension, so it is cheap for small distances and for short bounds on unrelated input;
//! * a rolling band (Ukkonen's cutoff) of width `2k + 1`, which costs `O(n k)` time and `O(k)` memory;
//! * a bit-parallel kernel (Myers 1999, Hyyro's block carries). Patterns of up to 64 tokens use one
//!   word. Longer patterns use only the blocks that hold a row of the band `|i - j| <= k`, so a column
//!   costs `O(k / 64)` blocks;
//! * a full dynamic program, kept as [`levenshtein_full_dp`] and used only as the test oracle.
//!
//! [`choose_kernel`] picks the cheapest of the three by a cost model. The constants are fitted on one
//! machine and are not portable. Every kernel is exact, so the choice never changes the answer.
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
/// The cost is that of the cheapest kernel for the inputs and the limit. It is `O(n + m)` when the
/// lengths differ by more than `limit`, `O((limit + 1)^2)` plus match extension when the wavefront is
/// cheapest, and at most `O(min(n, m) * limit)` for the band. The limit is a `u32`, so the returned
/// distance always fits a `u32`.
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
        return Some(distance_to_u32(a.len() + b.len()));
    }
    band(a, b, k.min(a.len().max(b.len()))).map(distance_to_u32)
}

/// The wavefront alone, with the contract of [`levenshtein_within`]. Exposed for the test suite and the
/// benchmark.
#[doc(hidden)]
pub fn levenshtein_within_wavefront<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    let k = limit_to_usize(limit);
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let k = k.min(a.len().max(b.len()));
    wavefront(a, b, k).map(distance_to_u32)
}

/// Bit-parallel kernel alone, single-word path, with the contract of [`levenshtein_within`]. The
/// shorter side after trimming is the pattern. A pattern longer than 64 tokens is routed to the banded
/// multiword kernel. Exposed for the test suite and the benchmark.
#[doc(hidden)]
pub fn levenshtein_within_myers_single<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    bit_parallel_entry(a, b, limit_to_usize(limit), |masks, p, t, class, k| {
        run_kernel(masks, p.len(), t, class, k)
    })
}

/// Bit-parallel kernel alone, full multiword path (every block in every column), with the contract of
/// [`levenshtein_within`]. Exposed for the test suite and the benchmark.
#[doc(hidden)]
pub fn levenshtein_within_myers_multi<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    bit_parallel_entry(a, b, limit_to_usize(limit), |masks, p, t, class, k| {
        myers_multi(masks, p.len(), t, class, k)
    })
}

/// Bit-parallel kernel alone, banded multiword path, with the contract of [`levenshtein_within`].
/// Exposed for the test suite and the benchmark.
#[doc(hidden)]
pub fn levenshtein_within_myers_banded<T: Eq>(a: &[T], b: &[T], limit: u32) -> Option<u32> {
    bit_parallel_entry(a, b, limit_to_usize(limit), |masks, p, t, class, k| {
        myers_banded(masks, p.len(), t, class, k)
    })
}

/// Bounded search for integer token ids, with the contract of [`levenshtein_within`].
///
/// Adds a symbol-count lower bound before the band or bit-parallel kernels, so unrelated inputs with a
/// wide bound are rejected in linear time. The classes of the bit-parallel kernel are the distinct ids
/// of the pattern. Each text token is mapped to its class by a dense table when the ids are small
/// relative to the pattern, and by binary search otherwise.
pub fn levenshtein_within_u32(a: &[u32], b: &[u32], limit: u32) -> Option<u32> {
    let k = limit_to_usize(limit);
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let (p, t) = orient(a, b);
    let k = k.min(t.len());
    let blocks = p.len().div_ceil(WORD_BITS);
    match choose_kernel(k, blocks, t.len(), Some(U32_LOOKUP_COST)) {
        Kernel::Wavefront => wavefront(a, b, k).map(distance_to_u32),
        Kernel::Band => {
            if histogram_lower_bound_u32(p, t) > k {
                return None;
            }
            band(a, b, k).map(distance_to_u32)
        }
        Kernel::BitParallel => {
            if histogram_lower_bound_u32(p, t) > k {
                return None;
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
    }
}

/// Lower bound on the unit-cost Levenshtein distance of two `u32` sequences: the total excess of symbol
/// counts, `sum over symbols of max(0, count_a - count_b)`, taken over `a` against `b`.
///
/// Every edit (insert, delete or substitute) changes this excess by at most one, and the excess of two
/// equal multisets is zero. So after `d` edits the excess is at most `d` away from zero, which means
/// `d` is at least the excess. Dense ids are counted in linear time, and sparse ids by sorting.
#[doc(hidden)]
pub fn histogram_lower_bound_u32(a: &[u32], b: &[u32]) -> usize {
    let max = a.iter().chain(b).copied().max().unwrap_or(0) as usize;
    if max < 4 * (a.len() + b.len()) + 256 {
        let mut count = vec![0isize; max + 1];
        for &x in a {
            count[x as usize] += 1;
        }
        for &y in b {
            count[y as usize] -= 1;
        }
        count.iter().filter(|&&c| c > 0).map(|&c| c as usize).sum()
    } else {
        let mut sa = a.to_vec();
        let mut sb = b.to_vec();
        sa.sort_unstable();
        sb.sort_unstable();
        let mut excess = 0;
        let mut i = 0;
        while i < sa.len() {
            let x = sa[i];
            let run_end = i + sa[i..].partition_point(|&y| y == x);
            let in_b = sb.partition_point(|&y| y < x);
            let in_b_end = in_b + sb[in_b..].partition_point(|&y| y == x);
            excess += (run_end - i).saturating_sub(in_b_end - in_b);
            i = run_end;
        }
        excess
    }
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

/// Orders two trimmed inputs as (shorter, longer). The shorter side is the bit-parallel pattern.
fn orient<'a, T>(a: &'a [T], b: &'a [T]) -> (&'a [T], &'a [T]) {
    if a.len() <= b.len() {
        (a, b)
    } else {
        (b, a)
    }
}

/// Strips the common prefix and suffix. Valid for unit-cost Levenshtein; see the module docs.
fn trim<'a, T: Eq>(a: &'a [T], b: &'a [T]) -> (&'a [T], &'a [T]) {
    let p = extend(a, b, 0, 0);
    let (a, b) = (&a[p..], &b[p..]);
    let s = common_suffix(a, b);
    (&a[..a.len() - s], &b[..b.len() - s])
}

/// Length of the common suffix of `a` and `b`, compared in chunks like [`extend`].
fn common_suffix<T: Eq>(a: &[T], b: &[T]) -> usize {
    let max = a.len().min(b.len());
    let (x, y) = (&a[a.len() - max..], &b[b.len() - max..]);
    let mut l = 0;
    while l + EXT_CHUNK <= max && x[max - l - EXT_CHUNK..max - l] == y[max - l - EXT_CHUNK..max - l]
    {
        l += EXT_CHUNK;
    }
    while l < max && x[max - l - 1] == y[max - l - 1] {
        l += 1;
    }
    l
}

/// Length of the common run of `a[i..]` and `b[j..]`. Compares in chunks first, so long matches cost
/// one slice comparison per chunk, which compiles to a `memcmp` for byte-like tokens.
fn extend<T: Eq>(a: &[T], b: &[T], i: usize, j: usize) -> usize {
    let max = (a.len() - i).min(b.len() - j);
    let (x, y) = (&a[i..i + max], &b[j..j + max]);
    let mut l = 0;
    while l + EXT_CHUNK <= max && x[l..l + EXT_CHUNK] == y[l..l + EXT_CHUNK] {
        l += EXT_CHUNK;
    }
    while l < max && x[l] == y[l] {
        l += 1;
    }
    l
}

/// The kernel that [`choose_kernel`] selects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kernel {
    Wavefront,
    Band,
    BitParallel,
}

/// Chooses the cheapest kernel by the cost model, in nanoseconds on the reference machine.
///
/// The wavefront costs `(k + 1)^2` diagonal steps. The rolling band costs `width` cells per text column.
/// The bit-parallel kernel costs one block per window block per text column, plus the class lookup of
/// `lookup` per column, or is unavailable when `lookup` is `None`. Ties favour the band.
fn choose_kernel(k: usize, blocks: usize, text_len: usize, lookup: Option<usize>) -> Kernel {
    let width = 2 * k + 1;
    let band = text_len.saturating_mul(width.saturating_mul(CELL_COST));
    let wavefront = (k + 1).saturating_mul(k + 1).saturating_mul(WF_STEP_COST);
    let mut best = (band, Kernel::Band);
    if wavefront < best.0 {
        best = (wavefront, Kernel::Wavefront);
    }
    if let Some(lookup) = lookup {
        let window = if blocks == 1 {
            1
        } else {
            width.div_ceil(WORD_BITS).saturating_add(1).min(blocks)
        };
        let bit_parallel =
            text_len.saturating_mul(window.saturating_mul(BLOCK_COST).saturating_add(lookup));
        if bit_parallel < best.0 {
            best = (bit_parallel, Kernel::BitParallel);
        }
    }
    best.1
}

/// Bounded search on `usize` thresholds: `Some(d)` if the distance `d` is at most `k`.
fn within_usize<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<usize> {
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(a.len() + b.len());
    }
    let (p, t) = orient(a, b);
    let k = k.min(t.len());
    let blocks = p.len().div_ceil(WORD_BITS);
    let first = choose_kernel(k, blocks, t.len(), Some(0));
    if first != Kernel::BitParallel {
        return run_non_bit_parallel(first, a, b, k);
    }
    // Each class costs one comparison per text column in the linear scan, and a scan beyond the band
    // width would cost more than the band, so the scan is capped there.
    let max_classes = (2 * k + 1).min((MAX_MASK_WORDS / blocks).saturating_sub(1));
    let Some((cls, reps)) = classify_scan(p, max_classes) else {
        let kernel = choose_kernel(k, blocks, t.len(), None);
        return run_non_bit_parallel(kernel, a, b, k);
    };
    let classes = reps.len();
    match choose_kernel(k, blocks, t.len(), Some(classes * LOOKUP_COST)) {
        Kernel::BitParallel => {
            let masks = Masks::new(&cls, classes);
            let class = |x: &T| reps.iter().position(|&r| p[r] == *x).unwrap_or(classes);
            run_kernel(&masks, p.len(), t, class, k)
        }
        kernel => run_non_bit_parallel(kernel, a, b, k),
    }
}

/// Runs the wavefront or the band on trimmed inputs. Callers pass the bit-parallel choice elsewhere.
fn run_non_bit_parallel<T: Eq>(kernel: Kernel, a: &[T], b: &[T], k: usize) -> Option<usize> {
    match kernel {
        Kernel::Wavefront => wavefront(a, b, k),
        Kernel::Band => band(a, b, k),
        Kernel::BitParallel => unreachable!("bit-parallel is run through its masks"),
    }
}

/// Runs the bit-parallel kernel on a built pattern: the single-word kernel for at most 64 tokens, else
/// the banded multiword kernel.
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
        myers_banded(masks, m, t, class, k)
    }
}

/// Shared entry for the bit-parallel test hooks: trims, classifies without a cap, and hands the masks
/// to `run`.
fn bit_parallel_entry<T: Eq>(
    a: &[T],
    b: &[T],
    k: usize,
    run: impl Fn(&Masks, &[T], &[T], &dyn Fn(&T) -> usize, usize) -> Option<usize>,
) -> Option<u32> {
    let (a, b) = trim(a, b);
    if a.len().abs_diff(b.len()) > k {
        return None;
    }
    if a.is_empty() || b.is_empty() {
        return Some(distance_to_u32(a.len() + b.len()));
    }
    let (p, t) = orient(a, b);
    let k = k.min(t.len());
    if k == 0 {
        return None;
    }
    let (cls, reps) =
        classify_scan(p, usize::MAX).expect("classification without a class cap cannot be refused");
    let masks = Masks::new(&cls, reps.len());
    let class = |x: &T| reps.iter().position(|&r| p[r] == *x).unwrap_or(reps.len());
    run(&masks, p, t, &class, k).map(distance_to_u32)
}

/// Sentinel for a wavefront diagonal that no cost has reached.
const UNREACHED: isize = isize::MIN;
/// Chunk size for the match-extension fast path, in tokens.
const EXT_CHUNK: usize = 16;

/// Furthest-reaching wavefront search (Ukkonen's diagonal transitions, as in Myers' O(ND) and in WFA).
///
/// Diagonal `d = j - i` holds the furthest pattern position `i` reached with cost at most the current
/// score `s`. Monotonicity along a diagonal (`D[i + 1][j + 1] >= D[i][j]` for unit costs) means every
/// point before that position on the diagonal also costs at most `s`, so the furthest point is a
/// complete summary of the diagonal. Each score extends the diagonals of the previous score by one
/// substitution, deletion or insertion, then slides along matches. The work is `O(k^2)` diagonal steps
/// plus the total match extension.
///
/// Requires trimmed inputs, both non-empty, and `|n - m| <= k`. Returns the distance if it is at most `k`.
fn wavefront<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<usize> {
    let (n, m) = (a.len() as isize, b.len() as isize);
    debug_assert!(n >= 1 && m >= 1 && (n - m).unsigned_abs() <= k);
    let end = m - n;
    // Diagonals run over `[-(k + 1), k + 1]`. The extra cell on each side stays unreached, so the
    // neighbour reads at the edges need no check.
    let off = k as isize + 1;
    let width = 2 * k + 3;
    let mut prev = vec![UNREACHED; width];
    let mut cur = vec![UNREACHED; width];
    let h0 = extend(a, b, 0, 0);
    if end == 0 && h0 == a.len() {
        return Some(0);
    }
    prev[off as usize] = h0 as isize;
    for s in 1..=k {
        let si = s as isize;
        for d in -si..=si {
            let idx = (d + off) as usize;
            let mut best = UNREACHED;
            // Substitution on the same diagonal, or keep the point if a side is exhausted.
            let same = prev[idx];
            if same != UNREACHED {
                let (i, j) = (same, same + d);
                best = best.max(if i < n && j < m { i + 1 } else { i });
            }
            // Deletion of a token of `a`: from diagonal `d + 1`, the pattern position advances.
            let del = prev[idx + 1];
            if del != UNREACHED && del < n {
                best = best.max(del + 1);
            }
            // Insertion of a token of `b`: from diagonal `d - 1`, the text position advances.
            let ins = prev[idx - 1];
            if ins != UNREACHED && ins + d - 1 < m {
                best = best.max(ins);
            }
            if best != UNREACHED {
                let (i, j) = (best as usize, (best + d) as usize);
                best += extend(a, b, i, j) as isize;
            }
            cur[idx] = best;
        }
        if cur[(end + off) as usize] >= n {
            return Some(s);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    None
}

/// Rolling band over the trimmed inputs, with the contract of [`band_rows`] and no row budget.
///
/// Row `i` holds `D[i][j]` for `j` in `[i - k, i + k]`, stored at index `c = j - i + k` in a buffer of
/// width `2k + 1`. Two rows are kept, so the memory is `O(k)`. Every stored value is capped at `k + 1`,
/// which stands for "more than `k`". Cells outside the band or the matrix hold the cap. Each row is
/// filled only over the columns `j` in `[0, m]`, so the inner loop has no range checks; the cells
/// outside that range are written with the cap.
fn band<T: Eq>(a: &[T], b: &[T], k: usize) -> Option<usize> {
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
            return None;
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    // After the last swap `prev` is row `n`; `j = m` sits at `c = m + k - n`.
    let d = prev[m + k - n];
    (d <= k).then_some(d)
}

const WORD_BITS: usize = 64;
/// Cost of one rolling band cell update, in nanoseconds. Fitted on the reference machine.
const CELL_COST: usize = 4;
/// Cost of one 64-bit block column of the bit-parallel kernel, in nanoseconds. Fitted on the reference
/// machine.
const BLOCK_COST: usize = 8;
/// Cost of one wavefront diagonal step, in nanoseconds. Fitted on the reference machine.
const WF_STEP_COST: usize = 10;
/// Cost of one class comparison per text column in the generic linear scan.
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

/// Bit-parallel Levenshtein restricted to the band `|i - j| <= k`, where row `i` is a pattern prefix
/// length and column `j` a text prefix length. Only the blocks that hold a row of the band are updated
/// in each column, so a column costs `O(k / 64)` blocks rather than `O(m / 64)`.
///
/// The blocks above the band are dropped. Their true values are above `k`, and an optimal path of cost
/// at most `k` never leaves the band, so the blocks below the band are only added as the band grows.
/// The top boundary of the lowest active block takes the horizontal delta `+1`, the same boundary as
/// row 0. Every value computed from the approximate boundary is at least the true value, and every
/// value at most `k` is exact because its optimal path stays inside the band. The score tracks the
/// value at the bottom row of the active window, which is row `m` in the last column.
fn myers_banded<T>(
    masks: &Masks,
    m: usize,
    t: &[T],
    class: impl Fn(&T) -> usize,
    k: usize,
) -> Option<usize> {
    debug_assert!(m >= 1 && !t.is_empty());
    // Trimmed inputs that differ have distance at least 1, so a zero bound is always exceeded.
    if k == 0 {
        return None;
    }
    let blocks = masks.blocks;
    debug_assert_eq!(blocks, m.div_ceil(WORD_BITS));
    let mut pv = vec![!0u64; blocks];
    let mut mv = vec![0u64; blocks];
    // The last active block at column `j` holds row `min(m, j + k)`, at bit `min(m, j + k) - 1`.
    let bottom_block = |j: usize| (m.min(j + k) - 1) / WORD_BITS;
    // The first active block at column `j` holds row `max(1, j - k)`, at bit `max(0, j - k - 1)`.
    let top_block = |j: usize| j.saturating_sub(k + 1) / WORD_BITS;
    // Column 0 is `D[i][0] = i`, which is the fresh vertical state of every block.
    let mut bb_prev = bottom_block(0);
    let mut score = m.min(WORD_BITS * (bb_prev + 1)) as isize;
    for (j0, x) in t.iter().enumerate() {
        let j = j0 + 1;
        let bb = bottom_block(j);
        let tb = top_block(j);
        debug_assert!(bb == bb_prev || bb == bb_prev + 1);
        let row = class(x) * blocks;
        // Every block is entered from the block above, and the top boundary of the first block is `+1`.
        let mut hin: i8 = 1;
        let mut old_bottom_delta: i8 = 0;
        let mut bottom_delta: i8 = 0;
        for b in tb..=bb {
            let row_end = m.min(WORD_BITS * (b + 1));
            let hbit = 1u64 << ((row_end - 1) % WORD_BITS);
            let (np, nm, cout, d) = block_step(masks.rows[row + b], pv[b], mv[b], hin, hbit);
            pv[b] = np;
            mv[b] = nm;
            hin = cout;
            if b == bb_prev {
                old_bottom_delta = d;
            }
            if b == bb {
                bottom_delta = d;
            }
        }
        if bb == bb_prev {
            score += isize::from(bottom_delta);
        } else {
            // The window grew by one block. Its rows add their vertical deltas of this column.
            score += isize::from(old_bottom_delta);
            let rows = m.min(WORD_BITS * (bb + 1)) - WORD_BITS * bb;
            let mask = if rows == WORD_BITS {
                !0u64
            } else {
                (1u64 << rows) - 1
            };
            score += (pv[bb] & mask).count_ones() as isize - (mv[bb] & mask).count_ones() as isize;
        }
        bb_prev = bb;
    }
    debug_assert_eq!(bb_prev, (m - 1) / WORD_BITS);
    let score = usize::try_from(score).expect("a value of the grid is non-negative");
    (score <= k).then_some(score)
}

/// Bit-parallel Levenshtein over `masks.blocks` 64-bit blocks (Myers 1999 section 4, Hyyro's block
/// carries). Each block takes the horizontal delta of the block above as its carry-in. Every block is
/// updated in every column, so this kernel is the reference for the banded one.
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
