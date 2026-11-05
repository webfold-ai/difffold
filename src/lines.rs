//! Exact line diff on the same intern-and-fold basis as the tree differ, written with recursion only.
//!
//! The result is a *minimal* edit script (fewest deleted plus inserted lines), the same objective as
//! `git diff --minimal` and Myers 1986. Speed comes from removing work that provably cannot matter
//! before the quadratic-in-D search runs:
//!
//! 1. the common prefix and suffix are cut on raw bytes, so only the changed middle is touched;
//! 2. every distinct line of the middle gets a dense id (exact: the table compares bytes on a hash hit);
//! 3. lines whose id occurs on only one side are certain edits and leave the search (an LCS never
//!    uses them);
//! 4. linear-space bidirectional Myers (middle snake) solves what is left.
//!
//! Traversals over slices of slices are structural recursions that halve the slice, so the call depth is
//! `O(log n)`; the Aeneas extraction used for the proofs cannot carry nested borrows through a loop. Plain
//! index loops (`while`) are used for the hash, the interner table and the histogram index, which hold no
//! nested borrows. The one inherently sequential recursion is the edit-distance sweep (`sweep`): its depth is
//! at most `D / 2 + 1` for edit distance `D`; callers with adversarial inputs of unbounded `D` should call from
//! a thread with a large stack (see `tests/adversarial.rs`). Slice primitives (`fill`, `==` on slices) are used
//! as primitives.

use std::hash::BuildHasher;

const K: u64 = 0x9E37_79B9_7F4A_7C15;
const NIL: u32 = u32::MAX;

/// A fresh random hash seed, one per diff call, so that an attacker cannot precompute colliding lines.
fn random_seed() -> u64 {
    let seed = std::collections::hash_map::RandomState::new().hash_one(0xD1FF_F01Du64);
    seed | 1
}

/// A keyed 64-bit multiply-fold hash of a line, eight bytes at a time.
fn hash_line(seed: u64, l: &[u8]) -> u64 {
    let mut h = seed ^ (l.len() as u64).wrapping_mul(K);
    let mut i = 0usize;
    while l.len() - i >= 8 {
        let w = u64::from_le_bytes([
            l[i],
            l[i + 1],
            l[i + 2],
            l[i + 3],
            l[i + 4],
            l[i + 5],
            l[i + 6],
            l[i + 7],
        ]);
        h = (h ^ w).wrapping_mul(K).rotate_left(29);
        i += 8;
    }
    let mut acc = 0u64;
    while i < l.len() {
        acc = (acc << 8) | u64::from(l[i]);
        i += 1;
    }
    h = (h ^ acc).wrapping_mul(K).rotate_left(29);
    h ^ (h >> 32)
}

/// Result of a line diff: which lines of the old text are deleted and which of the new are inserted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineDiff {
    /// `true` where the old line is deleted.
    pub deleted: Vec<bool>,
    /// `true` where the new line is inserted.
    pub inserted: Vec<bool>,
}

impl LineDiff {
    /// Number of deleted plus inserted lines: the edit cost.
    #[must_use]
    pub fn cost(&self) -> usize {
        count_true(&self.deleted) + count_true(&self.inserted)
    }
}

// ------------------------------------------------------------------ recursion combinators

/// Visit every element in order, halving the slice, so the depth is `O(log n)`.
fn each<T, F: FnMut(usize, &T)>(xs: &[T], base: usize, f: &mut F) {
    match xs.len() {
        0 => {}
        1 => f(base, &xs[0]),
        n => {
            let h = n / 2;
            each(&xs[..h], base, f);
            each(&xs[h..], base + h, f);
        }
    }
}

fn count_true(xs: &[bool]) -> usize {
    match xs.len() {
        0 => 0,
        1 => usize::from(xs[0]),
        n => count_true(&xs[..n / 2]) + count_true(&xs[n / 2..]),
    }
}

/// Bytes of `0x0A` in one little-endian word, exact and branch-free (SWAR).
fn nl_mask(w: u64) -> u64 {
    const LOW7: u64 = 0x7F7F_7F7F_7F7F_7F7F;
    let x = w ^ 0x0A0A_0A0A_0A0A_0A0A;
    // The high bit of a byte of `y` is set exactly when that byte of `x` is zero.
    !(((x & LOW7) + LOW7) | x | LOW7)
}

/// Number of set marks of a `nl_mask` word: its bits are 0 or 1 at bit 7 of each byte, so the product
/// sums the eight marks into the top byte.
fn newline_count(m: u64) -> usize {
    ((m >> 7).wrapping_mul(0x0101_0101_0101_0101) >> 56) as usize
}

/// Index of the lowest nonzero byte of a nonzero word, by shifting a byte at a time.
fn lowest_byte(m: u64, k: usize) -> usize {
    if m & 0xFF != 0 || k >= 7 {
        k
    } else {
        lowest_byte(m >> 8, k + 1)
    }
}

/// Load up to eight bytes as a word; missing high bytes are zero, which never equals a newline.
fn word(t: &[u8]) -> u64 {
    match t.len() {
        0 => 0,
        n if n >= 8 => u64::from_le_bytes([t[0], t[1], t[2], t[3], t[4], t[5], t[6], t[7]]),
        n => word(&t[..n - 1]) | (u64::from(t[n - 1]) << (8 * (n - 1))),
    }
}

/// Newlines among the first at most 64 bytes, a word at a time (depth at most 8).
fn count_block(t: &[u8]) -> usize {
    if t.is_empty() {
        0
    } else {
        newline_count(nl_mask(word(t))) + count_block(&t[t.len().min(8)..])
    }
}

fn count_byte(t: &[u8], _b: u8) -> usize {
    if t.len() <= 64 {
        count_block(t)
    } else {
        count_byte(&t[..t.len() / 2], b'\n') + count_byte(&t[t.len() / 2..], b'\n')
    }
}

/// Length of the common prefix, by halving: depth `O(log n)`.
fn common_prefix<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    let n = a.len().min(b.len());
    if n == 0 {
        0
    } else if n == 1 {
        usize::from(a[0] == b[0])
    } else {
        let h = n / 2;
        if a[..h] == b[..h] {
            h + common_prefix(&a[h..], &b[h..])
        } else {
            common_prefix(&a[..h], &b[..h])
        }
    }
}

/// Length of the common suffix, by halving.
fn common_suffix<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    let n = a.len().min(b.len());
    if n == 0 {
        0
    } else if n == 1 {
        usize::from(a[a.len() - 1] == b[b.len() - 1])
    } else {
        let h = n / 2;
        if a[a.len() - h..] == b[b.len() - h..] {
            h + common_suffix(&a[..a.len() - h], &b[..b.len() - h])
        } else {
            common_suffix(&a[a.len() - h..], &b[b.len() - h..])
        }
    }
}

/// Index of the first newline in the first at most 64 bytes, a word at a time.
fn first_in_block(t: &[u8], at: usize) -> Option<usize> {
    if at >= t.len() {
        None
    } else {
        let m = nl_mask(word(&t[at..]));
        if m != 0 {
            Some(at + lowest_byte(m, 0))
        } else {
            first_in_block(t, at + 8)
        }
    }
}

/// Index of the first newline, by halving down to word blocks.
fn first_nl(t: &[u8]) -> Option<usize> {
    if t.len() <= 64 {
        first_in_block(t, 0)
    } else {
        match first_nl(&t[..t.len() / 2]) {
            Some(i) => Some(i),
            None => match first_nl(&t[t.len() / 2..]) {
                Some(i) => Some(i + t.len() / 2),
                None => None,
            },
        }
    }
}

/// Index of the last newline in a short slice, scanning the end first.
fn last_in_block(t: &[u8]) -> Option<usize> {
    match t.len() {
        0 => None,
        n if t[n - 1] == b'\n' => Some(n - 1),
        n => last_in_block(&t[..n - 1]),
    }
}

/// Index of the last newline, by halving.
fn last_nl(t: &[u8]) -> Option<usize> {
    if t.len() <= 64 {
        last_in_block(t)
    } else {
        match last_nl(&t[t.len() / 2..]) {
            Some(i) => Some(i + t.len() / 2),
            None => last_nl(&t[..t.len() / 2]),
        }
    }
}

fn count_lines(t: &[u8]) -> usize {
    count_byte(t, b'\n') + usize::from(!t.is_empty() && t[t.len() - 1] != b'\n')
}

/// Chunk size below which lines are split one after another. The recursion depth there is at most
/// the number of lines in a chunk, so at most this many frames.
const SEQ_CHUNK: usize = 4096;

/// Split a short chunk line by line: one newline search per line.
fn split_seq<'a>(t: &'a [u8], out: &mut Vec<&'a [u8]>) {
    if !t.is_empty() {
        match first_nl(t) {
            Some(i) => {
                out.push(&t[..i + 1]);
                split_seq(&t[i + 1..], out);
            }
            None => out.push(t),
        }
    }
}

/// Split into lines, each keeping its terminator, by cutting the text at a newline near the middle
/// until chunks are short, then splitting each chunk sequentially.
fn split_into<'a>(t: &'a [u8], out: &mut Vec<&'a [u8]>) {
    if t.len() <= SEQ_CHUNK {
        split_seq(t, out);
    } else {
        let mid = t.len() / 2;
        // Cut after the first newline at or past the middle; fall back to the last newline before it.
        let cut = match first_nl(&t[mid..]) {
            Some(i) if mid + i + 1 < t.len() => Some(mid + i + 1),
            _ => match last_nl(&t[..mid]) {
                Some(i) => Some(i + 1),
                None => None,
            },
        };
        match cut {
            Some(c) => {
                split_into(&t[..c], out);
                split_into(&t[c..], out);
            }
            // One long line, possibly with a final terminator.
            None => out.push(t),
        }
    }
}

/// Split a text into lines, each keeping its terminator.
#[must_use]
pub fn split_lines(t: &[u8]) -> Vec<&[u8]> {
    let mut out = Vec::new();
    split_into(t, &mut out);
    out
}

// ------------------------------------------------------------------ interning

/// Ids of the lines of both sides, in order of first appearance: equal ids exactly for equal lines, all
/// below the returned count. The hash only picks a bucket; lines are compared byte for byte.
fn intern<'a>(a: &[&'a [u8]], b: &[&'a [u8]]) -> (Vec<u32>, Vec<u32>, usize) {
    intern_seeded(a, b, random_seed())
}

/// `intern` with an explicit hash seed. Lines hash into `head`, a table of at least `a.len() + b.len()`
/// buckets; each bucket heads a chain of ids through `nxt`, newest first, and `reps[id]` is the line.
fn intern_seeded<'a>(a: &[&'a [u8]], b: &[&'a [u8]], seed: u64) -> (Vec<u32>, Vec<u32>, usize) {
    let total = a.len() + b.len();
    let mut head = vec![NIL; table_size(total)];
    let mut nxt: Vec<u32> = Vec::with_capacity(total);
    let mut reps: Vec<&'a [u8]> = Vec::with_capacity(total);
    let mut ia = vec![0u32; a.len()];
    let mut ib = vec![0u32; b.len()];
    intern_all(a, 0, &mut head, &mut nxt, &mut reps, seed, &mut ia);
    intern_all(b, 0, &mut head, &mut nxt, &mut reps, seed, &mut ib);
    let n = reps.len();
    (ia, ib, n)
}

/// A power of two that is at least `total` and at least 2, so a bucket mask is `size - 1`.
fn table_size(total: usize) -> usize {
    let mut cap = 2usize;
    while cap < total {
        cap *= 2;
    }
    cap
}

/// Intern every line of `xs` in order, writing the id of `xs[k]` to `out[base + k]`. Halving keeps
/// the call depth `O(log n)`.
fn intern_all<'a>(
    xs: &[&'a [u8]],
    base: usize,
    head: &mut Vec<u32>,
    nxt: &mut Vec<u32>,
    reps: &mut Vec<&'a [u8]>,
    seed: u64,
    out: &mut [u32],
) {
    match xs.len() {
        0 => {}
        1 => out[base] = intern_line(head, nxt, reps, seed, xs[0]),
        n => {
            let h = n / 2;
            intern_all(&xs[..h], base, head, nxt, reps, seed, out);
            intern_all(&xs[h..], base + h, head, nxt, reps, seed, out);
        }
    }
}

/// The id of line `l`, adding it with the next free id if no earlier line equals it.
fn intern_line<'a>(
    head: &mut Vec<u32>,
    nxt: &mut Vec<u32>,
    reps: &mut Vec<&'a [u8]>,
    seed: u64,
    l: &'a [u8],
) -> u32 {
    let bucket = (hash_line(seed, l) as usize) & (head.len() - 1);
    let k = find_in_chain(reps, nxt, head[bucket], l);
    if k != NIL {
        k
    } else {
        let id = reps.len();
        assert!(id < NIL as usize, "fewer than 2^32 distinct lines");
        nxt.push(head[bucket]);
        head[bucket] = id as u32;
        reps.push(l);
        id as u32
    }
}

/// The first id on the chain starting at `k` whose line equals `l`, or `NIL`. Each link points to an
/// older id, so the walk ends; it is a tail call.
fn find_in_chain(reps: &Vec<&[u8]>, nxt: &Vec<u32>, k: u32, l: &[u8]) -> u32 {
    if k == NIL || reps[k as usize] == l {
        k
    } else {
        find_in_chain(reps, nxt, nxt[k as usize], l)
    }
}

// ------------------------------------------------------------------ the diff

/// Which line algorithm to run on the changed middle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Algo {
    /// Minimal edit script (Myers, same objective as `git diff --minimal`).
    Minimal,
    /// Histogram: anchor on the rarest common line, recurse on both sides. Not minimal.
    Histogram,
}

/// Diff two texts line by line with the minimal algorithm.
#[must_use]
pub fn diff_text(old: &[u8], new: &[u8]) -> LineDiff {
    diff_text_with(old, new, Algo::Minimal)
}

/// Diff two texts line by line with the chosen algorithm.
#[must_use]
pub fn diff_text_with(old: &[u8], new: &[u8], algo: Algo) -> LineDiff {
    diff_text_core::<HashLines>(old, new, algo)
}

/// The two stages of `diff_text_with` that depend on how lines are identified: interning lines to ids
/// and the (non-minimal) histogram differ. The minimal path runs `diff_ids` directly.
trait LineIds {
    /// Ids for the lines of both sides: equal ids exactly for equal lines, all below the returned count.
    fn intern(a: &[&[u8]], b: &[&[u8]]) -> (Vec<u32>, Vec<u32>, usize);
    fn histogram(a: &[u32], b: &[u32], n_ids: usize) -> LineDiff;
}

/// The production interner and histogram differ.
struct HashLines;

impl LineIds for HashLines {
    fn intern(a: &[&[u8]], b: &[&[u8]]) -> (Vec<u32>, Vec<u32>, usize) {
        intern(a, b)
    }
    fn histogram(a: &[u32], b: &[u32], n_ids: usize) -> LineDiff {
        diff_histogram_ids(a, b, n_ids)
    }
}

/// `diff_text_with` over an abstract line identification.
fn diff_text_core<L: LineIds>(old: &[u8], new: &[u8], algo: Algo) -> LineDiff {
    // Prefix: back up to the start of the line where the texts first differ.
    let p = line_start(old, common_prefix(old, new));
    let (ro, rn) = (&old[p..], &new[p..]);
    // Suffix: advance to the first full line of the common tail, in both texts.
    let q = suffix_on_line_start(ro, rn, common_suffix(ro, rn));
    let (mo, mn) = (&ro[..ro.len() - q], &rn[..rn.len() - q]);
    let (pre_lines, suf_old, suf_new) = (
        count_lines(&old[..p]),
        count_lines(&ro[ro.len() - q..]),
        count_lines(&rn[rn.len() - q..]),
    );
    let (la, lb) = (split_lines(mo), split_lines(mn));
    let (ia, ib, n_ids) = L::intern(&la, &lb);
    let mid = match algo {
        Algo::Minimal => diff_ids(&ia, &ib, n_ids),
        Algo::Histogram => L::histogram(&ia, &ib, n_ids),
    };
    let mut deleted = vec![false; pre_lines + la.len() + suf_old];
    let mut inserted = vec![false; pre_lines + lb.len() + suf_new];
    deleted[pre_lines..pre_lines + la.len()].copy_from_slice(&mid.deleted);
    inserted[pre_lines..pre_lines + lb.len()].copy_from_slice(&mid.inserted);
    LineDiff { deleted, inserted }
}

/// The largest line start at or before byte `p`: one past the last newline before `p`.
fn line_start(t: &[u8], p: usize) -> usize {
    match last_nl(&t[..p]) {
        Some(i) => i + 1,
        None => 0,
    }
}

/// Offset arithmetic of the shrink: the suffix restarts after its first newline.
fn shrink_suffix(ro: &[u8], q: usize) -> usize {
    match first_nl(&ro[ro.len() - q..]) {
        Some(k) => q - k - 1,
        None => 0,
    }
}

/// Shrink the common suffix length `q` until the suffix starts a line in both texts. The suffix
/// bytes are equal in both texts, so the first newline inside the suffix has the same offset in each.
fn suffix_on_line_start(ro: &[u8], rn: &[u8], q: usize) -> usize {
    if q == 0 {
        q
    } else if q < ro.len() && ro[ro.len() - q - 1] != b'\n' {
        shrink_suffix(ro, q)
    } else if q < rn.len() && rn[rn.len() - q - 1] != b'\n' {
        shrink_suffix(ro, q)
    } else {
        q
    }
}

/// Diff two id sequences whose ids are below `n_ids`.
#[must_use]
pub fn diff_ids(a: &[u32], b: &[u32], n_ids: usize) -> LineDiff {
    let mut deleted = vec![false; a.len()];
    let mut inserted = vec![false; b.len()];
    let pre = common_prefix(a, b);
    let suf = common_suffix(&a[pre..], &b[pre..]);
    let (am, bm) = (&a[pre..a.len() - suf], &b[pre..b.len() - suf]);
    let mut in_a = vec![false; n_ids];
    let mut in_b = vec![false; n_ids];
    mark_ids(am, &mut in_a);
    mark_ids(bm, &mut in_b);
    // Compact: keep only lines whose id occurs on the other side; the rest are certain edits.
    let (mut ca, mut pa) = (Vec::new(), Vec::new());
    compact_ids(am, pre, &in_b, &mut ca, &mut pa, &mut deleted);
    let (mut cb, mut pb) = (Vec::new(), Vec::new());
    compact_ids(bm, pre, &in_a, &mut cb, &mut pb, &mut inserted);
    let mut ra = vec![false; ca.len()];
    let mut rb = vec![false; cb.len()];
    let size = 2 * (ca.len() + cb.len()) + 3;
    let mut vf = vec![0i32; size];
    let mut vb = vec![0i32; size];
    solve(&ca, &cb, 0, 0, &mut ra, &mut rb, &mut vf, &mut vb);
    scatter_flags(&ra, &pa, &mut deleted);
    scatter_flags(&rb, &pb, &mut inserted);
    LineDiff { deleted, inserted }
}

/// Set `flags[x]` for every id `x` of `xs`, by halving.
fn mark_ids(xs: &[u32], flags: &mut [bool]) {
    match xs.len() {
        0 => {}
        1 => flags[xs[0] as usize] = true,
        n => {
            mark_ids(&xs[..n / 2], flags);
            mark_ids(&xs[n / 2..], flags);
        }
    }
}

/// Split `xs` (whose first element sits at position `base`) into the ids that occur on the other side,
/// pushed with their positions, and the certain edits, flagged in `edit`.
fn compact_ids(xs: &[u32], base: usize, other: &[bool], keep: &mut Vec<u32>, pos: &mut Vec<usize>, edit: &mut [bool]) {
    match xs.len() {
        0 => {}
        1 => {
            if other[xs[0] as usize] {
                keep.push(xs[0]);
                pos.push(base);
            } else {
                edit[base] = true;
            }
        }
        n => {
            compact_ids(&xs[..n / 2], base, other, keep, pos, edit);
            compact_ids(&xs[n / 2..], base + n / 2, other, keep, pos, edit);
        }
    }
}

/// Copy the solved flags `r[k]` back to position `pos[k]`, by halving.
fn scatter_flags(r: &[bool], pos: &[usize], out: &mut [bool]) {
    match r.len() {
        0 => {}
        1 => out[pos[0]] = r[0],
        n => {
            scatter_flags(&r[..n / 2], &pos[..n / 2], out);
            scatter_flags(&r[n / 2..], &pos[n / 2..], out);
        }
    }
}

/// Mark the minimal edits between `a` and `b`; `ao`/`bo` are the offsets of the slices in `ra`/`rb`.
#[allow(clippy::too_many_arguments)]
fn solve(
    a: &[u32],
    b: &[u32],
    ao: usize,
    bo: usize,
    ra: &mut [bool],
    rb: &mut [bool],
    vf: &mut [i32],
    vb: &mut [i32],
) {
    let s = common_prefix(a, b);
    let e = common_suffix(&a[s..], &b[s..]);
    let (a, b, ao, bo) = (&a[s..a.len() - e], &b[s..b.len() - e], ao + s, bo + s);
    if a.is_empty() {
        rb[bo..bo + b.len()].fill(true);
    } else if b.is_empty() {
        ra[ao..ao + a.len()].fill(true);
    } else {
        let (x, y) = middle(a, b, vf, vb);
        if (x == 0 && y == 0) || (x == a.len() && y == b.len()) {
            // No progress is possible from this split; mark everything.
            ra[ao..ao + a.len()].fill(true);
            rb[bo..bo + b.len()].fill(true);
        } else {
            solve(&a[..x], &b[..y], ao, bo, ra, rb, vf, vb);
            solve(&a[x..], &b[y..], ao + x, bo + y, ra, rb, vf, vb);
        }
    }
}

/// The state of one middle-snake search.
struct Search<'a> {
    a: &'a [u32],
    b: &'a [u32],
    n: i32,
    m: i32,
    delta: i32,
    odd: bool,
    off: i32,
    vf: &'a mut [i32],
    vb: &'a mut [i32],
}

impl Search<'_> {
    fn ix(&self, k: i32) -> usize {
        (self.off + k) as usize
    }
}

/// The middle snake of Myers' bidirectional search: a point `(x, y)` on a shortest edit path.
fn middle(a: &[u32], b: &[u32], vf: &mut [i32], vb: &mut [i32]) -> (usize, usize) {
    let n = a.len() as i32;
    let m = b.len() as i32;
    let mut s = Search {
        a,
        b,
        n,
        m,
        delta: n - m,
        odd: (n - m) & 1 != 0,
        off: n + m + 1,
        vf,
        vb,
    };
    let o = s.ix(1);
    s.vf[o] = 0;
    s.vb[o] = 0;
    sweep(&mut s, 0, (n + m + 1) / 2)
}

/// Diagonal count below which a block is walked sequentially instead of halved.
const DIAG_BLOCK: i32 = 64;

/// One round `d` of the sweep, then the next. Depth at most `max_d + 1`.
fn sweep(s: &mut Search, d: i32, max_d: i32) -> (usize, usize) {
    if d > max_d {
        (0, 0)
    } else if let Some(p) = forward(s, d, -d, d) {
        p
    } else if let Some(p) = backward(s, d, -d, d) {
        p
    } else {
        sweep(s, d + 1, max_d)
    }
}

/// Diagonals `lo..=hi` step 2 of the forward half-round. The diagonals of one round read only the
/// other parity, so they are independent and are split by halving: depth `O(log d)`. The leftmost
/// overlap wins, so the answer is deterministic.
fn forward(s: &mut Search, d: i32, lo: i32, hi: i32) -> Option<(usize, usize)> {
    if lo > hi {
        None
    } else if hi - lo <= DIAG_BLOCK {
        forward_seq(s, d, lo, hi)
    } else {
        let mid = lo + (((hi - lo) / 2) & !1);
        match forward(s, d, lo, mid) {
            Some(p) => Some(p),
            None => forward(s, d, mid + 2, hi),
        }
    }
}

/// A short block of diagonals, one after another. Tail recursion of depth at most `DIAG_BLOCK / 2`.
fn forward_seq(s: &mut Search, d: i32, lo: i32, hi: i32) -> Option<(usize, usize)> {
    if lo > hi {
        None
    } else if let Some(p) = forward_one(s, d, lo) {
        Some(p)
    } else {
        forward_seq(s, d, lo + 2, hi)
    }
}

fn forward_one(s: &mut Search, d: i32, k: i32) -> Option<(usize, usize)> {
    let (ikm, ikp) = (s.ix(k - 1), s.ix(k + 1));
    let x0 = if k == -d || (k != d && s.vf[ikm] < s.vf[ikp]) {
        s.vf[ikp]
    } else {
        s.vf[ikm] + 1
    };
    let y0 = x0 - k;
    let run = snake(s.a, s.b, x0, y0);
    let (x, y) = (x0 + run, y0 + run);
    let ik = s.ix(k);
    s.vf[ik] = x;
    let kb = s.delta - k;
    if s.odd && kb > -d && kb < d && x + s.vb[s.ix(kb)] >= s.n {
        Some((x as usize, y as usize))
    } else {
        None
    }
}

fn backward(s: &mut Search, d: i32, lo: i32, hi: i32) -> Option<(usize, usize)> {
    if lo > hi {
        None
    } else if hi - lo <= DIAG_BLOCK {
        backward_seq(s, d, lo, hi)
    } else {
        let mid = lo + (((hi - lo) / 2) & !1);
        match backward(s, d, lo, mid) {
            Some(p) => Some(p),
            None => backward(s, d, mid + 2, hi),
        }
    }
}

/// A short block of diagonals, one after another. Tail recursion of depth at most `DIAG_BLOCK / 2`.
fn backward_seq(s: &mut Search, d: i32, lo: i32, hi: i32) -> Option<(usize, usize)> {
    if lo > hi {
        None
    } else if let Some(p) = backward_one(s, d, lo) {
        Some(p)
    } else {
        backward_seq(s, d, lo + 2, hi)
    }
}

fn backward_one(s: &mut Search, d: i32, k: i32) -> Option<(usize, usize)> {
    let (ikm, ikp) = (s.ix(k - 1), s.ix(k + 1));
    let x0 = if k == -d || (k != d && s.vb[ikm] < s.vb[ikp]) {
        s.vb[ikp]
    } else {
        s.vb[ikm] + 1
    };
    let y0 = x0 - k;
    let run = snake_back(s.a, s.b, x0, y0);
    let (x, y) = (x0 + run, y0 + run);
    let ik = s.ix(k);
    s.vb[ik] = x;
    let kf = s.delta - k;
    if !s.odd && kf >= -d && kf <= d && x + s.vf[s.ix(kf)] >= s.n {
        Some(((s.n - x) as usize, (s.m - y) as usize))
    } else {
        None
    }
}

/// Rebuild check: the lines kept from both sides must be equal.
#[must_use]
pub fn replay_ok(old: &[u8], new: &[u8], d: &LineDiff) -> bool {
    let (la, lb) = (split_lines(old), split_lines(new));
    if d.deleted.len() != la.len() || d.inserted.len() != lb.len() {
        return false;
    }
    let mut ka: Vec<&[u8]> = Vec::new();
    let mut kb: Vec<&[u8]> = Vec::new();
    each(&la, 0, &mut |i, l| {
        if !d.deleted[i] {
            ka.push(l);
        }
    });
    each(&lb, 0, &mut |i, l| {
        if !d.inserted[i] {
            kb.push(l);
        }
    });
    ka == kb
}

// ------------------------------------------------------------------ histogram

/// Candidates whose line occurs more than this many times in the old range are not anchors.
const HIST_LIMIT: u32 = 64;
/// Recursion depth after which the rest of a range is handed to the minimal search, bounding stack use.
const HIST_DEPTH: u32 = 1500;
struct Hist {
    cnt: Vec<u32>,
    head: Vec<u32>,
    nxt: Vec<u32>,
    del: Vec<bool>,
    ins: Vec<bool>,
    vf: Vec<i32>,
    vb: Vec<i32>,
}

/// The best anchor found so far: occurrence count, match length, and the matching positions.
#[derive(Clone, Copy)]
struct Anchor {
    cnt: u32,
    len: usize,
    i: usize,
    j: usize,
    bl: usize,
}

/// Histogram diff of id sequences. The result is a valid edit script (kept lines equal, in order) but
/// is not guaranteed minimal; ranges with no usable anchor are solved by the minimal search.
#[must_use]
pub fn diff_histogram_ids(a: &[u32], b: &[u32], n_ids: usize) -> LineDiff {
    let size = 2 * (a.len() + b.len()) + 3;
    let mut h = Hist {
        cnt: vec![0; n_ids],
        head: vec![NIL; n_ids],
        nxt: vec![NIL; a.len()],
        del: vec![false; a.len()],
        ins: vec![false; b.len()],
        vf: vec![0; size],
        vb: vec![0; size],
    };
    hist(a, b, &mut h, (0, a.len()), (0, b.len()), 0);
    LineDiff {
        deleted: h.del,
        inserted: h.ins,
    }
}

fn hist(a: &[u32], b: &[u32], h: &mut Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize), depth: u32) {
    let p = common_prefix(&a[alo..ahi], &b[blo..bhi]);
    let (alo, blo) = (alo + p, blo + p);
    let sfx = common_suffix(&a[alo..ahi], &b[blo..bhi]);
    let (ahi, bhi) = (ahi - sfx, bhi - sfx);
    if alo == ahi {
        h.ins[blo..bhi].fill(true);
    } else if blo == bhi {
        h.del[alo..ahi].fill(true);
    } else if depth >= HIST_DEPTH {
        hist_fallback(a, b, h, (alo, ahi), (blo, bhi));
    } else {
        index_a(a, h, alo, ahi);
        let best = find_anchor(a, b, h, (alo, ahi), (blo, bhi));
        let common = any_common(b, h, blo, bhi);
        unindex_a(a, h, alo, ahi);
        match best {
            Some(an) => {
                let (i0, j0) = (an.i - an.bl, an.j - an.bl);
                let (i1, j1) = (i0 + an.len, j0 + an.len);
                hist(a, b, h, (alo, i0), (blo, j0), depth + 1);
                hist(a, b, h, (i1, ahi), (j1, bhi), depth + 1);
            }
            None if common => hist_fallback(a, b, h, (alo, ahi), (blo, bhi)),
            None => {
                h.del[alo..ahi].fill(true);
                h.ins[blo..bhi].fill(true);
            }
        }
    }
}

/// Solve a range with the minimal search.
fn hist_fallback(a: &[u32], b: &[u32], h: &mut Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize)) {
    solve(
        &a[alo..ahi],
        &b[blo..bhi],
        alo,
        blo,
        &mut h.del,
        &mut h.ins,
        &mut h.vf,
        &mut h.vb,
    );
}

/// Chain every position of `a[alo..ahi]` under its id, newest first, and count the occurrences.
fn index_a(a: &[u32], h: &mut Hist, alo: usize, ahi: usize) {
    let mut i = alo;
    while i < ahi {
        let id = a[i] as usize;
        h.cnt[id] += 1;
        h.nxt[i] = h.head[id];
        h.head[id] = i as u32;
        i += 1;
    }
}

/// Reset the counts and chain heads set by `index_a`.
fn unindex_a(a: &[u32], h: &mut Hist, alo: usize, ahi: usize) {
    let mut i = alo;
    while i < ahi {
        let id = a[i] as usize;
        h.cnt[id] = 0;
        h.head[id] = NIL;
        i += 1;
    }
}

fn any_common(b: &[u32], h: &Hist, blo: usize, bhi: usize) -> bool {
    let mut found = false;
    let mut j = blo;
    while j < bhi {
        if h.cnt[b[j] as usize] > 0 {
            found = true;
        }
        j += 1;
    }
    found
}

/// The rarest common line of `b[blo..bhi]` that occurs at most `HIST_LIMIT` times in the old range,
/// extended to the longest equal run around it.
fn find_anchor(a: &[u32], b: &[u32], h: &Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize)) -> Option<Anchor> {
    let mut best: Option<Anchor> = None;
    let mut j = blo;
    while j < bhi {
        let id = b[j] as usize;
        let c = h.cnt[id];
        if c > 0 && c <= HIST_LIMIT {
            let rarer = match best {
                None => true,
                Some(bst) => c <= bst.cnt,
            };
            if rarer {
                best = walk_chain(a, b, h, h.head[id], (alo, ahi), (blo, bhi), j, c, best);
            }
        }
        j += 1;
    }
    best
}

/// Try every old position of the line, keeping the better anchor. Recursion over the chain.
#[allow(clippy::too_many_arguments)]
fn walk_chain(
    a: &[u32],
    b: &[u32],
    h: &Hist,
    at: u32,
    (alo, ahi): (usize, usize),
    (blo, bhi): (usize, usize),
    j: usize,
    c: u32,
    best: Option<Anchor>,
) -> Option<Anchor> {
    if at == NIL {
        best
    } else {
        let i = at as usize;
        let bl = common_suffix(&a[alo..i], &b[blo..j]);
        let fl = common_prefix(&a[i..ahi], &b[j..bhi]);
        let cand = Anchor {
            cnt: c,
            len: bl + fl,
            i,
            j,
            bl,
        };
        let better = match best {
            None => true,
            Some(b0) => {
                if cand.cnt < b0.cnt {
                    true
                } else {
                    cand.cnt == b0.cnt && cand.len > b0.len
                }
            }
        };
        walk_chain(
            a,
            b,
            h,
            h.nxt[i],
            (alo, ahi),
            (blo, bhi),
            j,
            c,
            if better { Some(cand) } else { best },
        )
    }
}

/// Forward run of equal ids from `(x, y)`; most snakes are empty, so test one element first.
fn snake(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
    let (n, m) = (a.len() as i32, b.len() as i32);
    if x >= n || y >= m || a[x as usize] != b[y as usize] {
        0
    } else {
        common_prefix(&a[x as usize..], &b[y as usize..]) as i32
    }
}

/// Backward run of equal ids ending before `(n - x, m - y)`.
fn snake_back(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
    let (n, m) = (a.len() as i32, b.len() as i32);
    if x >= n || y >= m || a[(n - 1 - x) as usize] != b[(m - 1 - y) as usize] {
        0
    } else {
        common_suffix(&a[..(n - x) as usize], &b[..(m - y) as usize]) as i32
    }
}

/// Entry points for the agreement test of the extraction copy in `proof/extract/lines_core.rs`
/// (`tests/agree.rs`). Not part of the API.
#[doc(hidden)]
pub mod proof_api {
    /// `first_nl` of the real source.
    #[must_use]
    pub fn first_nl(t: &[u8]) -> Option<usize> {
        super::first_nl(t)
    }
    /// `last_nl` of the real source.
    #[must_use]
    pub fn last_nl(t: &[u8]) -> Option<usize> {
        super::last_nl(t)
    }
    /// `snake` of the real source.
    #[must_use]
    pub fn snake(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
        super::snake(a, b, x, y)
    }
    /// `snake_back` of the real source.
    #[must_use]
    pub fn snake_back(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
        super::snake_back(a, b, x, y)
    }
    /// `line_start` of the real source.
    #[must_use]
    pub fn line_start(t: &[u8], p: usize) -> usize {
        super::line_start(t, p)
    }
    /// `suffix_on_line_start` of the real source.
    #[must_use]
    pub fn suffix_on_line_start(ro: &[u8], rn: &[u8], q: usize) -> usize {
        super::suffix_on_line_start(ro, rn, q)
    }
    /// `count_lines` of the real source.
    #[must_use]
    pub fn count_lines(t: &[u8]) -> usize {
        super::count_lines(t)
    }
}
