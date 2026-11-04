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
//! **No `while`, `loop`, `for` or iterator chain appears in this file.** Every traversal is a
//! structural recursion, and wherever the traversal order does not matter it halves the slice, so the
//! call depth is `O(log n)`. The one inherently sequential recursion is the edit-distance sweep
//! (`sweep`): its depth is at most `D / 2 + 1` for edit distance `D`; callers with adversarial inputs
//! of unbounded `D` should call from a thread with a large stack (see `tests/adversarial.rs`).
//! The standard library's hash table and slice primitives (`fill`, `==` on slices) are used as
//! primitives and are not part of the recursion discipline.

use std::collections::HashMap;
use std::hash::{BuildHasher, Hasher};

/// A keyed 64-bit multiply-fold hasher over bytes, eight at a time. The key is random per diff call,
/// so an attacker cannot precompute colliding lines.
#[derive(Clone, Copy)]
pub struct FoldState(u64);

impl FoldState {
    fn random() -> Self {
        let seed = std::collections::hash_map::RandomState::new().hash_one(0xD1FF_F01Du64);
        FoldState(seed | 1)
    }
}

/// The hasher state for [`FoldState`].
pub struct Fold(u64);

impl BuildHasher for FoldState {
    type Hasher = Fold;
    fn build_hasher(&self) -> Fold {
        Fold(self.0)
    }
}

const K: u64 = 0x9E37_79B9_7F4A_7C15;

/// Fold eight-byte words of `bytes` into `h`, by recursion on the word count.
fn fold_words(h: u64, bytes: &[u8]) -> u64 {
    if bytes.len() < 8 {
        fold_tail(h, bytes, 0, 0)
    } else {
        let w = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        fold_words((h ^ w).wrapping_mul(K).rotate_left(29), &bytes[8..])
    }
}

/// Fold the fewer-than-eight remaining bytes.
fn fold_tail(h: u64, rest: &[u8], at: usize, acc: u64) -> u64 {
    if at == rest.len() {
        (h ^ acc).wrapping_mul(K).rotate_left(29)
    } else {
        fold_tail(h, rest, at + 1, acc | (u64::from(rest[at]) << (8 * at)))
    }
}

/// Fold a byte string: blocks of at most 64 bytes word by word, longer strings by halving at a word
/// boundary and combining the two halves, so the depth is `O(log n)` in every build profile.
fn fold_bytes(h: u64, bytes: &[u8]) -> u64 {
    if bytes.len() <= 64 {
        fold_words(h, bytes)
    } else {
        let mid = (bytes.len() / 2) & !7;
        let (l, r) = (
            fold_bytes(h, &bytes[..mid]),
            fold_bytes(h ^ K, &bytes[mid..]),
        );
        (l.rotate_left(17) ^ r).wrapping_mul(K).rotate_left(29)
    }
}

impl Hasher for Fold {
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 32)
    }
    fn write(&mut self, bytes: &[u8]) {
        let h = self.0 ^ (bytes.len() as u64).wrapping_mul(K);
        self.0 = fold_bytes(h, bytes);
    }
}

type FoldMap<'a> = HashMap<&'a [u8], u32, FoldState>;

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
        nl_mask(word(t)).count_ones() as usize + count_block(&t[t.len().min(8)..])
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
            Some(at + (m.trailing_zeros() / 8) as usize)
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
        first_nl(&t[..t.len() / 2]).or_else(|| first_nl(&t[t.len() / 2..]).map(|i| i + t.len() / 2))
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
        last_nl(&t[t.len() / 2..])
            .map(|i| i + t.len() / 2)
            .or_else(|| last_nl(&t[..t.len() / 2]))
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
                out.push(&t[..=i]);
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
        let cut = first_nl(&t[mid..])
            .map(|i| mid + i + 1)
            .filter(|&c| c < t.len())
            .or_else(|| last_nl(&t[..mid]).map(|i| i + 1));
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

fn intern<'a>(a: &[&'a [u8]], b: &[&'a [u8]]) -> (Vec<u32>, Vec<u32>, usize) {
    let mut map: FoldMap<'a> =
        HashMap::with_capacity_and_hasher(a.len() + b.len(), FoldState::random());
    let mut ia = vec![0u32; a.len()];
    let mut ib = vec![0u32; b.len()];
    let mut take = |l: &'a [u8]| -> u32 {
        let next = u32::try_from(map.len()).expect("fewer than 2^32 distinct lines");
        *map.entry(l).or_insert(next)
    };
    each(a, 0, &mut |i, l| ia[i] = take(l));
    each(b, 0, &mut |i, l| ib[i] = take(l));
    let n = map.len();
    (ia, ib, n)
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
    let (ia, ib, n_ids) = intern(&la, &lb);
    let mid = match algo {
        Algo::Minimal => diff_ids(&ia, &ib, n_ids),
        Algo::Histogram => diff_histogram_ids(&ia, &ib, n_ids),
    };
    let mut deleted = vec![false; pre_lines + la.len() + suf_old];
    let mut inserted = vec![false; pre_lines + lb.len() + suf_new];
    deleted[pre_lines..pre_lines + la.len()].copy_from_slice(&mid.deleted);
    inserted[pre_lines..pre_lines + lb.len()].copy_from_slice(&mid.inserted);
    LineDiff { deleted, inserted }
}

/// The largest line start at or before byte `p`: one past the last newline before `p`.
fn line_start(t: &[u8], p: usize) -> usize {
    last_nl(&t[..p]).map_or(0, |i| i + 1)
}

/// Shrink the common suffix length `q` until the suffix starts a line in both texts. The suffix
/// bytes are equal in both texts, so the first newline inside the suffix has the same offset in each.
fn suffix_on_line_start(ro: &[u8], rn: &[u8], q: usize) -> usize {
    let starts = |t: &[u8]| q >= t.len() || t[t.len() - q - 1] == b'\n';
    if q == 0 || (starts(ro) && starts(rn)) {
        q
    } else {
        first_nl(&ro[ro.len() - q..]).map_or(0, |k| q - k - 1)
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
    each(am, 0, &mut |_, &x| in_a[x as usize] = true);
    each(bm, 0, &mut |_, &x| in_b[x as usize] = true);
    // Compact: keep only lines whose id occurs on the other side; the rest are certain edits.
    let (mut ca, mut pa) = (Vec::new(), Vec::new());
    each(am, pre, &mut |i, &x| {
        if in_b[x as usize] {
            ca.push(x);
            pa.push(i);
        } else {
            deleted[i] = true;
        }
    });
    let (mut cb, mut pb) = (Vec::new(), Vec::new());
    each(bm, pre, &mut |j, &x| {
        if in_a[x as usize] {
            cb.push(x);
            pb.push(j);
        } else {
            inserted[j] = true;
        }
    });
    let mut ra = vec![false; ca.len()];
    let mut rb = vec![false; cb.len()];
    let size = 2 * (ca.len() + cb.len()) + 3;
    let mut vf = vec![0i32; size];
    let mut vb = vec![0i32; size];
    solve(&ca, &cb, 0, 0, &mut ra, &mut rb, &mut vf, &mut vb);
    each(&ra, 0, &mut |k, &d| deleted[pa[k]] = d);
    each(&rb, 0, &mut |k, &d| inserted[pb[k]] = d);
    LineDiff { deleted, inserted }
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
        forward(s, d, lo, mid).or_else(|| forward(s, d, mid + 2, hi))
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
    let run = snake(s, x0, y0);
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
        backward(s, d, lo, mid).or_else(|| backward(s, d, mid + 2, hi))
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
    let run = snake_back(s, x0, y0);
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
const NIL: u32 = u32::MAX;

struct Hist<'a> {
    a: &'a [u32],
    b: &'a [u32],
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
        a,
        b,
        cnt: vec![0; n_ids],
        head: vec![NIL; n_ids],
        nxt: vec![NIL; a.len()],
        del: vec![false; a.len()],
        ins: vec![false; b.len()],
        vf: vec![0; size],
        vb: vec![0; size],
    };
    hist(&mut h, (0, a.len()), (0, b.len()), 0);
    LineDiff {
        deleted: h.del,
        inserted: h.ins,
    }
}

fn hist(h: &mut Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize), depth: u32) {
    let p = common_prefix(&h.a[alo..ahi], &h.b[blo..bhi]);
    let (alo, blo) = (alo + p, blo + p);
    let sfx = common_suffix(&h.a[alo..ahi], &h.b[blo..bhi]);
    let (ahi, bhi) = (ahi - sfx, bhi - sfx);
    if alo == ahi {
        h.ins[blo..bhi].fill(true);
    } else if blo == bhi {
        h.del[alo..ahi].fill(true);
    } else if depth >= HIST_DEPTH {
        hist_fallback(h, (alo, ahi), (blo, bhi));
    } else {
        index_a(h, alo, ahi);
        let best = find_anchor(h, (alo, ahi), (blo, bhi));
        let common = any_common(h, blo, bhi);
        unindex_a(h, alo, ahi);
        match best {
            Some(an) => {
                let (i0, j0) = (an.i - an.bl, an.j - an.bl);
                let (i1, j1) = (i0 + an.len, j0 + an.len);
                hist(h, (alo, i0), (blo, j0), depth + 1);
                hist(h, (i1, ahi), (j1, bhi), depth + 1);
            }
            None if common => hist_fallback(h, (alo, ahi), (blo, bhi)),
            None => {
                h.del[alo..ahi].fill(true);
                h.ins[blo..bhi].fill(true);
            }
        }
    }
}

/// Solve a range with the minimal search.
fn hist_fallback(h: &mut Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize)) {
    let (a, b) = (h.a, h.b);
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

fn index_a(h: &mut Hist, alo: usize, ahi: usize) {
    let a = h.a;
    each(&a[alo..ahi], alo, &mut |i, &id| {
        let id = id as usize;
        h.cnt[id] += 1;
        h.nxt[i] = h.head[id];
        h.head[id] = i as u32;
    });
}

fn unindex_a(h: &mut Hist, alo: usize, ahi: usize) {
    let a = h.a;
    each(&a[alo..ahi], alo, &mut |_, &id| {
        h.cnt[id as usize] = 0;
        h.head[id as usize] = NIL;
    });
}

fn any_common(h: &mut Hist, blo: usize, bhi: usize) -> bool {
    let b = h.b;
    let mut found = false;
    each(&b[blo..bhi], blo, &mut |_, &id| {
        found |= h.cnt[id as usize] > 0
    });
    found
}

/// The rarest common line of `b[blo..bhi]` that occurs at most `HIST_LIMIT` times in the old range,
/// extended to the longest equal run around it.
fn find_anchor(h: &Hist, (alo, ahi): (usize, usize), (blo, bhi): (usize, usize)) -> Option<Anchor> {
    let mut best: Option<Anchor> = None;
    each(&h.b[blo..bhi], blo, &mut |j, &id| {
        let c = h.cnt[id as usize];
        if c > 0 && c <= HIST_LIMIT && best.is_none_or(|bst| c <= bst.cnt) {
            best = walk_chain(h, h.head[id as usize], (alo, ahi), (blo, bhi), j, c, best);
        }
    });
    best
}

/// Try every old position of the line, keeping the better anchor. Recursion over the chain.
fn walk_chain(
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
        let bl = common_suffix(&h.a[alo..i], &h.b[blo..j]);
        let fl = common_prefix(&h.a[i..ahi], &h.b[j..bhi]);
        let cand = Anchor {
            cnt: c,
            len: bl + fl,
            i,
            j,
            bl,
        };
        let better = match best {
            None => true,
            Some(b0) => cand.cnt < b0.cnt || (cand.cnt == b0.cnt && cand.len > b0.len),
        };
        walk_chain(
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
fn snake(s: &Search, x: i32, y: i32) -> i32 {
    if x >= s.n || y >= s.m || s.a[x as usize] != s.b[y as usize] {
        0
    } else {
        common_prefix(&s.a[x as usize..], &s.b[y as usize..]) as i32
    }
}

/// Backward run of equal ids ending before `(n - x, m - y)`.
fn snake_back(s: &Search, x: i32, y: i32) -> i32 {
    if x >= s.n || y >= s.m || s.a[(s.n - 1 - x) as usize] != s.b[(s.m - 1 - y) as usize] {
        0
    } else {
        common_suffix(&s.a[..(s.n - x) as usize], &s.b[..(s.m - y) as usize]) as i32
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
    /// `snake` of the real source on a search state with the given lists (`tests/myers_core.rs`).
    #[must_use]
    pub fn snake(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
        let s = super::Search { a, b, n: a.len() as i32, m: b.len() as i32, delta: 0, odd: false, off: 0, vf: &mut [], vb: &mut [] };
        super::snake(&s, x, y)
    }
    /// `snake_back` of the real source on a search state with the given lists.
    #[must_use]
    pub fn snake_back(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
        let s = super::Search { a, b, n: a.len() as i32, m: b.len() as i32, delta: 0, odd: false, off: 0, vf: &mut [], vb: &mut [] };
        super::snake_back(&s, x, y)
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
