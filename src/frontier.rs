//! Experimental frontier (best-first) and linear-space aligners for the same top-down objective as
//! [`crate::diff`]. Nothing here is used by the production differ.
//!
//! Cost model (identical to `diff.rs`): delete or insert a child costs its subtree size, pairing two
//! children costs `dist`, `dist(x, x) = 0` by id, `dist(x, y) = [label differs] + align(kids)`.
//!
//! * [`Algo::Threshold`] is a re-implementation of the doubling threshold DP. With `sym = false`
//!   and [`Orient::Keep`] it must reproduce `diff.rs`'s `cells`, `pairs` and `rounds` counters exactly
//!   (checked by `frontier_exp`).
//! * [`Algo::AStar`] is best-first search on the alignment grid with `h(i,j) = |R_a(i) - R_b(j)|`,
//!   which is consistent (see `astar`), so each cell is closed at most once. Diagonal edges are
//!   resolved lazily: they enter the queue at the cheap lower bound `|size a - size b|` and the
//!   recursive `dist` is called only when that entry is popped.
//! * [`Frontier::align_linear`] is a Hirschberg-style bidirectional reconstruction that keeps one
//!   banded row per direction instead of all rows.

use crate::intern::{Arena, Id};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::hash::{BuildHasherDefault, Hasher};

/// Priority-queue entry: (f, inverse g, cell, g, lazy).
type HeapEntry = Reverse<(u32, u32, u32, u32, bool)>;

const INF: u32 = u32::MAX / 4;

/// Multiplicative hasher for the integer pair keys.
#[derive(Default)]
pub struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, b: &[u8]) {
        for &x in b {
            self.0 = (self.0.rotate_left(5) ^ u64::from(x)).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}
type Memo = HashMap<u64, u32, BuildHasherDefault<Fx>>;

/// Which list is the row side, and so which list indexes the outer loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Orient {
    /// As given (before-list is the row side).
    Keep,
    /// The list with fewer elements is the row side.
    ShorterRows,
    /// The list with more elements is the row side.
    LongerRows,
    /// The list with the smaller total size is the row side.
    SmallerSizeRows,
}

/// Which solver to run on an align.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algo {
    /// Doubling threshold DP with stored rows.
    Threshold,
    /// Best-first search.
    AStar,
    /// Best-first when `max(n, m) >= k`, else threshold.
    Hybrid(usize),
}

/// A dispatch policy.
#[derive(Clone, Copy, Debug)]
pub struct Policy {
    /// Solver choice.
    pub algo: Algo,
    /// Orientation choice.
    pub orient: Orient,
    /// Memoise on the unordered pair (distances are symmetric).
    pub sym: bool,
}

impl Policy {
    /// Reproduces `diff.rs`.
    pub const THRESHOLD: Policy = Policy {
        algo: Algo::Threshold,
        orient: Orient::Keep,
        sym: false,
    };
    /// Best-first with ordered memo keys.
    pub const ASTAR: Policy = Policy {
        algo: Algo::AStar,
        orient: Orient::Keep,
        sym: false,
    };
}

/// One step of an alignment as indices into the lists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// Pair `a[i]` with `b[j]`.
    Pair(usize, usize),
    /// Delete `a[i]`.
    Del(usize),
    /// Insert `b[j]`.
    Ins(usize),
}

/// Work counters.
#[derive(Clone, Copy, Debug, Default)]
pub struct FStats {
    /// Non-trivial aligns (both middle lists non-empty).
    pub aligns: u64,
    /// Grid cells evaluated (threshold: cells filled over all rounds; best-first: cells closed).
    pub cells: u64,
    /// Distinct unequal pairs whose distance was computed.
    pub pairs: u64,
    /// Memo hits.
    pub memo_hits: u64,
    /// Threshold rounds (threshold only).
    pub rounds: u64,
    /// Heap pushes (best-first only).
    pub pushes: u64,
}

/// One banded DP row: kept cells `lo .. lo + v.len()`.
#[derive(Clone, Debug)]
pub struct Row {
    lo: usize,
    v: Vec<u32>,
}

impl Row {
    fn at(&self, j: usize) -> Option<u32> {
        let k = j.checked_sub(self.lo)?;
        self.v.get(k).copied().filter(|&x| x < INF)
    }
}

/// Result of a per-align run.
#[derive(Clone, Debug)]
pub struct AlignRun {
    /// Optimal cost.
    pub cost: u32,
    /// Cells evaluated by this align alone (not counting nested aligns).
    pub cells: u64,
}

/// The experimental differ.
pub struct Frontier<'a> {
    arena: &'a Arena,
    /// Dispatch policy.
    pub policy: Policy,
    memo: Memo,
    /// Counters.
    pub stats: FStats,
    cur_cells: u64,
}

fn suffix_sums(x: &[u32]) -> Vec<u32> {
    let mut out = vec![0u32; x.len() + 1];
    for i in (0..x.len()).rev() {
        out[i] = out[i + 1] + x[i];
    }
    out
}

fn h(ra: &[u32], rb: &[u32], i: usize, j: usize) -> u32 {
    ra[i].abs_diff(rb[j])
}

impl<'a> Frontier<'a> {
    /// A fresh differ.
    #[must_use]
    pub fn new(arena: &'a Arena, policy: Policy) -> Self {
        Self {
            arena,
            policy,
            memo: Memo::default(),
            stats: FStats::default(),
            cur_cells: 0,
        }
    }

    /// Number of memoised pairs.
    #[must_use]
    pub fn memo_len(&self) -> usize {
        self.memo.len()
    }

    /// Memoised unequal pairs, as `(x, y)` ids.
    #[must_use]
    pub fn memo_pairs(&self) -> Vec<(Id, Id)> {
        self.memo
            .keys()
            .map(|&k| (Id((k >> 32) as u32), Id(k as u32)))
            .collect()
    }

    fn key(&self, x: Id, y: Id) -> u64 {
        let (p, q) = if self.policy.sym && y.0 < x.0 {
            (y, x)
        } else {
            (x, y)
        };
        (u64::from(p.0) << 32) | u64::from(q.0)
    }

    /// Top-down distance.
    pub fn dist(&mut self, x: Id, y: Id) -> u32 {
        if x == y {
            return 0;
        }
        let key = self.key(x, y);
        if let Some(&d) = self.memo.get(&key) {
            self.stats.memo_hits += 1;
            return d;
        }
        self.stats.pairs += 1;
        let rel = u32::from(self.arena.label(x) != self.arena.label(y));
        let arena = self.arena;
        let d = rel + self.align(arena.kids(x), arena.kids(y)).cost;
        self.memo.insert(key, d);
        d
    }

    /// Align two child lists (strip equal ends, then dispatch). Cells are those of this align only.
    pub fn align(&mut self, a: &[Id], b: &[Id]) -> AlignRun {
        let saved = std::mem::replace(&mut self.cur_cells, 0);
        let (n, m) = (a.len(), b.len());
        let mut p = 0;
        while p < n.min(m) && a[p] == b[p] {
            p += 1;
        }
        let mut s = 0;
        while s < n.min(m) - p && a[n - 1 - s] == b[m - 1 - s] {
            s += 1;
        }
        let cost = self.align_mid(&a[p..n - s], &b[p..m - s]);
        let cells = self.cur_cells;
        self.stats.cells += cells;
        self.cur_cells = saved;
        AlignRun { cost, cells }
    }

    fn sizes(&self, a: &[Id]) -> Vec<u32> {
        a.iter().map(|&x| self.arena.size(x)).collect()
    }

    fn choose(&self, a: &[Id], b: &[Id], sa: &[u32], sb: &[u32]) -> (bool, Algo) {
        let swap = match self.policy.orient {
            Orient::Keep => false,
            Orient::ShorterRows => a.len() > b.len(),
            Orient::LongerRows => a.len() < b.len(),
            Orient::SmallerSizeRows => sa.iter().sum::<u32>() > sb.iter().sum::<u32>(),
        };
        let algo = match self.policy.algo {
            Algo::Hybrid(k) => {
                if a.len().max(b.len()) >= k {
                    Algo::AStar
                } else {
                    Algo::Threshold
                }
            }
            other => other,
        };
        (swap, algo)
    }

    fn align_mid(&mut self, a: &[Id], b: &[Id]) -> u32 {
        let (sa, sb) = (self.sizes(a), self.sizes(b));
        if a.is_empty() || b.is_empty() {
            return sa.iter().sum::<u32>() + sb.iter().sum::<u32>();
        }
        self.stats.aligns += 1;
        let (swap, algo) = self.choose(a, b, &sa, &sb);
        let (a, b, sa, sb) = if swap { (b, a, sb, sa) } else { (a, b, sa, sb) };
        match algo {
            Algo::AStar => self.astar(a, b, &sa, &sb),
            Algo::Threshold | Algo::Hybrid(_) => self.threshold(a, b, &sa, &sb).0,
        }
    }

    // ----------------------------------------------------------------------------------------
    // Threshold DP, a faithful copy of diff.rs's fill with the stored rows exposed.
    // ----------------------------------------------------------------------------------------

    fn threshold(&mut self, a: &[Id], b: &[Id], sa: &[u32], sb: &[u32]) -> (u32, Vec<Row>) {
        let (ra, rb) = (suffix_sums(sa), suffix_sums(sb));
        let mut tau = h(&ra, &rb, 0, 0);
        loop {
            self.stats.rounds += 1;
            if let Some(rows) = self.fill(a, b, sa, sb, &ra, &rb, tau, a.len(), true) {
                let cost = rows
                    .last()
                    .and_then(|r| r.at(b.len()))
                    .expect("final cell kept");
                return (cost, rows);
            }
            tau = tau.saturating_mul(2).max(tau + 1);
        }
    }

    /// Rows `0..=upto`. With `keep_all` false only the last row is returned. `None` when some row
    /// has no kept cell, or (when `upto == n`) the final cell is pruned.
    #[allow(clippy::too_many_arguments)]
    fn fill(
        &mut self,
        a: &[Id],
        b: &[Id],
        sa: &[u32],
        sb: &[u32],
        ra: &[u32],
        rb: &[u32],
        tau: u32,
        upto: usize,
        keep_all: bool,
    ) -> Option<Vec<Row>> {
        let m = b.len();
        let mut v0 = vec![0u32];
        for j in 1..=m {
            let f = v0[j - 1] + sb[j - 1];
            if f + h(ra, rb, 0, j) > tau {
                break;
            }
            v0.push(f);
        }
        let mut rows: Vec<Row> = vec![Row { lo: 0, v: v0 }];
        for i in 1..=upto {
            let row = self.next_row(rows.last().expect("row"), i, a, b, sa, sb, ra, rb, tau)?;
            if keep_all {
                rows.push(row);
            } else {
                rows.clear();
                rows.push(row);
            }
        }
        if upto == a.len() {
            rows.last().and_then(|r| r.at(m))?;
        }
        Some(rows)
    }

    #[allow(clippy::too_many_arguments)]
    fn next_row(
        &mut self,
        prev: &Row,
        i: usize,
        a: &[Id],
        b: &[Id],
        sa: &[u32],
        sb: &[u32],
        ra: &[u32],
        rb: &[u32],
        tau: u32,
    ) -> Option<Row> {
        let m = b.len();
        let (plo, phi) = (prev.lo, prev.lo + prev.v.len() - 1);
        let mut v: Vec<u32> = Vec::new();
        let mut j = plo;
        loop {
            let del = prev.at(j).map_or(INF, |x| x + sa[i - 1]);
            let ins = if j > plo {
                v.last().copied().unwrap_or(INF).saturating_add(sb[j - 1])
            } else {
                INF
            };
            let mut best = del.min(ins);
            if j > 0 {
                if let Some(diag) = prev.at(j - 1) {
                    let lbound = diag + sa[i - 1].abs_diff(sb[j - 1]);
                    if lbound < best && lbound + h(ra, rb, i, j) <= tau {
                        best = best.min(diag + self.dist(a[i - 1], b[j - 1]));
                    }
                }
            }
            self.cur_cells += 1;
            let keep = best + h(ra, rb, i, j) <= tau;
            v.push(if keep { best } else { INF });
            j += 1;
            let more_diag = j <= phi + 1;
            let more_ins = v.last().is_some_and(|&x| x < INF);
            if j > m || !(more_diag || more_ins) {
                break;
            }
        }
        let first = v.iter().position(|&x| x < INF)?;
        let last = v.iter().rposition(|&x| x < INF)?;
        Some(Row {
            lo: plo + first,
            v: v[first..=last].to_vec(),
        })
    }

    fn trace(&mut self, a: &[Id], b: &[Id], sa: &[u32], sb: &[u32], rows: &[Row]) -> Vec<Step> {
        let (mut i, mut j) = (a.len(), b.len());
        let mut out = Vec::with_capacity(i + j);
        let get = |i: usize, j: usize| rows[i].at(j).unwrap_or(INF);
        while i > 0 || j > 0 {
            let here = get(i, j);
            if i > 0 && j > 0 {
                let diag = get(i - 1, j - 1);
                if diag < INF {
                    if a[i - 1] == b[j - 1] && diag == here {
                        out.push(Step::Pair(i - 1, j - 1));
                        i -= 1;
                        j -= 1;
                        continue;
                    }
                    let lb = diag + sa[i - 1].abs_diff(sb[j - 1]);
                    if lb <= here && diag + self.dist(a[i - 1], b[j - 1]) == here {
                        out.push(Step::Pair(i - 1, j - 1));
                        i -= 1;
                        j -= 1;
                        continue;
                    }
                }
            }
            if i > 0 && get(i - 1, j).saturating_add(sa[i - 1]) == here {
                out.push(Step::Del(i - 1));
                i -= 1;
            } else {
                assert!(
                    j > 0 && get(i, j - 1).saturating_add(sb[j - 1]) == here,
                    "trace invariant"
                );
                out.push(Step::Ins(j - 1));
                j -= 1;
            }
        }
        out.reverse();
        out
    }

    /// Stored-rows alignment of two non-empty lists: cost, steps, and the number of `u32` cells held.
    pub fn align_rows(&mut self, a: &[Id], b: &[Id]) -> (u32, Vec<Step>, usize) {
        let (sa, sb) = (self.sizes(a), self.sizes(b));
        let (cost, rows) = self.threshold(a, b, &sa, &sb);
        let held = rows.iter().map(|r| r.v.len()).sum();
        let steps = self.trace(a, b, &sa, &sb, &rows);
        (cost, steps, held)
    }

    // ----------------------------------------------------------------------------------------
    // Best-first search.
    // ----------------------------------------------------------------------------------------

    /// A* on the grid. `h` is consistent: a delete or insert changes `h` by at most the edge cost
    /// (the size of the consumed child), and a diagonal changes it by `|sa - sb| <= dist`.
    fn astar(&mut self, a: &[Id], b: &[Id], sa: &[u32], sb: &[u32]) -> u32 {
        let (n, m) = (a.len(), b.len());
        let w = m + 1;
        let (ra, rb) = (suffix_sums(sa), suffix_sums(sb));
        // 0 = unset; otherwise (g + 1) with bit 31 marking a closed cell.
        const CLOSED: u32 = 1 << 31;
        let mut g = vec![0u32; (n + 1) * w];
        let mut heap: BinaryHeap<HeapEntry> = BinaryHeap::new();
        // Entry: (f, inverse g for deeper-first ties, cell, g, lazy).
        let push = |heap: &mut BinaryHeap<HeapEntry>,
                    stats: &mut FStats,
                    i: usize,
                    j: usize,
                    gv: u32,
                    lazy: bool| {
            let f = gv + h(&ra, &rb, i, j);
            stats.pushes += 1;
            heap.push(Reverse((f, u32::MAX - gv, (i * w + j) as u32, gv, lazy)));
        };
        g[0] = 1;
        push(&mut heap, &mut self.stats, 0, 0, 0, false);
        while let Some(Reverse((_, _, cell, gv, lazy))) = heap.pop() {
            let (i, j) = (cell as usize / w, cell as usize % w);
            let cur = g[cell as usize];
            if cur & CLOSED != 0 {
                continue;
            }
            if lazy {
                let lb = sa[i - 1].abs_diff(sb[j - 1]);
                let gsrc = gv - lb;
                if cur != 0 && cur - 1 <= gv {
                    continue;
                }
                let d = self.dist(a[i - 1], b[j - 1]);
                let gn = gsrc + d;
                let cur = g[cell as usize];
                if cur == 0 || gn < cur - 1 {
                    g[cell as usize] = gn + 1;
                    push(&mut heap, &mut self.stats, i, j, gn, false);
                }
                continue;
            }
            if cur - 1 != gv {
                continue;
            }
            g[cell as usize] = cur | CLOSED;
            self.cur_cells += 1;
            if i == n && j == m {
                return gv;
            }
            if i < n {
                let gn = gv + sa[i];
                let c = (i + 1) * w + j;
                if g[c] & CLOSED == 0 && (g[c] == 0 || gn < g[c] - 1) {
                    g[c] = gn + 1;
                    push(&mut heap, &mut self.stats, i + 1, j, gn, false);
                }
            }
            if j < m {
                let gn = gv + sb[j];
                let c = i * w + j + 1;
                if g[c] & CLOSED == 0 && (g[c] == 0 || gn < g[c] - 1) {
                    g[c] = gn + 1;
                    push(&mut heap, &mut self.stats, i, j + 1, gn, false);
                }
            }
            if i < n && j < m {
                let c = (i + 1) * w + j + 1;
                if g[c] & CLOSED == 0 {
                    if a[i] == b[j] {
                        if g[c] == 0 || gv < g[c] - 1 {
                            g[c] = gv + 1;
                            push(&mut heap, &mut self.stats, i + 1, j + 1, gv, false);
                        }
                    } else {
                        let lb = sa[i].abs_diff(sb[j]);
                        if g[c] == 0 || gv + lb < g[c] - 1 {
                            push(&mut heap, &mut self.stats, i + 1, j + 1, gv + lb, true);
                        }
                    }
                }
            }
        }
        unreachable!("the final cell is always reachable")
    }

    // ----------------------------------------------------------------------------------------
    // Linear-space bidirectional reconstruction.
    // ----------------------------------------------------------------------------------------

    /// Optimal cost by threshold doubling with only the last row kept.
    fn cost_only(&mut self, a: &[Id], b: &[Id], sa: &[u32], sb: &[u32]) -> u32 {
        let (ra, rb) = (suffix_sums(sa), suffix_sums(sb));
        let mut tau = h(&ra, &rb, 0, 0);
        loop {
            self.stats.rounds += 1;
            if let Some(rows) = self.fill(a, b, sa, sb, &ra, &rb, tau, a.len(), false) {
                return rows[0].at(b.len()).expect("final cell kept");
            }
            tau = tau.saturating_mul(2).max(tau + 1);
        }
    }

    /// Hirschberg-style reconstruction of one optimal alignment of two non-empty lists. Holds at
    /// most two banded rows (plus reversed copies of the inputs) at a time. Returns cost, steps and
    /// the largest number of `u32` row cells held at once.
    pub fn align_linear(&mut self, a: &[Id], b: &[Id]) -> (u32, Vec<Step>, usize) {
        let (sa, sb) = (self.sizes(a), self.sizes(b));
        let c = self.cost_only(a, b, &sa, &sb);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let mut peak = 0;
        self.hirsch(a, b, c, 0, 0, &mut out, &mut peak);
        (c, out, peak)
    }

    #[allow(clippy::too_many_arguments)]
    fn hirsch(
        &mut self,
        a: &[Id],
        b: &[Id],
        c: u32,
        oi: usize,
        oj: usize,
        out: &mut Vec<Step>,
        peak: &mut usize,
    ) {
        let (n, m) = (a.len(), b.len());
        if n == 0 {
            out.extend((0..m).map(|j| Step::Ins(oj + j)));
            return;
        }
        if m == 0 {
            out.extend((0..n).map(|i| Step::Del(oi + i)));
            return;
        }
        let (sa, sb) = (self.sizes(a), self.sizes(b));
        if n == 1 {
            let (ra, rb) = (suffix_sums(&sa), suffix_sums(&sb));
            let rows = self
                .fill(a, b, &sa, &sb, &ra, &rb, c, 1, true)
                .expect("subproblem cost is exact");
            *peak = (*peak).max(rows.iter().map(|r| r.v.len()).sum());
            for st in self.trace(a, b, &sa, &sb, &rows) {
                out.push(match st {
                    Step::Pair(i, j) => Step::Pair(oi + i, oj + j),
                    Step::Del(i) => Step::Del(oi + i),
                    Step::Ins(j) => Step::Ins(oj + j),
                });
            }
            return;
        }
        let mid = n / 2;
        let (ra, rb) = (suffix_sums(&sa), suffix_sums(&sb));
        let fwd = self
            .fill(a, b, &sa, &sb, &ra, &rb, c, mid, false)
            .expect("forward half within exact cost");
        let fwd = fwd.into_iter().next().expect("row");
        let ar: Vec<Id> = a.iter().rev().copied().collect();
        let br: Vec<Id> = b.iter().rev().copied().collect();
        let sar: Vec<u32> = sa.iter().rev().copied().collect();
        let sbr: Vec<u32> = sb.iter().rev().copied().collect();
        let (rar, rbr) = (suffix_sums(&sar), suffix_sums(&sbr));
        let rev = self
            .fill(&ar, &br, &sar, &sbr, &rar, &rbr, c, n - mid, false)
            .expect("reverse half within exact cost");
        let rev = rev.into_iter().next().expect("row");
        *peak = (*peak).max(fwd.v.len() + rev.v.len());
        let mut split = None;
        for j in 0..=m {
            if let (Some(f), Some(r)) = (fwd.at(j), rev.at(m - j)) {
                if f + r == c {
                    split = Some((j, f, r));
                    break;
                }
            }
        }
        let (j, f, r) = split.expect("an optimal path crosses the middle row inside both bands");
        self.hirsch(&a[..mid], &b[..j], f, oi, oj, out, peak);
        self.hirsch(&a[mid..], &b[j..], r, oi + mid, oj + j, out, peak);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff::align_within;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn rand_tree(r: &mut Rng, a: &mut Arena, depth: u32, labels: u64) -> Id {
        let n = if depth == 0 { 0 } else { r.below(4) as usize };
        let k: Vec<Id> = (0..n).map(|_| rand_tree(r, a, depth - 1, labels)).collect();
        a.mk(r.below(labels) as u32, &k)
    }

    fn oracle_list(a: &Arena, ka: &[Id], kb: &[Id]) -> u32 {
        let (n, m) = (ka.len(), kb.len());
        let mut d = vec![vec![0u32; m + 1]; n + 1];
        for i in 1..=n {
            d[i][0] = d[i - 1][0] + a.size(ka[i - 1]);
        }
        for j in 1..=m {
            d[0][j] = d[0][j - 1] + a.size(kb[j - 1]);
        }
        for i in 1..=n {
            for j in 1..=m {
                let del = d[i - 1][j] + a.size(ka[i - 1]);
                let ins = d[i][j - 1] + a.size(kb[j - 1]);
                let pr = d[i - 1][j - 1] + oracle_tree(a, ka[i - 1], kb[j - 1]);
                d[i][j] = del.min(ins).min(pr);
            }
        }
        d[n][m]
    }

    fn oracle_tree(a: &Arena, x: Id, y: Id) -> u32 {
        u32::from(a.label(x) != a.label(y)) + oracle_list(a, a.kids(x), a.kids(y))
    }

    fn step_cost(f: &mut Frontier, a: &[Id], b: &[Id], steps: &[Step]) -> u32 {
        let ar = f.arena;
        steps
            .iter()
            .map(|s| match *s {
                Step::Pair(i, j) => f.dist(a[i], b[j]),
                Step::Del(i) => ar.size(a[i]),
                Step::Ins(j) => ar.size(b[j]),
            })
            .sum()
    }

    #[test]
    fn all_solvers_agree_with_oracle_and_diff_rs() {
        let mut r = Rng(0x1234_5678_9abc_def1);
        for case in 0..1500 {
            let mut arena = Arena::new();
            let labels = 1 + r.below(3);
            let pool: Vec<Id> = (0..6)
                .map(|_| rand_tree(&mut r, &mut arena, 3, labels))
                .collect();
            let la = (0..r.below(13))
                .map(|_| pool[r.below(6) as usize])
                .collect::<Vec<_>>();
            let lb = (0..r.below(13))
                .map(|_| pool[r.below(6) as usize])
                .collect::<Vec<_>>();
            let want = oracle_list(&arena, &la, &lb);
            assert_eq!(
                align_within(&arena, &la, &lb, 1 << 20),
                Some(want),
                "diff.rs vs oracle, case {case}"
            );
            let policies = [
                Policy::THRESHOLD,
                Policy::ASTAR,
                Policy {
                    algo: Algo::AStar,
                    orient: Orient::ShorterRows,
                    sym: true,
                },
                Policy {
                    algo: Algo::Threshold,
                    orient: Orient::LongerRows,
                    sym: true,
                },
                Policy {
                    algo: Algo::Hybrid(3),
                    orient: Orient::SmallerSizeRows,
                    sym: true,
                },
            ];
            for p in policies {
                let mut f = Frontier::new(&arena, p);
                let got = f.align(&la, &lb);
                assert_eq!(got.cost, want, "{p:?} case {case}");
            }
            if !la.is_empty() && !lb.is_empty() {
                let mut f = Frontier::new(&arena, Policy::THRESHOLD);
                let (la_s, lb_s): (&[Id], &[Id]) = (&la, &lb);
                let (c1, s1, _) = f.align_rows(la_s, lb_s);
                let (c2, s2, _) = f.align_linear(la_s, lb_s);
                assert_eq!((c1, c2), (want, want), "rows/linear cost case {case}");
                assert_eq!(
                    step_cost(&mut f, la_s, lb_s, &s1),
                    want,
                    "rows steps case {case}"
                );
                assert_eq!(
                    step_cost(&mut f, la_s, lb_s, &s2),
                    want,
                    "linear steps case {case}"
                );
                // The steps must consume both lists in order exactly once.
                let (mut ci, mut cj) = (0, 0);
                for s in &s2 {
                    match *s {
                        Step::Pair(i, j) => {
                            assert_eq!((i, j), (ci, cj));
                            ci += 1;
                            cj += 1;
                        }
                        Step::Del(i) => {
                            assert_eq!(i, ci);
                            ci += 1;
                        }
                        Step::Ins(j) => {
                            assert_eq!(j, cj);
                            cj += 1;
                        }
                    }
                }
                assert_eq!((ci, cj), (la.len(), lb.len()));
            }
        }
    }

    #[test]
    fn tree_distance_matches_oracle() {
        let mut r = Rng(77);
        for _ in 0..300 {
            let mut arena = Arena::new();
            let x = rand_tree(&mut r, &mut arena, 4, 2);
            let y = rand_tree(&mut r, &mut arena, 4, 2);
            let want = oracle_tree(&arena, x, y);
            for p in [
                Policy::THRESHOLD,
                Policy::ASTAR,
                Policy {
                    algo: Algo::AStar,
                    orient: Orient::ShorterRows,
                    sym: true,
                },
            ] {
                let mut f = Frontier::new(&arena, p);
                assert_eq!(f.dist(x, y), want);
            }
        }
    }
}
