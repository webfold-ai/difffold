//! Exact threshold filter for general ordered tree edit distance.
//!
//! [`within`] answers "is the tree edit distance at most `tau`?". It returns `Some(d)` with the exact
//! distance `d` from [`crate::ted`] when `d <= tau`, and `None` otherwise. A pair is rejected only by a
//! stage whose lower bound already exceeds `tau`, so no pair within the threshold is ever rejected.
//!
//! The stages run cheapest first, and the exact solver runs only on the survivors:
//!
//! 1. size: `|n - m|`.
//! 2. label multiset: the number of nodes that cannot be matched to an equal label.
//! 3. preorder sequence: Levenshtein distance over labels.
//! 4. postorder sequence: the same over postorder.
//! 5. exact: [`crate::ted::ted_within`], the existing threshold search of the exact solver.
//!
//! # Cost model
//!
//! The exact solver charges 1 per inserted or deleted node. A relabel costs 0 when the labels are equal,
//! 1 when the labels differ and the kinds agree, and 2 when the kinds differ. Every stage below is a
//! lower bound under that model.
//!
//! * Size. A mapping of `k` pairs deletes `n - k` and inserts `m - k` nodes, so it costs at least `|n - m|`.
//! * Labels. A mapping of `k` pairs costs `n + m - k - e` or more, where `e` counts the pairs with equal
//!   labels, because every pair with unequal labels costs at least 1. Since `k <= min(n, m)` and `e` is at
//!   most the multiset overlap of the labels, the cost is at least `max(n, m) - overlap`. Kinds are
//!   ignored here, which only weakens the bound.
//! * Traversals. A valid tree edit mapping is one to one and preserves the ancestor relation in both
//!   directions. Such a mapping is monotone in postorder, and it is also monotone in preorder: for two
//!   mapped pairs, either one node is an ancestor of the other on both sides, or both are disjoint
//!   subtrees ordered the same way on both sides. Its mapped pairs therefore form a monotone alignment of
//!   the two sequences, with unmapped nodes as indels. Each indel costs 1 in both the solver and the
//!   Levenshtein distance. The symbol of a node is its label alone. A mapped pair with equal labels costs 0
//!   in the solver, whatever the kinds, and 0 as a substitution. A mapped pair with different labels costs
//!   1 or 2 in the solver, and 1 as a substitution. So the Levenshtein distance over labels is at most the
//!   mapping cost. The symbol must not include the kind: a pair with equal labels and different kinds costs
//!   0 in the solver, so a kind-aware symbol would charge 1 there and could reject a pair within the
//!   threshold. `tests/ted_filter.rs` pins this case.
//!
//! # Trap: insert/delete-only distances
//!
//! The insert/delete-only line distance of [`crate::lines`] (Myers, `n + m - 2 LCS`) charges 2 per relabel,
//! while a tree edit charges 1. It can exceed the tree distance, so it must not be used as a stage here.
//! The stages in this module use the substitution cost of 1 instead. `tests/ted_filter.rs` pins a pair
//! where the insert/delete-only distance exceeds the tree distance.
//!
//! The traversal stages are tested for exactness, not proved. See `notes/lanes/TED-FILTER.md`.

use crate::ted::{ted_within, PostTree};
use std::collections::HashMap;
use std::time::Instant;

/// Work and rejection counts of one pipeline stage.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct StageStats {
    /// Pairs that reached this stage.
    pub entered: u64,
    /// Pairs this stage rejected (its lower bound exceeded `tau`, or for the exact stage, the distance did).
    pub rejected: u64,
    /// Wall time spent in this stage, in nanoseconds.
    pub nanos: u64,
}

impl StageStats {
    fn record(&mut self, rejected: bool, started: Instant) {
        self.entered += 1;
        self.rejected += u64::from(rejected);
        self.nanos += elapsed_nanos(started);
    }

    fn add(&mut self, other: &StageStats) {
        self.entered += other.entered;
        self.rejected += other.rejected;
        self.nanos += other.nanos;
    }
}

/// Per-stage statistics of one [`within_stats`] call, or summed over many calls with [`FilterStats::add`].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct FilterStats {
    /// Stage 1, the size bound.
    pub size: StageStats,
    /// Stage 2, the label multiset bound.
    pub labels: StageStats,
    /// Time to build the label sequences for stages 3 and 4, in nanoseconds.
    pub prep_nanos: u64,
    /// Stage 3, the preorder sequence Levenshtein bound.
    pub preorder: StageStats,
    /// Stage 4, the postorder sequence Levenshtein bound.
    pub postorder: StageStats,
    /// Stage 5, the exact threshold solver on the survivors.
    pub exact: StageStats,
}

impl FilterStats {
    /// Add the counts and times of `other` to `self`.
    pub fn add(&mut self, other: &FilterStats) {
        self.size.add(&other.size);
        self.labels.add(&other.labels);
        self.prep_nanos += other.prep_nanos;
        self.preorder.add(&other.preorder);
        self.postorder.add(&other.postorder);
        self.exact.add(&other.exact);
    }

    /// Time spent in the filter stages, excluding the exact solver, in nanoseconds.
    #[must_use]
    pub fn filter_nanos(&self) -> u64 {
        self.size.nanos
            + self.labels.nanos
            + self.prep_nanos
            + self.preorder.nanos
            + self.postorder.nanos
    }
}

/// `Some(d)` with the exact tree edit distance `d` when `d <= tau`, else `None`.
#[must_use]
pub fn within(a: &PostTree, b: &PostTree, tau: u32) -> Option<u32> {
    within_stats(a, b, tau).0
}

/// [`within`] with per-stage counts and times.
#[must_use]
pub fn within_stats(a: &PostTree, b: &PostTree, tau: u32) -> (Option<u32>, FilterStats) {
    let mut st = FilterStats::default();
    let (n, m) = (a.len(), b.len());
    if n == 0 || m == 0 {
        // Inserting or deleting every node of the other tree is the only mapping, and the solver agrees.
        let d = u32::try_from(n.max(m)).expect("tree sizes fit in u32");
        return ((d <= tau).then_some(d), st);
    }
    let tau_us = tau as usize;

    let t = Instant::now();
    let reject = n.abs_diff(m) > tau_us;
    st.size.record(reject, t);
    if reject {
        return (None, st);
    }

    let t = Instant::now();
    let reject = label_lower_bound(a, b) as usize > tau_us;
    st.labels.record(reject, t);
    if reject {
        return (None, st);
    }

    let t = Instant::now();
    let mut ids = HashMap::new();
    let sa = sequences(a, &mut ids);
    let sb = sequences(b, &mut ids);
    st.prep_nanos = elapsed_nanos(t);

    let t = Instant::now();
    let reject = levenshtein_within(&sa.pre, &sb.pre, tau_us).is_none();
    st.preorder.record(reject, t);
    if reject {
        return (None, st);
    }

    let t = Instant::now();
    let reject = levenshtein_within(&sa.post, &sb.post, tau_us).is_none();
    st.postorder.record(reject, t);
    if reject {
        return (None, st);
    }

    // The distance never exceeds n + m, and the exact solver allocates a band of width 2 tau + 1, so the
    // threshold is clamped to n + m. At that clamp the result is always Some.
    let cap = u32::try_from(n + m).unwrap_or(u32::MAX);
    let t = Instant::now();
    let d = ted_within(a, b, tau.min(cap));
    st.exact.record(d.is_none(), t);
    (d, st)
}

/// Stage 1 as a lower bound: `|n - m|`.
#[must_use]
pub fn size_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    u32::try_from(a.len().abs_diff(b.len())).expect("tree sizes fit in u32")
}

/// Stage 2 as a lower bound: `max(n, m)` minus the size of the label multiset intersection.
#[must_use]
pub fn label_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    let mut la = a.label.clone();
    let mut lb = b.label.clone();
    la.sort_unstable();
    lb.sort_unstable();
    let (mut i, mut j, mut common) = (0, 0, 0usize);
    while i < la.len() && j < lb.len() {
        match la[i].cmp(&lb[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                common += 1;
                i += 1;
                j += 1;
            }
        }
    }
    u32::try_from(a.len().max(b.len()) - common).expect("tree sizes fit in u32")
}

/// Stage 3 as a lower bound: the preorder sequence Levenshtein distance over labels.
#[must_use]
pub fn preorder_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    let mut ids = HashMap::new();
    let sa = sequences(a, &mut ids);
    let sb = sequences(b, &mut ids);
    levenshtein_distance(&sa.pre, &sb.pre)
}

/// Stage 4 as a lower bound: the postorder sequence Levenshtein distance over labels.
#[must_use]
pub fn postorder_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    let mut ids = HashMap::new();
    let sa = sequences(a, &mut ids);
    let sb = sequences(b, &mut ids);
    levenshtein_distance(&sa.post, &sb.post)
}

/// Unbounded Levenshtein distance, as a `u32`. Only for the lower-bound functions and tests.
fn levenshtein_distance(x: &[u32], y: &[u32]) -> u32 {
    let k = x.len() + y.len();
    let d = levenshtein_within(x, y, k).expect("the distance never exceeds the total length");
    u32::try_from(d).expect("sequence lengths fit in u32")
}

/// Symbol sequences of one tree: label ids in postorder and in preorder.
struct Sequences {
    pre: Vec<u32>,
    post: Vec<u32>,
}

/// The preorder and postorder label sequences of `t`. Symbols are dense ids shared through `ids`, so two
/// trees built with the same map compare symbols by equality.
///
/// The preorder of a postorder tree is the order by leftmost leaf ascending, then by postorder index
/// descending. Nodes with the same leftmost leaf form one chain of ancestors, which is ordered from the
/// top down by decreasing index. Nodes with different leftmost leaves are either disjoint, in which case
/// the one with the smaller leftmost leaf is to the left, or nested, in which case the outer one has the
/// smaller leftmost leaf.
fn sequences(t: &PostTree, ids: &mut HashMap<u32, u32>) -> Sequences {
    let n = t.len();
    let mut sym = Vec::with_capacity(n);
    for &label in &t.label {
        let next = u32::try_from(ids.len()).expect("symbol count fits in u32");
        sym.push(*ids.entry(label).or_insert(next));
    }
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_unstable_by(|&x, &y| t.lml[x].cmp(&t.lml[y]).then(y.cmp(&x)));
    let pre = order.iter().map(|&x| sym[x]).collect();
    Sequences { pre, post: sym }
}

/// Levenshtein distance over `u32` symbols with unit insert, delete and substitute costs, computed only if
/// it is at most `k` (Ukkonen's cutoff). Returns `Some(d)` with the exact distance `d <= k`, else `None`.
///
/// This is a plain dynamic program, not the insert/delete-only line engine. A substitution costs 1 here,
/// which is what the traversal bounds in the module documentation need.
#[must_use]
pub fn levenshtein_within(x: &[u32], y: &[u32], k: usize) -> Option<usize> {
    let (n, m) = (x.len(), y.len());
    if n.abs_diff(m) > k {
        return None;
    }
    // The distance is at most max(n, m), so a larger k is equivalent and keeps `inf` small.
    let k = k.min(n.max(m));
    // Every cell value is capped at `inf`. A cell above `k` cannot lead to a result within `k`.
    let inf = k + 1;
    let mut prev = vec![inf; m + 1];
    let mut cur = vec![inf; m + 1];
    for (j, cell) in prev.iter_mut().enumerate().take(m.min(k) + 1) {
        *cell = j;
    }
    for i in 1..=n {
        // Band of row i: columns j with |i - j| <= k. Cells outside it are `inf`.
        let lo = i.saturating_sub(k).max(1);
        let hi = (i + k).min(m);
        cur[0] = if i <= k { i } else { inf };
        if lo >= 2 {
            // The left neighbour of the first band cell lies outside the band and must read as `inf`.
            cur[lo - 1] = inf;
        }
        let mut row_min = cur[0];
        for j in lo..=hi {
            let sub = prev[j - 1] + usize::from(x[i - 1] != y[j - 1]);
            let del = prev[j] + 1;
            let ins = cur[j - 1] + 1;
            let v = sub.min(del).min(ins).min(inf);
            cur[j] = v;
            row_min = row_min.min(v);
        }
        if hi < m {
            // The next row reads one cell past this band, which must read as `inf`.
            cur[hi + 1] = inf;
        }
        if row_min > k {
            // Every path to the last cell passes through this row, and values never decrease along a path.
            return None;
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    let d = prev[m];
    (d <= k).then_some(d)
}

fn elapsed_nanos(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}
