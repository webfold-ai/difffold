//! Exact ordered tree edit distance (Zhang-Shasha objective, unit insert, delete and relabel costs).
//!
//! Deleting a node promotes its children, so this is the classical general objective that RTED and
//! APTED compute, not the top-down (Selkow) objective of [`crate::diff`].
//!
//! The speed comes from asking "is the distance at most `tau`?" with a doubling `tau`, and from two
//! pruning facts that are exact (they discard only mappings that cost more than `tau`):
//!
//! 1. A tree edit mapping preserves "before in postorder", so the nodes before `i` that are mapped
//!    correspond to the mapped nodes before `j`. Every unmapped node shifts a pair by one, hence a pair
//!    `(i, j)` in a mapping of cost at most `tau` has `|i - j| <= tau`. Subtree distances are only
//!    needed for such pairs.
//! 2. In a forest distance table, a cell whose two forests differ in size by more than `tau` costs more
//!    than `tau`, so only a diagonal band of width `2 tau + 1` is computed. A row whose band is all
//!    above `tau` ends the table, because values never fall below the row minimum.
//!
//! This module is a loop-based first version. The recursion-only discipline of [`crate::lines`] has not
//! been applied here yet.

use crate::intern::{Arena, Id};

/// A tree in postorder with 1-based indices: node `i` has label `label[i - 1]` and leftmost leaf `lml[i - 1]`.
pub struct PostTree {
    /// Label id per node, in postorder.
    pub label: Vec<u32>,
    /// 1-based postorder index of the leftmost leaf of each node's subtree.
    pub lml: Vec<u32>,
    /// Keyroots (1-based), ascending: the nodes that are the root or have a left sibling.
    pub keyroots: Vec<u32>,
    /// Child lists (0-based indices), kept so the mirror image can be built.
    kids: Vec<Vec<u32>>,
    /// Node kind per node. Relabelling within a kind costs 1, across kinds 2 (the same as deleting and inserting).
    /// All zero by default, which makes every relabel cost 1: the classical unit-cost model.
    pub kind: Vec<u32>,
}

impl PostTree {
    /// Build from labels and child lists in postorder (children have smaller indices).
    #[must_use]
    pub fn from_kids(label: Vec<u32>, kids: &[Vec<u32>]) -> Self {
        let n = label.len();
        let mut lml = vec![0u32; n];
        let mut i = 0;
        while i < n {
            #[allow(clippy::len_zero)]
            let v = if kids[i].len() == 0 {
                i as u32 + 1
            } else {
                lml[kids[i][0] as usize]
            };
            lml[i] = v;
            i += 1;
        }
        let mut seen = vec![false; n + 2];
        let mut keyroots = Vec::new();
        i = n;
        while i > 0 {
            i -= 1;
            let l = lml[i] as usize;
            if !seen[l] {
                seen[l] = true;
                keyroots.push(i as u32 + 1);
            }
        }
        keyroots.reverse();
        let kind = vec![0u32; n];
        PostTree {
            label,
            lml,
            keyroots,
            kids: kids.to_vec(),
            kind,
        }
    }

    /// Attach node kinds (one per node, in postorder). With kinds, relabelling across kinds costs 2.
    #[must_use]
    pub fn with_kinds(mut self, kind: Vec<u32>) -> Self {
        assert_eq!(kind.len(), self.label.len(), "one kind per node");
        self.kind = kind;
        self
    }

    /// The mirror image (children in reverse order). Mirroring both trees leaves the distance unchanged.
    ///
    /// The postorder of the mirror image is the reverse of the preorder of `self`, and the preorder index of a node
    /// (1-based) is its leftmost leaf plus its depth, so node `x` moves to `n - lml[x] - depth[x]` (0-based).
    #[must_use]
    pub fn mirror(&self) -> PostTree {
        let n = self.label.len();
        if n == 0 {
            return PostTree::from_kids(Vec::new(), &[]);
        }
        let depth = depths(self);
        let mut pos = vec![0usize; n];
        let mut x = 0;
        while x < n {
            let l = self.lml[x] as usize;
            let d = depth[x];
            let q = n - l;
            let v = q - d;
            pos[x] = v;
            x += 1;
        }
        let mut label = vec![0u32; n];
        let mut kind = vec![0u32; n];
        let mut kids: Vec<Vec<u32>> = vec![Vec::new(); n];
        x = 0;
        while x < n {
            let y = pos[x];
            label[y] = self.label[x];
            kind[y] = self.kind[x];
            let mut ks = Vec::new();
            let mut j = self.kids[x].len();
            while j > 0 {
                j -= 1;
                ks.push(pos[self.kids[x][j] as usize] as u32);
            }
            kids[y] = ks;
            x += 1;
        }
        PostTree::from_kids(label, &kids).with_kinds(kind)
    }

    /// Work estimate of the left-path decomposition against `other`: the product of the keyroot subtree sizes.
    fn cost_against(&self, other: &PostTree) -> u128 {
        keyroot_work(self) * keyroot_work(other)
    }

    /// Expand an arena tree (a DAG when subtrees repeat) into its postorder tree.
    #[must_use]
    pub fn from_arena(arena: &Arena, root: Id) -> Self {
        let (mut label, mut kids) = (Vec::new(), Vec::new());
        expand(arena, root, &mut label, &mut kids);
        Self::from_kids(label, &kids)
    }

    /// Node count.
    #[must_use]
    pub fn len(&self) -> usize {
        self.label.len()
    }

    /// Whether the tree is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        #[allow(clippy::len_zero)]
        let e = self.label.len() == 0;
        e
    }
}

fn expand(arena: &Arena, x: Id, label: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
    let ks: Vec<u32> = arena
        .kids(x)
        .iter()
        .map(|&k| expand(arena, k, label, kids))
        .collect();
    label.push(arena.label(x));
    kids.push(ks);
    label.len() as u32 - 1
}

/// The depth of every node (the root has depth 0). Parents have larger indices than their children, so the
/// nodes are visited from the root down.
fn depths(t: &PostTree) -> Vec<usize> {
    let n = t.label.len();
    let mut depth = vec![0usize; n];
    let mut p = n;
    while p > 0 {
        p -= 1;
        let d = depth[p] + 1;
        let mut j = 0;
        while j < t.kids[p].len() {
            depth[t.kids[p][j] as usize] = d;
            j += 1;
        }
    }
    depth
}

/// The 1-based preorder index of every node: its leftmost leaf plus its depth.
fn preorder(t: &PostTree) -> Vec<usize> {
    let n = t.label.len();
    let depth = depths(t);
    let mut pre = vec![0usize; n];
    let mut x = 0;
    while x < n {
        let l = t.lml[x] as usize;
        let d = depth[x];
        let v = l + d;
        pre[x] = v;
        x += 1;
    }
    pre
}

/// The sum of the keyroot subtree sizes.
fn keyroot_work(t: &PostTree) -> u128 {
    let mut s = 0u128;
    let mut i = 0;
    while i < t.keyroots.len() {
        let k = t.keyroots[i];
        s += (k - t.lml[k as usize - 1] + 1) as u128;
        i += 1;
    }
    s
}

/// Work counters of one [`ted_stats`] run.
#[derive(Debug, Default, Clone, Copy)]
pub struct Stats {
    /// Forest-distance cells evaluated, summed over all threshold attempts.
    pub cells: u64,
    /// Keyroot-pair windows run.
    pub windows: u64,
    /// Keyroot-pair windows skipped by the position filter.
    pub skipped: u64,
    /// Threshold values tried.
    pub attempts: u32,
    /// Whether the mirrored (right-path) orientation was chosen.
    pub mirrored: bool,
}

/// The exact distance, by doubling the threshold.
#[must_use]
pub fn ted(a: &PostTree, b: &PostTree) -> u32 {
    ted_stats(a, b).0
}

/// The exact distance with work counters.
#[must_use]
pub fn ted_stats(a: &PostTree, b: &PostTree) -> (u32, Stats) {
    let mut st = Stats::default();
    if a.is_empty() || b.is_empty() {
        return (umax(a.len(), b.len()) as u32, st);
    }
    // Left paths or right paths, whichever the keyroot sizes say is cheaper.
    let ma = a.mirror();
    let mb = b.mirror();
    if ma.cost_against(&mb) < a.cost_against(b) {
        st.mirrored = true;
        let d = ted_oriented(&ma, &mb, &mut st);
        (d, st)
    } else {
        let d = ted_oriented(a, b, &mut st);
        (d, st)
    }
}

/// Plain Zhang-Shasha: left paths, the threshold set to its maximum so no band or early exit applies.
/// The objective-matched unpruned baseline for measuring what the pruning contributes.
#[must_use]
pub fn ted_unpruned(a: &PostTree, b: &PostTree) -> u32 {
    let mut st = Stats::default();
    within(a, b, (a.len() + b.len()) as u32, &mut st).expect("the distance never exceeds n + m")
}

/// The relabel cost of node `x` of `a` to node `y` of `b` (1-based): 0 for equal labels, 1 within a kind, 2 across kinds.
fn relabel_cost(a: &PostTree, b: &PostTree, x: usize, y: usize) -> u32 {
    if a.label[x - 1] == b.label[y - 1] {
        0
    } else if a.kind[x - 1] == b.kind[y - 1] {
        1
    } else {
        2
    }
}

/// A lower bound on the distance: `max(n, m)` minus the size of the label multiset overlap. A mapping
/// of `k` pairs costs `n + m - k` plus its relabels, and at most `overlap` pairs can have equal labels.
fn label_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    // Counting instead of sorting: label ids are dense interner ids, so a count table over the labels of
    // `a` is small, and each label of `b` consumes one count of the same label.
    let mut top = 0usize;
    let mut i = 0;
    while i < a.label.len() {
        let l = a.label[i] as usize;
        if l >= top {
            top = l + 1;
        }
        i += 1;
    }
    let mut cnt = vec![0u32; top];
    i = 0;
    while i < a.label.len() {
        let l = a.label[i] as usize;
        cnt[l] += 1;
        i += 1;
    }
    let mut common = 0u32;
    i = 0;
    while i < b.label.len() {
        let l = b.label[i] as usize;
        if l < top && cnt[l] > 0 {
            cnt[l] -= 1;
            common += 1;
        }
        i += 1;
    }
    umax(a.len(), b.len()) as u32 - common
}

fn ted_oriented(a: &PostTree, b: &PostTree, st: &mut Stats) -> u32 {
    let n = a.len();
    let m = b.len();
    let cap = (n + m) as u32;
    let mut tau = max32(adiff(n, m) as u32, label_lower_bound(a, b));
    tau = max32(tau, 1);
    loop {
        // Once the band would cover a third of the table, skip the remaining doubling steps.
        if (tau as u64) * 3 >= umax(n, m) as u64 {
            tau = cap;
        }
        st.attempts = st.attempts.wrapping_add(1);
        let r = within_td(a, b, min32(tau, cap), st);
        if let Some(d) = r.0 {
            return d;
        }
        tau = dbl32(tau);
    }
}

/// The larger of two `u32`.
#[inline]
fn max32(x: u32, y: u32) -> u32 {
    if x >= y {
        x
    } else {
        y
    }
}

/// `x.saturating_mul(2)`.
#[inline]
fn dbl32(x: u32) -> u32 {
    if x >= 2_147_483_648 {
        u32::MAX
    } else {
        2 * x
    }
}

/// `Some(d)` with the exact distance when it is at most `tau`, else `None`.
#[must_use]
pub fn ted_within(a: &PostTree, b: &PostTree, tau: u32) -> Option<u32> {
    within(a, b, tau, &mut Stats::default())
}

fn within(a: &PostTree, b: &PostTree, tau: u32, st: &mut Stats) -> Option<u32> {
    within_td(a, b, tau, st).0
}

/// The larger of two `usize`.
#[inline]
fn umax(x: usize, y: usize) -> usize {
    if x >= y {
        x
    } else {
        y
    }
}

/// The smaller of two `usize`.
#[inline]
fn umin(x: usize, y: usize) -> usize {
    if x <= y {
        x
    } else {
        y
    }
}

/// `|x - y|`.
#[inline]
fn adiff(x: usize, y: usize) -> usize {
    if x >= y {
        x - y
    } else {
        y - x
    }
}

/// The smaller of two `u32`.
#[inline]
fn min32(x: u32, y: u32) -> u32 {
    if x <= y {
        x
    } else {
        y
    }
}

/// The band index `x * w + (y + t - x)` of a cell `(x, y)` with `|x - y| <= t` in a table of row width `w`.
#[inline]
fn bidx(w: usize, t: usize, x: usize, y: usize) -> usize {
    x * w + (y + t - x)
}

/// The cell `(pp, qq)` of a band table, or `inf` outside the band.
#[inline]
fn get_cell(fd: &[u32], w: usize, t: usize, inf: u32, pp: usize, qq: usize) -> u32 {
    if adiff(pp, qq) <= t {
        fd[bidx(w, t, pp, qq)]
    } else {
        inf
    }
}

/// [`within`] that also returns the subtree-distance table, banded by `|x - y| <= tau`.
fn within_td(a: &PostTree, b: &PostTree, tau: u32, st: &mut Stats) -> (Option<u32>, Vec<u32>) {
    let n = a.len();
    let m = b.len();
    if adiff(n, m) as u32 > tau {
        return (None, Vec::new());
    }
    if n == 0 || m == 0 {
        let d = umax(n, m) as u32;
        if d <= tau {
            return (Some(d), Vec::new());
        }
        return (None, Vec::new());
    }
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    // td[x][y], banded by |x - y| <= t; index x * w + (y + t - x).
    let mut td = vec![inf; (n + 1) * w];
    let rows = umax(n, m) + 1;
    let mut fd = vec![inf; rows * w];
    let mut ia = 0;
    while ia < a.keyroots.len() {
        let i0 = a.keyroots[ia] as usize;
        let li = a.lml[i0 - 1] as usize;
        let mut ib = 0;
        while ib < b.keyroots.len() {
            let j0 = b.keyroots[ib] as usize;
            let lj = b.lml[j0 - 1] as usize;
            if adiff(li, lj) > 2 * t {
                st.skipped = st.skipped.wrapping_add(1);
            } else {
                st.windows = st.windows.wrapping_add(1);
                fill_window(a, b, &mut td, &mut fd, (i0, j0), tau, st);
            }
            ib += 1;
        }
        ia += 1;
    }
    let d = if adiff(n, m) <= t {
        td[bidx(w, t, n, m)]
    } else {
        inf
    };
    if d <= tau {
        (Some(d), td)
    } else {
        (None, td)
    }
}

/// Fill the forest-distance table of the window `(i0, j0)` and record the subtree distances of its
/// left-path pairs in `td`.
fn fill_window(
    a: &PostTree,
    b: &PostTree,
    td: &mut [u32],
    fd: &mut [u32],
    (i0, j0): (usize, usize),
    tau: u32,
    st: &mut Stats,
) {
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    let li = a.lml[i0 - 1] as usize;
    let lj = b.lml[j0 - 1] as usize;
    let si = i0 - li + 1;
    let sj = j0 - lj + 1;
    fd[bidx(w, t, 0, 0)] = 0;
    let lim_q = umin(sj, t);
    let mut q = 1;
    while q <= lim_q {
        fd[bidx(w, t, 0, q)] = q as u32;
        q += 1;
    }
    let lim_p = umin(si, t);
    let mut p = 1;
    while p <= lim_p {
        fd[bidx(w, t, p, 0)] = p as u32;
        p += 1;
    }
    p = 1;
    while p <= si {
        let qlo = umax(p.saturating_sub(t), 1);
        let qhi = umin(sj, p + t);
        let x = li + p - 1;
        let lx = a.lml[x - 1] as usize;
        let mut row_min = if p <= t { fd[bidx(w, t, p, 0)] } else { inf };
        q = qlo;
        while q <= qhi {
            st.cells = st.cells.wrapping_add(1);
            let y = lj + q - 1;
            let ly = b.lml[y - 1] as usize;
            let del = get_cell(fd, w, t, inf, p - 1, q) + 1;
            let ins = get_cell(fd, w, t, inf, p, q - 1) + 1;
            let v = if lx == li && ly == lj {
                let ren = relabel_cost(a, b, x, y);
                let diag = get_cell(fd, w, t, inf, p - 1, q - 1) + ren;
                let v = min32(min32(min32(del, ins), diag), inf);
                if adiff(x, y) <= t {
                    td[bidx(w, t, x, y)] = v;
                }
                v
            } else {
                let tdv = if adiff(x, y) <= t {
                    td[bidx(w, t, x, y)]
                } else {
                    inf
                };
                let sub = get_cell(fd, w, t, inf, lx - li, ly - lj) + tdv;
                min32(min32(min32(del, ins), sub), inf)
            };
            fd[bidx(w, t, p, q)] = v;
            row_min = min32(row_min, v);
            q += 1;
        }
        if qlo > qhi || row_min > tau {
            break;
        }
        p += 1;
    }
}

/// An optimal edit mapping: `pairs` holds 1-based postorder indices `(node of a, node of b)`.
#[derive(Debug, Clone)]
pub struct Mapping {
    /// The exact distance.
    pub cost: u32,
    /// Matched node pairs, ascending in the first component.
    pub pairs: Vec<(u32, u32)>,
}

/// An optimal mapping, recovered by tracing back through the forest tables at the exact distance.
#[must_use]
pub fn ted_mapping(a: &PostTree, b: &PostTree) -> Mapping {
    ted_mapping_with(a, b, true)
}

/// [`ted_mapping`] with the tie-break made explicit. Among equal-cost optimal mappings, `prefer_match`
/// picks the one that matches a pair over deleting and inserting it; `false` prefers delete, then insert.
#[must_use]
pub fn ted_mapping_with(a: &PostTree, b: &PostTree, prefer_match: bool) -> Mapping {
    let cost = ted(a, b);
    if a.is_empty() || b.is_empty() {
        return Mapping {
            cost,
            pairs: Vec::new(),
        };
    }
    let (n, m) = (a.len(), b.len());
    let mut st = Stats::default();
    let (d, mut td) = within_td(a, b, cost, &mut st);
    debug_assert_eq!(d, Some(cost));
    let t = cost as usize;
    let inf = cost + 1;
    let w = 2 * t + 1;
    let tdi = |x: usize, y: usize| x * w + (y + t - x);
    let mut pairs = Vec::new();
    let mut stack = vec![(n, m)];
    while let Some((i, j)) = stack.pop() {
        let (li, lj) = (a.lml[i - 1] as usize, b.lml[j - 1] as usize);
        let (si, sj) = (i - li + 1, j - lj + 1);
        let fdi = |p: usize, q: usize| p * w + (q + t - p);
        let mut fd = vec![inf; (si + 1) * w];
        fill_window(a, b, &mut td, &mut fd, (i, j), cost, &mut st);
        let get = |p: usize, q: usize| {
            if p.abs_diff(q) <= t {
                fd[fdi(p, q)]
            } else {
                inf
            }
        };
        let (mut p, mut q) = (si, sj);
        while p > 0 || q > 0 {
            let v = get(p, q);
            let (x, y) = (li + p.max(1) - 1, lj + q.max(1) - 1);
            let leaf_case =
                p > 0 && q > 0 && a.lml[x - 1] as usize == li && b.lml[y - 1] as usize == lj;
            // The diagonal candidate: relabel or match a whole pair, or a subtree pair through the table.
            let diag_ok = if p == 0 || q == 0 {
                false
            } else if leaf_case {
                relabel_cost(a, b, x, y) < 2 && get(p - 1, q - 1) + relabel_cost(a, b, x, y) == v
            } else {
                let tdv = if x.abs_diff(y) <= t {
                    td[tdi(x, y)]
                } else {
                    inf
                };
                get(a.lml[x - 1] as usize - li, b.lml[y - 1] as usize - lj) + tdv == v
            };
            if prefer_match && diag_ok {
                if leaf_case {
                    pairs.push((x as u32, y as u32));
                    p -= 1;
                    q -= 1;
                } else {
                    stack.push((x, y));
                    p = a.lml[x - 1] as usize - li;
                    q = b.lml[y - 1] as usize - lj;
                }
            } else if p > 0 && get(p - 1, q) + 1 == v {
                p -= 1;
            } else if q > 0 && get(p, q - 1) + 1 == v {
                q -= 1;
            } else if leaf_case {
                pairs.push((x as u32, y as u32));
                p -= 1;
                q -= 1;
            } else {
                stack.push((x, y));
                p = a.lml[x - 1] as usize - li;
                q = b.lml[y - 1] as usize - lj;
            }
        }
    }
    pairs.sort_unstable();
    Mapping { cost, pairs }
}

/// The verdict of [`check_core`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// A legal tree edit mapping; the payload is the cost of its edit script.
    Cost(u32),
    /// The pair `(x, y)` names a node outside the trees.
    Range(usize, usize),
    /// The pair `(x, y)` reuses a node already mapped.
    Dup(usize, usize),
    /// The pair `(x, y)` reverses the postorder of an earlier pair.
    Post(usize, usize),
    /// The pair `(x, y)` reverses the preorder of an earlier pair.
    Pre(usize, usize),
}

/// The checker behind [`check_mapping`].
///
/// A mapping is a legal tree edit mapping exactly when it is one to one and preserves both the postorder and
/// the preorder (equivalently, the postorder and the ancestor relation). The postorder is checked by walking the
/// nodes of `a` in postorder and the preorder by walking them in preorder, each time requiring the images in `b`
/// to increase.
pub fn check_core(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Check {
    let n = a.label.len();
    let m = b.label.len();
    let mut to_b = vec![0usize; n + 1];
    let mut to_a = vec![0usize; m + 1];
    let mut verdict = Check::Cost(0);
    let mut ok = true;
    let mut i = 0;
    while ok && i < pairs.len() {
        let x = pairs[i].0 as usize;
        let y = pairs[i].1 as usize;
        if x == 0 || x > n || y == 0 || y > m {
            verdict = Check::Range(x, y);
            ok = false;
        } else if to_b[x] != 0 || to_a[y] != 0 {
            verdict = Check::Dup(x, y);
            ok = false;
        } else {
            to_b[x] = y;
            to_a[y] = x;
            i += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let mut prev = 0;
    let mut x = 1;
    while ok && x <= n {
        let y = to_b[x];
        if y != 0 && y <= prev {
            verdict = Check::Post(x, y);
            ok = false;
        } else {
            if y != 0 {
                prev = y;
            }
            x += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let pa = preorder(a);
    let pb = preorder(b);
    let mut at = vec![0usize; n + 1];
    x = 1;
    while x <= n {
        at[pa[x - 1]] = x;
        x += 1;
    }
    let mut prev_pre = 0;
    let mut k = 1;
    while ok && k <= n {
        let x = at[k];
        let y = to_b[x];
        if y != 0 && pb[y - 1] <= prev_pre {
            verdict = Check::Pre(x, y);
            ok = false;
        } else {
            if y != 0 {
                prev_pre = pb[y - 1];
            }
            k += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let mut relabels = 0u32;
    x = 1;
    while x <= n {
        let y = to_b[x];
        if y != 0 {
            relabels += relabel_cost(a, b, x, y);
        }
        x += 1;
    }
    let cnt = pairs.len() as u32;
    Check::Cost((n as u32 - cnt) + (m as u32 - cnt) + relabels)
}

/// Independent validity check of a mapping. Returns the edit script cost it implies
/// (unmapped nodes of `a` deleted with their children promoted, unmapped nodes of `b` inserted, mapped
/// pairs with different labels relabelled) when the mapping is a legal tree edit mapping, else the reason.
///
/// Legal means: one to one; ancestor relations are preserved in both directions; sibling order is
/// preserved. Equivalently, deleting the unmapped nodes of `a` and of `b` (promoting children) leaves
/// two ordered forests that coincide under the mapping, so the replay produces `b`.
pub fn check_mapping(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Result<u32, String> {
    match check_core(a, b, pairs) {
        Check::Cost(c) => Ok(c),
        Check::Range(x, y) => Err(format!("pair ({x}, {y}) out of range")),
        Check::Dup(x, y) => Err(format!("not one to one at ({x}, {y})")),
        Check::Post(x, y) => Err(format!("postorder broken at ({x}, {y})")),
        Check::Pre(x, y) => Err(format!(
            "ancestor relation or sibling order broken at ({x}, {y})"
        )),
    }
}

struct RNode {
    label: u32,
    kids: Vec<usize>,
    parent: usize,
    /// The 1-based node of `b` this node corresponds to, 0 if none.
    bid: usize,
    alive: bool,
}

/// Execute the edit script implied by a mapping and check that it turns `a` into `b`.
///
/// The script is: relabel the mapped pairs whose labels differ; delete every unmapped node of `a`, its
/// children taking its place among its parent's children; insert every unmapped node of `b`, deepest
/// first, as the parent of the run of current siblings that lie below it in `b` (or, for a leaf, at the
/// position `b` dictates). After the last operation the working tree must equal `b` exactly: labels, shape
/// and sibling order. Returns the number of operations, which must equal the mapping's cost.
///
/// Insert placement consults the structure of `b`, so this checks that the mapping is executable and
/// that deletion with promotion, relabelling and insertion compose to `b`; it does not derive the
/// script independently of `b`.
pub fn replay_script(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Result<u32, String> {
    let (n, m) = (a.len(), b.len());
    if n == 0 || m == 0 {
        return Ok(n.max(m) as u32);
    }
    let root_slot = n;
    let mut nodes: Vec<RNode> = (0..n)
        .map(|i| RNode {
            label: a.label[i],
            kids: a.kids[i].iter().map(|&k| k as usize).collect(),
            parent: root_slot,
            bid: 0,
            alive: true,
        })
        .collect();
    for i in 0..n {
        for &k in &a.kids[i] {
            nodes[k as usize].parent = i;
        }
    }
    nodes.push(RNode {
        label: 0,
        kids: vec![n - 1],
        parent: usize::MAX,
        bid: 0,
        alive: true,
    });
    let (mut to_b, mut arena_of_b) = (vec![0usize; n + 1], vec![usize::MAX; m + 1]);
    let mut ops = 0u32;
    for &(x, y) in pairs {
        let (x, y) = (x as usize, y as usize);
        if x == 0 || x > n || y == 0 || y > m || to_b[x] != 0 || arena_of_b[y] != usize::MAX {
            return Err(format!("bad pair ({x}, {y})"));
        }
        to_b[x] = y;
        arena_of_b[y] = x - 1;
        nodes[x - 1].bid = y;
        if a.label[x - 1] != b.label[y - 1] {
            nodes[x - 1].label = b.label[y - 1];
            ops += 1;
        }
    }
    // Delete every unmapped node of a, promoting its children.
    for x in 0..n {
        if to_b[x + 1] != 0 {
            continue;
        }
        let p = nodes[x].parent;
        let at = nodes[p]
            .kids
            .iter()
            .position(|&c| c == x)
            .ok_or("deleted node missing from its parent")?;
        let moved = std::mem::take(&mut nodes[x].kids);
        for &c in &moved {
            nodes[c].parent = p;
        }
        nodes[p].kids.splice(at..=at, moved);
        nodes[x].alive = false;
        ops += 1;
    }
    // Insert the unmapped nodes of b, deepest first.
    let mut parent_b = vec![0usize; m + 1];
    for (i, ks) in b.kids.iter().enumerate() {
        for &k in ks {
            parent_b[k as usize + 1] = i + 1;
        }
    }
    let depth = |mut v: usize| {
        let mut d = 0;
        while parent_b[v] != 0 {
            v = parent_b[v];
            d += 1;
        }
        d
    };
    let mut todo: Vec<usize> = (1..=m).filter(|&v| arena_of_b[v] == usize::MAX).collect();
    todo.sort_by_key(|&v| std::cmp::Reverse(depth(v)));
    for v in todo {
        let mut u = parent_b[v];
        while u != 0 && arena_of_b[u] == usize::MAX {
            u = parent_b[u];
        }
        let p = if u == 0 { root_slot } else { arena_of_b[u] };
        let lv = b.lml[v - 1] as usize;
        let below = |c: usize, nodes: &Vec<RNode>| lv <= nodes[c].bid && nodes[c].bid < v;
        let kids = nodes[p].kids.clone();
        let first = kids.iter().position(|&c| below(c, &nodes));
        let (start, end) = match first {
            Some(s) => {
                let e = s + kids[s..].iter().take_while(|&&c| below(c, &nodes)).count();
                if kids[e..].iter().any(|&c| below(c, &nodes)) {
                    return Err(format!("children of inserted node {v} are not contiguous"));
                }
                (s, e)
            }
            None => {
                let s = kids
                    .iter()
                    .position(|&c| b.lml[nodes[c].bid - 1] as usize > v)
                    .unwrap_or(kids.len());
                (s, s)
            }
        };
        let run: Vec<usize> = kids[start..end].to_vec();
        let id = nodes.len();
        for &c in &run {
            nodes[c].parent = id;
        }
        nodes.push(RNode {
            label: b.label[v - 1],
            kids: run,
            parent: p,
            bid: v,
            alive: true,
        });
        nodes[p].kids.splice(start..end, [id]);
        arena_of_b[v] = id;
        ops += 1;
    }
    // The working tree must now be exactly b.
    if nodes[root_slot].kids != [arena_of_b[m]] {
        return Err("the result is not a single tree rooted at the root of b".into());
    }
    let mut stack = vec![(arena_of_b[m], m)];
    while let Some((x, v)) = stack.pop() {
        if nodes[x].label != b.label[v - 1] {
            return Err(format!("label differs at node {v}"));
        }
        let want: Vec<usize> = b.kids[v - 1].iter().map(|&k| k as usize + 1).collect();
        let got: Vec<usize> = nodes[x].kids.iter().map(|&c| nodes[c].bid).collect();
        if want != got {
            return Err(format!(
                "children of node {v} differ: expected {want:?}, got {got:?}"
            ));
        }
        stack.extend(nodes[x].kids.iter().map(|&c| (c, nodes[c].bid)));
    }
    Ok(ops)
}
