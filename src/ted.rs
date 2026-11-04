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
        for i in 0..n {
            lml[i] = kids[i].first().map_or(i as u32 + 1, |&k| lml[k as usize]);
        }
        let mut seen = vec![false; n + 2];
        let mut keyroots = Vec::new();
        for i in (0..n).rev() {
            if !seen[lml[i] as usize] {
                seen[lml[i] as usize] = true;
                keyroots.push(i as u32 + 1);
            }
        }
        keyroots.reverse();
        let kind = vec![0u32; label.len()];
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
    #[must_use]
    pub fn mirror(&self) -> PostTree {
        if self.is_empty() {
            return PostTree::from_kids(Vec::new(), &[]);
        }
        let (mut label, mut kids, mut kind) = (Vec::new(), Vec::new(), Vec::new());
        mirror_expand(self, self.len() - 1, &mut label, &mut kids, &mut kind);
        PostTree::from_kids(label, &kids).with_kinds(kind)
    }

    /// Work estimate of the left-path decomposition against `other`: the product of the keyroot subtree sizes.
    fn cost_against(&self, other: &PostTree) -> u128 {
        let sum = |t: &PostTree| -> u128 {
            t.keyroots
                .iter()
                .map(|&k| u128::from(k - t.lml[k as usize - 1] + 1))
                .sum()
        };
        sum(self) * sum(other)
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
        self.label.is_empty()
    }
}

fn mirror_expand(
    t: &PostTree,
    i: usize,
    label: &mut Vec<u32>,
    kids: &mut Vec<Vec<u32>>,
    kind: &mut Vec<u32>,
) -> u32 {
    let ks: Vec<u32> = t.kids[i]
        .iter()
        .rev()
        .map(|&k| mirror_expand(t, k as usize, label, kids, kind))
        .collect();
    label.push(t.label[i]);
    kind.push(t.kind[i]);
    kids.push(ks);
    label.len() as u32 - 1
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
    if a.is_empty() || b.is_empty() {
        return (a.len().max(b.len()) as u32, Stats::default());
    }
    // Left paths or right paths, whichever the keyroot sizes say is cheaper.
    let (ma, mb) = (a.mirror(), b.mirror());
    let mut st = Stats::default();
    if ma.cost_against(&mb) < a.cost_against(b) {
        st.mirrored = true;
        (ted_oriented(&ma, &mb, &mut st), st)
    } else {
        (ted_oriented(a, b, &mut st), st)
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
    let (mut la, mut lb) = (a.label.clone(), b.label.clone());
    la.sort_unstable();
    lb.sort_unstable();
    let (mut i, mut j, mut common) = (0, 0, 0u32);
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
    a.len().max(b.len()) as u32 - common
}

fn ted_oriented(a: &PostTree, b: &PostTree, st: &mut Stats) -> u32 {
    let cap = (a.len() + b.len()) as u32;
    let mut tau = (a.len().abs_diff(b.len()) as u32)
        .max(label_lower_bound(a, b))
        .max(1);
    loop {
        // Once the band would cover a third of the table, skip the remaining doubling steps.
        if u64::from(tau) * 3 >= a.len().max(b.len()) as u64 {
            tau = cap;
        }
        st.attempts += 1;
        if let Some(d) = within(a, b, tau.min(cap), st) {
            return d;
        }
        tau = tau.saturating_mul(2);
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

/// [`within`] that also returns the subtree-distance table, banded by `|x - y| <= tau`.
fn within_td(a: &PostTree, b: &PostTree, tau: u32, st: &mut Stats) -> (Option<u32>, Vec<u32>) {
    let (n, m) = (a.len(), b.len());
    if n.abs_diff(m) as u32 > tau {
        return (None, Vec::new());
    }
    if n == 0 || m == 0 {
        return (Some(n.max(m) as u32).filter(|&d| d <= tau), Vec::new());
    }
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    // td[x][y], banded by |x - y| <= t; index x * w + (y + t - x).
    let mut td = vec![inf; (n + 1) * w];
    let tdi = |x: usize, y: usize| x * w + (y + t - x);
    let in_band = |x: usize, y: usize| x.abs_diff(y) <= t;
    let rows = n.max(m) + 1;
    let mut fd = vec![inf; rows * w];
    for &i0 in &a.keyroots {
        let i0 = i0 as usize;
        let li = a.lml[i0 - 1] as usize;
        for &j0 in &b.keyroots {
            let j0 = j0 as usize;
            let lj = b.lml[j0 - 1] as usize;
            if li.abs_diff(lj) > 2 * t {
                st.skipped += 1;
                continue;
            }
            st.windows += 1;
            fill_window(a, b, &mut td, &mut fd, (i0, j0), tau, st);
        }
    }
    let d = if in_band(n, m) { td[tdi(n, m)] } else { inf };
    ((d <= tau).then_some(d), td)
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
    let tdi = |x: usize, y: usize| x * w + (y + t - x);
    let in_band = |x: usize, y: usize| x.abs_diff(y) <= t;
    let fdi = |p: usize, q: usize| p * w + (q + t - p);
    let li = a.lml[i0 - 1] as usize;
    let lj = b.lml[j0 - 1] as usize;
    let (si, sj) = (i0 - li + 1, j0 - lj + 1);
    fd[fdi(0, 0)] = 0;
    for q in 1..=sj.min(t) {
        fd[fdi(0, q)] = q as u32;
    }
    for p in 1..=si.min(t) {
        fd[fdi(p, 0)] = p as u32;
    }
    for p in 1..=si {
        let (qlo, qhi) = (p.saturating_sub(t).max(1), sj.min(p + t));
        let x = li + p - 1;
        let lx = a.lml[x - 1] as usize;
        let mut row_min = if p <= t { fd[fdi(p, 0)] } else { inf };
        for q in qlo..=qhi {
            st.cells += 1;
            let y = lj + q - 1;
            let ly = b.lml[y - 1] as usize;
            let get = |pp: usize, qq: usize, fd: &[u32]| {
                if pp.abs_diff(qq) <= t {
                    fd[fdi(pp, qq)]
                } else {
                    inf
                }
            };
            let del = get(p - 1, q, fd) + 1;
            let ins = get(p, q - 1, fd) + 1;
            let v = if lx == li && ly == lj {
                let ren = relabel_cost(a, b, x, y);
                let v = del.min(ins).min(get(p - 1, q - 1, fd) + ren).min(inf);
                if in_band(x, y) {
                    td[tdi(x, y)] = v;
                }
                v
            } else {
                let tdv = if in_band(x, y) { td[tdi(x, y)] } else { inf };
                del.min(ins).min(get(lx - li, ly - lj, fd) + tdv).min(inf)
            };
            fd[fdi(p, q)] = v;
            row_min = row_min.min(v);
        }
        if qlo > qhi || row_min > tau {
            break;
        }
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

/// Independent validity check of a mapping. Returns the edit script cost it implies
/// (unmapped nodes of `a` deleted with their children promoted, unmapped nodes of `b` inserted, mapped
/// pairs with different labels relabelled) when the mapping is a legal tree edit mapping, else the reason.
///
/// Legal means: one to one; ancestor relations are preserved in both directions; sibling order is
/// preserved. Equivalently, deleting the unmapped nodes of `a` and of `b` (promoting children) leaves
/// two ordered forests that coincide under the mapping, so the replay produces `b`.
pub fn check_mapping(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Result<u32, String> {
    let (n, m) = (a.len(), b.len());
    let (mut to_b, mut to_a) = (vec![0usize; n + 1], vec![0usize; m + 1]);
    for &(x, y) in pairs {
        let (x, y) = (x as usize, y as usize);
        if x == 0 || x > n || y == 0 || y > m {
            return Err(format!("pair ({x}, {y}) out of range"));
        }
        if to_b[x] != 0 || to_a[y] != 0 {
            return Err(format!("not one to one at ({x}, {y})"));
        }
        to_b[x] = y;
        to_a[y] = x;
    }
    let parents = |t: &PostTree| -> Vec<usize> {
        let mut par = vec![0usize; t.len() + 1];
        for (i, ks) in t.kids.iter().enumerate() {
            for &k in ks {
                par[k as usize + 1] = i + 1;
            }
        }
        par
    };
    let (pa, pb) = (parents(a), parents(b));
    // Nearest mapped proper ancestor, 0 for none.
    let near = |par: &[usize], mapped: &dyn Fn(usize) -> bool, mut v: usize| -> usize {
        loop {
            v = par[v];
            if v == 0 || mapped(v) {
                return v;
            }
        }
    };
    let mut last_child_of: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();
    let mut relabels = 0u32;
    for x in 1..=n {
        let y = to_b[x];
        if y == 0 {
            continue;
        }
        let ax = near(&pa, &|v| to_b[v] != 0, x);
        let by = near(&pb, &|v| to_a[v] != 0, y);
        let ax_in_b = if ax == 0 { 0 } else { to_b[ax] };
        if ax_in_b != by {
            return Err(format!(
                "ancestor relation broken at ({x}, {y}): parent {ax_in_b} vs {by}"
            ));
        }
        // Siblings visited in increasing a-postorder must have increasing b-postorder.
        let prev = last_child_of.insert(by, y).unwrap_or(0);
        if prev > y {
            return Err(format!(
                "sibling order broken under {by}: {prev} before {y}"
            ));
        }
        relabels += relabel_cost(a, b, x, y);
    }
    let k = pairs.len() as u32;
    Ok((n as u32 - k) + (m as u32 - k) + relabels)
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

/// Entry points for the agreement test of the extraction copy in `proof/extract/ted_core.rs`
/// (`tests/ted_core.rs`). Not part of the API.
#[doc(hidden)]
pub mod proof_api {
    use super::{PostTree, Stats};
    /// `label_lower_bound` of the real source.
    #[must_use]
    pub fn label_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
        super::label_lower_bound(a, b)
    }
    /// `fill_window` of the real source.
    pub fn fill_window(
        a: &PostTree,
        b: &PostTree,
        td: &mut [u32],
        fd: &mut [u32],
        i0: usize,
        j0: usize,
        tau: u32,
    ) {
        super::fill_window(a, b, td, fd, (i0, j0), tau, &mut Stats::default());
    }
    /// `within_td` of the real source.
    #[must_use]
    pub fn within_td(a: &PostTree, b: &PostTree, tau: u32) -> (Option<u32>, Vec<u32>) {
        super::within_td(a, b, tau, &mut Stats::default())
    }
}
