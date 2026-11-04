//! Machine-readable ambiguity: where the two final snapshots do not determine the lineage.
//!
//! Node numbers are preorder indices (root 0, text nodes included) of before.html / after.html.
//! A group lists interchangeable subtree roots; descendants follow their root by isomorphism.
//!
//! Admissible correspondences = truth with every group's root-level matching replaced by any
//! one-to-one matching of `before` roots to `after` roots whose size is in `[min, max]`.

use crate::json::J;
use crate::rng::{hash_parts, mix};
use crate::tree::Node;
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GroupKind {
    /// Identical sibling subtrees under a truth-corresponded parent. Any permutation is admissible.
    PermutableSiblings,
    /// A moved subtree whose content is unchanged: "moved" and "deleted + identical insert" are
    /// indistinguishable. Matching or abstaining are both admissible.
    OptionalMatch,
    /// Maximal unmatched before-subtree and unmatched after-subtree with identical content in
    /// different places: delete + insert, or a move. Matching or abstaining are both admissible.
    UnmatchedLookalike,
}

impl GroupKind {
    pub fn name(&self) -> &'static str {
        match self {
            GroupKind::PermutableSiblings => "permutable_siblings",
            GroupKind::OptionalMatch => "optional_match",
            GroupKind::UnmatchedLookalike => "unmatched_lookalike",
        }
    }
    pub fn from_name(s: &str) -> Option<GroupKind> {
        Some(match s {
            "permutable_siblings" => GroupKind::PermutableSiblings,
            "optional_match" => GroupKind::OptionalMatch,
            "unmatched_lookalike" => GroupKind::UnmatchedLookalike,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Group {
    pub id: usize,
    pub kind: GroupKind,
    pub before: Vec<usize>,
    pub after: Vec<usize>,
    /// Nodes per member subtree.
    pub size: usize,
    pub min: usize,
    pub max: usize,
    /// How many member pairs the truth matches.
    pub truth: usize,
    /// Truth equals the document-order matching (i-th with i-th). Always true for non-permutable kinds.
    pub truth_in_order: bool,
    /// Harmless: equal counts and in order. Does not make the pair `ambiguous`.
    pub trivial: bool,
    pub hash: u64,
}

impl Group {
    pub fn to_json(&self) -> J {
        J::obj(vec![
            ("id", J::Int(self.id as i64)),
            ("kind", J::s(self.kind.name())),
            ("before", J::ints(self.before.iter().copied())),
            ("after", J::ints(self.after.iter().copied())),
            ("size", J::Int(self.size as i64)),
            ("min_matches", J::Int(self.min as i64)),
            ("max_matches", J::Int(self.max as i64)),
            ("truth_matches", J::Int(self.truth as i64)),
            ("truth_in_order", J::Bool(self.truth_in_order)),
            ("trivial", J::Bool(self.trivial)),
            ("content_hash", J::s(&format!("{:016x}", self.hash))),
        ])
    }
    pub fn from_json(j: &J) -> Result<Group, String> {
        let g = |k: &str| j.get(k).ok_or_else(|| format!("group missing {}", k));
        let ints = |k: &str| -> Result<Vec<usize>, String> {
            g(k)?.as_arr().ok_or("not array")?.iter().map(|x| x.as_usize().ok_or("not usize".to_string())).collect()
        };
        Ok(Group {
            id: g("id")?.as_usize().ok_or("id")?,
            kind: GroupKind::from_name(g("kind")?.as_str().ok_or("kind")?).ok_or("unknown group kind")?,
            before: ints("before")?,
            after: ints("after")?,
            size: g("size")?.as_usize().ok_or("size")?,
            min: g("min_matches")?.as_usize().ok_or("min")?,
            max: g("max_matches")?.as_usize().ok_or("max")?,
            truth: g("truth_matches")?.as_usize().ok_or("truth")?,
            truth_in_order: g("truth_in_order")?.as_bool().ok_or("tio")?,
            trivial: g("trivial")?.as_bool().ok_or("trivial")?,
            hash: u64::from_str_radix(g("content_hash")?.as_str().ok_or("hash")?, 16).map_err(|e| e.to_string())?,
        })
    }
}

pub fn ambiguous(groups: &[Group]) -> bool {
    groups.iter().any(|g| !g.trivial)
}

/// Longest increasing subsequence membership flags (strictly increasing values).
pub fn lis_flags(seq: &[usize]) -> Vec<bool> {
    let n = seq.len();
    let mut tails: Vec<usize> = vec![]; // indices
    let mut prev = vec![usize::MAX; n];
    for i in 0..n {
        let pos = tails.partition_point(|&t| seq[t] < seq[i]);
        if pos > 0 {
            prev[i] = tails[pos - 1];
        }
        if pos == tails.len() {
            tails.push(i);
        } else {
            tails[pos] = i;
        }
    }
    let mut flags = vec![false; n];
    let mut cur = tails.last().copied();
    while let Some(i) = cur {
        flags[i] = true;
        cur = if prev[i] == usize::MAX { None } else { Some(prev[i]) };
    }
    flags
}

pub struct Info<'a> {
    pub nodes: Vec<&'a Node>,
    pub parent: Vec<usize>,
    pub children: Vec<Vec<usize>>,
    pub size: Vec<usize>,
    pub hash: Vec<u64>,
    pub idx: HashMap<u32, usize>,
}

impl<'a> Info<'a> {
    pub fn new(root: &'a Node) -> Info<'a> {
        let mut nodes = vec![];
        let mut parent = vec![];
        fn go<'a>(n: &'a Node, p: usize, nodes: &mut Vec<&'a Node>, parent: &mut Vec<usize>) {
            let me = nodes.len();
            nodes.push(n);
            parent.push(p);
            for c in &n.children {
                go(c, me, nodes, parent);
            }
        }
        go(root, usize::MAX, &mut nodes, &mut parent);
        let n = nodes.len();
        let mut children = vec![vec![]; n];
        for i in 1..n {
            children[parent[i]].push(i);
        }
        let mut size = vec![1usize; n];
        let mut hash = vec![0u64; n];
        for i in (0..n).rev() {
            let nd = nodes[i];
            let mut parts: Vec<&str> = vec![&nd.tag, &nd.text];
            for (k, v) in &nd.attrs {
                parts.push(k);
                parts.push(v);
            }
            let mut h = hash_parts(&parts);
            for &c in &children[i] {
                size[i] += size[c];
                h = mix(h, hash[c]);
            }
            hash[i] = mix(h, children[i].len() as u64);
        }
        let idx = nodes.iter().enumerate().map(|(i, n)| (n.lid, i)).collect();
        Info { nodes, parent, children, size, hash, idx }
    }
}

/// Truth pairs as preorder index pairs, by lid intersection. Sorted by before index.
pub fn truth_pairs(b: &Info, a: &Info) -> Vec<(usize, usize)> {
    let mut v: Vec<(usize, usize)> = b.nodes.iter().enumerate().filter_map(|(i, n)| a.idx.get(&n.lid).map(|&j| (i, j))).collect();
    v.sort();
    v
}

pub fn compute(before: &Node, after: &Node) -> Vec<Group> {
    let b = Info::new(before);
    let a = Info::new(after);
    let (nb, na) = (b.nodes.len(), a.nodes.len());
    let pairs = truth_pairs(&b, &a);
    let mut pb: Vec<Option<usize>> = vec![None; nb];
    let mut pa: Vec<Option<usize>> = vec![None; na];
    for &(i, j) in &pairs {
        pb[i] = Some(j);
        pa[j] = Some(i);
    }
    let mut cov_b = vec![false; nb];
    let mut cov_a = vec![false; na];
    let mut groups: Vec<Group> = vec![];

    let range_free = |cov: &Vec<bool>, r: usize, s: usize| !cov[r..r + s].iter().any(|&c| c);

    // Phase 1: identical sibling classes under truth-corresponded parents, scanned in after-preorder.
    let mut by_a: Vec<(usize, usize)> = pairs.iter().map(|&(i, j)| (j, i)).collect();
    by_a.sort();
    for &(ja, ib) in &by_a {
        if cov_a[ja] || cov_b[ib] {
            continue;
        }
        let mut classes: BTreeMap<u64, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
        for &c in &b.children[ib] {
            classes.entry(b.hash[c]).or_default().0.push(c);
        }
        for &c in &a.children[ja] {
            classes.entry(a.hash[c]).or_default().1.push(c);
        }
        for (h, (bm, am)) in classes {
            if bm.is_empty() || am.is_empty() {
                continue;
            }
            let mut truth = 0;
            let mut in_order = true;
            for (rb, &x) in bm.iter().enumerate() {
                if let Some(y) = pb[x] {
                    if let Some(ra) = am.iter().position(|&z| z == y) {
                        truth += 1;
                        if ra != rb {
                            in_order = false;
                        }
                    }
                }
            }
            let mx = bm.len().min(am.len());
            if !(bm.len() + am.len() >= 3 || truth < mx) {
                continue;
            }
            if truth != mx {
                in_order = false;
            }
            let sz = b.size[bm[0]];
            if !bm.iter().all(|&x| range_free(&cov_b, x, sz)) || !am.iter().all(|&x| range_free(&cov_a, x, sz)) {
                continue;
            }
            for &x in &bm {
                cov_b[x..x + sz].iter_mut().for_each(|c| *c = true);
            }
            for &x in &am {
                cov_a[x..x + sz].iter_mut().for_each(|c| *c = true);
            }
            let trivial = bm.len() == am.len() && in_order;
            groups.push(Group { id: 0, kind: GroupKind::PermutableSiblings, before: bm, after: am, size: sz, min: truth, max: mx, truth, truth_in_order: in_order, trivial, hash: h });
        }
    }

    // Phase 2: moved but unchanged subtrees.
    let mut moved = vec![false; na];
    for ja in 0..na {
        if let Some(ib) = pa[ja] {
            if ja == 0 {
                continue;
            }
            let same_parent = pb[b.parent[ib]] == Some(a.parent[ja]);
            if !same_parent {
                moved[ja] = true;
            }
        }
    }
    for ja in 0..na {
        let kids = &a.children[ja];
        let mut seq = vec![];
        let mut who = vec![];
        for &c in kids {
            if let Some(ib) = pa[c] {
                if pb[b.parent[ib]] == Some(ja) {
                    seq.push(ib);
                    who.push(c);
                }
            }
        }
        let fl = lis_flags(&seq);
        for (k, &c) in who.iter().enumerate() {
            if !fl[k] {
                moved[c] = true;
            }
        }
    }
    for ja in 0..na {
        if !moved[ja] || cov_a[ja] {
            continue;
        }
        let ib = pa[ja].unwrap();
        if cov_b[ib] || a.hash[ja] != b.hash[ib] || a.size[ja] != b.size[ib] {
            continue;
        }
        let sz = a.size[ja];
        if !range_free(&cov_a, ja, sz) || !range_free(&cov_b, ib, sz) {
            continue;
        }
        cov_a[ja..ja + sz].iter_mut().for_each(|c| *c = true);
        cov_b[ib..ib + sz].iter_mut().for_each(|c| *c = true);
        groups.push(Group { id: 0, kind: GroupKind::OptionalMatch, before: vec![ib], after: vec![ja], size: sz, min: 0, max: 1, truth: 1, truth_in_order: true, trivial: false, hash: a.hash[ja] });
    }

    // Phase 3: unmatched lookalikes.
    let roots = |info: &Info, p: &Vec<Option<usize>>, cov: &Vec<bool>| -> Vec<usize> {
        let n = info.nodes.len();
        let mut pref = vec![0usize; n + 1];
        for i in 0..n {
            pref[i + 1] = pref[i] + usize::from(p[i].is_some());
        }
        (0..n)
            .filter(|&i| {
                p[i].is_none()
                    && !cov[i]
                    && (i == 0 || p[info.parent[i]].is_some() || cov[info.parent[i]])
                    && pref[i + info.size[i]] - pref[i] == 0
                    && !cov[i..i + info.size[i]].iter().any(|&c| c)
            })
            .collect()
    };
    let rb = roots(&b, &pb, &cov_b);
    let ra = roots(&a, &pa, &cov_a);
    let mut classes: BTreeMap<u64, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for &x in &rb {
        classes.entry(b.hash[x]).or_default().0.push(x);
    }
    for &x in &ra {
        classes.entry(a.hash[x]).or_default().1.push(x);
    }
    for (h, (bm, am)) in classes {
        if bm.is_empty() || am.is_empty() {
            continue;
        }
        let sz = b.size[bm[0]];
        let mx = bm.len().min(am.len());
        groups.push(Group { id: 0, kind: GroupKind::UnmatchedLookalike, before: bm, after: am, size: sz, min: 0, max: mx, truth: 0, truth_in_order: true, trivial: false, hash: h });
    }

    groups.sort_by_key(|g| (g.before.first().copied().unwrap_or(0).min(g.after.first().copied().unwrap_or(usize::MAX)), g.kind.name()));
    for (i, g) in groups.iter_mut().enumerate() {
        g.id = i;
    }
    groups
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Score {
    /// Node pairs matched as in the truth, or inside an admissible group matching.
    pub correct: usize,
    /// Truth pairs left unmatched by the prediction (not excused by a group).
    pub missed_match: usize,
    /// The subset of `missed_match` whose truth edit is a move.
    pub missed_move: usize,
    /// Confident wrong matches: predicted pairs that are neither truth nor admissible.
    pub wrong_identity: usize,
    /// Ambiguous groups (min 0) where the prediction correctly left everything unmatched.
    pub abstain_ok_groups: usize,
    /// Groups where the prediction chose a different but admissible matching than the truth.
    pub admissible_alternative_groups: usize,
}

struct Cov {
    // node index -> (group, member index, offset)
    m: HashMap<usize, (usize, usize, usize)>,
}

fn build_cov(groups: &[Group], before: bool) -> Cov {
    let mut m = HashMap::new();
    for (gi, g) in groups.iter().enumerate() {
        let list = if before { &g.before } else { &g.after };
        for (mi, &r) in list.iter().enumerate() {
            for o in 0..g.size {
                m.insert(r + o, (gi, mi, o));
            }
        }
    }
    Cov { m }
}

/// Classify a predicted correspondence against the truth and the ambiguity groups.
/// `moved_before` holds before-indices whose truth edit is a move (for `missed_move`).
pub fn score(groups: &[Group], truth: &[(usize, usize)], moved_before: &HashSet<usize>, pred: &[(usize, usize)]) -> Score {
    let cb = build_cov(groups, true);
    let ca = build_cov(groups, false);
    let tset: HashSet<(usize, usize)> = truth.iter().copied().collect();
    let pset: HashSet<(usize, usize)> = pred.iter().copied().collect();
    let mut s = Score::default();
    let mut per_group: Vec<Vec<(usize, usize, usize, usize)>> = vec![vec![]; groups.len()]; // (bm, am, bo, ao)
    let mut pred_b: HashSet<usize> = HashSet::new();
    for &(b, a) in &pset {
        pred_b.insert(b);
        match (cb.m.get(&b), ca.m.get(&a)) {
            (None, None) => {
                if tset.contains(&(b, a)) {
                    s.correct += 1;
                } else {
                    s.wrong_identity += 1;
                }
            }
            (Some(&(g1, m1, o1)), Some(&(g2, m2, o2))) if g1 == g2 => per_group[g1].push((m1, m2, o1, o2)),
            _ => s.wrong_identity += 1,
        }
    }
    for &(b, a) in &tset {
        if cb.m.contains_key(&b) || ca.m.contains_key(&a) {
            continue;
        }
        if !pset.contains(&(b, a)) && !pred_b.contains(&b) {
            s.missed_match += 1;
            if moved_before.contains(&b) {
                s.missed_move += 1;
            }
        }
    }
    for (gi, g) in groups.iter().enumerate() {
        let ps = &per_group[gi];
        let mut member: HashMap<(usize, usize), usize> = HashMap::new();
        let mut ok = true;
        for &(m1, m2, o1, o2) in ps {
            if o1 != o2 {
                ok = false;
            }
            *member.entry((m1, m2)).or_default() += 1;
        }
        let mut used_b = HashSet::new();
        let mut used_a = HashSet::new();
        for (&(m1, m2), &c) in &member {
            if c != g.size || !used_b.insert(m1) || !used_a.insert(m2) {
                ok = false;
            }
        }
        let m = member.len();
        if !ok || m > g.max {
            s.wrong_identity += ps.len();
            continue;
        }
        if m < g.min {
            s.missed_match += (g.min - m) * g.size + ps.len();
            continue;
        }
        s.correct += ps.len();
        if m == 0 && g.min == 0 {
            s.abstain_ok_groups += 1;
        } else {
            let truth_in: HashSet<(usize, usize)> = truth.iter().copied().collect();
            let same = member.keys().all(|&(m1, m2)| truth_in.contains(&(g.before[m1], g.after[m2])));
            if !same {
                s.admissible_alternative_groups += 1;
            }
        }
    }
    s
}

/// True when `pred` is an admissible correspondence: nothing wrong and nothing missed.
pub fn admissible(groups: &[Group], truth: &[(usize, usize)], pred: &[(usize, usize)]) -> bool {
    let s = score(groups, truth, &HashSet::new(), pred);
    s.wrong_identity == 0 && s.missed_match == 0
}
