//! Research harness: why difffold's tree mapping differs from OmniDiff's hand-authored ground truth.
//!
//! The front end (tree-sitter conversion, ground-truth loading, taxonomy, `evaluate`) is copied from
//! `src/bin/score_accuracy.rs` so that "perfect" means exactly what it means there. On top of it this
//! binary runs a banded tree edit distance with arbitrary costs (`wted.rs`) to measure, per fixture, the
//! minimum cost, the number of optimal mappings, the best optimal mapping against the ground truth
//! (the oracle tie-break), whether the ground truth is itself a tree edit mapping and what it costs,
//! alternative cost models and tie-break costs, and a fitted tie-break (`learn`).
//!
//! usage:
//!   mechanics <diffs-dir> <out.csv> [nmax] [threads] [fixture-substring]
//!   mechanics learn <diffs-dir> [nmax] [threads] [epochs]
//!
//! Environment: `MECH_NMIN`, `MECH_REDUCED`, `MECH_SKIPLIB`, `MECH_ARMS`, `MECH_DUMP`, `MECH_TIMING`,
//! `MECH_VERBOSE`. See `notes/research/ACCURACY-MECHANICS.md` for the method and the results.

use difffold::ted::{ted_mapping, PostTree};
use difffold::{Arena, Id};
use serde_json::Value;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use tree_sitter::{Language, Node, Parser};

const NIL: u32 = u32::MAX;

// ---------------------------------------------------------------- trees

#[derive(Default)]
struct Interner {
    labels: HashMap<(u16, Option<Vec<u8>>), u32>,
}

impl Interner {
    fn label(&mut self, kind: u16, text: Option<&[u8]>) -> u32 {
        let next = u32::try_from(self.labels.len()).unwrap();
        *self
            .labels
            .entry((kind, text.map(<[u8]>::to_vec)))
            .or_insert(next)
    }
}

/// A tree-sitter tree flattened to preorder arrays.
#[derive(Default)]
struct Tree {
    kind: Vec<&'static str>,
    parent: Vec<u32>,
    kids: Vec<Vec<u32>>,
    id: Vec<Id>,
    label: Vec<u32>,
    /// Structurally visible, as OmniDiff defines it.
    vis: Vec<bool>,
    /// A leaf that counts for the changed-span view.
    token: Vec<bool>,
    /// A named tree-sitter node (not anonymous punctuation or keyword).
    named: Vec<bool>,
    rng: Vec<(usize, usize)>,
    size: Vec<u32>,
}

fn is_visible(n: Node, src: &[u8]) -> bool {
    if n.child_count() == 0 {
        return true;
    }
    let has = |a: usize, b: usize| !src[a..b].iter().all(u8::is_ascii_whitespace);
    let mut pos = n.start_byte();
    let mut c = n.walk();
    for ch in n.children(&mut c) {
        if ch.start_byte() > pos && has(pos, ch.start_byte()) {
            return true;
        }
        pos = pos.max(ch.end_byte());
    }
    n.end_byte() > pos && has(pos, n.end_byte())
}

fn convert(
    n: Node,
    src: &[u8],
    arena: &mut Arena,
    it: &mut Interner,
    t: &mut Tree,
    parent: u32,
) -> Id {
    let idx = u32::try_from(t.kind.len()).unwrap();
    t.kind.push(n.kind());
    t.parent.push(parent);
    t.kids.push(Vec::new());
    t.id.push(Id(0));
    t.label.push(0);
    t.size.push(0);
    t.vis.push(is_visible(n, src));
    t.named.push(n.is_named());
    t.rng.push((n.start_byte(), n.end_byte()));
    let text = &src[n.byte_range()];
    let leaf = n.child_count() == 0;
    let punct = !n.is_named() && !text.iter().any(u8::is_ascii_alphanumeric);
    t.token
        .push(leaf && !text.trim_ascii().is_empty() && !n.kind().contains("comment") && !punct);
    if parent != NIL {
        t.kids[parent as usize].push(idx);
    }
    let (id, label) = if leaf {
        let l = it.label(n.kind_id(), Some(text));
        (arena.mk(l, &[]), l)
    } else {
        let mut kids = Vec::with_capacity(n.child_count());
        let mut c = n.walk();
        for ch in n.children(&mut c) {
            kids.push(convert(ch, src, arena, it, t, idx));
        }
        let l = it.label(n.kind_id(), None);
        (arena.mk(l, &kids), l)
    };
    t.id[idx as usize] = id;
    t.label[idx as usize] = label;
    t.size[idx as usize] = arena.size(id);
    id
}

/// Optimal general tree edit mapping (deleting a node promotes its children) as preorder index pairs.
fn ted_pairs(bt: &Tree, at: &Tree, kinds_on: bool, hyg: bool, moves: bool) -> Vec<(u32, u32)> {
    // Iterative postorder numbering: `order[k]` is the preorder index of the k-th node in postorder.
    let post = |t: &Tree| -> (Vec<u32>, Vec<u32>) {
        let (mut order, mut stack) = (Vec::with_capacity(t.kind.len()), vec![(0u32, 0usize)]);
        while let Some((v, next)) = stack.pop() {
            if next < t.kids[v as usize].len() {
                stack.push((v, next + 1));
                stack.push((t.kids[v as usize][next], 0));
            } else {
                order.push(v);
            }
        }
        let mut pos = vec![0u32; t.kind.len()];
        for (k, &v) in order.iter().enumerate() {
            pos[v as usize] = k as u32;
        }
        (order, pos)
    };
    let mut kind_ids: HashMap<&'static str, u32> = HashMap::new();
    let mut build = |t: &Tree, order: &[u32], pos: &[u32]| -> PostTree {
        let label: Vec<u32> = order.iter().map(|&v| t.label[v as usize]).collect();
        let kids: Vec<Vec<u32>> = order
            .iter()
            .map(|&v| {
                t.kids[v as usize]
                    .iter()
                    .map(|&c| pos[c as usize])
                    .collect()
            })
            .collect();
        let pt = PostTree::from_kids(label, &kids);
        if kinds_on {
            let kind: Vec<u32> = order
                .iter()
                .map(|&v| {
                    let n = kind_ids.len() as u32;
                    *kind_ids.entry(t.kind[v as usize]).or_insert(n)
                })
                .collect();
            pt.with_kinds(kind)
        } else {
            pt
        }
    };
    let ((oa, pa), (ob, pb)) = (post(bt), post(at));
    let (ta, tb) = (build(bt, &oa, &pa), build(at, &ob, &pb));
    let m = ted_mapping(&ta, &tb);
    let mut pairs: Vec<(u32, u32)> = m
        .pairs
        .iter()
        .map(|&(x, y)| (oa[x as usize - 1], ob[y as usize - 1]))
        .collect();
    if hyg {
        drop_orphan_updates(bt, at, &mut pairs);
    }
    if moves {
        recover_moves(bt, at, &mut pairs);
    }
    pairs
}

/// Mapping hygiene. A leaf paired with a leaf of different text (an update) is kept only when the parents of the two
/// leaves are paired with each other; otherwise the pairing is an accident of the cost model and is dropped.
fn drop_orphan_updates(bt: &Tree, at: &Tree, pairs: &mut Vec<(u32, u32)>) {
    let set: std::collections::HashSet<(u32, u32)> = pairs.iter().copied().collect();
    pairs.retain(|&(x, y)| {
        let (xu, yu) = (x as usize, y as usize);
        if bt.label[xu] == at.label[yu] || !bt.kids[xu].is_empty() || !at.kids[yu].is_empty() {
            return true;
        }
        let (px, py) = (bt.parent[xu], at.parent[yu]);
        px != NIL && py != NIL && set.contains(&(px, py))
    });
}

/// Move recovery. Classical edit distance has no move operation, so a moved or reordered subtree is deleted on
/// one side and inserted on the other. A maximal subtree that is entirely unmapped on both sides and has the same
/// content (same hash-consed id) is matched node for node.
fn recover_moves(bt: &Tree, at: &Tree, pairs: &mut Vec<(u32, u32)>) {
    let roots = |t: &Tree, mapped: &[bool]| -> HashMap<u32, Vec<u32>> {
        // A node is "dead" when it and its whole subtree are unmapped; preorder indices make children larger than parents.
        let n = t.kind.len();
        let mut dead = vec![false; n];
        for v in (0..n).rev() {
            dead[v] = !mapped[v] && t.kids[v].iter().all(|&k| dead[k as usize]);
        }
        let mut by: HashMap<u32, Vec<u32>> = HashMap::new();
        for v in 0..n {
            if dead[v]
                && (t.parent[v] == NIL || !dead[t.parent[v] as usize])
                && !t.kids[v].is_empty()
            {
                by.entry(t.id[v].0).or_default().push(v as u32);
            }
        }
        by
    };
    let (mut ma, mut mb) = (vec![false; bt.kind.len()], vec![false; at.kind.len()]);
    for &(x, y) in pairs.iter() {
        ma[x as usize] = true;
        mb[y as usize] = true;
    }
    let (ra, rb) = (roots(bt, &ma), roots(at, &mb));
    for (id, xs) in &ra {
        let Some(ys) = rb.get(id) else { continue };
        for (&x, &y) in xs.iter().zip(ys.iter()) {
            let mut stack = vec![(x, y)];
            while let Some((u, v)) = stack.pop() {
                pairs.push((u, v));
                for (&cu, &cv) in bt.kids[u as usize].iter().zip(at.kids[v as usize].iter()) {
                    stack.push((cu, cv));
                }
            }
        }
    }
}

fn lang(ext: &str) -> Option<(&'static str, Language)> {
    Some(match ext {
        "java" => ("java", tree_sitter_java::LANGUAGE.into()),
        "go" => ("go", tree_sitter_go::LANGUAGE.into()),
        "c" | "h" => ("c", tree_sitter_c::LANGUAGE.into()),
        "py" => ("python", tree_sitter_python::LANGUAGE.into()),
        "js" | "mjs" => ("javascript", tree_sitter_javascript::LANGUAGE.into()),
        "ts" => (
            "typescript",
            tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into(),
        ),
        "tsx" => ("tsx", tree_sitter_typescript::LANGUAGE_TSX.into()),
        "rs" => ("rust", tree_sitter_rust::LANGUAGE.into()),
        _ => return None,
    })
}

// ---------------------------------------------------------------- ground truth

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    Identical,
    Update,
    Mbni,
}

struct Group {
    before: Vec<u32>,
    after: Vec<u32>,
    all_to_all: bool,
}

#[derive(Default)]
struct Gt {
    pairs: Vec<(u32, u32, Op)>,
    del: Vec<u32>,
    ins: Vec<u32>,
    groups: Vec<Group>,
    embedded: usize,
}

/// Resolves a ground-truth path: each segment is `kind:n`, the n-th child of that kind (1-based).
fn resolve_fast(t: &Tree, path: &Value) -> Result<u32, String> {
    let mut cur = 0u32;
    for seg in path.as_array().ok_or("path not an array")? {
        let s = seg.as_str().ok_or("segment not a string")?;
        let (kind, occ) = match s.rsplit_once(':') {
            Some((k, n)) => match n.parse::<u32>() {
                Ok(n) => (k, n),
                Err(_) => (s, 1),
            },
            None => (s, 1),
        };
        let kind: &str = kind;
        let found = t.kids[cur as usize]
            .iter()
            .filter(|&&k| t.kind[k as usize] == kind)
            .nth(occ as usize - 1)
            .copied();
        cur = found.ok_or_else(|| format!("path segment {s} not found"))?;
    }
    Ok(cur)
}

fn load_gt(json: &Value, bt: &Tree, at: &Tree) -> Result<Gt, String> {
    let mut gt = Gt::default();
    for e in json["entries"].as_array().ok_or("no entries")? {
        let op = e["operation"].as_str().ok_or("no operation")?;
        let bp = &e["before_path"];
        let ap = &e["after_path"];
        match op {
            "identical" | "update" | "match_but_not_identical" => {
                let (b, a) = (resolve_fast(bt, bp)?, resolve_fast(at, ap)?);
                let o = match op {
                    "identical" => Op::Identical,
                    "update" => Op::Update,
                    _ => Op::Mbni,
                };
                gt.pairs.push((b, a, o));
            }
            "identical_with_children" => {
                let (b, a) = (resolve_fast(bt, bp)?, resolve_fast(at, ap)?);
                let s = bt.size[b as usize];
                if s != at.size[a as usize] {
                    return Err("identical_with_children subtrees differ in size".into());
                }
                for k in 0..s {
                    if bt.kind[(b + k) as usize] != at.kind[(a + k) as usize] {
                        return Err("identical_with_children subtrees differ in kind".into());
                    }
                    gt.pairs.push((b + k, a + k, Op::Identical));
                }
            }
            "delete" => gt.del.push(resolve_fast(bt, bp)?),
            "delete_with_children" => {
                let b = resolve_fast(bt, bp)?;
                gt.del.extend(b..b + bt.size[b as usize]);
            }
            "insert" => gt.ins.push(resolve_fast(at, ap)?),
            "insert_with_children" => {
                let a = resolve_fast(at, ap)?;
                gt.ins.extend(a..a + at.size[a as usize]);
            }
            other => return Err(format!("unknown operation {other}")),
        }
    }
    if let Some(gs) = json["groups"].as_array() {
        for g in gs {
            let r = |t: &Tree, k: &str| -> Result<Vec<u32>, String> {
                g[k].as_array()
                    .ok_or("group paths")?
                    .iter()
                    .map(|p| resolve_fast(t, p))
                    .collect()
            };
            gt.groups.push(Group {
                before: r(bt, "before_paths")?,
                after: r(at, "after_paths")?,
                all_to_all: g["pairing"].as_str() == Some("all_to_all"),
            });
        }
    }
    gt.embedded = json["embedded"].as_array().map_or(0, Vec::len);
    Ok(gt)
}

// ---------------------------------------------------------------- tools

struct Tool {
    b2a: Vec<Vec<u32>>,
    a2b: Vec<Vec<u32>>,
}

impl Tool {
    fn from_pairs(nb: usize, na: usize, pairs: impl Iterator<Item = (u32, u32)>) -> Self {
        let mut t = Tool {
            b2a: vec![Vec::new(); nb],
            a2b: vec![Vec::new(); na],
        };
        for (b, a) in pairs {
            t.b2a[b as usize].push(a);
            t.a2b[a as usize].push(b);
        }
        t
    }
}

// ---------------------------------------------------------------- taxonomy

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum Cls {
    /// Leaf relabel or text edit with the parent pair intact.
    Local,
    /// A node or subtree inserted or deleted under a matched parent, nothing matched inside it.
    Sibling,
    /// Insert or delete among identical siblings, or a ground-truth N:M group.
    Repeated,
    /// A matched child that crosses other matched siblings under the same matched parent.
    Reorder,
    /// A matched node whose parent is not matched to its parent, and which is not a wrap.
    Move,
    /// A new or removed container between a matched ancestor and matched descendants.
    Wrap,
    /// A fixture that keeps under a quarter of its nodes identical.
    Rewrite,
    /// Unchanged context (identical nodes and containers) and collateral damage in it.
    Context,
}

const CLASSES: [Cls; 8] = [
    Cls::Local,
    Cls::Sibling,
    Cls::Repeated,
    Cls::Reorder,
    Cls::Move,
    Cls::Wrap,
    Cls::Rewrite,
    Cls::Context,
];

fn cls_name(c: Cls) -> &'static str {
    match c {
        Cls::Local => "local_edit",
        Cls::Sibling => "sibling_ins_del",
        Cls::Repeated => "repeated_children",
        Cls::Reorder => "reorder",
        Cls::Move => "cross_parent_move",
        Cls::Wrap => "wrap_unwrap",
        Cls::Rewrite => "wholesale_rewrite",
        Cls::Context => "context",
    }
}

struct Classes {
    /// Cause class per ground-truth pair, aligned with `gt.pairs`.
    pair: Vec<Cls>,
    del: Vec<Cls>,
    ins: Vec<Cls>,
    /// Best number of ground-truth pairs a top-down ordered mapping can contain (kept from the scorer).
    #[allow(dead_code)]
    bound: u32,
    n_move: u32,
    n_wrap: u32,
    n_reorder: u32,
    rewrite: bool,
    /// Which classes occur at all, from structure (before the rewrite override).
    present: [bool; 8],
}

fn cls_ix(c: Cls) -> usize {
    CLASSES.iter().position(|&x| x == c).unwrap()
}

/// Max-weight increasing chain per matched parent, bottom-up. Returns `best` per before-node
/// (valid for paired nodes) and which consistent children lie on their parent's chain.
fn chains(bt: &Tree, g_b2a: &[u32], at: &Tree) -> (Vec<u32>, Vec<bool>) {
    let n = bt.kind.len();
    let mut best = vec![0u32; n];
    let mut on = vec![false; n];
    for b in (0..n).rev() {
        let a = g_b2a[b];
        if a == NIL {
            continue;
        }
        // Consistent children in before order, keyed by their after index.
        let cs: Vec<(u32, u32)> = bt.kids[b]
            .iter()
            .filter(|&&c| g_b2a[c as usize] != NIL && at.parent[g_b2a[c as usize] as usize] == a)
            .map(|&c| (c, g_b2a[c as usize]))
            .collect();
        let k = cs.len();
        let mut ds: Vec<u32> = cs.iter().map(|x| x.1).collect();
        ds.sort_unstable();
        let rank = |d: u32| ds.binary_search(&d).unwrap() + 1;
        // Fenwick tree of (best dp, index) over after rank.
        let mut bit: Vec<(u64, usize)> = vec![(0, usize::MAX); k + 1];
        let mut dp = vec![0u64; k];
        let mut prev = vec![usize::MAX; k];
        let (mut top, mut top_i) = (0u64, usize::MAX);
        for (i, &(c, d)) in cs.iter().enumerate() {
            let mut r = rank(d) - 1;
            let mut q = (0u64, usize::MAX);
            while r > 0 {
                if bit[r].0 > q.0 {
                    q = bit[r];
                }
                r -= r & r.wrapping_neg();
            }
            dp[i] = q.0 + u64::from(best[c as usize]);
            prev[i] = q.1;
            let mut r = rank(d);
            while r <= k {
                if dp[i] > bit[r].0 {
                    bit[r] = (dp[i], i);
                }
                r += r & r.wrapping_neg();
            }
            if dp[i] > top {
                top = dp[i];
                top_i = i;
            }
        }
        let mut i = top_i;
        while i != usize::MAX {
            on[cs[i].0 as usize] = true;
            i = prev[i];
        }
        best[b] = 1 + u32::try_from(top).unwrap();
    }
    (best, on)
}

fn is_anc(t: &Tree, x: u32, y: u32) -> bool {
    x < y && y < x + t.size[x as usize]
}

fn classify(gt: &Gt, bt: &Tree, at: &Tree) -> Classes {
    let (nb, na) = (bt.kind.len(), at.kind.len());
    let mut g_b2a = vec![NIL; nb];
    let mut g_a2b = vec![NIL; na];
    for &(b, a, _) in &gt.pairs {
        g_b2a[b as usize] = a;
        g_a2b[a as usize] = b;
    }
    let (best, on) = chains(bt, &g_b2a, at);
    let bound = if g_b2a[0] == 0 { best[0] } else { 0 };
    let mut present = [false; 8];
    // Pair kinds by node.
    let mut own = vec![Cls::Context; nb];
    let (mut n_move, mut n_wrap, mut n_reorder) = (0, 0, 0);
    for &(b, a, op) in &gt.pairs {
        let (pb, pa) = (bt.parent[b as usize], at.parent[a as usize]);
        let consistent = b == 0 || (g_b2a[pb as usize] == pa);
        let c = if consistent {
            if !on[b as usize] && b != 0 {
                n_reorder += 1;
                Cls::Reorder
            } else if op == Op::Update
                || bt.label[b as usize] != at.label[a as usize] && bt.kids[b as usize].is_empty()
            {
                Cls::Local
            } else {
                Cls::Context
            }
        } else {
            // Nearest matched proper ancestor of b and where it went.
            let mut anc = pb;
            while anc != NIL && g_b2a[anc as usize] == NIL {
                anc = bt.parent[anc as usize];
            }
            if anc != NIL && is_anc(at, g_b2a[anc as usize], a) {
                n_wrap += 1;
                Cls::Wrap
            } else {
                n_move += 1;
                Cls::Move
            }
        };
        own[b as usize] = c;
    }
    // Prefix counts of pairs, to ask "does this inserted/deleted node contain a matched node".
    let prefix = |m: &[u32]| {
        let mut p = vec![0u32; m.len() + 1];
        for i in 0..m.len() {
            p[i + 1] = p[i] + u32::from(m[i] != NIL);
        }
        p
    };
    let (pb_pre, pa_pre) = (prefix(&g_b2a), prefix(&g_a2b));
    // Cause class per pair: an inconsistent ancestor-or-self wins over the node's own class.
    let mut cause = vec![Cls::Context; nb];
    for b in 0..nb {
        if g_b2a[b] == NIL {
            continue;
        }
        let c = own[b];
        let inherited = bt.parent[b];
        cause[b] = if matches!(c, Cls::Move | Cls::Wrap | Cls::Reorder) {
            c
        } else if inherited != NIL
            && matches!(
                cause[inherited as usize],
                Cls::Move | Cls::Wrap | Cls::Reorder
            )
            && g_b2a[inherited as usize] != NIL
        {
            cause[inherited as usize]
        } else {
            c
        };
    }
    // Deleted and inserted nodes.
    let mut del_mark = vec![false; nb];
    for &d in &gt.del {
        del_mark[d as usize] = true;
    }
    let mut ins_mark = vec![false; na];
    for &i in &gt.ins {
        ins_mark[i as usize] = true;
    }
    let root_cls = |t: &Tree, x: u32, pre: &[u32], mark: &[bool]| {
        let (lo, hi) = (x as usize + 1, (x + t.size[x as usize]) as usize);
        if pre[hi] - pre[lo] > 0 {
            return Cls::Wrap;
        }
        let p = t.parent[x as usize];
        if p != NIL
            && t.kids[p as usize]
                .iter()
                .any(|&s| s != x && t.id[s as usize] == t.id[x as usize])
        {
            return Cls::Repeated;
        }
        let _ = mark;
        Cls::Sibling
    };
    let mut del_cause = vec![Cls::Sibling; nb];
    for b in 0..nb {
        if !del_mark[b] {
            continue;
        }
        let p = bt.parent[b];
        del_cause[b] = if p != NIL && del_mark[p as usize] {
            del_cause[p as usize]
        } else {
            root_cls(bt, b as u32, &pb_pre, &del_mark)
        };
    }
    let mut ins_cause = vec![Cls::Sibling; na];
    for a in 0..na {
        if !ins_mark[a] {
            continue;
        }
        let p = at.parent[a];
        ins_cause[a] = if p != NIL && ins_mark[p as usize] {
            ins_cause[p as usize]
        } else {
            root_cls(at, a as u32, &pa_pre, &ins_mark)
        };
    }
    // Wholesale rewrite: under a quarter of all nodes are identical, matched pairs.
    let identical = gt.pairs.iter().filter(|p| p.2 == Op::Identical).count();
    let rewrite = 2 * identical * 4 < nb + na;
    let mut pair: Vec<Cls> = gt.pairs.iter().map(|p| cause[p.0 as usize]).collect();
    let mut del: Vec<Cls> = gt.del.iter().map(|&d| del_cause[d as usize]).collect();
    let mut ins: Vec<Cls> = gt.ins.iter().map(|&i| ins_cause[i as usize]).collect();
    for c in pair.iter().chain(del.iter()).chain(ins.iter()) {
        present[cls_ix(*c)] = true;
    }
    if !gt.groups.is_empty() {
        present[cls_ix(Cls::Repeated)] = true;
    }
    if rewrite {
        present[cls_ix(Cls::Rewrite)] = true;
        pair.iter_mut()
            .chain(del.iter_mut())
            .chain(ins.iter_mut())
            .for_each(|c| *c = Cls::Rewrite);
    }
    Classes {
        pair,
        del,
        ins,
        bound,
        n_move,
        n_wrap,
        n_reorder,
        rewrite,
        present,
    }
}

// ---------------------------------------------------------------- scoring

struct Dec {
    cls: Cls,
    vis: bool,
    named: bool,
    fail: bool,
}

fn evaluate(gt: &Gt, cl: &Classes, bt: &Tree, at: &Tree, tool: &Tool) -> Vec<Dec> {
    let mut out = Vec::new();
    for (i, &(b, a, _)) in gt.pairs.iter().enumerate() {
        out.push(Dec {
            cls: cl.pair[i],
            vis: bt.vis[b as usize],
            named: bt.named[b as usize],
            fail: tool.b2a[b as usize] != [a],
        });
    }
    for (i, &b) in gt.del.iter().enumerate() {
        out.push(Dec {
            cls: cl.del[i],
            vis: bt.vis[b as usize],
            named: bt.named[b as usize],
            fail: !tool.b2a[b as usize].is_empty(),
        });
    }
    for (i, &a) in gt.ins.iter().enumerate() {
        out.push(Dec {
            cls: cl.ins[i],
            vis: at.vis[a as usize],
            named: at.named[a as usize],
            fail: !tool.a2b[a as usize].is_empty(),
        });
    }
    // Groups, following OmniDiff's check without the subtree-closure step.
    for g in &gt.groups {
        let rep = Cls::Repeated;
        let (bs, as_): (
            std::collections::HashSet<u32>,
            std::collections::HashSet<u32>,
        ) = (
            g.before.iter().copied().collect(),
            g.after.iter().copied().collect(),
        );
        let mut matched = 0usize;
        let mut matched_after = std::collections::HashSet::new();
        for &b in &g.before {
            let p = &tool.b2a[b as usize];
            let ok_leftover = !g.all_to_all && p.is_empty();
            let ok_match = !p.is_empty() && p.iter().all(|x| as_.contains(x));
            if ok_match {
                matched += 1;
                matched_after.insert(p[0]);
            }
            out.push(Dec {
                cls: rep,
                vis: bt.vis[b as usize],
                named: bt.named[b as usize],
                fail: !(ok_leftover || ok_match),
            });
        }
        for &a in &g.after {
            if matched_after.contains(&a) {
                continue;
            }
            let p = &tool.a2b[a as usize];
            let ok_leftover = !g.all_to_all && p.is_empty();
            let ok_match = g.all_to_all && !p.is_empty() && p.iter().all(|x| bs.contains(x));
            if ok_match {
                matched += 1;
            }
            out.push(Dec {
                cls: rep,
                vis: at.vis[a as usize],
                named: at.named[a as usize],
                fail: !(ok_leftover || ok_match),
            });
        }
        if !g.all_to_all {
            let first = g.before.first().is_none_or(|&b| bt.vis[b as usize]);
            out.push(Dec {
                cls: rep,
                vis: first,
                named: true,
                fail: matched != g.before.len().min(g.after.len()),
            });
        }
    }
    if cl.rewrite {
        out.iter_mut().for_each(|d| d.cls = Cls::Rewrite);
    }
    out
}

fn find(dir: &Path, prefix: &str) -> Option<PathBuf> {
    std::fs::read_dir(dir)
        .ok()?
        .flatten()
        .map(|e| e.path())
        .find(|p| {
            p.file_name()
                .and_then(|f| f.to_str())
                .is_some_and(|f| f.starts_with(prefix))
        })
}

// ================================================================ experiments

mod wted;

use difffold::diff_checked;
use difffold::mapping::correspondence;
use difffold::ted::{check_mapping, ted};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use wted::{solve_auto, Costs, Params, FORBID};

const K: u64 = 1 << 36;
const W_VIS: u64 = 1 << 17;

/// Everything about one tree in postorder form (index x - 1 for the 1-based postorder node x).
struct Side {
    order: Vec<u32>,
    pt: PostTree,
    kind: Vec<u32>,
    leaf: Vec<bool>,
    named: Vec<bool>,
    pkind: Vec<u32>,
    gkind: Vec<u32>,
    path: Vec<u64>,
    sib: Vec<u32>,
    depth: Vec<u32>,
    /// Hash-consed id of the previous and next sibling subtree, `u32::MAX` for none.
    prev_id: Vec<u32>,
    next_id: Vec<u32>,
    /// Hash-consed id of the parent subtree.
    pid: Vec<u32>,
    /// Subtree size.
    size: Vec<u32>,
    /// Update family: bit 0 identifier-like, bits 1 to 6 operator families.
    fam: Vec<u8>,
}

fn postorder(t: &Tree) -> (Vec<u32>, Vec<u32>) {
    let (mut order, mut stack) = (Vec::with_capacity(t.kind.len()), vec![(0u32, 0usize)]);
    while let Some((v, next)) = stack.pop() {
        if next < t.kids[v as usize].len() {
            stack.push((v, next + 1));
            stack.push((t.kids[v as usize][next], 0));
        } else {
            order.push(v);
        }
    }
    let mut pos = vec![0u32; t.kind.len()];
    for (k, &v) in order.iter().enumerate() {
        pos[v as usize] = k as u32;
    }
    (order, pos)
}

/// The update family of a tree-sitter kind: identifier-like kinds share one, and operators share a family
/// with the operators of the same sort.
fn family(kind: &str) -> u8 {
    const CMP: &[&str] = &["<", ">", "<=", ">=", "==", "!=", "===", "!=="];
    const ARITH: &[&str] = &["+", "-", "*", "/", "%", "**"];
    const BIT: &[&str] = &["&", "|", "^", "<<", ">>", ">>>"];
    const LOGIC: &[&str] = &["&&", "||", "and", "or"];
    const ASSIGN: &[&str] = &[
        "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
    ];
    const INCR: &[&str] = &["++", "--"];
    let mut f = 0u8;
    if kind.contains("identifier") {
        f |= 1;
    }
    for (i, set) in [CMP, ARITH, BIT, LOGIC, ASSIGN, INCR].iter().enumerate() {
        if set.contains(&kind) {
            f |= 2 << i;
        }
    }
    f
}

/// Hash-consed id of the previous or next sibling subtree of `v`.
fn neighbour(t: &Tree, v: usize, next: bool) -> u32 {
    let p = t.parent[v];
    if p == NIL {
        return u32::MAX;
    }
    let kids = &t.kids[p as usize];
    let i = kids.iter().position(|&c| c as usize == v).unwrap();
    let j = if next { i + 1 } else { i.wrapping_sub(1) };
    kids.get(j).map_or(u32::MAX, |&c| t.id[c as usize].0)
}

fn build_side(
    t: &Tree,
    kind_ids: &mut HashMap<&'static str, u32>,
    with_kinds: bool,
) -> (Side, Vec<u32>) {
    let (order, pos) = postorder(t);
    let label: Vec<u32> = order.iter().map(|&v| t.label[v as usize]).collect();
    let kids: Vec<Vec<u32>> = order
        .iter()
        .map(|&v| {
            t.kids[v as usize]
                .iter()
                .map(|&c| pos[c as usize])
                .collect()
        })
        .collect();
    let mut pt = PostTree::from_kids(label, &kids);
    let kind: Vec<u32> = order
        .iter()
        .map(|&v| {
            let n = kind_ids.len() as u32;
            *kind_ids.entry(t.kind[v as usize]).or_insert(n)
        })
        .collect();
    if with_kinds {
        pt = pt.with_kinds(kind.clone());
    }
    // Context features per preorder node, then permuted into postorder.
    let n = t.kind.len();
    let mut depth = vec![0u32; n];
    let mut path = vec![0u64; n];
    let mut sib = vec![0u32; n];
    let kid_of = |v: usize| *kind_ids.get(t.kind[v]).unwrap() as u64;
    for v in 0..n {
        let p = t.parent[v];
        if p != NIL {
            depth[v] = depth[p as usize] + 1;
            path[v] = path[p as usize]
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(kid_of(v) + 1);
            sib[v] = t.kids[p as usize]
                .iter()
                .position(|&c| c as usize == v)
                .unwrap() as u32;
        } else {
            path[v] = kid_of(v) + 1;
        }
    }
    let pk = |v: usize| -> u32 {
        let p = t.parent[v];
        if p == NIL {
            u32::MAX
        } else {
            kid_of(p as usize) as u32
        }
    };
    let side = Side {
        pkind: order.iter().map(|&v| pk(v as usize)).collect(),
        gkind: order
            .iter()
            .map(|&v| {
                let p = t.parent[v as usize];
                if p == NIL {
                    u32::MAX
                } else {
                    pk(p as usize)
                }
            })
            .collect(),
        path: order.iter().map(|&v| path[v as usize]).collect(),
        sib: order.iter().map(|&v| sib[v as usize]).collect(),
        depth: order.iter().map(|&v| depth[v as usize]).collect(),
        prev_id: order
            .iter()
            .map(|&v| neighbour(t, v as usize, false))
            .collect(),
        pid: order
            .iter()
            .map(|&v| {
                let p = t.parent[v as usize];
                if p == NIL {
                    u32::MAX
                } else {
                    t.id[p as usize].0
                }
            })
            .collect(),
        size: order.iter().map(|&v| t.size[v as usize]).collect(),
        fam: order.iter().map(|&v| family(t.kind[v as usize])).collect(),
        next_id: order
            .iter()
            .map(|&v| neighbour(t, v as usize, true))
            .collect(),
        leaf: order
            .iter()
            .map(|&v| t.kids[v as usize].is_empty())
            .collect(),
        named: order.iter().map(|&v| t.named[v as usize]).collect(),
        kind,
        order,
        pt,
    };
    (side, pos)
}

/// Number of tie-break features.
const NF: usize = 11;

/// Context mismatch features of the pair (xi, yi), 0-based postorder.
fn feat(a: &Side, b: &Side, xi: usize, yi: usize) -> [u8; NF] {
    let path = a.path[xi] != b.path[yi];
    [
        u8::from(a.pkind[xi] != b.pkind[yi]),
        u8::from(a.gkind[xi] != b.gkind[yi]),
        u8::from(path),
        u8::from(a.prev_id[xi] != b.prev_id[yi]),
        u8::from(a.next_id[xi] != b.next_id[yi]),
        a.depth[xi].abs_diff(b.depth[yi]).min(3) as u8,
        a.sib[xi].abs_diff(b.sib[yi]).min(3) as u8,
        u8::from(a.pid[xi] != b.pid[yi]),
        a.size[xi].abs_diff(b.size[yi]).min(3) as u8,
        u8::from(a.leaf[xi] && !a.named[xi] && path),
        u8::from(a.pt.label[xi] != b.pt.label[yi]),
    ]
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Prim {
    Kinds,
    Unit,
    NoRel,
    IntCheap,
    IntExp,
    AnonCheap,
    /// Kinds, plus 1 when the parent kinds differ.
    CtxP1,
    /// Kinds, plus 2 (a pair never beats delete plus insert) when the parent kinds differ.
    CtxP2,
    /// Kinds, plus 1 when the root paths differ.
    CtxPath1,
    /// Kinds, plus 2 when the root paths differ.
    CtxPath2,
    /// Kinds, plus cost-1 updates between identifier-like kinds and within operator families.
    Fam,
}

impl Prim {
    fn m0(self) -> u64 {
        match self {
            Prim::Kinds
            | Prim::Unit
            | Prim::NoRel
            | Prim::AnonCheap
            | Prim::CtxP1
            | Prim::CtxP2
            | Prim::CtxPath1
            | Prim::CtxPath2
            | Prim::Fam => 1,
            Prim::IntCheap | Prim::IntExp => 2,
        }
    }
    fn name(self) -> &'static str {
        match self {
            Prim::Kinds => "kinds",
            Prim::Unit => "unit",
            Prim::NoRel => "norel",
            Prim::IntCheap => "intcheap",
            Prim::IntExp => "intexp",
            Prim::AnonCheap => "anoncheap",
            Prim::CtxP1 => "ctxp1",
            Prim::CtxP2 => "ctxp2",
            Prim::CtxPath1 => "ctxpath1",
            Prim::CtxPath2 => "ctxpath2",
            Prim::Fam => "fam",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tie {
    None,
    Oracle,
    Parent,
    Path2,
    PathFull,
    Sib,
    ParentSib,
    Depth,
    /// Sibling neighbours: previous and next sibling subtree identical.
    Neigh,
    /// Same root path plus identical sibling neighbours.
    NeighPath,
    /// Ground-truth oracle restricted to the pairs the library traceback can emit.
    OracleStrict,
    /// Weighted sum of context mismatch features.
    Learned,
}

impl Tie {
    fn name(self) -> &'static str {
        match self {
            Tie::None => "none",
            Tie::Oracle => "oracle",
            Tie::Parent => "parent",
            Tie::Path2 => "path2",
            Tie::PathFull => "path",
            Tie::Sib => "sib",
            Tie::ParentSib => "parentsib",
            Tie::Depth => "depth",
            Tie::Neigh => "neigh",
            Tie::NeighPath => "neighpath",
            Tie::OracleStrict => "oraclestrict",
            Tie::Learned => "learned",
        }
    }
}

/// GT-derived penalties, indexed by postorder node (0-based).
struct Sec {
    partner_b: Vec<u32>, // 1-based postorder node of the other tree, 0 for none
    partner_a: Vec<u32>,
    del_b: Vec<bool>,
    ins_a: Vec<bool>,
    grp_b: Vec<u32>,
    grp_a: Vec<u32>,
    grp_all_b: Vec<bool>,
    wb: Vec<u64>,
    wa: Vec<u64>,
    free_b: Vec<bool>,
    free_a: Vec<bool>,
}

struct Model<'a> {
    a: &'a Side,
    b: &'a Side,
    prim: Prim,
    tie: Tie,
    /// Pairs whose relabel is no cheaper than delete plus insert are not offered.
    drop_dominated: bool,
    sec: &'a Sec,
    /// Weights of the learned tie-break.
    w: &'a [u64],
}

impl Model<'_> {
    fn dprim(&self, s: &Side, i: usize) -> u64 {
        match self.prim {
            Prim::Kinds
            | Prim::Unit
            | Prim::NoRel
            | Prim::CtxP1
            | Prim::CtxP2
            | Prim::CtxPath1
            | Prim::CtxPath2
            | Prim::Fam => 1,
            Prim::IntCheap => {
                if s.leaf[i] {
                    3
                } else {
                    2
                }
            }
            Prim::IntExp => {
                if s.leaf[i] {
                    2
                } else {
                    3
                }
            }
            Prim::AnonCheap => {
                if s.named[i] {
                    2
                } else {
                    1
                }
            }
        }
    }
    fn pprim(&self, x: usize, y: usize) -> u64 {
        let (a, b) = (self.a, self.b);
        let (xi, yi) = (x - 1, y - 1);
        let kinds_rel = |same_label: bool| -> u64 {
            if same_label {
                0
            } else if a.kind[xi] == b.kind[yi] {
                1
            } else {
                2
            }
        };
        let same_label = a.pt.label[xi] == b.pt.label[yi];
        match self.prim {
            Prim::Kinds => kinds_rel(same_label),
            Prim::Fam => {
                if same_label {
                    0
                } else if a.kind[xi] == b.kind[yi] || a.fam[xi] & b.fam[yi] != 0 {
                    1
                } else {
                    2
                }
            }
            Prim::CtxP1 | Prim::CtxP2 | Prim::CtxPath1 | Prim::CtxPath2 => {
                let (mismatch, pen) = match self.prim {
                    Prim::CtxP1 => (a.pkind[xi] != b.pkind[yi], 1),
                    Prim::CtxP2 => (a.pkind[xi] != b.pkind[yi], 2),
                    Prim::CtxPath1 => (a.path[xi] != b.path[yi], 1),
                    _ => (a.path[xi] != b.path[yi], 2),
                };
                (kinds_rel(same_label) + if mismatch { pen } else { 0 }).min(2)
            }
            Prim::Unit => u64::from(!same_label),
            Prim::NoRel => {
                if same_label {
                    0
                } else {
                    2
                }
            }
            Prim::IntCheap | Prim::IntExp | Prim::AnonCheap => {
                if same_label {
                    return 0;
                }
                let both = self.dprim(a, xi) + self.dprim(b, yi);
                if a.kind[xi] == b.kind[yi] && a.leaf[xi] && b.leaf[yi] {
                    both / 2
                } else {
                    both
                }
            }
        }
    }
    fn sec_pair(&self, x: usize, y: usize) -> u64 {
        let (a, b, s) = (self.a, self.b, self.sec);
        let (xi, yi) = (x - 1, y - 1);
        match self.tie {
            Tie::None => 0,
            Tie::Oracle | Tie::OracleStrict => {
                if s.partner_b[xi] as usize == y {
                    return 0;
                }
                let mut v = 0;
                if s.partner_b[xi] != 0 || s.del_b[xi] {
                    v += s.wb[xi];
                }
                if s.partner_b[xi] != 0 && s.del_b[xi] {
                    // cannot happen (a node is not both paired and deleted), kept explicit
                    v += 0;
                }
                if s.ins_a[yi] {
                    v += s.wa[yi];
                }
                if s.grp_b[xi] != u32::MAX && s.grp_b[xi] != s.grp_a[yi] {
                    v += s.wb[xi];
                }
                if s.grp_a[yi] != u32::MAX && s.grp_b[xi] != s.grp_a[yi] {
                    v += s.wa[yi];
                }
                v
            }
            Tie::Parent => u64::from(a.pkind[xi] != b.pkind[yi]),
            Tie::Path2 => {
                u64::from(a.pkind[xi] != b.pkind[yi]) + u64::from(a.gkind[xi] != b.gkind[yi])
            }
            Tie::PathFull => u64::from(a.path[xi] != b.path[yi]),
            Tie::Sib => u64::from(a.sib[xi].abs_diff(b.sib[yi]).min(3)),
            Tie::ParentSib => {
                4 * u64::from(a.pkind[xi] != b.pkind[yi])
                    + u64::from(a.sib[xi].abs_diff(b.sib[yi]).min(3))
            }
            Tie::Depth => u64::from(a.depth[xi].abs_diff(b.depth[yi]).min(4)),
            Tie::Learned => feat(a, b, xi, yi)
                .iter()
                .zip(self.w.iter())
                .map(|(&f, &w)| u64::from(f) * w)
                .sum(),
            Tie::Neigh => {
                u64::from(a.prev_id[xi] != b.prev_id[yi])
                    + u64::from(a.next_id[xi] != b.next_id[yi])
            }
            Tie::NeighPath => {
                4 * u64::from(a.path[xi] != b.path[yi])
                    + u64::from(a.prev_id[xi] != b.prev_id[yi])
                    + u64::from(a.next_id[xi] != b.next_id[yi])
            }
        }
    }
}

impl Costs for Model<'_> {
    fn pair(&self, x: usize, y: usize) -> u64 {
        let pp = self.pprim(x, y);
        if self.drop_dominated
            && pp > 0
            && pp >= self.dprim(self.a, x - 1) + self.dprim(self.b, y - 1)
        {
            return FORBID;
        }
        pp * K + self.sec_pair(x, y)
    }
    fn del(&self, x: usize) -> u64 {
        let s = self.sec;
        let extra = if matches!(self.tie, Tie::Oracle | Tie::OracleStrict)
            && (s.partner_b[x - 1] != 0 || (s.grp_b[x - 1] != u32::MAX && s.grp_all_b[x - 1]))
        {
            s.wb[x - 1]
        } else {
            0
        };
        self.dprim(self.a, x - 1) * K + extra
    }
    fn ins(&self, y: usize) -> u64 {
        self.dprim(self.b, y - 1) * K
    }
}

/// Costs for the "is the ground truth realisable" experiments.
struct Forced<'a> {
    a: &'a Side,
    b: &'a Side,
    sec: &'a Sec,
    /// Maximise retained ground-truth pairs: pair cost 0 and only ground-truth pairs allowed.
    max_subset: bool,
}

impl Costs for Forced<'_> {
    fn pair(&self, x: usize, y: usize) -> u64 {
        let s = self.sec;
        let ok = s.partner_b[x - 1] as usize == y
            || (s.free_b[x - 1] && s.free_a[y - 1] && !self.max_subset)
            || (s.grp_b[x - 1] != u32::MAX && s.grp_b[x - 1] == s.grp_a[y - 1] && !self.max_subset);
        if !ok {
            return FORBID;
        }
        if self.max_subset {
            return 0;
        }
        let (a, b) = (self.a, self.b);
        let rel = if a.pt.label[x - 1] == b.pt.label[y - 1] {
            0
        } else if a.kind[x - 1] == b.kind[y - 1] {
            1
        } else {
            2
        };
        rel * K
    }
    fn del(&self, x: usize) -> u64 {
        if !self.max_subset && self.sec.partner_b[x - 1] != 0 {
            FORBID
        } else {
            K
        }
    }
    fn ins(&self, y: usize) -> u64 {
        if !self.max_subset && self.sec.partner_a[y - 1] != 0 {
            FORBID
        } else {
            K
        }
    }
}

struct Ev {
    vis: u32,
    named_vis: u32,
    all: u32,
    cls: [u32; 8],
}

fn eval(gt: &Gt, cl: &Classes, bt: &Tree, at: &Tree, pairs: &[(u32, u32)]) -> Ev {
    let tool = Tool::from_pairs(bt.kind.len(), at.kind.len(), pairs.iter().copied());
    let decs = evaluate(gt, cl, bt, at, &tool);
    let mut e = Ev {
        vis: 0,
        named_vis: 0,
        all: 0,
        cls: [0; 8],
    };
    for d in &decs {
        if d.fail {
            e.all += 1;
            if d.vis {
                e.vis += 1;
                e.cls[cls_ix(d.cls)] += 1;
                if d.named {
                    e.named_vis += 1;
                }
            }
        }
    }
    e
}

fn to_pre(sa: &Side, sb: &Side, m: &[(u32, u32)]) -> Vec<(u32, u32)> {
    m.iter()
        .map(|&(x, y)| (sa.order[x as usize - 1], sb.order[y as usize - 1]))
        .collect()
}

type Row = Vec<(String, String)>;

fn put(r: &mut Row, k: &str, v: impl std::fmt::Display) {
    r.push((k.to_string(), v.to_string()));
}

fn put_ev(r: &mut Row, arm: &str, e: &Ev, with_cls: bool) {
    put(r, &format!("{arm}_v"), e.vis);
    put(r, &format!("{arm}_n"), e.named_vis);
    put(r, &format!("{arm}_a"), e.all);
    if with_cls {
        for (i, c) in CLASSES.iter().enumerate() {
            put(r, &format!("{arm}_c_{}", cls_name(*c)), e.cls[i]);
        }
    }
}

fn na_ev(r: &mut Row, arm: &str, with_cls: bool) {
    for s in ["v", "n", "a"] {
        put(r, &format!("{arm}_{s}"), "NA");
    }
    if with_cls {
        for c in CLASSES {
            put(r, &format!("{arm}_c_{}", cls_name(c)), "NA");
        }
    }
}

struct Cfg {
    nmin: usize,
    reduced: bool,
    skiplib: bool,
    nmax: usize,
    mem: u128,
    count_mem: u128,
}

fn analyze(ds: &str, dir: &Path, cfg: &Cfg) -> Result<Row, String> {
    let name = dir.file_name().unwrap().to_string_lossy().to_string();
    let (Some(bp), Some(ap)) = (find(dir, "before."), find(dir, "after.")) else {
        return Err("no before/after pair".into());
    };
    let ext = bp
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .split('.')
        .nth(1)
        .unwrap_or("")
        .to_string();
    let Some((lname, l)) = lang(&ext) else {
        return Err(format!("language not parsed here: .{ext}"));
    };
    let (bs, as_) = (std::fs::read(&bp).unwrap(), std::fs::read(&ap).unwrap());
    let mut parser = Parser::new();
    parser.set_language(&l).unwrap();
    let (tb, ta) = (
        parser.parse(&bs, None).ok_or("parse failed")?,
        parser.parse(&as_, None).ok_or("parse failed")?,
    );
    let mut arena = Arena::new();
    let mut it = Interner::default();
    let (mut bt, mut at) = (Tree::default(), Tree::default());
    let x = convert(tb.root_node(), &bs, &mut arena, &mut it, &mut bt, NIL);
    let y = convert(ta.root_node(), &as_, &mut arena, &mut it, &mut at, NIL);
    let (nb, na) = (bt.kind.len(), at.kind.len());
    let json: Value = serde_json::from_str(
        &std::fs::read_to_string(dir.join("human_mapping.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| format!("human_mapping.json: {e}"))?;
    let gt = load_gt(&json, &bt, &at).map_err(|e| format!("ground truth: {e}"))?;
    if gt.pairs.is_empty() && gt.groups.is_empty() {
        return Err("ground truth has no pairs".into());
    }
    let cl = classify(&gt, &bt, &at);
    let mut r: Row = Vec::new();
    put(&mut r, "dataset", ds);
    put(&mut r, "fixture", &name);
    put(&mut r, "lang", lname);
    put(&mut r, "nb", nb);
    put(&mut r, "na", na);
    put(&mut r, "rewrite", u8::from(cl.rewrite));
    put(&mut r, "n_move", cl.n_move);
    put(&mut r, "n_wrap", cl.n_wrap);
    put(&mut r, "n_reorder", cl.n_reorder);
    for c in CLASSES {
        put(
            &mut r,
            &format!("has_{}", cls_name(c)),
            u8::from(cl.present[cls_ix(c)]),
        );
    }
    put(&mut r, "gt_pairs", gt.pairs.len());
    put(&mut r, "gt_del", gt.del.len());
    put(&mut r, "gt_ins", gt.ins.len());
    put(&mut r, "gt_groups", gt.groups.len());
    // Top-down baseline.
    let res = diff_checked(&mut arena, x, y);
    let corr = correspondence(&arena, x, y, &res.edit);
    let td: Vec<(u32, u32)> = corr.pairs.iter().map(|p| (p.before, p.after)).collect();
    put_ev(&mut r, "topdown", &eval(&gt, &cl, &bt, &at, &td), false);
    let big = nb.max(na) > 20_000;
    // Library TED mappings (kinds on), with the published post-processing steps.
    if cfg.skiplib {
        for arm in ["L_kinds", "L_D", "L_E"] {
            na_ev(&mut r, arm, arm == "L_E");
        }
    } else {
        let lib_kinds = if big {
            td.clone()
        } else {
            ted_pairs(&bt, &at, true, false, false)
        };
        put_ev(
            &mut r,
            "L_kinds",
            &eval(&gt, &cl, &bt, &at, &lib_kinds),
            false,
        );

        if std::env::var("MECH_DUMP").is_ok() {
            // Show the first decisions the plain optimal mapping gets wrong.
            let mut m_b2a: HashMap<u32, u32> = HashMap::new();
            for &(b, a) in &lib_kinds {
                m_b2a.insert(b, a);
            }
            let snip = |src: &[u8], rng: (usize, usize)| -> String {
                String::from_utf8_lossy(&src[rng.0..rng.1.min(rng.0 + 40)]).replace('\n', " ")
            };
            let mut shown = 0;
            for &(b, a, _) in &gt.pairs {
                if m_b2a.get(&b) != Some(&a) && bt.vis[b as usize] && shown < 25 {
                    shown += 1;
                    let got = m_b2a.get(&b).map(|&g| {
                        format!("{}:{}", at.kind[g as usize], snip(&as_, at.rng[g as usize]))
                    });
                    eprintln!(
                        "GT-PAIR {}:{} -> {}:{} | tool: {:?}",
                        bt.kind[b as usize],
                        snip(&bs, bt.rng[b as usize]),
                        at.kind[a as usize],
                        snip(&as_, at.rng[a as usize]),
                        got
                    );
                }
            }
            for &b in &gt.del {
                if m_b2a.contains_key(&b) && bt.vis[b as usize] && shown < 50 {
                    shown += 1;
                    let g = m_b2a[&b];
                    eprintln!(
                        "GT-DEL {}:{} | tool maps to {}:{}",
                        bt.kind[b as usize],
                        snip(&bs, bt.rng[b as usize]),
                        at.kind[g as usize],
                        snip(&as_, at.rng[g as usize])
                    );
                }
            }
        }
        let mut lib_d = lib_kinds.clone();
        if !big {
            recover_moves(&bt, &at, &mut lib_d);
        }
        put_ev(&mut r, "L_D", &eval(&gt, &cl, &bt, &at, &lib_d), false);
        let mut lib_e = lib_kinds.clone();
        if !big {
            drop_orphan_updates(&bt, &at, &mut lib_e);
            recover_moves(&bt, &at, &mut lib_e);
        }
        put_ev(&mut r, "L_E", &eval(&gt, &cl, &bt, &at, &lib_e), true);
    }
    put(&mut r, "lib_fallback", u8::from(big));

    let engine = nb.max(na) <= cfg.nmax && nb.max(na) > cfg.nmin;
    put(&mut r, "engine", u8::from(engine));
    // Arms list (fixed so every row has the same columns).
    let mut arms: Vec<(Prim, Tie)> = vec![(Prim::Kinds, Tie::None), (Prim::Kinds, Tie::Oracle)];
    let reduced = cfg.reduced;
    for t in [
        Tie::Parent,
        Tie::Path2,
        Tie::PathFull,
        Tie::Sib,
        Tie::ParentSib,
        Tie::Depth,
    ] {
        arms.push((Prim::Kinds, t));
    }
    for p in [
        Prim::Unit,
        Prim::NoRel,
        Prim::IntCheap,
        Prim::IntExp,
        Prim::AnonCheap,
        Prim::CtxP1,
        Prim::CtxP2,
        Prim::CtxPath1,
        Prim::CtxPath2,
    ] {
        arms.push((p, Tie::None));
        arms.push((p, Tie::Oracle));
    }
    if let Ok(list) = std::env::var("MECH_ARMS") {
        arms = list
            .split(',')
            .map(|n| {
                let (pn, tn) = n.split_once(':').unwrap_or(("kinds", n));
                let prim = match pn {
                    "kinds" => Prim::Kinds,
                    "fam" => Prim::Fam,
                    other => panic!("unknown prim {other}"),
                };
                let tie = match tn {
                    "neigh" => Tie::Neigh,
                    "neighpath" => Tie::NeighPath,
                    "oraclestrict" => Tie::OracleStrict,
                    "oracle" => Tie::Oracle,
                    "none" => Tie::None,
                    "path" => Tie::PathFull,
                    "depth" => Tie::Depth,
                    other => panic!("unknown arm {other}"),
                };
                (prim, tie)
            })
            .collect();
    } else if reduced {
        arms = vec![
            (Prim::Kinds, Tie::None),
            (Prim::Kinds, Tie::Oracle),
            (Prim::Kinds, Tie::PathFull),
            (Prim::Kinds, Tie::Depth),
            (Prim::NoRel, Tie::Oracle),
            (Prim::CtxP2, Tie::Oracle),
        ];
    }
    let arm_name = |p: Prim, t: Tie| format!("e_{}_{}", p.name(), t.name());
    if !engine || big {
        for &(p, t) in &arms {
            let an = arm_name(p, t);
            na_ev(
                &mut r,
                &an,
                p == Prim::Kinds && matches!(t, Tie::None | Tie::Oracle),
            );
            if p == Prim::Kinds {
                na_ev(&mut r, &format!("{an}_mv"), false);
            }
            put(&mut r, &format!("{an}_prim"), "NA");
            put(&mut r, &format!("{an}_sec"), "NA");
        }
        for k in [
            "gt_legal",
            "gt_keep",
            "gt_drop",
            "gt_cost",
            "copt",
            "log10_nopt",
            "free_b",
            "free_a",
            "nopt_exact",
        ] {
            put(&mut r, k, "NA");
        }
        return Ok(r);
    }

    // Postorder forms.
    let mut kind_ids: HashMap<&'static str, u32> = HashMap::new();
    let (sa, pa) = build_side(&bt, &mut kind_ids, true);
    let (sb, pb) = build_side(&at, &mut kind_ids, true);
    // GT in postorder.
    let (n, m) = (nb, na);
    let mut sec = Sec {
        partner_b: vec![0; n],
        partner_a: vec![0; m],
        del_b: vec![false; n],
        ins_a: vec![false; m],
        grp_b: vec![u32::MAX; n],
        grp_a: vec![u32::MAX; m],
        grp_all_b: vec![false; n],
        wb: sa
            .order
            .iter()
            .map(|&v| if bt.vis[v as usize] { W_VIS } else { 1 })
            .collect(),
        wa: sb
            .order
            .iter()
            .map(|&v| if at.vis[v as usize] { W_VIS } else { 1 })
            .collect(),
        free_b: vec![true; n],
        free_a: vec![true; m],
    };
    let mut gpairs: Vec<(u32, u32)> = Vec::new();
    for &(b, a, _) in &gt.pairs {
        let (x, y) = (pa[b as usize] as usize, pb[a as usize] as usize);
        sec.partner_b[x] = y as u32 + 1;
        sec.partner_a[y] = x as u32 + 1;
        sec.free_b[x] = false;
        sec.free_a[y] = false;
        gpairs.push((x as u32 + 1, y as u32 + 1));
    }
    for &b in &gt.del {
        let x = pa[b as usize] as usize;
        sec.del_b[x] = true;
        sec.free_b[x] = false;
    }
    for &a in &gt.ins {
        let y = pb[a as usize] as usize;
        sec.ins_a[y] = true;
        sec.free_a[y] = false;
    }
    for (gi, g) in gt.groups.iter().enumerate() {
        for &b in &g.before {
            let x = pa[b as usize] as usize;
            sec.grp_b[x] = gi as u32;
            sec.grp_all_b[x] = g.all_to_all;
            sec.free_b[x] = false;
        }
        for &a in &g.after {
            let y = pb[a as usize] as usize;
            sec.grp_a[y] = gi as u32;
            sec.free_a[y] = false;
        }
    }
    gpairs.sort_unstable();
    put(&mut r, "free_b", sec.free_b.iter().filter(|&&f| f).count());
    put(&mut r, "free_a", sec.free_a.iter().filter(|&&f| f).count());

    // Library distance with kinds (cap for every kinds-based arm).
    let copt = u64::from(ted(&sa.pt, &sb.pt));
    put(&mut r, "copt", copt);

    // Ground truth realisable as a tree edit mapping?
    let mut sorted_pairs = gpairs.clone();
    sorted_pairs.sort_unstable();
    let legal = check_mapping(&sa.pt, &sb.pt, &sorted_pairs).is_ok();
    put(&mut r, "gt_legal", u8::from(legal));
    let p1 = Params { k: K, m0: 1 };
    let cap_max = (n + m) as u64;
    {
        let fc = Forced {
            a: &sa,
            b: &sb,
            sec: &sec,
            max_subset: true,
        };
        let p0 = Params { k: 1, m0: 1 };
        let free_cnt =
            sec.free_b.iter().filter(|&&f| f).count() + sec.free_a.iter().filter(|&&f| f).count();
        let _ = p0;
        let fcp = Params { k: K, m0: 1 };
        // value = (unmatched nodes) * K; unmatched nodes = n + m - 2 * kept.
        let c0 = (copt).max((free_cnt + gt.del.len() + gt.ins.len()) as u64);
        match solve_auto(&sa.pt, &sb.pt, &fc, fcp, c0, cap_max, cfg.mem, false) {
            Ok((s, _)) => {
                let unmatched = s.value / K;
                let kept = (n as u64 + m as u64 - unmatched) / 2;
                put(&mut r, "gt_keep", kept);
                put(
                    &mut r,
                    "gt_drop",
                    gt.pairs.len() as u64 - kept.min(gt.pairs.len() as u64),
                );
            }
            Err(e) => {
                put(&mut r, "gt_keep", format!("NA({e})"));
                put(&mut r, "gt_drop", "NA");
            }
        }
        if legal {
            let fc = Forced {
                a: &sa,
                b: &sb,
                sec: &sec,
                max_subset: false,
            };
            match solve_auto(&sa.pt, &sb.pt, &fc, p1, copt, copt * 4 + 64, cfg.mem, false) {
                Ok((s, _)) => put(&mut r, "gt_cost", s.value / K),
                Err(e) => put(&mut r, "gt_cost", format!("NA({e})")),
            }
        } else {
            put(&mut r, "gt_cost", "NA");
        }
    }

    // Engine arms.
    let mut oracle_map: Option<Vec<(u32, u32)>> = None;
    for &(p, t) in &arms {
        let an = arm_name(p, t);
        let model = Model {
            a: &sa,
            b: &sb,
            prim: p,
            tie: t,
            drop_dominated: t != Tie::Oracle,
            sec: &sec,
            w: &[],
        };
        let prm = Params { k: K, m0: p.m0() };
        let cap0 = copt * p.m0();
        let with_cls = p == Prim::Kinds && matches!(t, Tie::None | Tie::Oracle);
        let t0 = std::time::Instant::now();
        let res = solve_auto(
            &sa.pt,
            &sb.pt,
            &model,
            prm,
            cap0,
            cap_max * 3,
            cfg.mem,
            false,
        );
        if std::env::var("MECH_TIMING").is_ok() {
            eprintln!("{name} {an} {:?} n={n} m={m} copt={copt}", t0.elapsed());
        }
        match res {
            Ok((s, _cap)) => {
                let mp = s.mapping(&sa.pt, &sb.pt, &model, true);
                let pre = to_pre(&sa, &sb, &mp);
                put_ev(&mut r, &an, &eval(&gt, &cl, &bt, &at, &pre), with_cls);
                put(&mut r, &format!("{an}_prim"), s.value / K);
                put(&mut r, &format!("{an}_sec"), s.value % K);
                if p == Prim::Kinds {
                    let mut pm = pre.clone();
                    recover_moves(&bt, &at, &mut pm);
                    put_ev(
                        &mut r,
                        &format!("{an}_mv"),
                        &eval(&gt, &cl, &bt, &at, &pm),
                        false,
                    );
                }
                if p == Prim::Kinds && t == Tie::Oracle {
                    oracle_map = Some(pre);
                }
            }
            Err(e) => {
                na_ev(&mut r, &an, with_cls);
                if p == Prim::Kinds {
                    na_ev(&mut r, &format!("{an}_mv"), false);
                }
                put(&mut r, &format!("{an}_prim"), format!("NA({e})"));
                put(&mut r, &format!("{an}_sec"), "NA");
            }
        }
    }
    let _ = oracle_map;

    // Count the optimal mappings (kinds model, dominated pairs allowed).
    let model = Model {
        a: &sa,
        b: &sb,
        prim: Prim::Kinds,
        tie: Tie::None,
        drop_dominated: false,
        sec: &sec,
        w: &[],
    };
    if wted::bytes_needed(n, m, copt, p1, true) <= cfg.count_mem {
        match solve_auto(&sa.pt, &sb.pt, &model, p1, copt, copt, cfg.count_mem, true) {
            Ok((s, _)) => {
                put(&mut r, "log10_nopt", s.count.max(1.0).log10());
                put(
                    &mut r,
                    "nopt_exact",
                    if s.count < 9.0e15 {
                        s.count.to_string()
                    } else {
                        "big".to_string()
                    },
                );
            }
            Err(e) => {
                put(&mut r, "log10_nopt", format!("NA({e})"));
                put(&mut r, "nopt_exact", "NA");
            }
        }
    } else {
        put(&mut r, "log10_nopt", "NA(mem)");
        put(&mut r, "nopt_exact", "NA");
    }
    Ok(r)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("learn") {
        learn_main(&args[2..]);
        return;
    }
    if args.len() < 3 {
        eprintln!("usage: mechanics <diffs-dir> <out.csv> [nmax] [threads] [only-substring]");
        std::process::exit(2);
    }
    let root = PathBuf::from(&args[1]);
    let nmax: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(3000);
    let threads: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(3);
    let only = args.get(5).cloned();
    let mut dirs: Vec<(String, PathBuf)> = Vec::new();
    for ds in ["defects4j", "full", "handmade", "small", "stratified"] {
        let Ok(rd) = std::fs::read_dir(root.join(ds)) else {
            continue;
        };
        let mut v: Vec<PathBuf> = rd
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.is_dir() && p.join("human_mapping.json").exists())
            .collect();
        v.sort();
        for p in v {
            if only
                .as_ref()
                .is_none_or(|o| p.to_string_lossy().contains(o.as_str()))
            {
                dirs.push((ds.to_string(), p));
            }
        }
    }
    let nmin: usize = std::env::var("MECH_NMIN")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let cfg = Cfg {
        nmin,
        reduced: std::env::var("MECH_REDUCED").is_ok(),
        skiplib: std::env::var("MECH_SKIPLIB").is_ok(),
        nmax,
        mem: 3_000_000_000,
        count_mem: 1_000_000_000,
    };
    let next = AtomicUsize::new(0);
    let rows: Mutex<Vec<(usize, Row)>> = Mutex::new(Vec::new());
    let skipped: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= dirs.len() {
                    break;
                }
                let (ds, p) = &dirs[i];
                match analyze(ds, p, &cfg) {
                    Ok(r) => rows.lock().unwrap().push((i, r)),
                    Err(e) => skipped.lock().unwrap().push((p.display().to_string(), e)),
                }
                if i % 50 == 0 {
                    eprintln!("progress {i}/{}", dirs.len());
                }
            });
        }
    });
    let mut rows = rows.into_inner().unwrap();
    rows.sort_by_key(|r| r.0);
    // Header: keys in order of first appearance across rows, so a row that skipped the engine still lines up.
    let mut header: Vec<String> = Vec::new();
    for (_, r) in &rows {
        for (k, _) in r {
            if !header.contains(k) {
                header.push(k.clone());
            }
        }
    }
    let mut out = header.join(",");
    out.push('\n');
    for (_, r) in &rows {
        let line: Vec<String> = header
            .iter()
            .map(|h| {
                r.iter()
                    .find(|(k, _)| k == h)
                    .map_or("NA".to_string(), |(_, v)| v.replace(',', ";"))
            })
            .collect();
        out.push_str(&line.join(","));
        out.push('\n');
    }
    std::fs::write(&args[2], out).unwrap();
    eprintln!(
        "rows {} skipped {}",
        rows.len(),
        skipped.lock().unwrap().len()
    );
}

// ================================================================ learned tie-break

struct Prep {
    name: String,
    bt: Tree,
    at: Tree,
    gt: Gt,
    cl: Classes,
    sa: Side,
    sb: Side,
    sec: Sec,
    copt: u64,
    oracle_v: u32,
    target_phi: [i64; NF],
}

fn build_sec(gt: &Gt, bt: &Tree, at: &Tree, sa: &Side, sb: &Side, pa: &[u32], pb: &[u32]) -> Sec {
    let (n, m) = (bt.kind.len(), at.kind.len());
    let mut sec = Sec {
        partner_b: vec![0; n],
        partner_a: vec![0; m],
        del_b: vec![false; n],
        ins_a: vec![false; m],
        grp_b: vec![u32::MAX; n],
        grp_a: vec![u32::MAX; m],
        grp_all_b: vec![false; n],
        wb: sa
            .order
            .iter()
            .map(|&v| if bt.vis[v as usize] { W_VIS } else { 1 })
            .collect(),
        wa: sb
            .order
            .iter()
            .map(|&v| if at.vis[v as usize] { W_VIS } else { 1 })
            .collect(),
        free_b: vec![true; n],
        free_a: vec![true; m],
    };
    for &(b, a, _) in &gt.pairs {
        let (x, y) = (pa[b as usize] as usize, pb[a as usize] as usize);
        sec.partner_b[x] = y as u32 + 1;
        sec.partner_a[y] = x as u32 + 1;
        sec.free_b[x] = false;
        sec.free_a[y] = false;
    }
    for &b in &gt.del {
        let x = pa[b as usize] as usize;
        sec.del_b[x] = true;
        sec.free_b[x] = false;
    }
    for &a in &gt.ins {
        let y = pb[a as usize] as usize;
        sec.ins_a[y] = true;
        sec.free_a[y] = false;
    }
    for (gi, g) in gt.groups.iter().enumerate() {
        for &b in &g.before {
            let x = pa[b as usize] as usize;
            sec.grp_b[x] = gi as u32;
            sec.grp_all_b[x] = g.all_to_all;
            sec.free_b[x] = false;
        }
        for &a in &g.after {
            let y = pb[a as usize] as usize;
            sec.grp_a[y] = gi as u32;
            sec.free_a[y] = false;
        }
    }
    sec
}

fn phi(sa: &Side, sb: &Side, post_pairs: &[(u32, u32)]) -> [i64; NF] {
    let mut t = [0i64; NF];
    for &(x, y) in post_pairs {
        for (i, f) in feat(sa, sb, x as usize - 1, y as usize - 1)
            .iter()
            .enumerate()
        {
            t[i] += i64::from(*f);
        }
    }
    t
}

fn prepare(ds: &str, dir: &Path, nmax: usize, mem: u128) -> Result<Prep, String> {
    let name = format!("{ds}/{}", dir.file_name().unwrap().to_string_lossy());
    let (Some(bp), Some(ap)) = (find(dir, "before."), find(dir, "after.")) else {
        return Err("no pair".into());
    };
    let ext = bp
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .split('.')
        .nth(1)
        .unwrap_or("")
        .to_string();
    let Some((_, l)) = lang(&ext) else {
        return Err("lang".into());
    };
    let (bs, as_) = (std::fs::read(&bp).unwrap(), std::fs::read(&ap).unwrap());
    let mut parser = Parser::new();
    parser.set_language(&l).unwrap();
    let (tb, ta) = (
        parser.parse(&bs, None).ok_or("parse")?,
        parser.parse(&as_, None).ok_or("parse")?,
    );
    let mut arena = Arena::new();
    let mut it = Interner::default();
    let (mut bt, mut at) = (Tree::default(), Tree::default());
    convert(tb.root_node(), &bs, &mut arena, &mut it, &mut bt, NIL);
    convert(ta.root_node(), &as_, &mut arena, &mut it, &mut at, NIL);
    if bt.kind.len().max(at.kind.len()) > nmax {
        return Err("too big".into());
    }
    let json: Value = serde_json::from_str(
        &std::fs::read_to_string(dir.join("human_mapping.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let gt = load_gt(&json, &bt, &at)?;
    if gt.pairs.is_empty() && gt.groups.is_empty() {
        return Err("no gt".into());
    }
    let cl = classify(&gt, &bt, &at);
    let mut kind_ids: HashMap<&'static str, u32> = HashMap::new();
    let (sa, pa) = build_side(&bt, &mut kind_ids, true);
    let (sb, pb) = build_side(&at, &mut kind_ids, true);
    let sec = build_sec(&gt, &bt, &at, &sa, &sb, &pa, &pb);
    let copt = u64::from(ted(&sa.pt, &sb.pt));
    let model = Model {
        a: &sa,
        b: &sb,
        prim: Prim::Kinds,
        tie: Tie::Oracle,
        drop_dominated: false,
        sec: &sec,
        w: &[],
    };
    let (sol, _) = solve_auto(
        &sa.pt,
        &sb.pt,
        &model,
        Params { k: K, m0: 1 },
        copt,
        copt * 3 + 8,
        mem,
        false,
    )?;
    let mp = sol.mapping(&sa.pt, &sb.pt, &model, true);
    let oracle_v = eval(&gt, &cl, &bt, &at, &to_pre(&sa, &sb, &mp)).vis;
    // The training target only uses pairs the library traceback could emit.
    let strict = Model {
        drop_dominated: true,
        tie: Tie::OracleStrict,
        ..model
    };
    let (sol2, _) = solve_auto(
        &sa.pt,
        &sb.pt,
        &strict,
        Params { k: K, m0: 1 },
        copt,
        copt * 3 + 8,
        mem,
        false,
    )?;
    let mp2 = sol2.mapping(&sa.pt, &sb.pt, &strict, true);
    let ov2 = eval(&gt, &cl, &bt, &at, &to_pre(&sa, &sb, &mp2)).vis;
    let target_phi = phi(&sa, &sb, &mp2);
    let _ = ov2;
    Ok(Prep {
        name,
        bt,
        at,
        gt,
        cl,
        sa,
        sb,
        sec,
        copt,
        oracle_v,
        target_phi,
    })
}

/// Solve with learned weights and return (visible fails, phi of the mapping, visible fails after move recovery).
fn run_learned(p: &Prep, w: &[u64], mem: u128) -> Option<(u32, [i64; NF], u32)> {
    let model = Model {
        a: &p.sa,
        b: &p.sb,
        prim: Prim::Kinds,
        tie: Tie::Learned,
        drop_dominated: true,
        sec: &p.sec,
        w,
    };
    let (sol, _) = solve_auto(
        &p.sa.pt,
        &p.sb.pt,
        &model,
        Params { k: K, m0: 1 },
        p.copt,
        p.copt * 3 + 8,
        mem,
        false,
    )
    .ok()?;
    let mp = sol.mapping(&p.sa.pt, &p.sb.pt, &model, true);
    let pre = to_pre(&p.sa, &p.sb, &mp);
    let v = eval(&p.gt, &p.cl, &p.bt, &p.at, &pre).vis;
    let mut pm = pre;
    recover_moves(&p.bt, &p.at, &mut pm);
    let vm = eval(&p.gt, &p.cl, &p.bt, &p.at, &pm).vis;
    Some((v, phi(&p.sa, &p.sb, &mp), vm))
}

fn par_map<T: Sync, R: Send>(items: &[T], threads: usize, f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let out: Mutex<Vec<(usize, R)>> = Mutex::new(Vec::new());
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= items.len() {
                    break;
                }
                let r = f(&items[i]);
                out.lock().unwrap().push((i, r));
            });
        }
    });
    let mut v = out.into_inner().unwrap();
    v.sort_by_key(|x| x.0);
    v.into_iter().map(|x| x.1).collect()
}

fn learn_main(args: &[String]) {
    let root = PathBuf::from(&args[0]);
    let nmax: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2500);
    let threads: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(3);
    let epochs: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(10);
    let mem: u128 = 2_000_000_000;
    let mut dirs: Vec<(String, PathBuf)> = Vec::new();
    for ds in ["defects4j", "full", "handmade", "small", "stratified"] {
        let Ok(rd) = std::fs::read_dir(root.join(ds)) else {
            continue;
        };
        let mut v: Vec<PathBuf> = rd
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.is_dir() && p.join("human_mapping.json").exists())
            .collect();
        v.sort();
        for p in v {
            dirs.push((ds.to_string(), p));
        }
    }
    let preps: Vec<Option<Prep>> =
        par_map(&dirs, threads, |(ds, p)| prepare(ds, p, nmax, mem).ok());
    let preps: Vec<Prep> = preps.into_iter().flatten().collect();
    eprintln!("prepared {} fixtures", preps.len());
    let tie_ok = preps.iter().filter(|p| p.oracle_v == 0).count();
    eprintln!("oracle-perfect (tie-fixable or already right): {tie_ok}");
    // Baseline with all-zero weights.
    let zero = vec![0u64; NF];
    let base: Vec<Option<(u32, [i64; NF], u32)>> =
        par_map(&preps, threads, |p| run_learned(p, &zero, mem));
    let base_perfect = base.iter().filter(|r| r.is_some_and(|x| x.0 == 0)).count();
    println!("w=0 perfect {base_perfect}/{}", preps.len());
    let mut report = String::new();
    let mut total_test = (0usize, 0usize, 0usize, 0usize);
    for fold in 0..2usize {
        let train: Vec<usize> = (0..preps.len())
            .filter(|i| i % 2 == fold && preps[*i].oracle_v == 0)
            .collect();
        let test: Vec<usize> = (0..preps.len()).filter(|i| i % 2 != fold).collect();
        // Perceptron with real weights (resolution 1/4 of a cost unit), a decaying step, and the best
        // epoch on the training half kept.
        let mut wr = vec![0f64; NF];
        let to_int = |wr: &[f64]| -> Vec<u64> {
            wr.iter()
                .map(|&x| (x * 4.0).round().max(0.0) as u64)
                .collect()
        };
        let mut best: (usize, Vec<u64>) = (0, vec![0u64; NF]);
        for ep in 0..epochs {
            let w = to_int(&wr);
            let res: Vec<Option<(u32, [i64; NF], u32)>> =
                par_map(&train, threads, |&i| run_learned(&preps[i], &w, mem));
            let mut sum = [0i64; NF];
            let mut ok = 0;
            let mut changed = 0;
            for (k, r) in res.iter().enumerate() {
                if let Some((v, ph, _)) = r {
                    ok += usize::from(*v == 0);
                    let mut any = false;
                    for j in 0..NF {
                        let d = ph[j] - preps[train[k]].target_phi[j];
                        sum[j] += d;
                        any |= d != 0;
                    }
                    changed += usize::from(any);
                }
            }
            eprintln!(
                "fold {fold} epoch {ep} train perfect {ok}/{} w={w:?} sumdiff={sum:?}",
                train.len()
            );
            if ok > best.0 {
                best = (ok, w.clone());
            }
            if changed == 0 {
                break;
            }
            let eta = 1.0 / (1.0 + ep as f64 / 2.0);
            for j in 0..NF {
                wr[j] = (wr[j] + eta * sum[j] as f64 / changed as f64).max(0.0);
            }
        }
        let w = best.1.clone();
        let res: Vec<Option<(u32, [i64; NF], u32)>> =
            par_map(&test, threads, |&i| run_learned(&preps[i], &w, mem));
        if std::env::var("MECH_VERBOSE").is_ok() {
            for (k, &i) in test.iter().enumerate() {
                println!(
                    "{} baseline {:?} learned {:?}",
                    preps[i].name,
                    base[i].map(|x| x.0),
                    res[k].map(|x| x.0)
                );
            }
        }
        let perf = res.iter().filter(|r| r.is_some_and(|x| x.0 == 0)).count();
        let perf_mv = res.iter().filter(|r| r.is_some_and(|x| x.2 == 0)).count();
        let base_perf = test
            .iter()
            .filter(|&&i| base[i].is_some_and(|x| x.0 == 0))
            .count();
        let base_perf_mv = test
            .iter()
            .filter(|&&i| base[i].is_some_and(|x| x.2 == 0))
            .count();
        let line = format!("fold {fold}: trained on {} (odd/even split), test {} fixtures: baseline perfect {base_perf} (+moves {base_perf_mv}), learned perfect {perf} (+moves {perf_mv}), weights {w:?}\n", train.len(), test.len());
        print!("{line}");
        report.push_str(&line);
        total_test.0 += test.len();
        total_test.1 += base_perf;
        total_test.2 += perf;
        total_test.3 += perf_mv;
    }
    println!(
        "two-fold cross-validated: {} fixtures, baseline {} ({:.1}%), learned {} ({:.1}%), learned+moves {} ({:.1}%)",
        total_test.0,
        total_test.1,
        100.0 * total_test.1 as f64 / total_test.0 as f64,
        total_test.2,
        100.0 * total_test.2 as f64 / total_test.0 as f64,
        total_test.3,
        100.0 * total_test.3 as f64 / total_test.0 as f64
    );
}
