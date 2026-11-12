//! Scores correspondence accuracy of difffold and OmniDiff against OmniDiff's hand-authored
//! `human_mapping.json` ground truth.
//!
//! usage: score_accuracy <diffs-dir> <omni-dump-dir> <out-dir>
//!
//! `<omni-dump-dir>` is the output of `tools/omni_dump` (OmniDiff's node mapping per fixture).
//! See results/accuracy/SUMMARY.md for the metric definitions and the commands to reproduce.

use difffold::mapping::correspondence;
use difffold::{diff_checked, Arena};
use serde_json::Value;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use tree_sitter::Parser;

mod ted_pairs;

use difffold::ts::{convert, lang, Interner, Tree, NIL};
use ted_pairs::ted_pairs;

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
    /// Best number of ground-truth pairs a top-down ordered mapping can contain.
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
    fail: bool,
    /// Before and after node of the decision, `NIL` when absent (debug output only).
    b: u32,
    a: u32,
}

fn evaluate(gt: &Gt, cl: &Classes, bt: &Tree, at: &Tree, tool: &Tool) -> Vec<Dec> {
    let mut out = Vec::new();
    for (i, &(b, a, _)) in gt.pairs.iter().enumerate() {
        out.push(Dec {
            cls: cl.pair[i],
            vis: bt.vis[b as usize],
            fail: tool.b2a[b as usize] != [a],
            b,
            a,
        });
    }
    for (i, &b) in gt.del.iter().enumerate() {
        out.push(Dec {
            cls: cl.del[i],
            vis: bt.vis[b as usize],
            fail: !tool.b2a[b as usize].is_empty(),
            b,
            a: NIL,
        });
    }
    for (i, &a) in gt.ins.iter().enumerate() {
        out.push(Dec {
            cls: cl.ins[i],
            vis: at.vis[a as usize],
            fail: !tool.a2b[a as usize].is_empty(),
            b: NIL,
            a,
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
                fail: !(ok_leftover || ok_match),
                b,
                a: NIL,
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
                fail: !(ok_leftover || ok_match),
                b: NIL,
                a,
            });
        }
        if !g.all_to_all {
            let first = g.before.first().is_none_or(|&b| bt.vis[b as usize]);
            out.push(Dec {
                cls: rep,
                vis: first,
                fail: matched != g.before.len().min(g.after.len()),
                b: NIL,
                a: NIL,
            });
        }
    }
    if cl.rewrite {
        out.iter_mut().for_each(|d| d.cls = Cls::Rewrite);
    }
    out
}

#[derive(Default, Clone)]
struct Prf {
    tp: u64,
    fp: u64,
    fn_: u64,
}

impl Prf {
    fn p(&self) -> f64 {
        if self.tp + self.fp == 0 {
            1.0
        } else {
            self.tp as f64 / (self.tp + self.fp) as f64
        }
    }
    fn r(&self) -> f64 {
        if self.tp + self.fn_ == 0 {
            1.0
        } else {
            self.tp as f64 / (self.tp + self.fn_) as f64
        }
    }
    fn f1(&self) -> f64 {
        let (p, r) = (self.p(), self.r());
        if p + r == 0.0 {
            0.0
        } else {
            2.0 * p * r / (p + r)
        }
    }
    fn add(&mut self, o: &Prf) {
        self.tp += o.tp;
        self.fp += o.fp;
        self.fn_ += o.fn_;
    }
}

/// Pair-level precision and recall of the tool's pairs against the ground truth's pairs.
fn pair_prf(gt: &Gt, bt: &Tree, at: &Tree, tool: &Tool) -> Prf {
    let (nb, na) = (bt.kind.len(), at.kind.len());
    let mut g_b2a = vec![NIL; nb];
    let mut gb = vec![false; nb];
    let mut ga = vec![false; na];
    for &(b, a, _) in &gt.pairs {
        g_b2a[b as usize] = a;
        gb[b as usize] = true;
        ga[a as usize] = true;
    }
    gt.del.iter().for_each(|&b| gb[b as usize] = true);
    gt.ins.iter().for_each(|&a| ga[a as usize] = true);
    let mut grp_b = vec![false; nb];
    let mut grp_a = vec![false; na];
    for g in &gt.groups {
        g.before.iter().for_each(|&b| grp_b[b as usize] = true);
        g.after.iter().for_each(|&a| grp_a[a as usize] = true);
    }
    let mut p = Prf::default();
    for &(b, a, _) in &gt.pairs {
        if tool.b2a[b as usize].contains(&a) {
            p.tp += 1;
        } else {
            p.fn_ += 1;
        }
    }
    for b in 0..nb {
        for &a in &tool.b2a[b] {
            if grp_b[b] || grp_a[a as usize] || !(gb[b] || ga[a as usize]) {
                continue;
            }
            if g_b2a[b] != a {
                p.fp += 1;
            }
        }
    }
    p
}

/// Changed-span view. A token is a leaf that is not whitespace, a comment, or punctuation (an
/// anonymous node without letters or digits). Parent nodes never count. A token is changed when
/// it is unmatched or no partner has the same label (kind and text). Moved identical tokens are
/// therefore unchanged. Only tokens that the ground truth grades are judged.
fn span_prf(gt: &Gt, bt: &Tree, at: &Tree, tool: &Tool) -> Prf {
    let (nb, na) = (bt.kind.len(), at.kind.len());
    let mut g_b2a = vec![NIL; nb];
    let mut g_a2b = vec![NIL; na];
    let mut gb = vec![false; nb];
    let mut ga = vec![false; na];
    for &(b, a, _) in &gt.pairs {
        g_b2a[b as usize] = a;
        g_a2b[a as usize] = b;
        gb[b as usize] = true;
        ga[a as usize] = true;
    }
    gt.del.iter().for_each(|&b| gb[b as usize] = true);
    gt.ins.iter().for_each(|&a| ga[a as usize] = true);
    for g in &gt.groups {
        g.before.iter().for_each(|&b| {
            let (lo, hi) = (b as usize, (b + bt.size[b as usize]) as usize);
            gb[lo..hi].iter_mut().for_each(|x| *x = false);
        });
        g.after.iter().for_each(|&a| {
            let (lo, hi) = (a as usize, (a + at.size[a as usize]) as usize);
            ga[lo..hi].iter_mut().for_each(|x| *x = false);
        });
    }
    let mut p = Prf::default();
    for b in 0..nb {
        if !gb[b] || !bt.token[b] {
            continue;
        }
        let truth = g_b2a[b] == NIL || at.label[g_b2a[b] as usize] != bt.label[b];
        let said = tool.b2a[b]
            .iter()
            .all(|&a| at.label[a as usize] != bt.label[b]);
        tally(&mut p, truth, said);
    }
    for a in 0..na {
        if !ga[a] || !at.token[a] {
            continue;
        }
        let truth = g_a2b[a] == NIL || bt.label[g_a2b[a] as usize] != at.label[a];
        let said = tool.a2b[a]
            .iter()
            .all(|&b| bt.label[b as usize] != at.label[a]);
        tally(&mut p, truth, said);
    }
    p
}

fn tally(p: &mut Prf, truth: bool, said: bool) {
    match (truth, said) {
        (true, true) => p.tp += 1,
        (false, true) => p.fp += 1,
        (true, false) => p.fn_ += 1,
        (false, false) => {}
    }
}

// ---------------------------------------------------------------- driver

struct Row {
    dataset: String,
    fixture: String,
    lang: &'static str,
    tool: &'static str,
    nb: usize,
    na: usize,
    decisions: usize,
    fails: usize,
    vis_fails: usize,
    vis_nodes: usize,
    pair: Prf,
    span: Prf,
    native: Option<(i64, i64)>,
}

impl Row {
    fn perfect(&self) -> bool {
        self.vis_fails == 0
    }
    fn strict(&self) -> bool {
        self.fails == 0
    }
    fn near(&self) -> bool {
        self.vis_nodes == 0 || (self.vis_fails as f64) / (self.vis_nodes as f64) <= 0.01
    }
    fn acc(&self) -> f64 {
        if self.decisions == 0 {
            1.0
        } else {
            1.0 - self.fails as f64 / self.decisions as f64
        }
    }
}

struct Fx {
    dataset: String,
    name: String,
    lang: &'static str,
    cl: Classes,
    n_gt_del: usize,
    n_gt_ins: usize,
    n_groups: usize,
    identical: usize,
    updates: usize,
    gt_pairs: usize,
    d: Row,
    o: Row,
    dd: Vec<Dec>,
    od: Vec<Dec>,
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

fn load_omni(path: &Path, nb: usize, na: usize) -> Result<(Tool, i64, i64), String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("omnidiff dump unreadable: {e}"))?;
    let mut lines = text.lines();
    let head: Vec<i64> = lines
        .next()
        .ok_or("empty dump")?
        .split(' ')
        .map(|x| x.parse().unwrap_or(-1))
        .collect();
    if head[0] as usize != nb || head[1] as usize != na {
        return Err(format!(
            "node count differs from OmniDiff's parse ({}/{} vs {}/{})",
            nb, na, head[0], head[1]
        ));
    }
    let pairs = lines.filter_map(|l| {
        let (b, a) = l.split_once(' ')?;
        Some((b.parse().ok()?, a.parse().ok()?))
    });
    Ok((Tool::from_pairs(nb, na, pairs), head[2], head[3]))
}

fn one(ds: &str, dir: &Path, dump: &Path) -> Result<Fx, String> {
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
    let solo = dump == Path::new("-");
    let dump_file = dump.join(format!("{ds}__{name}.map"));
    if !solo && !dump_file.exists() {
        let err =
            std::fs::read_to_string(dump.join(format!("{ds}__{name}.err"))).unwrap_or_default();
        return Err(format!("OmniDiff produced no mapping: {err}"));
    }
    let (omni, nvis, ntot) = if solo {
        (Tool::from_pairs(nb, na, std::iter::empty()), 0, 0)
    } else {
        load_omni(&dump_file, nb, na)?
    };
    let res = diff_checked(&mut arena, x, y);
    let corr = correspondence(&arena, x, y, &res.edit);
    assert_eq!(
        (corr.before_len as usize, corr.after_len as usize),
        (nb, na)
    );
    let mut refine_phase: Option<Vec<u8>> = None;
    let dtool = if let Ok(spec) = std::env::var("DFOLD_REFINE") {
        let mut opts = difffold::refine::Options::parse(&spec).expect("DFOLD_REFINE");
        if let Some(d) = std::env::var("DFOLD_DICE")
            .ok()
            .and_then(|v| v.parse().ok())
        {
            opts.dice = d;
        }
        if let Some(d) = std::env::var("DFOLD_KEEP")
            .ok()
            .and_then(|v| v.parse().ok())
        {
            opts.keep = d;
        }
        if let Some(d) = std::env::var("DFOLD_ANCHOR")
            .ok()
            .and_then(|v| v.parse().ok())
        {
            opts.anchor_below = d;
        }
        if let Some(d) = std::env::var("DFOLD_MINEXACT")
            .ok()
            .and_then(|v| v.parse().ok())
        {
            opts.min_exact = d;
        }
        let (bf, af) = (
            difffold::refine::Flat::from_arena(&arena, x, |l| it.kind_of(l)),
            difffold::refine::Flat::from_arena(&arena, y, |l| it.kind_of(l)),
        );
        let (m, rs) = difffold::refine::refine(&arena, &bf, &af, &corr, &opts);
        if std::env::var("DFOLD_DEBUG").is_ok_and(|k| name.contains(&k)) {
            eprintln!("REFINE {name} {rs:?}");
            refine_phase = Some(m.phase.clone());
        }
        Tool::from_pairs(nb, na, m.pairs())
    } else if std::env::var("DFOLD_TED").is_ok() && nb.max(na) <= 20_000 {
        Tool::from_pairs(nb, na, ted_pairs(&bt, &at).into_iter())
    } else {
        Tool::from_pairs(nb, na, corr.pairs.iter().map(|p| (p.before, p.after)))
    };
    let cl = classify(&gt, &bt, &at);
    if std::env::var("DFOLD_DEBUG").is_ok_and(|k| name.contains(&k)) {
        let dec = evaluate(&gt, &cl, &bt, &at, &dtool);
        let snip = |t: &Tree, src: &[u8], v: u32| -> String {
            if v == NIL {
                return "-".into();
            }
            let (s, e) = t.span[v as usize];
            let txt = String::from_utf8_lossy(&src[s as usize..e as usize]).replace('\n', " ");
            format!(
                "{}#{} {:?}",
                t.kind[v as usize],
                v,
                txt.chars().take(60).collect::<String>()
            )
        };
        for d in dec.iter().filter(|d| d.fail) {
            let got: Vec<String> = if d.b != NIL {
                dtool.b2a[d.b as usize]
                    .iter()
                    .map(|&x| snip(&at, &as_, x))
                    .collect()
            } else if d.a != NIL {
                dtool.a2b[d.a as usize]
                    .iter()
                    .map(|&x| snip(&bt, &bs, x))
                    .collect()
            } else {
                Vec::new()
            };
            eprintln!(
                "FAIL {}{} | {name} | B {} | A {} | tool {:?} phase {:?}",
                cls_name(d.cls),
                if d.vis { "" } else { " (invisible)" },
                snip(&bt, &bs, d.b),
                snip(&at, &as_, d.a),
                got,
                refine_phase
                    .as_ref()
                    .and_then(|p| (d.b != NIL).then(|| p[d.b as usize]))
            );
        }
    }
    let vis_nodes = bt.vis.iter().filter(|&&v| v).count() + at.vis.iter().filter(|&&v| v).count();
    let mk = |tool_name: &'static str, tool: &Tool, native: Option<(i64, i64)>| {
        let dec = evaluate(&gt, &cl, &bt, &at, tool);
        let row = Row {
            dataset: ds.to_string(),
            fixture: name.clone(),
            lang: lname,
            tool: tool_name,
            nb,
            na,
            decisions: dec.len(),
            fails: dec.iter().filter(|d| d.fail).count(),
            vis_fails: dec.iter().filter(|d| d.fail && d.vis).count(),
            vis_nodes,
            pair: pair_prf(&gt, &bt, &at, tool),
            span: span_prf(&gt, &bt, &at, tool),
            native,
        };
        (row, dec)
    };
    let (d, dd) = mk("difffold", &dtool, None);
    let (o, od) = mk("omnidiff", &omni, Some((nvis, ntot)));
    let identical = gt.pairs.iter().filter(|p| p.2 == Op::Identical).count();
    let updates = gt.pairs.iter().filter(|p| p.2 != Op::Identical).count();
    Ok(Fx {
        dataset: ds.to_string(),
        name,
        lang: lname,
        n_gt_del: gt.del.len(),
        n_gt_ins: gt.ins.len(),
        n_groups: gt.groups.len(),
        identical,
        updates,
        gt_pairs: gt.pairs.len(),
        cl,
        d,
        o,
        dd,
        od,
    })
}

#[derive(Default)]
struct Agg {
    n: usize,
    perfect: usize,
    strict: usize,
    near: usize,
    dec: usize,
    fails: usize,
    pair: Prf,
    span: Prf,
    macro_acc: f64,
    macro_pp: f64,
    macro_pr: f64,
    macro_pf: f64,
    macro_sp: f64,
    macro_sr: f64,
    macro_sf: f64,
}

impl Agg {
    fn add(&mut self, r: &Row) {
        self.n += 1;
        self.perfect += usize::from(r.perfect());
        self.strict += usize::from(r.strict());
        self.near += usize::from(r.near());
        self.dec += r.decisions;
        self.fails += r.fails;
        self.pair.add(&r.pair);
        self.span.add(&r.span);
        self.macro_acc += r.acc();
        self.macro_pp += r.pair.p();
        self.macro_pr += r.pair.r();
        self.macro_pf += r.pair.f1();
        self.macro_sp += r.span.p();
        self.macro_sr += r.span.r();
        self.macro_sf += r.span.f1();
    }
}

fn pct(a: usize, b: usize) -> String {
    if b == 0 {
        "n/a".into()
    } else {
        format!("{:.1}%", 100.0 * a as f64 / b as f64)
    }
}

fn f(x: f64) -> String {
    format!("{:.3}", x)
}

fn tables(rows: &[&Row], title: &str, md: &mut String) {
    let mut by: BTreeMap<(&str, &str), Agg> = BTreeMap::new();
    for r in rows {
        by.entry((r.lang, r.tool)).or_default().add(r);
        by.entry(("ALL", r.tool)).or_default().add(r);
    }
    writeln!(md, "### {title}\n").unwrap();
    writeln!(md, "Micro (sums over fixtures):\n").unwrap();
    writeln!(md, "| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |").unwrap();
    writeln!(md, "|---|---|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
    let mut langs: Vec<&str> = by.keys().map(|k| k.0).filter(|l| *l != "ALL").collect();
    langs.dedup();
    langs.push("ALL");
    for l in &langs {
        for t in ["difffold", "omnidiff"] {
            let Some(a) = by.get(&(*l, t)) else { continue };
            writeln!(
                md,
                "| {l} | {t} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                a.n,
                f(1.0 - a.fails as f64 / a.dec.max(1) as f64),
                f(a.pair.p()),
                f(a.pair.r()),
                f(a.pair.f1()),
                f(a.span.p()),
                f(a.span.r()),
                f(a.span.f1()),
                pct(a.perfect, a.n),
                pct(a.near, a.n),
                pct(a.strict, a.n)
            )
            .unwrap();
        }
    }
    writeln!(md, "\nMacro (mean of per-fixture values):\n").unwrap();
    writeln!(
        md,
        "| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |"
    )
    .unwrap();
    writeln!(md, "|---|---|---|---|---|---|---|---|---|").unwrap();
    for l in &langs {
        for t in ["difffold", "omnidiff"] {
            let Some(a) = by.get(&(*l, t)) else { continue };
            let n = a.n as f64;
            writeln!(
                md,
                "| {l} | {t} | {} | {} | {} | {} | {} | {} | {} |",
                f(a.macro_acc / n),
                f(a.macro_pp / n),
                f(a.macro_pr / n),
                f(a.macro_pf / n),
                f(a.macro_sp / n),
                f(a.macro_sr / n),
                f(a.macro_sf / n)
            )
            .unwrap();
        }
    }
    writeln!(md).unwrap();
}

fn csv_row(r: &Row) -> String {
    format!(
        "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
        r.dataset,
        r.fixture,
        r.lang,
        r.tool,
        r.nb,
        r.na,
        r.decisions,
        r.fails,
        r.vis_fails,
        r.vis_nodes,
        u8::from(r.perfect()),
        u8::from(r.near()),
        u8::from(r.strict()),
        f(r.acc()),
        r.pair.tp,
        r.pair.fp,
        r.pair.fn_,
        r.span.tp,
        r.span.fp,
        r.span.fn_,
        f(r.span.f1()),
        r.native.map_or(String::new(), |n| n.0.to_string()),
        r.native.map_or(String::new(), |n| n.1.to_string())
    )
}

fn run(args: Vec<String>) {
    let (diffs, dump, out) = (
        PathBuf::from(&args[1]),
        PathBuf::from(&args[2]),
        PathBuf::from(&args[3]),
    );
    // Pass `-` as the dump directory to score difffold alone.
    std::fs::create_dir_all(&out).unwrap();
    let mut fixtures: Vec<Fx> = Vec::new();
    let mut unscorable: Vec<(String, String, String)> = Vec::new();
    let mut datasets: Vec<PathBuf> = std::fs::read_dir(&diffs)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    datasets.sort();
    for ds in datasets {
        let dsn = ds.file_name().unwrap().to_string_lossy().to_string();
        let mut fxs: Vec<PathBuf> = std::fs::read_dir(&ds)
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.join("human_mapping.json").exists())
            .collect();
        fxs.sort();
        for fx in fxs {
            match one(&dsn, &fx, &dump) {
                Ok(x) => fixtures.push(x),
                Err(e) => unscorable.push((
                    dsn.clone(),
                    fx.file_name().unwrap().to_string_lossy().to_string(),
                    e,
                )),
            }
        }
    }
    eprintln!(
        "scored {} fixtures, {} unscorable",
        fixtures.len(),
        unscorable.len()
    );
    if dump == Path::new("-") {
        // Solo mode: difffold only, no OmniDiff rows (the empty OmniDiff tool is a placeholder).
        let mut csv = String::from("dataset,fixture,lang,tool,nodes_before,nodes_after,decisions,mismatches,visible_mismatches,visible_nodes,perfect,near_perfect,strict_perfect,accuracy,pair_tp,pair_fp,pair_fn,span_tp,span_fp,span_fn,span_f1,omni_native_visible,omni_native_total\n");
        for x in &fixtures {
            writeln!(csv, "{}", csv_row(&x.d)).unwrap();
        }
        let ted_mode = std::env::var("DFOLD_TED").is_ok();
        std::fs::write(
            out.join(if ted_mode {
                "accuracy-ted-only.csv"
            } else {
                "accuracy-difffold-only.csv"
            }),
            csv,
        )
        .unwrap();
        let mut md = String::from(if std::env::var("DFOLD_TED").is_ok() {
            "# Accuracy against hand-authored ground truth (difffold general tree edit mapping, trees over 20000 nodes fall back to the top-down mapping)\n\n"
        } else {
            "# Accuracy against hand-authored ground truth (difffold only)\n\n"
        });
        let all: Vec<&Row> = fixtures.iter().map(|x| &x.d).collect();
        tables(&all, "All scorable fixtures", &mut md);
        let nr: Vec<&Row> = fixtures
            .iter()
            .filter(|x| !x.cl.rewrite)
            .map(|x| &x.d)
            .collect();
        tables(&nr, "Excluding wholesale-rewrite fixtures", &mut md);
        writeln!(md, "Unscorable fixtures: {}", unscorable.len()).unwrap();
        writeln!(
            md,
            "\n### Decisions by cause class (pair, delete and insert decisions; micro)\n\n| class | decisions | fails | accuracy |\n|---|---|---|---|"
        )
        .unwrap();
        let mut cls_csv = String::from("class,fixtures,decisions,fails\n");
        for c in CLASSES {
            let (mut dec, mut fails, mut fx) = (0usize, 0usize, 0usize);
            for x in &fixtures {
                fx += usize::from(if c == Cls::Rewrite {
                    x.cl.rewrite
                } else {
                    !x.cl.rewrite && x.cl.present[cls_ix(c)]
                });
                for d in x.dd.iter().filter(|d| d.cls == c) {
                    dec += 1;
                    fails += usize::from(d.fail);
                }
            }
            writeln!(
                md,
                "| {} | {dec} | {fails} | {} |",
                cls_name(c),
                f(1.0 - fails as f64 / dec.max(1) as f64)
            )
            .unwrap();
            writeln!(cls_csv, "{},{fx},{dec},{fails}", cls_name(c)).unwrap();
        }
        std::fs::write(
            out.join(if ted_mode {
                "class_failures-ted-only.csv"
            } else {
                "class_failures-difffold-only.csv"
            }),
            cls_csv,
        )
        .unwrap();
        std::fs::write(
            out.join(if ted_mode {
                "SUMMARY-ted-only.md"
            } else {
                "SUMMARY-difffold-only.md"
            }),
            md,
        )
        .unwrap();
        return;
    }

    // CSVs.
    let header = "dataset,fixture,lang,tool,nodes_before,nodes_after,decisions,mismatches,visible_mismatches,visible_nodes,perfect,near_perfect,strict_perfect,accuracy,pair_tp,pair_fp,pair_fn,span_tp,span_fp,span_fn,span_f1,omni_native_visible,omni_native_total";
    let mut csv = format!("{header}\n");
    for x in &fixtures {
        writeln!(csv, "{}", csv_row(&x.d)).unwrap();
        writeln!(csv, "{}", csv_row(&x.o)).unwrap();
    }
    std::fs::write(out.join("fixtures.csv"), csv).unwrap();
    let mut un = String::from("dataset,fixture,reason\n");
    for (d, n, r) in &unscorable {
        writeln!(un, "{d},{n},\"{}\"", r.replace('"', "'")).unwrap();
    }
    std::fs::write(out.join("unscorable.csv"), un).unwrap();

    let mut md = String::new();
    // Taxonomy CSV.
    let mut tx = String::from("dataset,fixture,lang,gt_pairs,gt_identical,gt_changed,gt_deleted,gt_inserted,groups,topdown_bound_pairs,n_move_roots,n_wrap_roots,n_reorder,rewrite,has_local,has_sibling,has_repeated,has_reorder,has_move,has_wrap\n");
    for x in &fixtures {
        let p = |c: Cls| u8::from(x.cl.present[cls_ix(c)]);
        writeln!(
            tx,
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
            x.dataset,
            x.name,
            x.lang,
            x.gt_pairs,
            x.identical,
            x.updates,
            x.n_gt_del,
            x.n_gt_ins,
            x.n_groups,
            x.cl.bound,
            x.cl.n_move,
            x.cl.n_wrap,
            x.cl.n_reorder,
            u8::from(x.cl.rewrite),
            p(Cls::Local),
            p(Cls::Sibling),
            p(Cls::Repeated),
            p(Cls::Reorder),
            p(Cls::Move),
            p(Cls::Wrap)
        )
        .unwrap();
    }
    std::fs::write(out.join("taxonomy.csv"), tx).unwrap();

    // Headline tables.
    let all: Vec<&Row> = fixtures.iter().flat_map(|x| [&x.d, &x.o]).collect();
    writeln!(
        md,
        "## Fixtures scored: {} (unscorable: {})\n",
        fixtures.len(),
        unscorable.len()
    )
    .unwrap();
    tables(&all, "All scorable fixtures", &mut md);
    let non_rewrite: Vec<&Row> = fixtures
        .iter()
        .filter(|x| !x.cl.rewrite)
        .flat_map(|x| [&x.d, &x.o])
        .collect();
    tables(
        &non_rewrite,
        "Excluding wholesale-rewrite fixtures",
        &mut md,
    );

    // Unscorable by reason.
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    for (_, _, r) in &unscorable {
        let key = r.split(':').next().unwrap_or(r).to_string();
        let key = if r.starts_with("language not parsed here") {
            r.clone()
        } else {
            key
        };
        *reasons.entry(key).or_default() += 1;
    }
    writeln!(md, "### Unscorable fixtures by reason (full list: unscorable.csv)\n\n| reason | fixtures |\n|---|---|").unwrap();
    for (r, n) in &reasons {
        writeln!(md, "| {r} | {n} |").unwrap();
    }

    // Ground-truth composition and top-down bound.
    writeln!(
        md,
        "\n### Ground-truth composition and the top-down ceiling\n"
    )
    .unwrap();
    writeln!(md, "| lang | fixtures | GT pairs | identical pairs | changed pairs | GT deleted nodes | GT inserted nodes | cross-parent move roots | wrap/unwrap roots | reorder pairs | top-down ceiling (pair recall) | fixtures at ceiling 100% |").unwrap();
    writeln!(md, "|---|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
    let mut langs: Vec<&str> = fixtures.iter().map(|x| x.lang).collect();
    langs.sort();
    langs.dedup();
    langs.push("ALL");
    for l in &langs {
        let xs: Vec<&Fx> = fixtures
            .iter()
            .filter(|x| *l == "ALL" || x.lang == *l)
            .collect();
        let s = |g: &dyn Fn(&Fx) -> usize| xs.iter().map(|x| g(x)).sum::<usize>();
        let pairs = s(&|x| x.gt_pairs);
        let bound = s(&|x| x.cl.bound as usize);
        let full = xs
            .iter()
            .filter(|x| x.cl.bound as usize == x.gt_pairs && x.n_groups == 0)
            .count();
        writeln!(
            md,
            "| {l} | {} | {pairs} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            xs.len(),
            s(&|x| x.identical),
            s(&|x| x.updates),
            s(&|x| x.n_gt_del),
            s(&|x| x.n_gt_ins),
            s(&|x| x.cl.n_move as usize),
            s(&|x| x.cl.n_wrap as usize),
            s(&|x| x.cl.n_reorder as usize),
            f(bound as f64 / pairs.max(1) as f64),
            pct(full, xs.len())
        )
        .unwrap();
    }

    // Per class.
    writeln!(md, "\n### Failures by root-cause class (decisions: pair, delete, insert and group-member checks)\n").unwrap();
    writeln!(md, "Fixture-level attribution: a fixture flagged wholesale rewrite counts all its decisions there; otherwise a failed decision is charged to the class of its root cause (see definitions).\n").unwrap();
    writeln!(md, "| class | fixtures containing | decisions | difffold fails | omnidiff fails | difffold acc | omnidiff acc | gap (fails) | share of gap | perfect fixtures difffold | perfect fixtures omnidiff |").unwrap();
    writeln!(md, "|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
    let mut cls_csv = String::from("class,fixtures,decisions,difffold_fails,omnidiff_fails\n");
    let mut totals = (0i64, 0i64);
    let mut per: Vec<(Cls, usize, usize, i64, i64, usize, usize)> = Vec::new();
    for c in CLASSES {
        let (mut fx, mut dec, mut df, mut of, mut pd, mut po) = (0, 0, 0i64, 0i64, 0, 0);
        for x in &fixtures {
            let has = if c == Cls::Rewrite {
                x.cl.rewrite
            } else {
                !x.cl.rewrite && x.cl.present[cls_ix(c)]
            };
            if has {
                fx += 1;
                pd += usize::from(x.d.perfect());
                po += usize::from(x.o.perfect());
            }
            for (d, o) in x.dd.iter().zip(&x.od) {
                if d.cls == c {
                    dec += 1;
                    df += i64::from(d.fail);
                    of += i64::from(o.fail);
                }
            }
        }
        totals.0 += df;
        totals.1 += of;
        per.push((c, fx, dec, df, of, pd, po));
    }
    let gap_total = (totals.0 - totals.1).max(1);
    for (c, fx, dec, df, of, pd, po) in &per {
        writeln!(
            md,
            "| {} | {fx} | {dec} | {df} | {of} | {} | {} | {} | {} | {} | {} |",
            cls_name(*c),
            f(1.0 - *df as f64 / (*dec).max(1) as f64),
            f(1.0 - *of as f64 / (*dec).max(1) as f64),
            df - of,
            pct((df - of).max(0) as usize, gap_total as usize),
            pct(*pd, *fx),
            pct(*po, *fx)
        )
        .unwrap();
        writeln!(cls_csv, "{},{fx},{dec},{df},{of}", cls_name(*c)).unwrap();
    }
    std::fs::write(out.join("class_failures.csv"), cls_csv).unwrap();

    // Wrap prevalence and fixture-level gap attribution.
    let n = fixtures.len();
    let wrap_any = fixtures
        .iter()
        .filter(|x| x.cl.present[cls_ix(Cls::Wrap)])
        .count();
    let move_any = fixtures
        .iter()
        .filter(|x| x.cl.present[cls_ix(Cls::Move)])
        .count();
    let reorder_any = fixtures
        .iter()
        .filter(|x| x.cl.present[cls_ix(Cls::Reorder)])
        .count();
    let worse: Vec<&Fx> = fixtures
        .iter()
        .filter(|x| x.d.vis_fails > x.o.vis_fails)
        .collect();
    let worse_wrap = worse
        .iter()
        .filter(|x| x.cl.present[cls_ix(Cls::Wrap)])
        .count();
    writeln!(md, "\nFixtures containing any wrap/unwrap: {wrap_any}/{n} ({}); any cross-parent move: {move_any}/{n} ({}); any reorder: {reorder_any}/{n} ({}).", pct(wrap_any, n), pct(move_any, n), pct(reorder_any, n)).unwrap();
    writeln!(md, "Fixtures where difffold has more visible mismatches than OmniDiff: {}/{n} ({}); of those, {worse_wrap} contain a wrap/unwrap.\n", worse.len(), pct(worse.len(), n)).unwrap();
    // Primary cause of the gap per worse fixture: class with the largest (difffold - omnidiff) fail excess.
    let mut primary: BTreeMap<&str, (usize, i64)> = BTreeMap::new();
    for x in &worse {
        let mut ex: HashMap<Cls, i64> = HashMap::new();
        for (d, o) in x.dd.iter().zip(&x.od) {
            *ex.entry(d.cls).or_default() += i64::from(d.fail) - i64::from(o.fail);
        }
        let (c, v) = ex.into_iter().max_by_key(|(c, v)| (*v, *c)).unwrap();
        let e = primary.entry(cls_name(c)).or_default();
        e.0 += 1;
        e.1 += v;
    }
    writeln!(md, "Primary cause of the gap in the fixtures where difffold is worse (class with the largest excess of failed decisions):\n\n| class | fixtures | excess failed decisions |\n|---|---|---|").unwrap();
    for (c, (k, v)) in &primary {
        writeln!(md, "| {c} | {k} | {v} |").unwrap();
    }

    // Fixtures where OmniDiff is perfect and difffold is not.
    let po: Vec<&Fx> = fixtures
        .iter()
        .filter(|x| x.o.perfect() && !x.d.perfect())
        .collect();
    writeln!(md, "\nFixtures where OmniDiff is perfect and difffold is not: {} ({} of all). Classes present in them:\n", po.len(), pct(po.len(), n)).unwrap();
    for c in CLASSES {
        let k = po
            .iter()
            .filter(|x| {
                if c == Cls::Rewrite {
                    x.cl.rewrite
                } else {
                    x.cl.present[cls_ix(c)]
                }
            })
            .count();
        writeln!(md, "- {}: {k}", cls_name(c)).unwrap();
    }
    let none = po
        .iter()
        .filter(|x| {
            !x.cl.rewrite
                && [Cls::Reorder, Cls::Move, Cls::Wrap, Cls::Repeated]
                    .iter()
                    .all(|&c| !x.cl.present[cls_ix(c)])
        })
        .count();
    writeln!(
        md,
        "- none of move, wrap/unwrap, reorder, repeated, rewrite: {none}"
    )
    .unwrap();

    // Worst 10.
    let mut ranked: Vec<&Fx> = fixtures.iter().collect();
    ranked.sort_by_key(|x| std::cmp::Reverse(x.d.vis_fails as i64 - x.o.vis_fails as i64));
    writeln!(
        md,
        "\n### 10 worst fixtures for difffold (visible mismatches minus OmniDiff's)\n"
    )
    .unwrap();
    writeln!(md, "| fixture | lang | difffold vis. mismatches | omnidiff | decisions | difffold excess fails by cause |\n|---|---|---|---|---|---|").unwrap();
    let mut worst_csv = String::from(
        "dataset,fixture,lang,difffold_visible,omnidiff_visible,decisions,cause_breakdown\n",
    );
    for x in ranked.iter().take(10) {
        let mut ex: BTreeMap<&str, i64> = BTreeMap::new();
        for (d, o) in x.dd.iter().zip(&x.od) {
            *ex.entry(cls_name(d.cls)).or_default() += i64::from(d.fail) - i64::from(o.fail);
        }
        let s: Vec<String> = ex
            .iter()
            .filter(|(_, v)| **v != 0)
            .map(|(k, v)| format!("{k}:{v:+}"))
            .collect();
        writeln!(
            md,
            "| {}/{} | {} | {} | {} | {} | {} |",
            x.dataset,
            x.name,
            x.lang,
            x.d.vis_fails,
            x.o.vis_fails,
            x.d.decisions,
            s.join(" ")
        )
        .unwrap();
        writeln!(
            worst_csv,
            "{},{},{},{},{},{},\"{}\"",
            x.dataset,
            x.name,
            x.lang,
            x.d.vis_fails,
            x.o.vis_fails,
            x.d.decisions,
            s.join(" ")
        )
        .unwrap();
    }
    std::fs::write(out.join("worst10.csv"), worst_csv).unwrap();

    // Calibration against OmniDiff's own checker.
    let (mut agree_zero, mut cmp, mut sum_native, mut sum_mine) = (0, 0, 0i64, 0i64);
    for x in &fixtures {
        if let Some((nv, _)) = x.o.native {
            if nv >= 0 {
                cmp += 1;
                agree_zero += usize::from((nv == 0) == (x.o.vis_fails == 0));
                sum_native += nv;
                sum_mine += x.o.vis_fails as i64;
            }
        }
    }
    writeln!(
        md,
        "\n### Calibration of this scorer against OmniDiff's own checker\n"
    )
    .unwrap();
    writeln!(md, "On {cmp} fixtures with a native result: OmniDiff native visible mismatches total {sum_native}, this scorer's {sum_mine}; zero/non-zero agreement {}. The scorer ignores operation kinds (Identical vs Update) and the subtree-closure step of groups; the native checker enforces both.", pct(agree_zero, cmp)).unwrap();

    std::fs::write(out.join("summary_tables.md"), &md).unwrap();
    println!("{md}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || run(args))
        .unwrap()
        .join()
        .unwrap();
}
