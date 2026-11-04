//! Converts GumTree node mappings (dumped by java/Eval.java as GumTree-preorder id pairs plus UTF-8 byte
//! ranges) into the per-fixture `.map` files that difffold's `score_accuracy` ingests (tree-sitter preorder
//! numbering, every named and anonymous node).
//!
//! usage: gt2map <diffs-sel-dir> <eval-out-dir>/<generator> <matcher> <out-raw-dir> <out-scoped-dir>
//!
//! GumTree node -> tree-sitter node is resolved by exact byte range. Several tree-sitter nodes can share one
//! range (single-child chains); GumTree nodes of the same range are aligned to them first by equal type name
//! and then bottom-up. `raw` maps only what GumTree says. `scoped` additionally adds the ground-truth pair
//! for every ground-truth pair whose two nodes are both not representable in GumTree's tree (no GumTree node
//! has that range on either side), so unrepresentable nodes (punctuation, wrapper nodes the generator drops) neither
//! help nor hurt, and only the nodes GumTree can express are judged.
use serde_json::Value;
use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use tree_sitter::{Language, Node, Parser};

#[derive(Default)]
struct T {
    kind: Vec<&'static str>,
    kids: Vec<Vec<u32>>,
    size: Vec<u32>,
    s: Vec<usize>,
    e: Vec<usize>,
}

fn build(n: Node, t: &mut T, parent: Option<u32>) -> u32 {
    // Returns the subtree size.
    let idx = t.kind.len() as u32;
    t.kind.push(n.kind());
    t.kids.push(Vec::new());
    t.size.push(0);
    t.s.push(n.start_byte());
    t.e.push(n.end_byte());
    if let Some(p) = parent {
        t.kids[p as usize].push(idx);
    }
    let mut c = n.walk();
    let mut sz = 1;
    for ch in n.children(&mut c) {
        sz += build(ch, t, Some(idx));
    }
    t.size[idx as usize] = sz;
    sz
}

fn lang(ext: &str) -> Option<Language> {
    Some(match ext {
        "java" => tree_sitter_java::LANGUAGE.into(),
        "go" => tree_sitter_go::LANGUAGE.into(),
        "c" | "h" => tree_sitter_c::LANGUAGE.into(),
        "py" => tree_sitter_python::LANGUAGE.into(),
        "js" | "mjs" => tree_sitter_javascript::LANGUAGE.into(),
        "ts" => tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into(),
        "tsx" => tree_sitter_typescript::LANGUAGE_TSX.into(),
        "rs" => tree_sitter_rust::LANGUAGE.into(),
        _ => return None,
    })
}

fn resolve(t: &T, path: &Value) -> Option<u32> {
    let mut cur = 0u32;
    for seg in path.as_array()? {
        let s = seg.as_str()?;
        let (kind, occ) = match s.rsplit_once(':') {
            Some((k, n)) => match n.parse::<u32>() {
                Ok(n) => (k, n),
                Err(_) => (s, 1),
            },
            None => (s, 1),
        };
        cur = t.kids[cur as usize].iter().filter(|&&k| t.kind[k as usize] == kind).nth(occ as usize - 1).copied()?;
    }
    Some(cur)
}

fn gt_pairs(json: &Value, bt: &T, at: &T) -> Option<Vec<(u32, u32)>> {
    let mut out = Vec::new();
    for e in json["entries"].as_array()? {
        let op = e["operation"].as_str()?;
        match op {
            "identical" | "update" | "match_but_not_identical" => out.push((resolve(bt, &e["before_path"])?, resolve(at, &e["after_path"])?)),
            "identical_with_children" => {
                let (b, a) = (resolve(bt, &e["before_path"])?, resolve(at, &e["after_path"])?);
                if bt.size[b as usize] != at.size[a as usize] {
                    return None;
                }
                for k in 0..bt.size[b as usize] {
                    out.push((b + k, a + k));
                }
            }
            _ => {}
        }
    }
    Some(out)
}

struct GNode {
    start: usize,
    end: usize,
    ty: String,
}

fn read_nodes(path: &Path) -> Option<(Vec<GNode>, Vec<GNode>)> {
    let text = std::fs::read_to_string(path).ok()?;
    let mut lines = text.lines();
    let h: Vec<usize> = lines.next()?.split(' ').map(|x| x.parse().unwrap()).collect();
    let (mut s, mut d) = (Vec::with_capacity(h[0]), Vec::with_capacity(h[1]));
    for l in lines {
        let p: Vec<&str> = l.splitn(6, ' ').collect();
        let g = GNode { start: p[2].parse().unwrap(), end: p[3].parse().unwrap(), ty: p[4].to_string() };
        if p[0] == "S" { s.push(g) } else { d.push(g) }
    }
    Some((s, d))
}

/// Maps each GumTree node to a tree-sitter node of exactly the same byte range.
fn align(g: &[GNode], t: &T, src: &[u8]) -> Vec<Option<u32>> {
    let mut ts_by: HashMap<(usize, usize), Vec<u32>> = HashMap::new();
    for i in 0..t.kind.len() {
        ts_by.entry((t.s[i], t.e[i])).or_default().push(i as u32);
    }
    let mut g_by: HashMap<(usize, usize), Vec<usize>> = HashMap::new();
    for (i, n) in g.iter().enumerate() {
        g_by.entry((n.start, n.end)).or_default().push(i);
    }
    let mut out = vec![None; g.len()];
    for (r, gs) in &g_by {
        let Some(ts) = ts_by.get(r) else { continue };
        let mut used = vec![false; ts.len()];
        let mut done = vec![false; gs.len()];
        for (gi, &g_i) in gs.iter().enumerate() {
            if let Some(k) = (0..ts.len()).find(|&k| !used[k] && t.kind[ts[k] as usize] == g[g_i].ty) {
                used[k] = true;
                done[gi] = true;
                out[g_i] = Some(ts[k]);
            }
        }
        let rg: Vec<usize> = (0..gs.len()).rev().filter(|&i| !done[i]).collect();
        let rt: Vec<usize> = (0..ts.len()).rev().filter(|&k| !used[k]).collect();
        for (a, b) in rg.iter().zip(rt.iter()) {
            out[gs[*a]] = Some(ts[*b]);
        }
    }
    // Fallback: a GumTree node whose range starts at a leading comment (JDT includes the Javadoc in a
    // declaration's range) maps to the outermost unused tree-sitter node with the same end that starts right
    // after the comment.
    let mut taken = vec![false; t.kind.len()];
    out.iter().flatten().for_each(|&i| taken[i as usize] = true);
    let mut by_end: HashMap<usize, Vec<u32>> = HashMap::new();
    for i in 0..t.kind.len() {
        by_end.entry(t.e[i]).or_default().push(i as u32);
    }
    for (i, n) in g.iter().enumerate() {
        if out[i].is_some() || n.end <= n.start {
            continue;
        }
        let Some(c) = by_end.get(&n.end) else { continue };
        let mut best: Option<u32> = None;
        for &k in c {
            let ks = t.s[k as usize];
            if ks > n.start && ks - n.start < 20000 && !taken[k as usize] {
                let gap = src[n.start..ks].trim_ascii();
                if gap.starts_with(b"/*") || gap.starts_with(b"//") {
                    if best.map_or(true, |b| ks < t.s[b as usize]) {
                        best = Some(k);
                    }
                }
            }
        }
        if let Some(b) = best {
            taken[b as usize] = true;
            out[i] = Some(b);
        }
    }
    if out[0].is_none() {
        out[0] = Some(0);
    }
    out
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let h = std::thread::Builder::new().stack_size(1 << 29).spawn(move || run(a)).unwrap();
    h.join().unwrap();
}

fn run(a: Vec<String>) {
    let (diffs, gdir, matcher, raw, scoped) = (PathBuf::from(&a[1]), PathBuf::from(&a[2]), &a[3], PathBuf::from(&a[4]), PathBuf::from(&a[5]));
    std::fs::create_dir_all(&raw).unwrap();
    std::fs::create_dir_all(&scoped).unwrap();
    let mut hist: HashMap<String, usize> = HashMap::new();
    let mut stats = String::from("key\tgt_pairs_total\tgumtree_pairs\tgumtree_pairs_unaligned\tts_nodes_b\tts_nodes_a\trep_b\trep_a\tgranted_pairs\n");
    let mut dsd: Vec<PathBuf> = std::fs::read_dir(&diffs).unwrap().flatten().map(|e| e.path()).collect();
    dsd.sort();
    for ds in dsd {
        let dsn = ds.file_name().unwrap().to_string_lossy().to_string();
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()) {
            let name = fx.file_name().unwrap().to_string_lossy().to_string();
            let key = format!("{dsn}__{name}");
            let pairs_file = gdir.join(matcher).join(format!("{key}.pairs"));
            let nodes_file = gdir.join("nodes").join(format!("{key}.nodes"));
            if !pairs_file.exists() || !nodes_file.exists() {
                continue;
            }
            let find = |p: &str| std::fs::read_dir(&fx).unwrap().flatten().map(|e| e.path()).find(|q| q.file_name().unwrap().to_str().unwrap().starts_with(p)).unwrap();
            let (bp, ap) = (find("before."), find("after."));
            let ext = bp.file_name().unwrap().to_str().unwrap().split('.').nth(1).unwrap_or("").to_string();
            let Some(l) = lang(&ext) else { continue };
            let (bs, as_) = (std::fs::read(&bp).unwrap(), std::fs::read(&ap).unwrap());
            let mut p = Parser::new();
            p.set_language(&l).unwrap();
            let (tb, ta) = (p.parse(&bs, None).unwrap(), p.parse(&as_, None).unwrap());
            let (mut bt, mut at) = (T::default(), T::default());
            build(tb.root_node(), &mut bt, None);
            build(ta.root_node(), &mut at, None);
            let (nb, na) = (bt.kind.len(), at.kind.len());
            let (gs, gd) = read_nodes(&nodes_file).unwrap();
            let (ms, md) = (align(&gs, &bt, &bs), align(&gd, &at, &as_));
            let mut rep_b = vec![false; nb];
            let mut rep_a = vec![false; na];
            ms.iter().flatten().for_each(|&i| rep_b[i as usize] = true);
            md.iter().flatten().for_each(|&i| rep_a[i as usize] = true);
            for (i, m) in ms.iter().enumerate() {
                if m.is_none() {
                    *hist.entry(gs[i].ty.clone()).or_default() += 1;
                }
            }
            let mut set: BTreeSet<(u32, u32)> = BTreeSet::new();
            let (mut total, mut bad) = (0, 0);
            for line in std::fs::read_to_string(&pairs_file).unwrap().lines() {
                let (x, y) = line.split_once(' ').unwrap();
                total += 1;
                match (ms[x.parse::<usize>().unwrap()], md[y.parse::<usize>().unwrap()]) {
                    (Some(x), Some(y)) => {
                        set.insert((x, y));
                    }
                    _ => bad += 1,
                }
            }
            let write = |dir: &Path, set: &BTreeSet<(u32, u32)>| {
                let mut s = format!("{nb} {na} 0 0\n");
                for (x, y) in set {
                    s.push_str(&format!("{x} {y}\n"));
                }
                std::fs::write(dir.join(format!("{key}.map")), s).unwrap();
            };
            write(&raw, &set);
            let mut sc = set.clone();
            let mut granted = 0;
            let mut gtn = 0;
            if let Ok(txt) = std::fs::read_to_string(fx.join("human_mapping.json")) {
                if let Some(gp) = serde_json::from_str::<Value>(&txt).ok().and_then(|j| gt_pairs(&j, &bt, &at)) {
                    gtn = gp.len();
                    for (b, a2) in gp {
                        if !rep_b[b as usize] && !rep_a[a2 as usize] {
                            sc.insert((b, a2));
                            granted += 1;
                        }
                    }
                }
            }
            write(&scoped, &sc);
            stats.push_str(&format!("{key}\t{gtn}\t{total}\t{bad}\t{nb}\t{na}\t{}\t{}\t{granted}\n", rep_b.iter().filter(|&&x| x).count(), rep_a.iter().filter(|&&x| x).count()));
        }
    }
    std::fs::write(raw.join("_stats.tsv"), stats).unwrap();
    let mut h: Vec<_> = hist.into_iter().collect();
    h.sort_by(|a, b| b.1.cmp(&a.1));
    let txt: Vec<String> = h.iter().map(|(k, v)| format!("{k}\t{v}")).collect();
    std::fs::write(raw.join("_unaligned_types.tsv"), txt.join("\n")).unwrap();
}
