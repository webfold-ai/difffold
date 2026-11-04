//! General tree edit distance: difffold::ted against the APTED port, on real tree-sitter ASTs.
//! usage: tedbench <diffs-dir> <out.csv> <max-nodes-per-side> [max-pairs] [reps]
//! Both compute the Zhang-Shasha objective with unit costs; distances are asserted equal.
use apted::{BracketStringInputParser, StringUnitCostModel, APTED};
use difffold::ted::{check_mapping, replay_script, ted_mapping, ted_stats, ted_unpruned, PostTree};
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;
use tree_sitter::{Language, Node, Parser};

struct Flat {
    label: Vec<u32>,
    kids: Vec<Vec<u32>>,
}

fn walk(n: Node, src: &[u8], it: &mut HashMap<(u16, Option<Vec<u8>>), u32>, f: &mut Flat) -> u32 {
    let (key, kids) = if n.child_count() == 0 {
        ((n.kind_id(), Some(src[n.byte_range()].to_vec())), vec![])
    } else {
        let mut c = n.walk();
        let ks: Vec<u32> = n.children(&mut c).map(|ch| walk(ch, src, it, f)).collect();
        ((n.kind_id(), None), ks)
    };
    let next = it.len() as u32;
    let l = *it.entry(key).or_insert(next);
    f.label.push(l);
    f.kids.push(kids);
    f.label.len() as u32 - 1
}

fn bracket(f: &Flat, i: usize, out: &mut String) {
    out.push('{');
    out.push_str(&f.label[i].to_string());
    for &k in &f.kids[i] {
        bracket(f, k as usize, out);
    }
    out.push('}');
}

/// Canonical subtree ids by hash-consing (label, child ids); returns the ids in postorder.
fn canon(f: &Flat, table: &mut HashMap<(u32, Vec<u32>), u32>) -> Vec<u32> {
    let mut ids = vec![0u32; f.label.len()];
    for i in 0..f.label.len() {
        let key = (f.label[i], f.kids[i].iter().map(|&k| ids[k as usize]).collect::<Vec<_>>());
        let next = table.len() as u32;
        ids[i] = *table.entry(key).or_insert(next);
    }
    ids
}

fn lang(ext: &str) -> Option<Language> {
    match ext {
        "java" => Some(tree_sitter_java::LANGUAGE.into()),
        "go" => Some(tree_sitter_go::LANGUAGE.into()),
        "c" | "h" => Some(tree_sitter_c::LANGUAGE.into()),
        _ => None,
    }
}

fn med(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn run(args: Vec<String>) {
    let root = PathBuf::from(&args[1]);
    let max_nodes: usize = args[3].parse().unwrap();
    let cap: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(300);
    let reps: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(3);
    let min_nodes: usize = args.get(6).and_then(|s| s.parse().ok()).unwrap_or(20);
    let mut out = std::fs::File::create(&args[2]).unwrap();
    writeln!(out, "fixture,nodes_before,nodes_after,dist,norm_dist,unique_before,shared_fraction,cells,windows,skipped,attempts,mirrored,difffold_us,unpruned_us,apted_us,mapping_us,mapping_pairs").unwrap();
    let mut done = 0;
    let mut dirs: Vec<PathBuf> = Vec::new();
    for ds in std::fs::read_dir(&root).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        dirs.extend(std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()));
    }
    dirs.sort();
    for fx in dirs {
        let find = |pre: &str| std::fs::read_dir(&fx).unwrap().flatten().map(|e| e.path()).find(|x| x.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(pre)));
        let (Some(bp), Some(ap)) = (find("before."), find("after.")) else { continue };
        let ext = bp.file_name().unwrap().to_str().unwrap().split('.').nth(1).unwrap_or("").to_string();
        let Some(l) = lang(&ext) else { continue };
        let (Ok(bs), Ok(as_)) = (std::fs::read(&bp), std::fs::read(&ap)) else { continue };
        let mut parser = Parser::new();
        parser.set_language(&l).unwrap();
        let (Some(tb), Some(ta)) = (parser.parse(&bs, None), parser.parse(&as_, None)) else { continue };
        let mut it = HashMap::new();
        let (mut fb, mut fa) = (Flat { label: vec![], kids: vec![] }, Flat { label: vec![], kids: vec![] });
        let rb = walk(tb.root_node(), &bs, &mut it, &mut fb);
        let ra = walk(ta.root_node(), &as_, &mut it, &mut fa);
        let (nb, na) = (fb.label.len(), fa.label.len());
        if nb > max_nodes || na > max_nodes || nb < min_nodes {
            continue;
        }
        let (pb, pa) = (PostTree::from_kids(fb.label.clone(), &fb.kids), PostTree::from_kids(fa.label.clone(), &fa.kids));
        let (mut sb, mut sa) = (String::new(), String::new());
        bracket(&fb, rb as usize, &mut sb);
        bracket(&fa, ra as usize, &mut sa);
        if let Ok(path) = std::env::var("TED_DUMP") {
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
            writeln!(f, "{sb}\n{sa}").unwrap();
        }
        let parser = BracketStringInputParser::new();
        let (t1, t2) = (parser.from_string(&sb), parser.from_string(&sa));
        let mut table = HashMap::new();
        let (cb, ca) = (canon(&fb, &mut table), canon(&fa, &mut table));
        let uniq_b: std::collections::HashSet<u32> = cb.iter().copied().collect();
        let set_a: std::collections::HashSet<u32> = ca.iter().copied().collect();
        let shared = cb.iter().filter(|c| set_a.contains(c)).count() as f64 / nb as f64;
        let mut dt = Vec::new();
        let (mut d_ours, mut stats) = (0, Default::default());
        for _ in 0..reps {
            let t = Instant::now();
            (d_ours, stats) = ted_stats(&pb, &pa);
            dt.push(t.elapsed().as_secs_f64() * 1e6);
        }
        let mut ut = f64::NAN;
        if nb.max(na) <= 3000 {
            let t = Instant::now();
            let du = ted_unpruned(&pb, &pa);
            ut = t.elapsed().as_secs_f64() * 1e6;
            assert_eq!(du, d_ours, "unpruned distance differs on {}", fx.display());
        }
        let mut at = Vec::new();
        let mut d_apted = 0.0f32;
        for _ in 0..reps {
            let t = Instant::now();
            d_apted = APTED::new(StringUnitCostModel).compute_edit_distance(&t1, &t2);
            at.push(t.elapsed().as_secs_f64() * 1e6);
        }
        let tm = Instant::now();
        let mp = ted_mapping(&pb, &pa);
        let map_us = tm.elapsed().as_secs_f64() * 1e6;
        let script = check_mapping(&pb, &pa, &mp.pairs).unwrap_or_else(|e| panic!("illegal mapping on {}: {e}", fx.display()));
        assert_eq!(script, d_ours, "mapping script cost differs from the distance on {}", fx.display());
        let replayed = replay_script(&pb, &pa, &mp.pairs).unwrap_or_else(|e| panic!("script replay failed on {}: {e}", fx.display()));
        assert_eq!(replayed, d_ours, "replayed operation count differs from the distance on {}", fx.display());
        assert_eq!(d_ours as f32, d_apted, "distance mismatch on {}", fx.display());
        writeln!(out, "{},{nb},{na},{d_ours},{:.4},{},{shared:.4},{},{},{},{},{},{:.0},{ut:.0},{:.0},{map_us:.0},{}", fx.file_name().unwrap().to_string_lossy(), f64::from(d_ours) / (nb + na) as f64, uniq_b.len(), stats.cells, stats.windows, stats.skipped, stats.attempts, u8::from(stats.mirrored), med(&mut dt), med(&mut at), mp.pairs.len()).unwrap();
        done += 1;
        if done >= cap {
            break;
        }
    }
    eprintln!("{done} pairs, all distances equal to APTED");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new().stack_size(256 << 20).spawn(move || run(args)).unwrap().join().unwrap();
}
