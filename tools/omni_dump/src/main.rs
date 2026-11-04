//! Dumps OmniDiff's node correspondence for every fixture with a human_mapping.json.
//!
//! usage: omni_dump <diffs-dir> <out-dir>
//!
//! One file per fixture, `<dataset>__<fixture>.map`:
//!   line 1: `<before nodes> <after nodes> <native visible mismatches> <native total mismatches> <visible nodes>`
//!   then one `<before preorder> <after preorder>` line per partner (group members list all partners).
//! Preorder indices count every tree-sitter node (named and anonymous), children in order.
use anyhow::Result;
use omnidiff::diff::NodeCache;
use omnidiff::test::helper;
use omnidiff::test::helper::human_mapping;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::PathBuf;

fn preorder(code: &omnidiff::code::Code) -> HashMap<usize, usize> {
    let mut out = HashMap::new();
    let mut cur = code.ast.as_ref().unwrap().root_node().walk();
    loop {
        let n = out.len();
        out.insert(cur.node().id(), n);
        if cur.goto_first_child() {
            continue;
        }
        loop {
            if cur.goto_next_sibling() {
                break;
            }
            if !cur.goto_parent() {
                return out;
            }
        }
    }
}

fn run(args: Vec<String>) -> Result<()> {
    let (dir, out) = (PathBuf::from(&args[1]), PathBuf::from(&args[2]));
    std::fs::create_dir_all(&out)?;
    let config = omnidiff::diff::HeuristicConfig::default();
    let mut done = 0;
    for ds in std::fs::read_dir(&dir)? {
        let ds = ds?.path();
        if !ds.is_dir() {
            continue;
        }
        for fx in std::fs::read_dir(&ds)? {
            let fx = fx?.path();
            if !fx.join("human_mapping.json").exists() {
                continue;
            }
            let name = fx.file_name().unwrap().to_string_lossy().to_string();
            let key = format!("{}__{}", ds.file_name().unwrap().to_string_lossy(), name);
            let res = (|| -> Result<String> {
                let Some((before, after)) = helper::code_pair_from_dir(&fx)? else { anyhow::bail!("no pair") };
                if before.ast.is_none() || after.ast.is_none() {
                    anyhow::bail!("no ast");
                }
                let diff = omnidiff::diff::diff_code_with_config(&before, &after, &config);
                let da = diff.ast.as_ref().ok_or_else(|| anyhow::anyhow!("no diff ast"))?;
                let (pb, pa) = (preorder(&before), preorder(&after));
                let node_cache = NodeCache::build(&before, &after);
                let (mut vis, mut tot, mut visn) = (-1i64, -1i64, -1i64);
                if let Ok(mapping) = human_mapping::load_with(&name, &before, &after) {
                    if let Ok(v) = human_mapping::visible_mismatches_with(&name, &before, &after, da, &node_cache, &config, &mapping) {
                        vis = v.visible.len() as i64;
                        tot = (v.visible.len() + v.invisible.len()) as i64;
                        visn = (v.before_visible_node_count + v.after_visible_node_count) as i64;
                    }
                }
                let mut s = format!("{} {} {} {} {}\n", pb.len(), pa.len(), vis, tot, visn);
                let mut rows: Vec<(usize, usize)> = Vec::new();
                for (&id, &i) in &pb {
                    for &p in da.before_partners(id) {
                        if let Some(&j) = pa.get(&p) {
                            rows.push((i, j));
                        }
                    }
                }
                rows.sort();
                for (i, j) in rows {
                    writeln!(s, "{i} {j}")?;
                }
                Ok(s)
            })();
            match res {
                Ok(s) => {
                    std::fs::write(out.join(format!("{key}.map")), s)?;
                    done += 1;
                }
                Err(e) => {
                    std::fs::write(out.join(format!("{key}.err")), format!("{e:#}"))?;
                }
            }
        }
    }
    eprintln!("dumped {done}");
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new().stack_size(512 << 20).spawn(move || run(args).unwrap()).unwrap().join().unwrap();
}
