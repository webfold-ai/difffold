//! Times OmniDiff in process on the fixtures, split the way `difffold`'s `dfold-cli --reps N` is.
//!
//! usage: omni_time <diffs-dir> <out.csv> <reps>
//!
//! For every fixture with a `human_mapping.json` whose pair OmniDiff parses, per pass:
//!   parse_ms  read and tree-sitter parse both files (`code_pair_from_dir_without_metadata`)
//!   load_ms   the same plus the AST metadata `diff_code` needs (`code_pair_from_dir`)
//!   diff_ms   `diff_code_with_config` on the loaded pair (default `HeuristicConfig`)
//! Medians, minima and maxima over `reps` passes are written. OmniDiff's own `omnidiff --mode json`
//! additionally renders JSON and is not timed here.
use anyhow::Result;
use omnidiff::test::helper;
use std::io::Write as _;
use std::path::PathBuf;
use std::time::Instant;

fn stats(v: &mut [f64]) -> (f64, f64, f64) {
    v.sort_by(f64::total_cmp);
    (v[v.len() / 2], v[0], v[v.len() - 1])
}

fn run(args: Vec<String>) -> Result<()> {
    let dir = PathBuf::from(&args[1]);
    let reps: usize = args[3].parse()?;
    let config = omnidiff::diff::HeuristicConfig::default();
    let mut out = std::fs::File::create(&args[2])?;
    writeln!(out, "dataset,fixture,reps,nodes_before,nodes_after,parse_med_ms,parse_min_ms,parse_max_ms,load_med_ms,load_min_ms,load_max_ms,diff_med_ms,diff_min_ms,diff_max_ms")?;
    let mut dss: Vec<PathBuf> = std::fs::read_dir(&dir)?.flatten().map(|e| e.path()).filter(|p| p.is_dir()).collect();
    dss.sort();
    let mut done = 0;
    for ds in dss {
        let mut fxs: Vec<PathBuf> = std::fs::read_dir(&ds)?.flatten().map(|e| e.path()).filter(|p| p.join("human_mapping.json").exists()).collect();
        fxs.sort();
        for fx in fxs {
            let run1 = || -> Result<Option<(f64, f64, f64, usize, usize)>> {
                let t = Instant::now();
                let Some(_) = helper::code_pair_from_dir_without_metadata(&fx)? else { return Ok(None) };
                let parse = t.elapsed().as_secs_f64() * 1e3;
                let t = Instant::now();
                let Some((b, a)) = helper::code_pair_from_dir(&fx)? else { return Ok(None) };
                let load = t.elapsed().as_secs_f64() * 1e3;
                if b.ast.is_none() || a.ast.is_none() {
                    return Ok(None);
                }
                let t = Instant::now();
                let d = omnidiff::diff::diff_code_with_config(&b, &a, &config);
                let diff = t.elapsed().as_secs_f64() * 1e3;
                std::hint::black_box(&d);
                Ok(Some((parse, load, diff, b.ast.as_ref().unwrap().root_node().descendant_count(), a.ast.as_ref().unwrap().root_node().descendant_count())))
            };
            let (mut p, mut l, mut d) = (vec![], vec![], vec![]);
            let (mut nb, mut na) = (0, 0);
            let mut ok = true;
            for _ in 0..reps {
                match run1() {
                    Ok(Some((x, y, z, b, a))) => {
                        p.push(x);
                        l.push(y);
                        d.push(z);
                        nb = b;
                        na = a;
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let (pm, pl, ph) = stats(&mut p);
            let (lm, ll, lh) = stats(&mut l);
            let (dm, dl, dh) = stats(&mut d);
            writeln!(out, "{},{},{reps},{nb},{na},{pm:.4},{pl:.4},{ph:.4},{lm:.4},{ll:.4},{lh:.4},{dm:.4},{dl:.4},{dh:.4}", ds.file_name().unwrap().to_string_lossy(), fx.file_name().unwrap().to_string_lossy())?;
            done += 1;
        }
    }
    eprintln!("timed {done} fixtures x {reps}");
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new().stack_size(512 << 20).spawn(move || run(args).unwrap()).unwrap().join().unwrap();
}
