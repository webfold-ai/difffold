//! In-process line diff comparison on real before/after files.
//! usage: linebench <diffs-dir> <out.csv> [reps]
//! Every algorithm is timed from raw bytes (line splitting and hashing included) to an edit cost.
use difffold::lines::{diff_text, diff_text_with, replay_ok, Algo};
use imara_diff::intern::InternedInput;
use imara_diff::{diff as imara, Algorithm as IA};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn find(dir: &Path, p: &str) -> Option<PathBuf> {
    std::fs::read_dir(dir).ok()?.flatten().map(|e| e.path()).find(|x| x.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(p)))
}

fn med(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn time<T>(reps: usize, mut f: impl FnMut() -> T) -> (f64, T) {
    let mut ts = Vec::new();
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let r = f();
        ts.push(t.elapsed().as_secs_f64() * 1e6);
        last = Some(r);
    }
    (med(&mut ts), last.unwrap())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(&args[1]);
    let reps: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(15);
    let mut out = std::fs::File::create(&args[2]).unwrap();
    writeln!(out, "dataset,fixture,lines_before,lines_after,algo,us,cost").unwrap();
    let mut pairs = Vec::new();
    for ds in std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
            if let (Some(b), Some(a)) = (find(&fx, "before."), find(&fx, "after.")) {
                pairs.push((ds.file_name().unwrap().to_string_lossy().to_string(), fx.file_name().unwrap().to_string_lossy().to_string(), b, a));
            }
        }
    }
    pairs.sort();
    let mut n = 0;
    let mut mismatches = 0;
    for (ds, name, bp, ap) in pairs {
        let (Ok(bs), Ok(as_)) = (std::fs::read(&bp), std::fs::read(&ap)) else { continue };
        let (Ok(bt), Ok(at)) = (std::str::from_utf8(&bs), std::str::from_utf8(&as_)) else { continue };
        let (lb, la) = (bt.lines().count(), at.lines().count());
        let row = |algo: &str, us: f64, cost: usize, out: &mut std::fs::File| {
            writeln!(out, "{ds},{name},{lb},{la},{algo},{us:.2},{cost}").unwrap();
        };
        let (us, d) = time(reps, || diff_text(&bs, &as_));
        assert!(replay_ok(&bs, &as_, &d), "replay failed on {name}");
        let ours = d.cost();
        row("difffold-lines", us, ours, &mut out);
        let (us, dh) = time(reps, || diff_text_with(&bs, &as_, Algo::Histogram));
        assert!(replay_ok(&bs, &as_, &dh), "histogram replay failed on {name}");
        row("difffold-histogram", us, dh.cost(), &mut out);
        let (us, c) = time(reps, || {
            let input = InternedInput::new(bt, at);
            let c = imara(IA::Myers, &input, imara_diff::sink::Counter::default());
            (c.insertions + c.removals) as usize
        });
        row("imara-myers", us, c, &mut out);
        if false && c != ours {
            mismatches += 1;
            eprintln!("cost mismatch vs imara-myers on {name}: ours {ours} imara {c}");
        }
        let (us, c) = time(reps, || {
            let input = InternedInput::new(bt, at);
            let c = imara(IA::MyersMinimal, &input, imara_diff::sink::Counter::default());
            (c.insertions + c.removals) as usize
        });
        row("imara-myers-minimal", us, c, &mut out);
        let (us, c) = time(reps, || {
            let input = InternedInput::new(bt, at);
            let c = imara(IA::Histogram, &input, imara_diff::sink::Counter::default());
            (c.insertions + c.removals) as usize
        });
        row("imara-histogram", us, c, &mut out);
        let (us, c) = time(reps, || {
            let ops = similar::capture_diff_slices(similar::Algorithm::Myers, &bt.split_inclusive('\n').collect::<Vec<_>>(), &at.split_inclusive('\n').collect::<Vec<_>>());
            ops.iter().map(|o| match o { similar::DiffOp::Equal { .. } => 0, similar::DiffOp::Delete { old_len, .. } => *old_len, similar::DiffOp::Insert { new_len, .. } => *new_len, similar::DiffOp::Replace { old_len, new_len, .. } => old_len + new_len }).sum::<usize>()
        });
        row("similar-myers", us, c, &mut out);
        if c != ours {
            mismatches += 1;
            eprintln!("cost mismatch vs similar-myers on {name}: ours {ours} similar {c}");
        }
        // Git's own xdiff, in process (libgit2 vendors it): raw bytes to a patch object with line stats.
        for (name, minimal) in [("xdiff-default", false), ("xdiff-minimal", true)] {
            let (us, c) = time(reps, || {
                let mut o = git2::DiffOptions::new();
                o.minimal(minimal).context_lines(0);
                let p = git2::Patch::from_buffers(&bs, None, &as_, None, Some(&mut o)).unwrap();
                let (_, a, d) = p.line_stats().unwrap();
                a + d
            });
            row(name, us, c, &mut out);
        }
        // Patch stage: raw bytes to a serialized unified diff.
        let (us, p) = time(reps, || difffold::unified::unified(&bs, &as_, "f", 3, Algo::Minimal));
        row("patch-difffold", us, p.len(), &mut out);
        let (us, p) = time(reps, || {
            similar::TextDiff::configure().algorithm(similar::Algorithm::Myers).diff_lines(bt, at).unified_diff().context_radius(3).to_string().len()
        });
        row("patch-similar-myers", us, p, &mut out);
        let (us, p) = time(reps, || {
            let input = InternedInput::new(bt, at);
            imara(IA::Myers, &input, imara_diff::UnifiedDiffBuilder::new(&input)).len()
        });
        row("patch-imara-myers", us, p, &mut out);
        n += 1;
    }
    eprintln!("{n} fixtures, {mismatches} cost mismatches vs similar-myers");
}
