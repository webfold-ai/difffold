//! Git's own xdiff (vendored in libgit2), measured on the same fixtures as `linebench`.
//!
//! usage: xdiff-baseline <fixtures-dir> <out.csv> [reps]
//!
//! Emits the two `xdiff-default` and `xdiff-minimal` rows in linebench's CSV format
//! (`dataset,fixture,lines_before,lines_after,algo,us,cost`). Kept out of the root
//! workspace so that the `git2` advisories (RUSTSEC-2026-0183/-0184) are not in the root lock.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn find(dir: &Path, p: &str) -> Option<PathBuf> {
    std::fs::read_dir(dir).ok()?.flatten().map(|e| e.path()).find(|x| {
        x.file_name()
            .and_then(|f| f.to_str())
            .is_some_and(|f| f.starts_with(p))
    })
}

fn med(v: &mut [f64]) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn time<T>(reps: usize, mut f: impl FnMut() -> T) -> (f64, T) {
    let mut t = Vec::with_capacity(reps);
    let mut last = None;
    for _ in 0..reps {
        let s = Instant::now();
        let r = f();
        t.push(s.elapsed().as_secs_f64() * 1e6);
        last = Some(r);
    }
    (med(&mut t), last.unwrap())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: xdiff-baseline <fixtures-dir> <out.csv> [reps]");
        std::process::exit(2);
    }
    let dir = PathBuf::from(&args[1]);
    let reps: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(15);
    let mut out = std::fs::File::create(&args[2]).unwrap();
    writeln!(out, "dataset,fixture,lines_before,lines_after,algo,us,cost").unwrap();
    let mut pairs = Vec::new();
    for ds in std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
            if let (Some(b), Some(a)) = (find(&fx, "before."), find(&fx, "after.")) {
                pairs.push((
                    ds.file_name().unwrap().to_string_lossy().to_string(),
                    fx.file_name().unwrap().to_string_lossy().to_string(),
                    b,
                    a,
                ));
            }
        }
    }
    pairs.sort();
    for (ds, name, bp, ap) in pairs {
        let (Ok(bs), Ok(as_)) = (std::fs::read(&bp), std::fs::read(&ap)) else {
            continue;
        };
        let (Ok(bt), Ok(at)) = (std::str::from_utf8(&bs), std::str::from_utf8(&as_)) else {
            continue;
        };
        let (lb, la) = (bt.lines().count(), at.lines().count());
        for (algo, minimal) in [("xdiff-default", false), ("xdiff-minimal", true)] {
            let (us, c) = time(reps, || {
                let mut o = git2::DiffOptions::new();
                o.minimal(minimal).context_lines(0);
                let p = git2::Patch::from_buffers(&bs, None, &as_, None, Some(&mut o)).unwrap();
                let (_, a, d) = p.line_stats().unwrap();
                a + d
            });
            writeln!(out, "{ds},{name},{lb},{la},{algo},{us:.2},{c}").unwrap();
        }
    }
}
