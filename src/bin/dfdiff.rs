//! `dfdiff`: a git-diff-compatible unified diff on the difffold line differ.
//!
//! usage: dfdiff [-U N] [--histogram] OLD NEW
//!        GIT_EXTERNAL_DIFF=dfdiff git diff      (git passes seven arguments; both forms work)
//! Output starts with `diff --git a/PATH b/PATH`, so `git apply` accepts it. This binary is output
//! plumbing: the algorithm is `difffold::lines`.
use difffold::lines::Algo;
use std::io::Write;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut ctx = 3usize;
    let mut algo = Algo::Minimal;
    let mut files = Vec::new();
    while !args.is_empty() {
        let a = args.remove(0);
        if a == "-U" {
            ctx = args.remove(0).parse().expect("context lines");
        } else if let Some(n) = a.strip_prefix("-U") {
            ctx = n.parse().expect("context lines");
        } else if a == "--histogram" {
            algo = Algo::Histogram;
        } else if a == "--minimal" {
            algo = Algo::Minimal;
        } else {
            files.push(a);
        }
    }
    // GIT_EXTERNAL_DIFF passes: path old-file old-hex old-mode new-file new-hex new-mode.
    let (name, old_path, new_path) = if files.len() == 7 { (files[0].clone(), files[1].clone(), files[4].clone()) } else { (files[1].clone(), files[0].clone(), files[1].clone()) };
    let (old_absent, new_absent) = (old_path == "/dev/null", new_path == "/dev/null");
    let old = if old_absent { Vec::new() } else { std::fs::read(&old_path).expect("read old") };
    let new = if new_absent { Vec::new() } else { std::fs::read(&new_path).expect("read new") };
    // GIT_EXTERNAL_DIFF passes the modes as the fourth and seventh arguments.
    let (kind, mode) = match (old_absent, new_absent) {
        (true, _) => (difffold::unified::Kind::Create, files.get(6).cloned().unwrap_or_else(|| "100644".into())),
        (_, true) => (difffold::unified::Kind::Delete, files.get(3).cloned().unwrap_or_else(|| "100644".into())),
        _ => (difffold::unified::Kind::Modify, "100644".into()),
    };
    let patch = difffold::unified::unified_with(&old, &new, &name, ctx, algo, kind, &mode);
    std::io::stdout().write_all(&patch).unwrap();
}
