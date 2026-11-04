//! `difffold-patch BEFORE AFTER`: emit a git-style unified patch that `git apply` accepts.
//!
//! Options: `--path NAME` (header name, default AFTER), `--old-path NAME`, `--old-mode OCT`,
//! `--new-mode OCT`, `--binary git|refuse`, `-U N`, `--stats`.
//! Exit codes: 0 patch written, 3 identical (nothing written), 4 refused (reason on stderr),
//! 2 usage or I/O error.

use gitcompat::patch::{make_patch, BinaryMode, Outcome, PatchSpec};
use std::io::Write;

fn main() {
    let mut args = std::env::args().skip(1);
    let mut pos = Vec::new();
    let (mut path, mut old_path, mut om, mut nm) = (None, None, 0o100_644u32, 0o100_644u32);
    let mut bm = BinaryMode::Git;
    let mut ctx = 3usize;
    let mut stats = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--path" => path = args.next(),
            "--old-path" => old_path = args.next(),
            "--old-mode" => {
                om = args
                    .next()
                    .and_then(|v| u32::from_str_radix(&v, 8).ok())
                    .unwrap_or(om)
            }
            "--new-mode" => {
                nm = args
                    .next()
                    .and_then(|v| u32::from_str_radix(&v, 8).ok())
                    .unwrap_or(nm)
            }
            "--binary" => {
                bm = if args.next().as_deref() == Some("refuse") {
                    BinaryMode::Refuse
                } else {
                    BinaryMode::Git
                }
            }
            "-U" => ctx = args.next().and_then(|v| v.parse().ok()).unwrap_or(3),
            "--stats" => stats = true,
            _ => pos.push(a),
        }
    }
    if pos.len() != 2 {
        eprintln!("usage: difffold-patch [options] BEFORE AFTER");
        std::process::exit(2);
    }
    let (Ok(before), Ok(after)) = (std::fs::read(&pos[0]), std::fs::read(&pos[1])) else {
        eprintln!("difffold-patch: cannot read inputs");
        std::process::exit(2);
    };
    let np = path.unwrap_or_else(|| pos[1].clone());
    let mut spec = PatchSpec::modify(&np);
    spec.old_path = old_path.unwrap_or_else(|| np.clone()).into_bytes();
    spec.old_mode = Some(om);
    spec.new_mode = Some(nm);
    spec.context = ctx;
    match make_patch(&spec, &before, &after, bm) {
        Outcome::Identical => {
            eprintln!("difffold-patch: identical");
            std::process::exit(3);
        }
        Outcome::Text { patch, stats: st } => {
            if stats {
                eprintln!(
                    "hunks={} added={} removed={} bytes={} capped={}",
                    st.hunks, st.added, st.removed, st.bytes, st.capped
                );
            }
            let _ = std::io::stdout().write_all(&patch);
        }
        Outcome::GitBinary { patch } => {
            let _ = std::io::stdout().write_all(&patch);
        }
        Outcome::Refused(why) => {
            eprintln!("difffold-patch: refused: {why}");
            std::process::exit(4);
        }
    }
}
