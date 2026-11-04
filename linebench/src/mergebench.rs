//! Three-way merge comparison with known answers.
//! usage: mergebench <diffs-dir> <out.csv> <mergiraf-binary|-> [max-scenarios]
//!
//! Scenarios are built from real before/after pairs. `base` is the before file. The change between
//! before and after is split into separated hunks.
//!   disjoint: left applies the even hunks, right the odd hunks. The correct merge is `after`.
//!   conflict: both sides rewrite the same hunk differently. A correct tool must not merge silently.
use difffold::lines::{diff_text, split_lines, Algo};
use difffold::merge::merge3;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy, PartialEq)]
enum Pick {
    Old,
    New,
    Alt,
}

struct Hunk {
    old: Vec<usize>,
    new: Vec<usize>,
}

enum Item {
    Eq(usize),
    Hunk(usize),
}

fn plan(a: &[u8], b: &[u8]) -> (Vec<Item>, Vec<Hunk>) {
    let d = diff_text(a, b);
    let (la, lb) = (split_lines(a), split_lines(b));
    let (mut items, mut hunks) = (Vec::new(), Vec::<Hunk>::new());
    let (mut i, mut j) = (0, 0);
    let mut open = false;
    while i < la.len() || j < lb.len() {
        if i < la.len() && d.deleted[i] {
            if !open {
                hunks.push(Hunk { old: vec![], new: vec![] });
                items.push(Item::Hunk(hunks.len() - 1));
                open = true;
            }
            hunks.last_mut().unwrap().old.push(i);
            i += 1;
        } else if j < lb.len() && d.inserted[j] {
            if !open {
                hunks.push(Hunk { old: vec![], new: vec![] });
                items.push(Item::Hunk(hunks.len() - 1));
                open = true;
            }
            hunks.last_mut().unwrap().new.push(j);
            j += 1;
        } else {
            open = false;
            items.push(Item::Eq(i));
            i += 1;
            j += 1;
        }
    }
    (items, hunks)
}

fn render(a: &[u8], b: &[u8], items: &[Item], hunks: &[Hunk], pick: &dyn Fn(usize) -> Pick) -> Vec<u8> {
    let (la, lb) = (split_lines(a), split_lines(b));
    let mut out = Vec::new();
    for it in items {
        match it {
            Item::Eq(i) => out.extend_from_slice(la[*i]),
            Item::Hunk(h) => match pick(*h) {
                Pick::Old => hunks[*h].old.iter().for_each(|&i| out.extend_from_slice(la[i])),
                Pick::New => hunks[*h].new.iter().for_each(|&j| out.extend_from_slice(lb[j])),
                Pick::Alt => out.extend_from_slice(format!("ALTERNATIVE REWRITE {h}\n").as_bytes()),
            },
        }
    }
    out
}

fn has_markers(t: &[u8]) -> bool {
    t.windows(8).any(|w| w == b"<<<<<<< ") || t.windows(7).any(|w| w == b"<<<<<<<")
}

fn run_merge(tool: &str, bin: &str, dir: &Path, ext: &str) -> Option<(Vec<u8>, bool)> {
    let (b, l, r, o) = (dir.join(format!("base{ext}")), dir.join(format!("left{ext}")), dir.join(format!("right{ext}")), dir.join(format!("out{ext}")));
    let _ = std::fs::remove_file(&o);
    match tool {
        "git-merge-file" => {
            let out = Command::new("git").env("GIT_CONFIG_GLOBAL", "/dev/null").env("GIT_CONFIG_SYSTEM", "/dev/null").args(["merge-file", "-p"]).arg(&l).arg(&b).arg(&r).output().ok()?;
            let code = out.status.code()?;
            if code < 0 || code > 127 {
                return None;
            }
            Some((out.stdout, code > 0))
        }
        "mergiraf" => {
            let out = Command::new(bin).args(["merge"]).arg(&b).arg(&l).arg(&r).arg("-o").arg(&o).output().ok()?;
            let text = std::fs::read(&o).ok()?;
            let conflicted = out.status.code() == Some(1) || has_markers(&text);
            Some((text, conflicted))
        }
        _ => None,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let root = PathBuf::from(&args[1]);
    let mut out = std::fs::File::create(&args[2]).unwrap();
    let mergiraf = args[3].clone();
    let cap: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(400);
    writeln!(out, "scenario,fixture,tool,outcome,us").unwrap();
    let tmp = std::env::temp_dir().join(format!("mb-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let mut n = 0;
    'all: for ds in std::fs::read_dir(&root).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
            let find = |p: &str| std::fs::read_dir(&fx).unwrap().flatten().map(|e| e.path()).find(|x| x.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(p)));
            let (Some(bp), Some(ap)) = (find("before."), find("after.")) else { continue };
            let fname = bp.file_name().unwrap().to_str().unwrap().to_string();
            let ext = match fname.split('.').nth(1) {
                Some(e @ ("java" | "go" | "c" | "rs" | "py" | "js" | "ts")) => format!(".{e}"),
                _ => continue,
            };
            let (Ok(a), Ok(b)) = (std::fs::read(&bp), std::fs::read(&ap)) else { continue };
            if a.len() > 300_000 || b.len() > 300_000 {
                continue;
            }
            let (items, hunks) = plan(&a, &b);
            if hunks.len() < 2 {
                continue;
            }
            let name = format!("{}/{}", ds.file_name().unwrap().to_string_lossy(), fx.file_name().unwrap().to_string_lossy());
            let scenarios: Vec<(&str, Vec<u8>, Vec<u8>, Option<Vec<u8>>)> = vec![
                ("disjoint", render(&a, &b, &items, &hunks, &|h| if h % 2 == 0 { Pick::New } else { Pick::Old }), render(&a, &b, &items, &hunks, &|h| if h % 2 == 1 { Pick::New } else { Pick::Old }), Some(b.clone())),
                ("conflict", render(&a, &b, &items, &hunks, &|h| if h == 0 { Pick::New } else { Pick::Old }), render(&a, &b, &items, &hunks, &|h| if h == 0 { Pick::Alt } else { Pick::Old }), None),
            ];
            for (sc, left, right, expect) in scenarios {
                std::fs::write(tmp.join(format!("base{ext}")), &a).unwrap();
                std::fs::write(tmp.join(format!("left{ext}")), &left).unwrap();
                std::fs::write(tmp.join(format!("right{ext}")), &right).unwrap();
                let judge = |text: &[u8], conflicted: bool| -> &'static str {
                    match (&expect, conflicted) {
                        (Some(e), false) => if text == e.as_slice() { "correct" } else { "silently_wrong" },
                        (Some(_), true) => "false_conflict",
                        (None, true) => "conflict_flagged",
                        (None, false) => "silently_wrong",
                    }
                };
                let t = std::time::Instant::now();
                let m = merge3(&a, &left, &right, Algo::Minimal);
                let us = t.elapsed().as_secs_f64() * 1e6;
                writeln!(out, "{sc},{name},difffold-merge3,{},{us:.0}", judge(&m.text, m.conflicts > 0)).unwrap();
                for (tool, bin) in [("git-merge-file", "git"), ("mergiraf", mergiraf.as_str())] {
                    if tool == "mergiraf" && mergiraf == "-" {
                        continue;
                    }
                    let t = std::time::Instant::now();
                    let r = run_merge(tool, bin, &tmp, &ext);
                    let us = t.elapsed().as_secs_f64() * 1e6;
                    let outcome = match r {
                        Some((text, c)) => judge(&text, c),
                        None => "tool_error",
                    };
                    writeln!(out, "{sc},{name},{tool},{outcome},{us:.0}").unwrap();
                }
            }
            n += 1;
            if n >= cap {
                break 'all;
            }
        }
    }
    eprintln!("{n} fixtures x 2 scenarios");
}
