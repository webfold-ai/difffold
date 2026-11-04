//! usage: rt <diffs-dir>   Round-trips every before/after pair through real `git apply`, both directions.
use difffold::lines::Algo;
use difffold::unified::unified;
use std::process::Command;

fn apply(dir: &std::path::Path, base: &[u8], patch: &[u8], reverse: bool) -> Option<Vec<u8>> {
    std::fs::write(dir.join("f"), base).ok()?;
    std::fs::write(dir.join("p.patch"), patch).ok()?;
    let mut c = Command::new("git");
    c.current_dir(dir)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .args(["apply", "--whitespace=nowarn"]);
    if reverse {
        c.arg("--reverse");
    }
    let ok = c.arg("p.patch").output().ok()?.status.success();
    if ok {
        std::fs::read(dir.join("f")).ok()
    } else {
        None
    }
}

fn main() {
    let root = std::path::PathBuf::from(std::env::args().nth(1).unwrap());
    let tmp = std::env::temp_dir().join(format!("rt-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let (mut ok, mut bad, mut empty) = (0, 0, 0);
    for ds in std::fs::read_dir(&root)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
    {
        for fx in std::fs::read_dir(&ds)
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.is_dir())
        {
            let find = |p: &str| {
                std::fs::read_dir(&fx)
                    .unwrap()
                    .flatten()
                    .map(|e| e.path())
                    .find(|x| {
                        x.file_name()
                            .and_then(|f| f.to_str())
                            .is_some_and(|f| f.starts_with(p))
                    })
            };
            let (Some(bp), Some(ap)) = (find("before."), find("after.")) else {
                continue;
            };
            let (Ok(a), Ok(b)) = (std::fs::read(bp), std::fs::read(ap)) else {
                continue;
            };
            if a.len() > 2_000_000 || b.len() > 2_000_000 {
                continue;
            }
            for algo in [Algo::Minimal, Algo::Histogram] {
                let p = unified(&a, &b, "f", 3, algo);
                if p.is_empty() {
                    if a == b {
                        empty += 1
                    } else {
                        bad += 1;
                        eprintln!("empty patch for differing files {}", fx.display())
                    }
                    continue;
                }
                let fwd = apply(&tmp, &a, &p, false).is_some_and(|g| g == b);
                let rev = apply(&tmp, &b, &p, true).is_some_and(|g| g == a);
                if fwd && rev {
                    ok += 1
                } else {
                    bad += 1;
                    eprintln!("FAIL {:?} fwd={fwd} rev={rev} {}", algo, fx.display())
                }
            }
        }
    }
    println!("round trips ok={ok} (forward and reverse, minimal and histogram) failed={bad} identical-files={empty}");
}
