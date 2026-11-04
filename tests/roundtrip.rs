//! Round trip through real `git apply`: forward and reverse, on edge cases that break naive emitters.
use difffold::lines::Algo;
use difffold::unified::unified;
use std::process::Command;

fn git_apply(base: &[u8], patch: &[u8], reverse: bool) -> Result<Vec<u8>, String> {
    let dir = std::env::temp_dir().join(format!(
        "dfrt-{}-{}",
        std::process::id(),
        base.len() ^ patch.len() << 7
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("f"), base).unwrap();
    std::fs::write(dir.join("p.patch"), patch).unwrap();
    let run = |extra: &[&str]| {
        let mut c = Command::new("git");
        c.current_dir(&dir)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .arg("apply")
            .arg("--whitespace=nowarn");
        if reverse {
            c.arg("--reverse");
        }
        c.args(extra).arg("p.patch").output().unwrap()
    };
    let chk = run(&["--check"]);
    if !chk.status.success() {
        return Err(format!("check: {}", String::from_utf8_lossy(&chk.stderr)));
    }
    let out = run(&[]);
    if !out.status.success() {
        return Err(format!("apply: {}", String::from_utf8_lossy(&out.stderr)));
    }
    let got = std::fs::read(dir.join("f")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    Ok(got)
}

fn check(a: &[u8], b: &[u8]) {
    for algo in [Algo::Minimal, Algo::Histogram] {
        let p = unified(a, b, "f", 3, algo);
        if p.is_empty() {
            assert_eq!(a, b);
            continue;
        }
        assert_eq!(
            git_apply(a, &p, false).unwrap_or_else(|e| panic!(
                "forward {e}\n a={a:?} b={b:?}\n{}",
                String::from_utf8_lossy(&p)
            )),
            b,
            "forward a={a:?} b={b:?}"
        );
        assert_eq!(
            git_apply(b, &p, true).unwrap_or_else(|e| panic!("reverse {e}\n a={a:?} b={b:?}")),
            a,
            "reverse a={a:?} b={b:?}"
        );
    }
}

#[test]
fn edge_cases() {
    let long: Vec<u8> = (0..60)
        .flat_map(|i| format!("row {i}\n").into_bytes())
        .collect();
    let mut edited = long.clone();
    edited.splice(0..0, b"first\n".iter().copied());
    let cases: Vec<(&[u8], &[u8])> = vec![
        (b"", b"a\n"),
        (b"a\n", b""),
        (b"a\nb\nc\n", b"x\ny\nz\n"),
        (b"a\nb\nc\n", b"z\na\nb\nc\n"),
        (b"a\nb\nc\n", b"a\nb\nc\nz\n"),
        (b"a\nb\nc\n", b"a\nb\nc"),
        (b"a\nb\nc", b"a\nb\nc\n"),
        (b"a\nb\nc", b"a\nb\nd"),
        (b"a\r\nb\r\n", b"a\nb\n"),
        (b"a\r\nb\r\n", b"a\r\nc\r\n"),
        (b"x\nx\nx\nx\n", b"x\nx\ny\nx\nx\n"),
        (b"a\n\n\nb\n", b"a\n\nb\n"),
        (b"\xff\xfe\n\0\n", b"\xff\xfe\n\0\n\x80\n"),
        (b"same\n", b"same\n"),
        (&long, &edited),
    ];
    for (a, b) in cases {
        check(a, b);
    }
}

#[test]
fn adjacent_edits_with_overlapping_context() {
    let a: Vec<u8> = (0..40)
        .flat_map(|i| format!("l{i}\n").into_bytes())
        .collect();
    let mut b = a.clone();
    // Two edits five lines apart so their three-line contexts overlap and merge into one hunk.
    b.splice(0..0, b"A\n".iter().copied());
    let tail = b.len();
    b.splice(tail / 2..tail / 2, b"B\n".iter().copied());
    check(&a, &b);
}

fn git_apply_named(
    base: Option<&[u8]>,
    patch: &[u8],
    file: &str,
) -> Result<Option<Vec<u8>>, String> {
    let dir = std::env::temp_dir().join(format!("dfrt2-{}-{}", std::process::id(), patch.len()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    if let Some(b) = base {
        std::fs::write(dir.join(file), b).unwrap();
    }
    std::fs::write(dir.join("p.patch"), patch).unwrap();
    let out = Command::new("git")
        .current_dir(&dir)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .args(["apply", "--whitespace=nowarn", "p.patch"])
        .output()
        .unwrap();
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).into_owned());
    }
    let got = std::fs::read(dir.join(file)).ok();
    let _ = std::fs::remove_dir_all(&dir);
    Ok(got)
}

#[test]
fn filenames_with_special_characters() {
    for name in ["a\tb", "q\"uote", "back\\slash", "uni\u{e9}code", "sp ace"] {
        let (a, b) = (b"x\ny\n".as_slice(), b"x\nz\n".as_slice());
        let p = difffold::unified::unified(a, b, name, 3, Algo::Minimal);
        let got =
            git_apply_named(Some(a), &p, name).unwrap_or_else(|e| panic!("name {name:?}: {e}"));
        assert_eq!(got.as_deref(), Some(b), "name {name:?}");
    }
}

#[test]
fn creation_and_deletion_headers() {
    use difffold::unified::{unified_with, Kind};
    let content = b"one\ntwo\n".as_slice();
    let create = unified_with(
        b"",
        content,
        "new.txt",
        3,
        Algo::Minimal,
        Kind::Create,
        "100644",
    );
    assert_eq!(
        git_apply_named(None, &create, "new.txt")
            .unwrap()
            .as_deref(),
        Some(content)
    );
    let empty_create = unified_with(
        b"",
        b"",
        "empty.txt",
        3,
        Algo::Minimal,
        Kind::Create,
        "100644",
    );
    assert_eq!(
        git_apply_named(None, &empty_create, "empty.txt")
            .unwrap()
            .as_deref(),
        Some(b"".as_slice())
    );
    let delete = unified_with(
        content,
        b"",
        "gone.txt",
        3,
        Algo::Minimal,
        Kind::Delete,
        "100644",
    );
    assert_eq!(
        git_apply_named(Some(content), &delete, "gone.txt").unwrap(),
        None,
        "deletion must remove the file"
    );
}
