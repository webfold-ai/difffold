//! The unified patches the bindings return must be accepted by real `git apply`, forwards and in
//! reverse, and rebuild the exact bytes. This is the contract `difffold::unified` states; here it is
//! checked through the bindings' own function, on inputs that stress the format. A patch with no
//! context lines (`context = 0`) needs `git apply --unidiff-zero`; that is Git's rule, and is applied here.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use difffold_bindings::api::unified_patch;

fn git_available() -> bool {
    Command::new("git")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

struct Dir(PathBuf);
impl Dir {
    fn new(tag: &str) -> Self {
        let p =
            std::env::temp_dir().join(format!("difffold-bindings-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        fs::create_dir_all(&p).expect("mkdir");
        let ok = Command::new("git")
            .args(["init", "-q"])
            .current_dir(&p)
            .status()
            .expect("git init");
        assert!(ok.success());
        Self(p)
    }
}
impl Drop for Dir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn git(dir: &Dir, args: &[&str]) -> std::process::Output {
    Command::new("git")
        .args(args)
        .current_dir(&dir.0)
        .output()
        .expect("git")
}

/// Apply the patch to `old` and require `new`; then reverse it and require `old` again.
fn round_trip(tag: &str, name: &str, old: &[u8], new: &[u8], ctx: usize, algorithm: &str) {
    let patch = unified_patch(old, new, name, ctx, algorithm).expect("patch");
    if old == new {
        assert!(patch.is_empty(), "{tag}: equal texts give an empty patch");
        return;
    }
    let dir = Dir::new(tag);
    let file = dir.0.join(name);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("mkdir");
    }
    fs::write(&file, old).expect("write old");
    fs::write(dir.0.join("p.patch"), &patch).expect("write patch");

    // Git refuses a patch with no context lines unless told to expect one.
    let zero: &[&str] = if ctx == 0 { &["--unidiff-zero"] } else { &[] };
    let run = |extra: &[&str]| {
        let mut args = vec!["apply"];
        args.extend_from_slice(zero);
        args.extend_from_slice(extra);
        args.push("p.patch");
        git(&dir, &args)
    };
    let check = run(&["--check"]);
    assert!(
        check.status.success(),
        "{tag}: --check failed: {}\n{}",
        String::from_utf8_lossy(&check.stderr),
        String::from_utf8_lossy(&patch)
    );
    let applied = run(&[]);
    assert!(
        applied.status.success(),
        "{tag}: apply failed: {}",
        String::from_utf8_lossy(&applied.stderr)
    );
    assert_eq!(fs::read(&file).expect("read"), new, "{tag}: forward");
    let reversed = run(&["--reverse"]);
    assert!(
        reversed.status.success(),
        "{tag}: reverse failed: {}",
        String::from_utf8_lossy(&reversed.stderr)
    );
    assert_eq!(fs::read(&file).expect("read"), old, "{tag}: reverse");
}

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
}

fn random_text(rng: &mut Rng, crlf: bool, final_newline: bool) -> Vec<u8> {
    let n = rng.below(30);
    let mut t = Vec::new();
    for i in 0..n {
        t.extend_from_slice(format!("row {}", rng.below(7)).as_bytes());
        if i + 1 < n || final_newline {
            t.extend_from_slice(if crlf { b"\r\n" } else { b"\n" });
        }
    }
    t
}

#[test]
fn random_texts_round_trip_through_git_apply() {
    if !git_available() {
        eprintln!("skipping: git not found");
        return;
    }
    let mut rng = Rng(11);
    for round in 0..60 {
        let crlf = round % 5 == 0;
        let old = random_text(&mut rng, crlf, round % 3 != 0);
        let new = random_text(&mut rng, crlf, round % 4 != 0);
        let ctx = (round % 5) as usize;
        let algorithm = if round % 2 == 0 {
            "minimal"
        } else {
            "histogram"
        };
        round_trip(&format!("rand{round}"), "f.txt", &old, &new, ctx, algorithm);
    }
}

#[test]
fn awkward_cases_round_trip() {
    if !git_available() {
        eprintln!("skipping: git not found");
        return;
    }
    // No newline at the end on either side, or only one.
    round_trip("nonl-a", "f", b"a\nb", b"a\nb\n", 3, "minimal");
    round_trip("nonl-b", "f", b"a\nb\n", b"a\nb", 3, "minimal");
    round_trip("nonl-c", "f", b"a\nb", b"a\nc", 3, "minimal");
    // Empty on one side (git treats a patch to or from an empty file like any other).
    round_trip("empty-old", "f", b"", b"x\ny\n", 3, "minimal");
    round_trip("empty-new", "f", b"x\ny\n", b"", 3, "minimal");
    // Mixed line endings, a bare CR, a line that starts like a hunk header, a very long line.
    round_trip(
        "crlf",
        "f",
        b"a\r\nb\r\nc\n",
        b"a\r\nX\r\nc\n",
        3,
        "minimal",
    );
    round_trip(
        "hunk-like",
        "f",
        b"@@ -1 +1 @@\n--- a\n+++ b\n",
        b"@@ -1 +1 @@\n--- a\n+++ c\n",
        3,
        "minimal",
    );
    let long = "z".repeat(200_000);
    round_trip(
        "long",
        "f",
        format!("a\n{long}\nb\n").as_bytes(),
        format!("a\n{long}!\nb\n").as_bytes(),
        3,
        "minimal",
    );
    // Zero context.
    round_trip(
        "ctx0",
        "f",
        b"1\n2\n3\n4\n5\n",
        b"1\nX\n3\nY\n5\n",
        0,
        "minimal",
    );
    // File names Git has to quote or that sit in a directory.
    round_trip("dir", "src/lib/f.rs", b"a\n", b"b\n", 3, "minimal");
    round_trip("space", "my file.txt", b"a\n", b"b\n", 3, "minimal");
    round_trip("quote", "q\"uote.txt", b"a\n", b"b\n", 3, "minimal");
    round_trip("tab", "tab\tname.txt", b"a\n", b"b\n", 3, "minimal");
    round_trip("unicode", "naïve-日本.txt", b"a\n", b"b\n", 3, "minimal");
}

#[test]
fn a_binary_looking_input_is_still_a_valid_patch_for_text_lines() {
    if !git_available() {
        eprintln!("skipping: git not found");
        return;
    }
    // Bytes that are not UTF-8 but contain no NUL: git applies these as text.
    round_trip(
        "latin1",
        "f",
        b"caf\xe9\nx\n",
        b"caf\xe9\ny\n",
        3,
        "minimal",
    );
}
