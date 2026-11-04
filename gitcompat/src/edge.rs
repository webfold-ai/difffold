//! Handwritten edge cases for the byte-certificate round trip.

use crate::patch::{BinaryMode, PatchSpec};

/// What the generator is expected to do with the case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expect {
    /// A text patch that git applies to the exact after-bytes.
    Text,
    /// A binary patch from git itself.
    GitBinary,
    /// Same bytes and metadata: empty patch.
    Identical,
    /// An explicit refusal.
    Refused,
}

/// One case.
pub struct Case {
    pub name: &'static str,
    pub before: Vec<u8>,
    pub after: Vec<u8>,
    pub spec: PatchSpec,
    pub binary: BinaryMode,
    pub expect: Expect,
}

fn c(name: &'static str, before: &[u8], after: &[u8]) -> Case {
    Case {
        name,
        before: before.to_vec(),
        after: after.to_vec(),
        spec: PatchSpec::modify("f.txt"),
        binary: BinaryMode::Git,
        expect: Expect::Text,
    }
}

fn lines(n: usize, f: impl Fn(usize) -> String) -> Vec<u8> {
    let mut v = Vec::new();
    for i in 0..n {
        v.extend_from_slice(f(i).as_bytes());
        v.push(b'\n');
    }
    v
}

/// Every handwritten case.
#[must_use]
pub fn cases() -> Vec<Case> {
    let mut v = vec![
        c("crlf_edit", b"a\r\nb\r\nc\r\n", b"a\r\nB\r\nc\r\n"),
        c("crlf_to_lf", b"a\r\nb\r\nc\r\n", b"a\nb\nc\n"),
        c("lf_to_crlf", b"a\nb\nc\n", b"a\r\nb\r\nc\r\n"),
        c("mixed_endings", b"a\r\nb\nc\r\nd", b"a\r\nb\r\nc\nd"),
        c("cr_only_lines", b"a\rb\rc", b"a\rb\rX"),
        c("crlf_no_final_newline", b"a\r\nb", b"a\r\nc"),
        c("trailing_cr_at_eof", b"a\r\nb\r", b"a\r\nb\r\n"),
        c("no_final_nl_both", b"a\nb", b"a\nc"),
        c("no_final_nl_before_only", b"a\nb", b"a\nb\n"),
        c("no_final_nl_after_only", b"a\nb\n", b"a\nb"),
        c("no_final_nl_as_context", b"a\nb\nc", b"X\nb\nc"),
        c(
            "no_final_nl_both_same_last_line",
            b"a\nb\nlast",
            b"a\nB\nlast",
        ),
        c("empty_to_nonempty", b"", b"hello\nworld\n"),
        c("nonempty_to_empty", b"hello\nworld\n", b""),
        c("empty_to_nonempty_no_nl", b"", b"x"),
        c("nonempty_no_nl_to_empty", b"x", b""),
        c("one_line_changed", b"x\n", b"y\n"),
        c("one_line_no_nl_changed", b"x", b"y"),
        c("one_line_add_nl", b"x", b"x\n"),
        c("only_newline_to_empty_line_pair", b"\n", b"\n\n"),
        c("blank_lines_only", b"\n\n\n\n", b"\n\n"),
        c("whitespace_trailing", b"a \nb\t\nc\n", b"a\nb\nc\n"),
        c(
            "whitespace_indent_tab_to_space",
            b"\tint x;\n\tint y;\n",
            b"    int x;\n    int y;\n",
        ),
        c("whitespace_only_file", b"  \n", b"   \n"),
        c("whitespace_blank_line_added", b"a\nb\n", b"a\n\nb\n"),
        c(
            "non_utf8_latin1",
            b"caf\xe9\nna\xefve\n",
            b"caf\xe9\nna\xefve!\n",
        ),
        c(
            "non_utf8_invalid_sequence",
            b"\xff\xfe\xfd\nx\n",
            b"\xff\xfe\xfc\nx\n",
        ),
        c("utf8_bom", b"\xef\xbb\xbfa\nb\n", b"\xef\xbb\xbfa\nc\n"),
        c(
            "utf8_multibyte",
            "h\u{e9}llo\n\u{4e16}\u{754c}\n".as_bytes(),
            "h\u{e9}llo\n\u{4e16}\u{754c}!\n".as_bytes(),
        ),
        c(
            "content_looks_like_patch",
            b"--- a/x\n+++ b/x\n@@ -1 +1 @@\n-old\n+new\n",
            b"--- a/x\n+++ b/y\n@@ -1 +1 @@\n-old\n+newer\n",
        ),
        c(
            "content_is_no_newline_marker",
            b"\\ No newline at end of file\nz\n",
            b"\\ No newline at end of file\nzz\n",
        ),
        c(
            "content_starts_with_diff_git",
            b"diff --git a/x b/x\nq\n",
            b"diff --git a/x b/x\nr\n",
        ),
        c("identical", b"same\nbytes\n", b"same\nbytes\n"),
        c("identical_empty", b"", b""),
        c("identical_no_nl", b"abc", b"abc"),
        c(
            "repeated_lines",
            &lines(200, |_| "same".into()),
            &lines(150, |_| "same".into()),
        ),
        c(
            "periodic",
            &lines(300, |i| format!("{}", i % 3)),
            &lines(310, |i| format!("{}", (i + 1) % 3)),
        ),
        c("swap_blocks", &lines(100, |i| format!("line {i}")), &{
            let mut a = lines(50, |i| format!("line {}", i + 50));
            a.extend(lines(50, |i| format!("line {i}")));
            a
        }),
        c(
            "all_different",
            &lines(2000, |i| format!("old {i}")),
            &lines(2000, |i| format!("new {i}")),
        ),
        c(
            "scattered_edits",
            &lines(10_000, |i| format!("row {i}")),
            &lines(10_000, |i| {
                if i % 97 == 0 {
                    format!("ROW {i}")
                } else {
                    format!("row {i}")
                }
            }),
        ),
    ];
    let long = |ch: u8, n: usize| {
        let mut x = vec![ch; n];
        x.push(b'\n');
        x
    };
    let mut lb = long(b'a', 1 << 20);
    lb.extend_from_slice(b"tail\n");
    let mut la = long(b'a', 1 << 20);
    la[500_000] = b'b';
    la.extend_from_slice(b"tail\n");
    v.push(c("very_long_line_1mib", &lb, &la));
    let mut lb2 = long(b'x', 300_000);
    lb2.extend_from_slice(&long(b'y', 300_000));
    let mut la2 = long(b'y', 300_000);
    la2.extend_from_slice(&long(b'x', 300_000));
    v.push(c("very_long_lines_swapped", &lb2, &la2));
    let mut nolf = vec![b'z'; 200_000];
    let nolf_b = nolf.clone();
    nolf.push(b'!');
    v.push(c("very_long_single_line_no_nl", &nolf_b, &nolf));

    // Metadata cases.
    let mut m = c(
        "mode_change_only",
        b"#!/bin/sh\necho hi\n",
        b"#!/bin/sh\necho hi\n",
    );
    m.spec.new_mode = Some(0o100_755);
    v.push(m);
    let mut m = c(
        "mode_change_and_content",
        b"#!/bin/sh\necho hi\n",
        b"#!/bin/sh\necho bye\n",
    );
    m.spec.new_mode = Some(0o100_755);
    v.push(m);
    let mut m = c("mode_remove_exec", b"x\n", b"y\n");
    m.spec.old_mode = Some(0o100_755);
    m.spec.new_mode = Some(0o100_644);
    v.push(m);
    let mut m = c("new_file", b"", b"brand new\nfile\n");
    m.spec.old_mode = None;
    v.push(m);
    let mut m = c("new_file_empty", b"", b"");
    m.spec.old_mode = None;
    v.push(m);
    let mut m = c("new_file_no_nl_exec", b"", b"echo");
    m.spec.old_mode = None;
    m.spec.new_mode = Some(0o100_755);
    v.push(m);
    let mut m = c("deleted_file", b"gone\nsoon\n", b"");
    m.spec.new_mode = None;
    v.push(m);
    let mut m = c("deleted_file_empty", b"", b"");
    m.spec.new_mode = None;
    v.push(m);
    let mut m = c("rename_pure", b"same\ncontent\n", b"same\ncontent\n");
    m.spec.new_path = b"renamed.txt".to_vec();
    v.push(m);
    let mut m = c(
        "rename_with_edit",
        b"one\ntwo\nthree\nfour\n",
        b"one\n2\nthree\nfour\n",
    );
    m.spec.new_path = b"dir/renamed.txt".to_vec();
    v.push(m);
    let mut m = c("rename_and_mode", b"one\ntwo\n", b"one\ntwo\nthree\n");
    m.spec.new_path = b"r2.txt".to_vec();
    m.spec.new_mode = Some(0o100_755);
    v.push(m);
    let mut m = c("path_with_space", b"a\n", b"b\n");
    m.spec.old_path = b"my dir/my file.txt".to_vec();
    m.spec.new_path = b"my dir/my file.txt".to_vec();
    v.push(m);
    let mut m = c("path_with_unicode_and_quote", b"a\n", b"b\n");
    m.spec.old_path = "d\u{e9}j\u{e0}/\"q\".txt".as_bytes().to_vec();
    m.spec.new_path = m.spec.old_path.clone();
    v.push(m);
    let mut m = c("rename_path_with_space", b"a\nb\n", b"a\nc\n");
    m.spec.old_path = b"old name.txt".to_vec();
    m.spec.new_path = b"new name.txt".to_vec();
    v.push(m);

    // Binary cases.
    let mut b = c("nul_bytes_modify", b"a\0b\0c\n", b"a\0B\0c\n");
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c("nul_bytes_binary_refuse", b"a\0b\n", b"a\0c\n");
    b.binary = BinaryMode::Refuse;
    b.expect = Expect::Refused;
    v.push(b);
    let mut b = c("nul_only_after", b"text\n", b"te\0xt\n");
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c("nul_only_before", b"te\0xt\n", b"text\n");
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c(
        "binary_random_256",
        &(0..=255u8).collect::<Vec<_>>(),
        &(0..=255u8).rev().collect::<Vec<_>>(),
    );
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c("binary_new_file", b"", b"\0\x01\x02");
    b.spec.old_mode = None;
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c("binary_deleted", b"\0\x01\x02", b"");
    b.spec.new_mode = None;
    b.expect = Expect::GitBinary;
    v.push(b);
    let mut b = c("binary_identical_mode_change", b"\0\0\0", b"\0\0\0");
    b.spec.new_mode = Some(0o100_755);
    b.expect = Expect::Text;
    v.push(b);
    let mut b = c("binary_identical", b"\0\0\0", b"\0\0\0");
    b.expect = Expect::Identical;
    v.push(b);
    for x in &mut v {
        if x.name.starts_with("identical") {
            x.expect = Expect::Identical;
        }
    }
    v
}
