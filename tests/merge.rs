use difffold::lines::Algo;
use difffold::merge::merge3;

#[test]
fn disjoint_edits_merge_cleanly() {
    let base = b"a\nb\nc\nd\ne\nf\ng\n";
    let left = b"A\nb\nc\nd\ne\nf\ng\n";
    let right = b"a\nb\nc\nd\ne\nf\nG\n";
    let m = merge3(base, left, right, Algo::Minimal);
    assert_eq!(m.conflicts, 0);
    assert_eq!(m.text, b"A\nb\nc\nd\ne\nf\nG\n");
}

#[test]
fn same_change_on_both_sides_is_not_a_conflict() {
    let m = merge3(b"a\nb\nc\n", b"a\nX\nc\n", b"a\nX\nc\n", Algo::Minimal);
    assert_eq!(m.conflicts, 0);
    assert_eq!(m.text, b"a\nX\nc\n");
}

#[test]
fn different_changes_to_one_line_conflict() {
    let m = merge3(b"a\nb\nc\n", b"a\nX\nc\n", b"a\nY\nc\n", Algo::Minimal);
    assert_eq!(m.conflicts, 1);
    assert!(m.text.windows(7).any(|w| w == b"<<<<<<<"));
}

#[test]
fn one_sided_edit_and_identity() {
    let b = b"x\ny\nz\n";
    assert_eq!(merge3(b, b, b"x\nQ\nz\n", Algo::Minimal).text, b"x\nQ\nz\n");
    assert_eq!(merge3(b, b, b, Algo::Minimal).text, b);
}
