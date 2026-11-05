//! Exports the tree-sitter ASTs of two Java files as postorder tree files for the `fastted` benchmark.
//!
//! usage: fastted_export <before.java> <after.java> <outdir>
//!
//! Writes `<outdir>/a.tree` and `<outdir>/b.tree`. Each file is a line with the node count `n`, then `n`
//! lines `label parent` in postorder (children before their parent), where `parent` is the postorder index
//! of the parent or `-1` for the root. Labels are interned per pair with the same rule as `ted_map`: leaves
//! are identified by kind and text, internal nodes by kind alone, so both trees share one label space.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;
use tree_sitter::{Node, Parser};

#[derive(Default)]
struct Interner {
    labels: HashMap<(u16, Option<Vec<u8>>), u32>,
}

impl Interner {
    fn label(&mut self, kind: u16, text: Option<&[u8]>) -> u32 {
        let next = u32::try_from(self.labels.len()).expect("label count fits in u32");
        *self
            .labels
            .entry((kind, text.map(<[u8]>::to_vec)))
            .or_insert(next)
    }
}

/// Appends `node` and its descendants to `rows` in postorder and returns the index of `node`.
fn emit(node: Node, src: &[u8], it: &mut Interner, rows: &mut Vec<(u32, i64)>) -> usize {
    let mut kids = Vec::with_capacity(node.child_count());
    let label = if node.child_count() == 0 {
        it.label(node.kind_id(), Some(&src[node.byte_range()]))
    } else {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            kids.push(emit(child, src, it, rows));
        }
        it.label(node.kind_id(), None)
    };
    let idx = rows.len();
    rows.push((label, -1));
    for k in kids {
        rows[k].1 = i64::try_from(idx).expect("index fits in i64");
    }
    idx
}

fn tree_text(path: &Path, it: &mut Interner, parser: &mut Parser) -> String {
    let src = std::fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let tree = parser
        .parse(&src, None)
        .unwrap_or_else(|| panic!("parse failed: {}", path.display()));
    let mut rows = Vec::new();
    emit(tree.root_node(), &src, it, &mut rows);
    let mut out = String::with_capacity(rows.len() * 12);
    writeln!(out, "{}", rows.len()).expect("write to string");
    for (label, parent) in rows {
        writeln!(out, "{label} {parent}").expect("write to string");
    }
    out
}

fn run() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [before, after, outdir] = args.as_slice() else {
        panic!("usage: fastted_export <before.java> <after.java> <outdir>");
    };
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_java::LANGUAGE.into())
        .expect("tree-sitter-java grammar loads");
    let mut it = Interner::default();
    let a = tree_text(Path::new(before), &mut it, &mut parser);
    let b = tree_text(Path::new(after), &mut it, &mut parser);
    std::fs::create_dir_all(outdir).expect("create output directory");
    std::fs::write(Path::new(outdir).join("a.tree"), a).expect("write a.tree");
    std::fs::write(Path::new(outdir).join("b.tree"), b).expect("write b.tree");
}

fn main() {
    // Deep ASTs recurse once per level, so run on a thread with a generous stack.
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(run)
        .expect("spawn export thread")
        .join()
        .expect("export thread completes");
}
