//! Build-impact proxy: how often does a source change leave the exported interface unchanged?
//!
//! usage: abi_cutoff <diffs-dir> <out.csv>
//! Content-hash invalidation (what `bazel-diff` style target fingerprints do) treats every changed file as
//! changing all dependents. With early cutoff, dependents only rebuild when the exported interface
//! (class headers, non-private member signatures, non-private fields) changes. This reports the share of
//! changed Java files whose interface is unchanged, i.e. the dependent rebuilds early cutoff would avoid.
//! Bazel itself is not run here. The signature extraction is tree-sitter based and approximate.
use std::collections::BTreeSet;
use std::io::Write;
use std::path::PathBuf;
use tree_sitter::{Node, Parser};

fn text<'a>(n: Node, src: &'a [u8]) -> &'a str {
    std::str::from_utf8(&src[n.byte_range()]).unwrap_or("")
}

fn header(n: Node, src: &[u8], body_kind: &str) -> String {
    let end = n.child_by_field_name("body").filter(|b| b.kind() == body_kind || body_kind.is_empty()).map_or(n.end_byte(), |b| b.start_byte());
    String::from_utf8_lossy(&src[n.start_byte()..end]).split_whitespace().collect::<Vec<_>>().join(" ")
}

fn private(n: Node, src: &[u8]) -> bool {
    (0..n.child_count()).filter_map(|i| n.child(i)).any(|c| c.kind() == "modifiers" && text(c, src).split_whitespace().any(|w| w == "private"))
}

fn walk(n: Node, src: &[u8], owner: &str, out: &mut BTreeSet<String>) {
    let mut next_owner = owner.to_string();
    match n.kind() {
        "class_declaration" | "interface_declaration" | "enum_declaration" | "record_declaration" | "annotation_type_declaration" => {
            let h = header(n, src, "");
            let name = n.child_by_field_name("name").map_or(String::new(), |x| text(x, src).to_string());
            next_owner = format!("{owner}.{name}");
            out.insert(format!("type:{owner}::{h}"));
        }
        "method_declaration" | "constructor_declaration" if !private(n, src) => {
            out.insert(format!("method:{owner}::{}", header(n, src, "")));
        }
        "field_declaration" | "constant_declaration" if !private(n, src) => {
            out.insert(format!("field:{owner}::{}", String::from_utf8_lossy(&src[n.byte_range()]).split_whitespace().collect::<Vec<_>>().join(" ")));
        }
        "import_declaration" | "package_declaration" => {
            out.insert(format!("import:{}", text(n, src)));
        }
        _ => {}
    }
    (0..n.child_count()).filter_map(|i| n.child(i)).for_each(|c| walk(c, src, &next_owner, out));
}

fn abi(src: &[u8], p: &mut Parser) -> Option<BTreeSet<String>> {
    let t = p.parse(src, None)?;
    let mut s = BTreeSet::new();
    walk(t.root_node(), src, "", &mut s);
    Some(s)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let root = PathBuf::from(&a[1]);
    let mut out = std::fs::File::create(&a[2]).unwrap();
    writeln!(out, "fixture,changed,abi_changed,abi_added,abi_removed").unwrap();
    let mut p = Parser::new();
    p.set_language(&tree_sitter_java::LANGUAGE.into()).unwrap();
    let (mut files, mut cut) = (0, 0);
    for ds in std::fs::read_dir(&root).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
            let find = |pre: &str| std::fs::read_dir(&fx).unwrap().flatten().map(|e| e.path()).find(|x| x.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(pre) && f.contains(".java")));
            let (Some(bp), Some(ap)) = (find("before."), find("after.")) else { continue };
            let (Ok(b), Ok(af)) = (std::fs::read(bp), std::fs::read(ap)) else { continue };
            if b == af {
                continue;
            }
            let (Some(sb), Some(sa)) = (abi(&b, &mut p), abi(&af, &mut p)) else { continue };
            let changed = sb != sa;
            files += 1;
            cut += usize::from(!changed);
            writeln!(out, "{}/{},1,{},{},{}", ds.file_name().unwrap().to_string_lossy(), fx.file_name().unwrap().to_string_lossy(), u8::from(changed), sa.difference(&sb).count(), sb.difference(&sa).count()).unwrap();
        }
    }
    println!("{files} changed java files; interface unchanged (early cutoff applies) in {cut} = {:.1}%", 100.0 * cut as f64 / files.max(1) as f64);
}
