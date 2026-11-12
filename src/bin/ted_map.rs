//! Prints the node mapping difffold computes for two Java files as JSON, for external benchmark
//! adapters (see tools/diffbenchmark_adapter/).
//!
//! usage: ted_map [--algo ted|topdown|refine] <before.java> <after.java>
//!
//! Output: {"pairs":[[bs,be,kind,as,ae,kind], ...],"nb":N,"na":M,"bn":[[s,e],...],"an":[[s,e],...]}, byte ranges and tree-sitter kinds
//! of matched node pairs, in preorder of the before tree. `topdown` is the ordered top-down mapping
//! implied by the certified script (`diff_checked` + `correspondence`); `ted` is the optimal general
//! tree edit mapping (`ted_mapping`); `refine` is `topdown` followed by the cross-level refinement
//! (`difffold::refine`, all phases).

use difffold::mapping::correspondence;
use difffold::refine::{refine, Flat, Options};
use difffold::ted::{ted_mapping, PostTree};
use difffold::ts::{convert, Interner, Tree, NIL};
use difffold::{diff_checked, Arena};
use std::fmt::Write as _;
use tree_sitter::Parser;

/// Optimal general tree edit mapping (deleting a node promotes its children) as preorder index pairs.
fn ted_pairs(bt: &Tree, at: &Tree) -> Vec<(u32, u32)> {
    let post = |t: &Tree| -> (Vec<u32>, Vec<u32>) {
        let (mut order, mut stack) = (Vec::with_capacity(t.kind.len()), vec![(0u32, 0usize)]);
        while let Some((v, next)) = stack.pop() {
            if next < t.kids[v as usize].len() {
                stack.push((v, next + 1));
                stack.push((t.kids[v as usize][next], 0));
            } else {
                order.push(v);
            }
        }
        let mut pos = vec![0u32; t.kind.len()];
        for (k, &v) in order.iter().enumerate() {
            pos[v as usize] = k as u32;
        }
        (order, pos)
    };
    let build = |t: &Tree, order: &[u32], pos: &[u32]| -> PostTree {
        let label: Vec<u32> = order.iter().map(|&v| t.label[v as usize]).collect();
        let kids: Vec<Vec<u32>> = order
            .iter()
            .map(|&v| {
                t.kids[v as usize]
                    .iter()
                    .map(|&c| pos[c as usize])
                    .collect()
            })
            .collect();
        PostTree::from_kids(label, &kids)
    };
    let ((oa, pa), (ob, pb)) = (post(bt), post(at));
    let m = ted_mapping(&build(bt, &oa, &pa), &build(at, &ob, &pb));
    m.pairs
        .iter()
        .map(|&(x, y)| (oa[x as usize - 1], ob[y as usize - 1]))
        .collect()
}

/// Anonymous tree-sitter kinds include quotes and backslashes, so kinds need JSON escaping.
fn json_str(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn fail(msg: &str) -> ! {
    eprintln!("ted_map: {msg}");
    std::process::exit(2);
}

fn main() {
    let mut algo = String::from("topdown");
    let mut files = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        if a == "--algo" {
            algo = args.next().unwrap_or_else(|| fail("--algo needs a value"));
        } else {
            files.push(a);
        }
    }
    if files.len() != 2 || !matches!(algo.as_str(), "ted" | "topdown" | "refine") {
        fail("usage: ted_map [--algo ted|topdown|refine] <before.java> <after.java>");
    }
    let (bs, as_) = (
        std::fs::read(&files[0]).unwrap_or_else(|e| fail(&e.to_string())),
        std::fs::read(&files[1]).unwrap_or_else(|e| fail(&e.to_string())),
    );
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_java::LANGUAGE.into())
        .unwrap();
    let tb = parser
        .parse(&bs, None)
        .unwrap_or_else(|| fail("parse failed"));
    let ta = parser
        .parse(&as_, None)
        .unwrap_or_else(|| fail("parse failed"));
    let mut arena = Arena::new();
    let mut it = Interner::default();
    let (mut bt, mut at) = (Tree::default(), Tree::default());
    let x = convert(tb.root_node(), &bs, &mut arena, &mut it, &mut bt, NIL);
    let y = convert(ta.root_node(), &as_, &mut arena, &mut it, &mut at, NIL);
    let pairs: Vec<(u32, u32)> = if algo == "ted" {
        ted_pairs(&bt, &at)
    } else {
        let res = diff_checked(&mut arena, x, y);
        let corr = correspondence(&arena, x, y, &res.edit);
        if algo == "refine" {
            let (bf, af) = (
                Flat::from_arena(&arena, x, |l| it.kind_of(l)),
                Flat::from_arena(&arena, y, |l| it.kind_of(l)),
            );
            let (m, _) = refine(&arena, &bf, &af, &corr, &Options::FULL);
            m.pairs().collect()
        } else {
            corr.pairs.iter().map(|p| (p.before, p.after)).collect()
        }
    };
    let mut out = String::with_capacity(pairs.len() * 48 + 64);
    out.push_str("{\"pairs\":[");
    for (i, &(b, a)) in pairs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let ((bs_, be), (as2, ae)) = (bt.span[b as usize], at.span[a as usize]);
        let _ = write!(
            out,
            "[{bs_},{be},{},{as2},{ae},{}]",
            json_str(bt.kind[b as usize]),
            json_str(at.kind[a as usize])
        );
    }
    // All node ranges of both trees, so adapters can tell which target-tree nodes have no counterpart at all.
    let ranges = |t: &Tree| {
        t.span
            .iter()
            .map(|&(s, e)| format!("[{s},{e}]"))
            .collect::<Vec<_>>()
            .join(",")
    };
    let _ = write!(
        out,
        "],\"nb\":{},\"na\":{},\"bn\":[{}],\"an\":[{}]}}",
        bt.kind.len(),
        at.kind.len(),
        ranges(&bt),
        ranges(&at)
    );
    println!("{out}");
}
