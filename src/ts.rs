//! Tree-sitter front end shared by the benchmark and scoring binaries (feature `ts`).
//!
//! Converts a tree-sitter parse into the hash-consed [`Arena`] and into preorder arrays. Preorder
//! counts every node, named and anonymous, children in order. Internal nodes are labelled by kind
//! only; leaves by kind and source text.

use crate::{Arena, Id};
use std::collections::HashMap;
use tree_sitter::{Language, Node};

/// "No node".
pub const NIL: u32 = u32::MAX;

/// Interns (kind, text) pairs as labels and remembers each label's kind.
#[derive(Default)]
pub struct Interner {
    labels: HashMap<(u16, Option<Vec<u8>>), u32>,
    kinds: Vec<u32>,
}

impl Interner {
    /// The label of a node of this kind and (for leaves) text.
    pub fn label(&mut self, kind: u16, text: Option<&[u8]>) -> u32 {
        let next = u32::try_from(self.labels.len()).unwrap();
        let l = *self
            .labels
            .entry((kind, text.map(<[u8]>::to_vec)))
            .or_insert(next);
        if l == next {
            self.kinds.push(u32::from(kind));
        }
        l
    }

    /// The kind id of a label produced by [`Interner::label`].
    #[must_use]
    pub fn kind_of(&self, label: u32) -> u32 {
        self.kinds[label as usize]
    }
}

/// A tree-sitter tree flattened to preorder arrays.
#[derive(Default)]
pub struct Tree {
    pub kind: Vec<&'static str>,
    pub parent: Vec<u32>,
    pub kids: Vec<Vec<u32>>,
    pub id: Vec<Id>,
    pub label: Vec<u32>,
    /// Structurally visible, as OmniDiff defines it.
    pub vis: Vec<bool>,
    /// A leaf that counts for the changed-span view.
    pub token: Vec<bool>,
    pub size: Vec<u32>,
    /// Source byte range of the node.
    pub span: Vec<(u32, u32)>,
}

/// Structural visibility as OmniDiff defines it.
pub fn is_visible(n: Node, src: &[u8]) -> bool {
    if n.child_count() == 0 {
        return true;
    }
    let has = |a: usize, b: usize| !src[a..b].iter().all(u8::is_ascii_whitespace);
    let mut pos = n.start_byte();
    let mut c = n.walk();
    for ch in n.children(&mut c) {
        if ch.start_byte() > pos && has(pos, ch.start_byte()) {
            return true;
        }
        pos = pos.max(ch.end_byte());
    }
    n.end_byte() > pos && has(pos, n.end_byte())
}

/// Converts a tree-sitter subtree into the arena and into `t`, returning its id.
pub fn convert(
    n: Node,
    src: &[u8],
    arena: &mut Arena,
    it: &mut Interner,
    t: &mut Tree,
    parent: u32,
) -> Id {
    let idx = u32::try_from(t.kind.len()).unwrap();
    t.kind.push(n.kind());
    t.parent.push(parent);
    t.kids.push(Vec::new());
    t.id.push(Id(0));
    t.label.push(0);
    t.size.push(0);
    t.span.push((n.start_byte() as u32, n.end_byte() as u32));
    t.vis.push(is_visible(n, src));
    let text = &src[n.byte_range()];
    let leaf = n.child_count() == 0;
    let punct = !n.is_named() && !text.iter().any(u8::is_ascii_alphanumeric);
    t.token
        .push(leaf && !text.trim_ascii().is_empty() && !n.kind().contains("comment") && !punct);
    if parent != NIL {
        t.kids[parent as usize].push(idx);
    }
    let (id, label) = if leaf {
        let l = it.label(n.kind_id(), Some(text));
        (arena.mk(l, &[]), l)
    } else {
        let mut kids = Vec::with_capacity(n.child_count());
        let mut c = n.walk();
        for ch in n.children(&mut c) {
            kids.push(convert(ch, src, arena, it, t, idx));
        }
        let l = it.label(n.kind_id(), None);
        (arena.mk(l, &kids), l)
    };
    t.id[idx as usize] = id;
    t.label[idx as usize] = label;
    t.size[idx as usize] = arena.size(id);
    id
}

/// The grammar for a file extension, with its language name.
#[must_use]
pub fn lang(ext: &str) -> Option<(&'static str, Language)> {
    Some(match ext {
        "java" => ("java", tree_sitter_java::LANGUAGE.into()),
        "go" => ("go", tree_sitter_go::LANGUAGE.into()),
        "c" | "h" => ("c", tree_sitter_c::LANGUAGE.into()),
        "py" => ("python", tree_sitter_python::LANGUAGE.into()),
        "js" | "mjs" => ("javascript", tree_sitter_javascript::LANGUAGE.into()),
        "ts" => (
            "typescript",
            tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into(),
        ),
        "tsx" => ("tsx", tree_sitter_typescript::LANGUAGE_TSX.into()),
        "rs" => ("rust", tree_sitter_rust::LANGUAGE.into()),
        _ => return None,
    })
}
