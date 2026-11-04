//! Structural summary through difffold (java, go, c). Needs the `structural` feature.
//!
//! This path produces the *structural certificate*: difffold's edit script was replayed on the
//! before-tree and rebuilt the after-tree id for id (`diff_checked`, contract C3). It says nothing
//! about bytes. Whitespace between tokens is not in the tree, so two files that differ only in
//! formatting have structural cost 0 while their bytes differ. See `README.md`.

/// Limits and switches for the structural path.
#[derive(Debug, Clone)]
pub struct StructOpts {
    pub max_bytes: usize,
    pub max_nodes: u32,
    /// Report a result even when tree-sitter inserted ERROR or MISSING nodes. The result is then
    /// advisory only.
    pub allow_parse_errors: bool,
    pub max_entries: usize,
}

impl Default for StructOpts {
    fn default() -> Self {
        StructOpts {
            max_bytes: 1 << 20,
            max_nodes: 400_000,
            allow_parse_errors: false,
            max_entries: 30,
        }
    }
}

/// A verified structural result.
#[derive(Debug, Clone)]
pub struct Summary {
    pub language: &'static str,
    pub cost: u32,
    pub nodes_before: u32,
    pub nodes_after: u32,
    pub entries: Vec<String>,
    pub entries_total: usize,
    pub parse_errors: bool,
}

/// The language a path maps to, by extension.
#[must_use]
pub fn language_for(path: &str) -> Option<&'static str> {
    let ext = path.rsplit('.').next()?;
    match ext {
        "java" => Some("java"),
        "go" => Some("go"),
        "c" | "h" => Some("c"),
        _ => None,
    }
}

/// Whether the structural backend is compiled in.
#[must_use]
pub const fn available() -> bool {
    cfg!(feature = "structural")
}

#[cfg(not(feature = "structural"))]
/// # Errors
/// Always: the feature is not compiled.
pub fn summarize(
    _lang: &'static str,
    _before: &[u8],
    _after: &[u8],
    _o: &StructOpts,
) -> Result<Summary, String> {
    Err("structural feature not compiled in (build with --features structural)".into())
}

#[cfg(feature = "structural")]
pub use imp::summarize;

#[cfg(feature = "structural")]
mod imp {
    use super::{StructOpts, Summary};
    use difffold::{diff_checked, Arena, Edit, Id};
    use std::collections::HashMap;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use tree_sitter::{Language, Node, Parser};

    struct Labels(HashMap<(u16, Option<Vec<u8>>), u32>);

    fn convert(n: Node, src: &[u8], arena: &mut Arena, it: &mut Labels) -> Id {
        let kind = n.kind_id();
        if n.child_count() == 0 {
            let next = u32::try_from(it.0.len()).unwrap_or(u32::MAX);
            let l = *it
                .0
                .entry((kind, Some(src[n.byte_range()].to_vec())))
                .or_insert(next);
            return arena.mk(l, &[]);
        }
        let mut kids = Vec::with_capacity(n.child_count());
        let mut c = n.walk();
        for ch in n.children(&mut c) {
            kids.push(convert(ch, src, arena, it));
        }
        let next = u32::try_from(it.0.len()).unwrap_or(u32::MAX);
        let l = *it.0.entry((kind, None)).or_insert(next);
        arena.mk(l, &kids)
    }

    fn language(name: &str) -> Language {
        match name {
            "java" => tree_sitter_java::LANGUAGE.into(),
            "go" => tree_sitter_go::LANGUAGE.into(),
            _ => tree_sitter_c::LANGUAGE.into(),
        }
    }

    fn snippet(n: Node, src: &[u8]) -> String {
        let t = String::from_utf8_lossy(&src[n.byte_range()]);
        let first = t.lines().next().unwrap_or("").trim();
        let mut s: String = first.chars().take(60).collect();
        if first.chars().count() > 60 || t.lines().count() > 1 {
            s.push_str("...");
        }
        s
    }

    struct W<'a> {
        arena: &'a Arena,
        bsrc: &'a [u8],
        asrc: &'a [u8],
        entries: Vec<String>,
        total: usize,
        cap: usize,
    }

    impl W<'_> {
        fn push(&mut self, s: String) {
            self.total += 1;
            if self.entries.len() < self.cap {
                self.entries.push(s);
            }
        }

        fn scope(n: Node, src: &[u8], outer: &str) -> String {
            let k = n.kind();
            if (k.ends_with("declaration") || k.ends_with("definition")) && n.is_named() {
                let name = n
                    .child_by_field_name("name")
                    .or_else(|| n.child_by_field_name("declarator"));
                return match name {
                    Some(nm) => format!("{k} {}", snippet(nm, src)),
                    None => k.to_string(),
                };
            }
            outer.to_string()
        }

        fn walk(&mut self, e: &Edit, bn: Node, an: Node, outer: &str) {
            let Edit::Upd {
                from,
                to_label,
                kids,
            } = e
            else {
                return;
            };
            let scope = Self::scope(bn, self.bsrc, outer);
            let in_scope = if scope.is_empty() {
                String::new()
            } else {
                format!("  [in {scope}]")
            };
            if bn.child_count() == 0 && an.child_count() == 0 {
                self.push(format!(
                    "~ before L{} / after L{}: `{}` -> `{}`{in_scope}",
                    bn.start_position().row + 1,
                    an.start_position().row + 1,
                    snippet(bn, self.bsrc),
                    snippet(an, self.asrc)
                ));
                return;
            }
            if self.arena.label(*from) != *to_label {
                self.push(format!(
                    "~ before L{}: node kind {} -> {}{in_scope}",
                    bn.start_position().row + 1,
                    bn.kind(),
                    an.kind()
                ));
            }
            let mut c1 = bn.walk();
            let bk: Vec<Node> = bn.children(&mut c1).collect();
            let mut c2 = an.walk();
            let ak: Vec<Node> = an.children(&mut c2).collect();
            let (mut bi, mut ai) = (0usize, 0usize);
            for k in kids {
                match k {
                    Edit::Keep(_) => {
                        bi += 1;
                        ai += 1;
                    }
                    Edit::Del(x) => {
                        let n = bk[bi];
                        self.push(format!(
                            "- before L{}: deleted {} ({} nodes) `{}`{in_scope}",
                            n.start_position().row + 1,
                            n.kind(),
                            self.arena.size(*x),
                            snippet(n, self.bsrc)
                        ));
                        bi += 1;
                    }
                    Edit::Ins(y) => {
                        let n = ak[ai];
                        self.push(format!(
                            "+ after L{}: inserted {} ({} nodes) `{}`{in_scope}",
                            n.start_position().row + 1,
                            n.kind(),
                            self.arena.size(*y),
                            snippet(n, self.asrc)
                        ));
                        ai += 1;
                    }
                    Edit::Upd { .. } => {
                        self.walk(k, bk[bi], ak[ai], &scope);
                        bi += 1;
                        ai += 1;
                    }
                }
            }
        }
    }

    /// # Errors
    /// Returns the reason when the structural path is skipped: not UTF-8, too large, parse errors,
    /// or a failed replay check.
    pub fn summarize(
        lang: &'static str,
        before: &[u8],
        after: &[u8],
        o: &StructOpts,
    ) -> Result<Summary, String> {
        if before.len() > o.max_bytes || after.len() > o.max_bytes {
            return Err(format!(
                "input larger than structural limit of {} bytes",
                o.max_bytes
            ));
        }
        if std::str::from_utf8(before).is_err() || std::str::from_utf8(after).is_err() {
            return Err("input is not valid UTF-8".into());
        }
        let mut parser = Parser::new();
        parser
            .set_language(&language(lang))
            .map_err(|e| format!("grammar load failed: {e}"))?;
        let tb = parser
            .parse(before, None)
            .ok_or("parse returned no tree (before)")?;
        let ta = parser
            .parse(after, None)
            .ok_or("parse returned no tree (after)")?;
        let errs = tb.root_node().has_error() || ta.root_node().has_error();
        if errs && !o.allow_parse_errors {
            return Err(
                "parse errors (tree-sitter ERROR or MISSING nodes) so the tree is not trustworthy"
                    .into(),
            );
        }
        let mut arena = Arena::new();
        let mut labels = Labels(HashMap::new());
        let x = convert(tb.root_node(), before, &mut arena, &mut labels);
        let y = convert(ta.root_node(), after, &mut arena, &mut labels);
        let (nb, na) = (arena.size(x), arena.size(y));
        if nb > o.max_nodes || na > o.max_nodes {
            return Err(format!("tree larger than {} nodes", o.max_nodes));
        }
        let res = catch_unwind(AssertUnwindSafe(|| diff_checked(&mut arena, x, y)))
            .map_err(|_| "structural replay check failed".to_string())?;
        let mut w = W {
            arena: &arena,
            bsrc: before,
            asrc: after,
            entries: Vec::new(),
            total: 0,
            cap: o.max_entries,
        };
        w.walk(&res.edit, tb.root_node(), ta.root_node(), "");
        Ok(Summary {
            language: lang,
            cost: res.cost,
            nodes_before: nb,
            nodes_after: na,
            entries: w.entries,
            entries_total: w.total,
            parse_errors: errs,
        })
    }
}
