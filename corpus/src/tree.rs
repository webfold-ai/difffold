//! Lineage-carrying DOM tree, HTML serializer and parser.

use crate::json::J;
use std::collections::{HashMap, HashSet};

pub const TEXT: &str = "#text";
pub const VOID: &[&str] = &["meta", "link", "img", "input", "br", "hr"];

pub fn is_void(tag: &str) -> bool {
    VOID.contains(&tag)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    /// Stable lineage id, unique within one pair (before and after share ids for the same thing).
    pub lid: u32,
    pub tag: String,
    /// Semantic role used by generators and for analysis. Never serialized to HTML.
    pub role: String,
    pub attrs: Vec<(String, String)>,
    /// Only used by `#text` nodes.
    pub text: String,
    pub children: Vec<Node>,
}

impl Node {
    pub fn new(lid: u32, tag: &str, role: &str) -> Node {
        Node { lid, tag: tag.into(), role: role.into(), attrs: vec![], text: String::new(), children: vec![] }
    }
    pub fn txt(lid: u32, s: &str) -> Node {
        Node { lid, tag: TEXT.into(), role: String::new(), attrs: vec![], text: s.into(), children: vec![] }
    }
    pub fn is_text(&self) -> bool {
        self.tag == TEXT
    }
    pub fn size(&self) -> usize {
        1 + self.children.iter().map(|c| c.size()).sum::<usize>()
    }
    pub fn attr(&self, n: &str) -> Option<&str> {
        self.attrs.iter().find(|(k, _)| k == n).map(|(_, v)| v.as_str())
    }
    pub fn set_attr(&mut self, n: &str, v: &str) {
        if let Some(a) = self.attrs.iter_mut().find(|(k, _)| k == n) {
            a.1 = v.to_string();
        } else {
            self.attrs.push((n.to_string(), v.to_string()));
        }
    }
    pub fn remove_attr(&mut self, n: &str) -> Option<String> {
        let i = self.attrs.iter().position(|(k, _)| k == n)?;
        Some(self.attrs.remove(i).1)
    }
    pub fn has_text_child(&self) -> bool {
        self.children.iter().any(|c| c.is_text())
    }
    /// The first text child's lid, if any.
    pub fn text_child(&self) -> Option<&Node> {
        self.children.iter().find(|c| c.is_text())
    }
    /// A copy without children.
    pub fn shell(&self) -> Node {
        Node { children: vec![], ..self.clone() }
    }
}

pub fn preorder<'a>(n: &'a Node, out: &mut Vec<&'a Node>) {
    out.push(n);
    for c in &n.children {
        preorder(c, out);
    }
}

pub fn find(n: &Node, lid: u32) -> Option<&Node> {
    if n.lid == lid {
        return Some(n);
    }
    n.children.iter().find_map(|c| find(c, lid))
}

pub fn find_mut(n: &mut Node, lid: u32) -> Option<&mut Node> {
    if n.lid == lid {
        return Some(n);
    }
    for c in n.children.iter_mut() {
        if let Some(x) = find_mut(c, lid) {
            return Some(x);
        }
    }
    None
}

pub fn detach(n: &mut Node, lid: u32) -> Option<Node> {
    if let Some(i) = n.children.iter().position(|c| c.lid == lid) {
        return Some(n.children.remove(i));
    }
    for c in n.children.iter_mut() {
        if let Some(x) = detach(c, lid) {
            return Some(x);
        }
    }
    None
}

pub fn path_of(n: &Node, lid: u32) -> Option<Vec<usize>> {
    if n.lid == lid {
        return Some(vec![]);
    }
    for (i, c) in n.children.iter().enumerate() {
        if let Some(mut p) = path_of(c, lid) {
            p.insert(0, i);
            return Some(p);
        }
    }
    None
}

pub fn path_string(p: &[usize]) -> String {
    if p.is_empty() {
        return "/".into();
    }
    p.iter().map(|i| format!("/{}", i)).collect()
}

/// Map lid -> (parent lid, child index).
pub fn parent_map(n: &Node) -> HashMap<u32, (u32, usize)> {
    fn go(n: &Node, m: &mut HashMap<u32, (u32, usize)>) {
        for (i, c) in n.children.iter().enumerate() {
            m.insert(c.lid, (n.lid, i));
            go(c, m);
        }
    }
    let mut m = HashMap::new();
    go(n, &mut m);
    m
}

pub fn lids_of(n: &Node) -> Vec<u32> {
    fn go(n: &Node, o: &mut Vec<u32>) {
        o.push(n.lid);
        for c in &n.children {
            go(c, o);
        }
    }
    let mut out = vec![];
    go(n, &mut out);
    out
}

pub fn lid_set(n: &Node) -> HashSet<u32> {
    lids_of(n).into_iter().collect()
}

pub fn relabel(n: &mut Node, next: &mut u32) {
    n.lid = *next;
    *next += 1;
    for c in n.children.iter_mut() {
        relabel(c, next);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Tree {
    pub root: Node,
    pub next_lid: u32,
}

impl Tree {
    pub fn new(root: Node, next_lid: u32) -> Tree {
        Tree { root, next_lid }
    }
    pub fn fresh(&mut self) -> u32 {
        let v = self.next_lid;
        self.next_lid += 1;
        v
    }
    pub fn find(&self, lid: u32) -> Option<&Node> {
        find(&self.root, lid)
    }
    pub fn find_mut(&mut self, lid: u32) -> Option<&mut Node> {
        find_mut(&mut self.root, lid)
    }
    pub fn count(&self) -> usize {
        self.root.size()
    }
    pub fn nodes(&self) -> Vec<&Node> {
        let mut v = vec![];
        preorder(&self.root, &mut v);
        v
    }
    pub fn by_role(&self, role: &str) -> Vec<u32> {
        self.nodes().into_iter().filter(|n| n.role == role).map(|n| n.lid).collect()
    }
    /// Deep copy with fresh lids.
    pub fn fresh_clone(&mut self, lid: u32) -> Option<Node> {
        let mut n = self.find(lid)?.clone();
        relabel(&mut n, &mut self.next_lid);
        Some(n)
    }
    pub fn check_invariants(&self) -> Result<(), String> {
        let mut seen = HashSet::new();
        fn go(n: &Node, seen: &mut HashSet<u32>, in_mixed_parent_text: bool) -> Result<(), String> {
            let _ = in_mixed_parent_text;
            if !seen.insert(n.lid) {
                return Err(format!("duplicate lid {}", n.lid));
            }
            if n.is_text() {
                if n.text.trim().is_empty() {
                    return Err(format!("blank text node {}", n.lid));
                }
                if n.text.contains('\n') {
                    return Err(format!("newline in text node {}", n.lid));
                }
                if !n.children.is_empty() {
                    return Err("text node with children".into());
                }
            }
            if is_void(&n.tag) && !n.children.is_empty() {
                return Err(format!("void element {} with children", n.tag));
            }
            let mut prev_text = false;
            for c in &n.children {
                if c.is_text() && prev_text {
                    return Err(format!("adjacent text nodes under {}", n.lid));
                }
                prev_text = c.is_text();
                go(c, seen, false)?;
            }
            Ok(())
        }
        go(&self.root, &mut seen, false)
    }
}

// ---------------------------------------------------------------- serialization

fn esc_text(s: &str, out: &mut String) {
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            c => out.push(c),
        }
    }
}

fn esc_attr(s: &str, out: &mut String) {
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
}

fn ser(n: &Node, out: &mut String) {
    if n.is_text() {
        esc_text(&n.text, out);
        return;
    }
    out.push('<');
    out.push_str(&n.tag);
    for (k, v) in &n.attrs {
        out.push(' ');
        out.push_str(k);
        out.push_str("=\"");
        esc_attr(v, out);
        out.push('"');
    }
    out.push('>');
    if is_void(&n.tag) {
        return;
    }
    let block = !n.has_text_child() && !n.children.is_empty();
    if block {
        out.push('\n');
    }
    for c in &n.children {
        ser(c, out);
        if block {
            out.push('\n');
        }
    }
    out.push_str("</");
    out.push_str(&n.tag);
    out.push('>');
}

pub fn to_html(root: &Node) -> String {
    let mut out = String::from("<!doctype html>\n");
    ser(root, &mut out);
    out.push('\n');
    out
}

// ---------------------------------------------------------------- parsing

fn unesc(s: &str) -> String {
    if !s.contains('&') {
        return s.to_string();
    }
    s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", "\"").replace("&amp;", "&")
}

/// Strict parser for the serializer's own output. All lids are 0 and roles empty.
pub fn parse_html(src: &str) -> Result<Node, String> {
    let b = src.as_bytes();
    let mut p = 0usize;
    let mut stack: Vec<Node> = vec![];
    let mut root: Option<Node> = None;
    while p < b.len() {
        if b[p] == b'<' {
            if src[p..].starts_with("<!") {
                let e = src[p..].find('>').ok_or("unterminated doctype")?;
                p += e + 1;
                continue;
            }
            if src[p..].starts_with("</") {
                let e = src[p..].find('>').ok_or("unterminated close tag")?;
                let name = &src[p + 2..p + e];
                p += e + 1;
                let n = stack.pop().ok_or_else(|| format!("stray close tag </{}>", name))?;
                if n.tag != name {
                    return Err(format!("mismatched close: <{}> closed by </{}>", n.tag, name));
                }
                match stack.last_mut() {
                    Some(par) => par.children.push(n),
                    None => {
                        if root.is_some() {
                            return Err("multiple roots".into());
                        }
                        root = Some(n);
                    }
                }
                continue;
            }
            p += 1;
            let st = p;
            while p < b.len() && !matches!(b[p], b' ' | b'>' | b'/') {
                p += 1;
            }
            let mut n = Node::new(0, &src[st..p], "");
            loop {
                while p < b.len() && b[p] == b' ' {
                    p += 1;
                }
                if p >= b.len() {
                    return Err("unterminated open tag".into());
                }
                if b[p] == b'>' {
                    p += 1;
                    break;
                }
                let ks = p;
                while p < b.len() && !matches!(b[p], b'=' | b' ' | b'>') {
                    p += 1;
                }
                let k = src[ks..p].to_string();
                let mut v = String::new();
                if p < b.len() && b[p] == b'=' {
                    p += 1;
                    if p >= b.len() || b[p] != b'"' {
                        return Err("attribute value not quoted".into());
                    }
                    p += 1;
                    let vs = p;
                    while p < b.len() && b[p] != b'"' {
                        p += 1;
                    }
                    if p >= b.len() {
                        return Err("unterminated attribute".into());
                    }
                    v = unesc(&src[vs..p]);
                    p += 1;
                }
                n.attrs.push((k, v));
            }
            if is_void(&n.tag) {
                match stack.last_mut() {
                    Some(par) => par.children.push(n),
                    None => return Err("void element at top level".into()),
                }
            } else {
                stack.push(n);
            }
        } else {
            let st = p;
            while p < b.len() && b[p] != b'<' {
                p += 1;
            }
            let t = &src[st..p];
            if t.trim().is_empty() {
                continue;
            }
            match stack.last_mut() {
                Some(par) => par.children.push(Node::txt(0, &unesc(t))),
                None => return Err("text outside root".into()),
            }
        }
    }
    if !stack.is_empty() {
        return Err("unclosed elements at end of input".into());
    }
    root.ok_or_else(|| "no root element".into())
}

/// Assign lids and roles in preorder. Errors when the counts differ.
pub fn assign(n: &mut Node, lids: &[u32], roles: &[String]) -> Result<(), String> {
    fn go(n: &mut Node, i: &mut usize, lids: &[u32], roles: &[String]) -> Result<(), String> {
        if *i >= lids.len() {
            return Err("more nodes in html than lids".into());
        }
        n.lid = lids[*i];
        if *i < roles.len() {
            n.role = roles[*i].clone();
        }
        *i += 1;
        for c in n.children.iter_mut() {
            go(c, i, lids, roles)?;
        }
        Ok(())
    }
    let mut i = 0;
    go(n, &mut i, lids, roles)?;
    if i != lids.len() {
        return Err(format!("html has {} nodes but {} lids", i, lids.len()));
    }
    Ok(())
}

// ---------------------------------------------------------------- json

pub fn node_to_json(n: &Node) -> J {
    J::obj(vec![
        ("lid", J::Int(n.lid as i64)),
        ("tag", J::s(&n.tag)),
        ("role", J::s(&n.role)),
        ("attrs", J::Arr(n.attrs.iter().map(|(k, v)| J::Arr(vec![J::s(k), J::s(v)])).collect())),
        ("text", J::s(&n.text)),
        ("children", J::Arr(n.children.iter().map(node_to_json).collect())),
    ])
}

pub fn node_from_json(j: &J) -> Result<Node, String> {
    let g = |k: &str| j.get(k).ok_or_else(|| format!("node missing {}", k));
    let mut attrs = vec![];
    for a in g("attrs")?.as_arr().ok_or("attrs not array")? {
        let a = a.as_arr().ok_or("attr not pair")?;
        attrs.push((
            a.first().and_then(|x| x.as_str()).ok_or("attr key")?.to_string(),
            a.get(1).and_then(|x| x.as_str()).ok_or("attr val")?.to_string(),
        ));
    }
    let mut children = vec![];
    for c in g("children")?.as_arr().ok_or("children not array")? {
        children.push(node_from_json(c)?);
    }
    Ok(Node {
        lid: g("lid")?.as_i64().ok_or("lid")? as u32,
        tag: g("tag")?.as_str().ok_or("tag")?.to_string(),
        role: g("role")?.as_str().ok_or("role")?.to_string(),
        attrs,
        text: g("text")?.as_str().ok_or("text")?.to_string(),
        children,
    })
}
