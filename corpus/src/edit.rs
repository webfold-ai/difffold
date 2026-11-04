//! Recorded edits and their replay semantics. The same `apply` is used by the generator and the
//! validator, so a recorded edit list is replayable by construction and checked end to end.

use crate::json::J;
use crate::tree::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Insert,
    Delete,
    Update,
    Move,
    Split,
    Merge,
    Noise,
}

impl Op {
    pub fn name(&self) -> &'static str {
        match self {
            Op::Insert => "insert",
            Op::Delete => "delete",
            Op::Update => "update",
            Op::Move => "move",
            Op::Split => "split",
            Op::Merge => "merge",
            Op::Noise => "noise",
        }
    }
    pub fn from_name(s: &str) -> Option<Op> {
        Some(match s {
            "insert" => Op::Insert,
            "delete" => Op::Delete,
            "update" => Op::Update,
            "move" => Op::Move,
            "split" => Op::Split,
            "merge" => Op::Merge,
            "noise" => Op::Noise,
            _ => return None,
        })
    }
    pub const ALL: [Op; 7] = [Op::Insert, Op::Delete, Op::Update, Op::Move, Op::Split, Op::Merge, Op::Noise];
}

/// Replay primitives. Indices are positions in the parent's child list at application time.
/// `Move` detaches the subtree first, then inserts it at `index` of the (post-detach) list.
#[derive(Clone, Debug, PartialEq)]
pub enum Act {
    Insert { parent: u32, index: usize, node: Node },
    Remove { lid: u32 },
    SetText { lid: u32, old: String, new: String },
    SetAttr { lid: u32, name: String, old: Option<String>, new: Option<String> },
    SetTag { lid: u32, old: String, new: String },
    ReorderAttrs { lid: u32, order: Vec<String> },
    Move { lid: u32, parent: u32, index: usize },
}

impl Act {
    pub fn lid(&self) -> u32 {
        match self {
            Act::Insert { node, .. } => node.lid,
            Act::Remove { lid }
            | Act::SetText { lid, .. }
            | Act::SetAttr { lid, .. }
            | Act::SetTag { lid, .. }
            | Act::ReorderAttrs { lid, .. }
            | Act::Move { lid, .. } => *lid,
        }
    }
    pub fn name(&self) -> &'static str {
        match self {
            Act::Insert { .. } => "insert",
            Act::Remove { .. } => "remove",
            Act::SetText { .. } => "set_text",
            Act::SetAttr { .. } => "set_attr",
            Act::SetTag { .. } => "set_tag",
            Act::ReorderAttrs { .. } => "reorder_attrs",
            Act::Move { .. } => "move",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Edit {
    pub op: Op,
    /// Finer label such as `price`, `href`, `wrap`, `reorder`.
    pub kind: String,
    /// Edits produced by one logical operation share a macro id.
    pub macro_id: u32,
    pub act: Act,
    /// Related lid: `split_source`, `merge_into`, `wrapper`.
    pub rel: Option<(String, u32)>,
}

pub fn apply(root: &mut Node, act: &Act) -> Result<(), String> {
    match act {
        Act::Insert { parent, index, node } => {
            let present = lid_set(root);
            for l in lids_of(node) {
                if present.contains(&l) {
                    return Err(format!("insert: lid {} already present", l));
                }
            }
            let p = find_mut(root, *parent).ok_or_else(|| format!("insert: no parent {}", parent))?;
            if p.is_text() || is_void(&p.tag) {
                return Err("insert: parent cannot have children".into());
            }
            if *index > p.children.len() {
                return Err(format!("insert: index {} > {}", index, p.children.len()));
            }
            p.children.insert(*index, node.clone());
        }
        Act::Remove { lid } => {
            if root.lid == *lid {
                return Err("remove: cannot remove root".into());
            }
            detach(root, *lid).ok_or_else(|| format!("remove: no node {}", lid))?;
        }
        Act::SetText { lid, old, new } => {
            let n = find_mut(root, *lid).ok_or_else(|| format!("set_text: no node {}", lid))?;
            if !n.is_text() || &n.text != old {
                return Err(format!("set_text: old text mismatch at {}", lid));
            }
            n.text = new.clone();
        }
        Act::SetAttr { lid, name, old, new } => {
            let n = find_mut(root, *lid).ok_or_else(|| format!("set_attr: no node {}", lid))?;
            if n.attr(name).map(|s| s.to_string()) != *old {
                return Err(format!("set_attr: old value mismatch for {} at {}", name, lid));
            }
            match new {
                Some(v) => n.set_attr(name, v),
                None => {
                    n.remove_attr(name);
                }
            }
        }
        Act::SetTag { lid, old, new } => {
            let n = find_mut(root, *lid).ok_or_else(|| format!("set_tag: no node {}", lid))?;
            if &n.tag != old {
                return Err("set_tag: old tag mismatch".into());
            }
            n.tag = new.clone();
        }
        Act::ReorderAttrs { lid, order } => {
            let n = find_mut(root, *lid).ok_or_else(|| format!("reorder_attrs: no node {}", lid))?;
            let mut cur: Vec<&str> = n.attrs.iter().map(|(k, _)| k.as_str()).collect();
            let mut want: Vec<&str> = order.iter().map(|s| s.as_str()).collect();
            cur.sort();
            want.sort();
            if cur != want {
                return Err("reorder_attrs: not a permutation".into());
            }
            let mut na = vec![];
            for k in order {
                let v = n.attr(k).unwrap().to_string();
                na.push((k.clone(), v));
            }
            n.attrs = na;
        }
        Act::Move { lid, parent, index } => {
            if root.lid == *lid {
                return Err("move: cannot move root".into());
            }
            let node = find(root, *lid).ok_or_else(|| format!("move: no node {}", lid))?;
            if find(node, *parent).is_some() {
                return Err("move: target parent inside moved subtree".into());
            }
            let node = detach(root, *lid).unwrap();
            let p = find_mut(root, *parent).ok_or_else(|| format!("move: no parent {}", parent))?;
            if p.is_text() || is_void(&p.tag) {
                return Err("move: parent cannot have children".into());
            }
            if *index > p.children.len() {
                return Err(format!("move: index {} > {}", index, p.children.len()));
            }
            p.children.insert(*index, node);
        }
    }
    Ok(())
}

pub fn edit_to_json(e: &Edit, step: usize, before_path: Option<String>, after_path: Option<String>) -> J {
    let mut v: Vec<(&str, J)> = vec![
        ("step", J::Int(step as i64)),
        ("op", J::s(e.op.name())),
        ("kind", J::s(&e.kind)),
        ("macro", J::Int(e.macro_id as i64)),
        ("act", J::s(e.act.name())),
        ("lid", J::Int(e.act.lid() as i64)),
        ("before_path", J::opt_s(&before_path)),
        ("after_path", J::opt_s(&after_path)),
    ];
    match &e.act {
        Act::Insert { parent, index, node } => {
            v.push(("parent", J::Int(*parent as i64)));
            v.push(("index", J::Int(*index as i64)));
            v.push(("node", node_to_json(node)));
        }
        Act::Remove { .. } => {}
        Act::SetText { old, new, .. } | Act::SetTag { old, new, .. } => {
            v.push(("old", J::s(old)));
            v.push(("new", J::s(new)));
        }
        Act::SetAttr { name, old, new, .. } => {
            v.push(("name", J::s(name)));
            v.push(("old", J::opt_s(old)));
            v.push(("new", J::opt_s(new)));
        }
        Act::ReorderAttrs { order, .. } => {
            v.push(("order", J::Arr(order.iter().map(|s| J::s(s)).collect())));
        }
        Act::Move { parent, index, .. } => {
            v.push(("parent", J::Int(*parent as i64)));
            v.push(("index", J::Int(*index as i64)));
        }
    }
    if let Some((r, l)) = &e.rel {
        v.push(("rel", J::obj(vec![("role", J::s(r)), ("lid", J::Int(*l as i64))])));
    }
    J::obj(v)
}

pub fn edit_from_json(j: &J) -> Result<Edit, String> {
    let g = |k: &str| j.get(k).ok_or_else(|| format!("edit missing {}", k));
    let op = Op::from_name(g("op")?.as_str().ok_or("op")?).ok_or("unknown op")?;
    let lid = g("lid")?.as_i64().ok_or("lid")? as u32;
    let s = |k: &str| -> Result<String, String> { Ok(g(k)?.as_str().ok_or(format!("{} not str", k))?.to_string()) };
    let os = |k: &str| -> Result<Option<String>, String> {
        let v = g(k)?;
        if v.is_null() {
            Ok(None)
        } else {
            Ok(Some(v.as_str().ok_or(format!("{} not str", k))?.to_string()))
        }
    };
    let act = match g("act")?.as_str().ok_or("act")? {
        "insert" => Act::Insert {
            parent: g("parent")?.as_i64().ok_or("parent")? as u32,
            index: g("index")?.as_usize().ok_or("index")?,
            node: node_from_json(g("node")?)?,
        },
        "remove" => Act::Remove { lid },
        "set_text" => Act::SetText { lid, old: s("old")?, new: s("new")? },
        "set_tag" => Act::SetTag { lid, old: s("old")?, new: s("new")? },
        "set_attr" => Act::SetAttr { lid, name: s("name")?, old: os("old")?, new: os("new")? },
        "reorder_attrs" => Act::ReorderAttrs {
            lid,
            order: g("order")?.as_arr().ok_or("order")?.iter().map(|x| x.as_str().unwrap_or("").to_string()).collect(),
        },
        "move" => Act::Move {
            lid,
            parent: g("parent")?.as_i64().ok_or("parent")? as u32,
            index: g("index")?.as_usize().ok_or("index")?,
        },
        o => return Err(format!("unknown act {}", o)),
    };
    let rel = match j.get("rel") {
        Some(r) => Some((
            r.get("role").and_then(|x| x.as_str()).ok_or("rel role")?.to_string(),
            r.get("lid").and_then(|x| x.as_i64()).ok_or("rel lid")? as u32,
        )),
        None => None,
    };
    Ok(Edit { op, kind: s("kind")?, macro_id: g("macro")?.as_i64().ok_or("macro")? as u32, act, rel })
}
