//! The general-TED mapping used by the `DFOLD_TED` run of the scorer, with its optional hygiene
//! and move-recovery post-passes (`DFOLD_HYGIENE`, `DFOLD_MOVES`).

use difffold::ted::{ted_mapping, PostTree};
use difffold::ts::{Tree, NIL};
use std::collections::HashMap;

/// Optimal general tree edit mapping (deleting a node promotes its children) as preorder index pairs.
pub fn ted_pairs(bt: &Tree, at: &Tree) -> Vec<(u32, u32)> {
    // Iterative postorder numbering: `order[k]` is the preorder index of the k-th node in postorder.
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
    let kinds_on = std::env::var("DFOLD_KINDS").is_ok();
    let mut kind_ids: HashMap<&'static str, u32> = HashMap::new();
    let mut build = |t: &Tree, order: &[u32], pos: &[u32]| -> PostTree {
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
        let pt = PostTree::from_kids(label, &kids);
        if kinds_on {
            let kind: Vec<u32> = order
                .iter()
                .map(|&v| {
                    let n = kind_ids.len() as u32;
                    *kind_ids.entry(t.kind[v as usize]).or_insert(n)
                })
                .collect();
            pt.with_kinds(kind)
        } else {
            pt
        }
    };
    let ((oa, pa), (ob, pb)) = (post(bt), post(at));
    let (ta, tb) = (build(bt, &oa, &pa), build(at, &ob, &pb));
    let m = ted_mapping(&ta, &tb);
    let mut pairs: Vec<(u32, u32)> = m
        .pairs
        .iter()
        .map(|&(x, y)| (oa[x as usize - 1], ob[y as usize - 1]))
        .collect();
    if std::env::var("DFOLD_HYGIENE").is_ok() {
        drop_orphan_updates(bt, at, &mut pairs);
    }
    if std::env::var("DFOLD_MOVES").is_ok() {
        recover_moves(bt, at, &mut pairs);
    }
    pairs
}

/// Mapping hygiene. A leaf paired with a leaf of different text (an update) is kept only when the parents of the two
/// leaves are paired with each other; otherwise the pairing is an accident of the cost model and is dropped.
fn drop_orphan_updates(bt: &Tree, at: &Tree, pairs: &mut Vec<(u32, u32)>) {
    let set: std::collections::HashSet<(u32, u32)> = pairs.iter().copied().collect();
    pairs.retain(|&(x, y)| {
        let (xu, yu) = (x as usize, y as usize);
        if bt.label[xu] == at.label[yu] || !bt.kids[xu].is_empty() || !at.kids[yu].is_empty() {
            return true;
        }
        let (px, py) = (bt.parent[xu], at.parent[yu]);
        px != NIL && py != NIL && set.contains(&(px, py))
    });
}

/// Move recovery. Classical edit distance has no move operation, so a moved or reordered subtree is deleted on
/// one side and inserted on the other. A maximal subtree that is entirely unmapped on both sides and has the same
/// content (same hash-consed id) is matched node for node.
fn recover_moves(bt: &Tree, at: &Tree, pairs: &mut Vec<(u32, u32)>) {
    let roots = |t: &Tree, mapped: &[bool]| -> HashMap<u32, Vec<u32>> {
        // A node is "dead" when it and its whole subtree are unmapped; preorder indices make children larger than parents.
        let n = t.kind.len();
        let mut dead = vec![false; n];
        for v in (0..n).rev() {
            dead[v] = !mapped[v] && t.kids[v].iter().all(|&k| dead[k as usize]);
        }
        let mut by: HashMap<u32, Vec<u32>> = HashMap::new();
        for v in 0..n {
            if dead[v]
                && (t.parent[v] == NIL || !dead[t.parent[v] as usize])
                && !t.kids[v].is_empty()
            {
                by.entry(t.id[v].0).or_default().push(v as u32);
            }
        }
        by
    };
    let (mut ma, mut mb) = (vec![false; bt.kind.len()], vec![false; at.kind.len()]);
    for &(x, y) in pairs.iter() {
        ma[x as usize] = true;
        mb[y as usize] = true;
    }
    let (ra, rb) = (roots(bt, &ma), roots(at, &mb));
    for (id, xs) in &ra {
        let Some(ys) = rb.get(id) else { continue };
        for (&x, &y) in xs.iter().zip(ys.iter()) {
            let mut stack = vec![(x, y)];
            while let Some((u, v)) = stack.pop() {
                pairs.push((u, v));
                for (&cu, &cv) in bt.kids[u as usize].iter().zip(at.kids[v as usize].iter()) {
                    stack.push((cu, cv));
                }
            }
        }
    }
}
