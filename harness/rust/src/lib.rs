//! Shared pieces of the comparison harness: parsing, label interning (identical to difffold's
//! `bench_fixtures`), a flat postorder tree, and two reference tree-distance algorithms.
//!
//! Objectives:
//! - `selkow` and difffold: top-down (Selkow). Deleting a node deletes its whole subtree; matched
//!   nodes need matched parents; unit cost per node; relabel costs 1; roots always pair.
//! - `zhang_shasha`: classical ordered-tree edit distance. Deleting a node promotes its children,
//!   so it may align across levels. Its optimum is <= the Selkow optimum. NOT objective-matched.

use difffold::{Arena, Id};
use std::cell::Cell;
use std::collections::HashMap;
use std::time::Instant;
use tree_sitter::{Language, Node};

pub fn lang(ext: &str) -> Option<Language> {
    match ext {
        "java" => Some(tree_sitter_java::LANGUAGE.into()),
        "go" => Some(tree_sitter_go::LANGUAGE.into()),
        "c" | "h" => Some(tree_sitter_c::LANGUAGE.into()),
        _ => None,
    }
}

pub fn ext_of(path: &str) -> &str {
    path.rsplit('/')
        .next()
        .unwrap_or(path)
        .rsplit('.')
        .next()
        .unwrap_or("")
}

#[derive(Default)]
pub struct Interner {
    labels: HashMap<(u16, Option<Vec<u8>>), u32>,
    kinds: Vec<u32>,
}

impl Interner {
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

    /// The tree-sitter kind of a label (used by the refinement phases).
    pub fn kind_of(&self, label: u32) -> u32 {
        self.kinds[label as usize]
    }
}

/// Tree-sitter node to difffold arena. Leaves carry their text, inner nodes only their kind.
pub fn convert(n: Node, src: &[u8], arena: &mut Arena, it: &mut Interner) -> Id {
    if n.child_count() == 0 {
        let l = it.label(n.kind_id(), Some(&src[n.byte_range()]));
        return arena.mk(l, &[]);
    }
    let mut kids = Vec::with_capacity(n.child_count());
    let mut c = n.walk();
    for ch in n.children(&mut c) {
        kids.push(convert(ch, src, arena, it));
    }
    let l = it.label(n.kind_id(), None);
    arena.mk(l, &kids)
}

/// A plain tree in postorder: node `i`'s children have smaller indices; the root is last.
pub struct Flat {
    pub label: Vec<u32>,
    pub kids: Vec<Vec<u32>>,
    pub size: Vec<u32>,
}

impl Flat {
    pub fn len(&self) -> usize {
        self.label.len()
    }
    pub fn is_empty(&self) -> bool {
        self.label.is_empty()
    }
    pub fn root(&self) -> u32 {
        (self.label.len() - 1) as u32
    }
}

pub fn flatten(n: Node, src: &[u8], it: &mut Interner) -> Flat {
    let mut f = Flat {
        label: vec![],
        kids: vec![],
        size: vec![],
    };
    go(n, src, it, &mut f);
    f
}

fn go(n: Node, src: &[u8], it: &mut Interner, f: &mut Flat) -> u32 {
    let (l, kids) = if n.child_count() == 0 {
        (it.label(n.kind_id(), Some(&src[n.byte_range()])), vec![])
    } else {
        let mut kids = Vec::with_capacity(n.child_count());
        let mut c = n.walk();
        for ch in n.children(&mut c) {
            kids.push(go(ch, src, it, f));
        }
        (it.label(n.kind_id(), None), kids)
    };
    let size = 1 + kids.iter().map(|&k| f.size[k as usize]).sum::<u32>();
    f.label.push(l);
    f.kids.push(kids);
    f.size.push(size);
    (f.label.len() - 1) as u32
}

/// Zhang-Shasha ordered tree edit distance with unit insert, delete and relabel costs.
/// Returns `None` on deadline. O(n*m) memory in u32.
pub fn zhang_shasha(a: &Flat, b: &Flat, deadline: Instant) -> Option<u32> {
    let (n, m) = (a.len(), b.len());
    let lml = |t: &Flat| -> Vec<usize> {
        let mut l = vec![0usize; t.len()];
        for i in 0..t.len() {
            l[i] = t.kids[i].first().map_or(i, |&k| l[k as usize]);
        }
        l
    };
    let keyroots = |l: &[usize]| -> Vec<usize> {
        let mut seen = vec![false; l.len()];
        let mut k = vec![];
        for i in (0..l.len()).rev() {
            if !seen[l[i]] {
                seen[l[i]] = true;
                k.push(i);
            }
        }
        k.reverse();
        k
    };
    let (la, lb) = (lml(a), lml(b));
    let (ka, kb) = (keyroots(&la), keyroots(&lb));
    // Indices are 1-based postorder positions; 0 is the empty forest.
    let w = m + 1;
    let mut td = vec![0u32; (n + 1) * w];
    let mut fd = vec![0u32; (n + 1) * w];
    for &i in &ka {
        for &j in &kb {
            if Instant::now() >= deadline {
                return None;
            }
            let (li, lj) = (la[i] + 1, lb[j] + 1);
            let (i, j) = (i + 1, j + 1);
            fd[(li - 1) * w + (lj - 1)] = 0;
            for x in li..=i {
                fd[x * w + lj - 1] = fd[(x - 1) * w + lj - 1] + 1;
            }
            for y in lj..=j {
                fd[(li - 1) * w + y] = fd[(li - 1) * w + y - 1] + 1;
            }
            for x in li..=i {
                let lx = la[x - 1] + 1;
                for y in lj..=j {
                    let ly = lb[y - 1] + 1;
                    let del = fd[(x - 1) * w + y] + 1;
                    let ins = fd[x * w + y - 1] + 1;
                    let v = if lx == li && ly == lj {
                        let ren = u32::from(a.label[x - 1] != b.label[y - 1]);
                        let v = del.min(ins).min(fd[(x - 1) * w + y - 1] + ren);
                        td[x * w + y] = v;
                        v
                    } else {
                        del.min(ins).min(fd[(lx - 1) * w + ly - 1] + td[x * w + y])
                    };
                    fd[x * w + y] = v;
                }
            }
        }
    }
    Some(td[n * w + m])
}

/// Selkow top-down distance by plain memoised recursion over node pairs. No hashing of subtrees,
/// no pruning. This is the objective-matched reference for difffold. `None` on deadline.
pub struct Selkow<'a> {
    a: &'a Flat,
    b: &'a Flat,
    memo: HashMap<u64, u32>,
    deadline: Instant,
    ticks: Cell<u32>,
    pub timed_out: Cell<bool>,
    pub pairs: u64,
}

impl<'a> Selkow<'a> {
    pub fn new(a: &'a Flat, b: &'a Flat, deadline: Instant) -> Self {
        Self {
            a,
            b,
            memo: HashMap::new(),
            deadline,
            ticks: Cell::new(0),
            timed_out: Cell::new(false),
            pairs: 0,
        }
    }

    pub fn run(&mut self) -> Option<u32> {
        let d = self.dist(self.a.root(), self.b.root());
        if self.timed_out.get() {
            None
        } else {
            Some(d)
        }
    }

    fn dist(&mut self, x: u32, y: u32) -> u32 {
        let key = (u64::from(x) << 32) | u64::from(y);
        if let Some(&v) = self.memo.get(&key) {
            return v;
        }
        let t = self.ticks.get() + 1;
        self.ticks.set(t);
        if t % 1024 == 0 && Instant::now() >= self.deadline {
            self.timed_out.set(true);
        }
        if self.timed_out.get() {
            return 0;
        }
        self.pairs += 1;
        let (a, b) = (self.a, self.b);
        let (ka, kb) = (&a.kids[x as usize], &b.kids[y as usize]);
        let (p, q) = (ka.len(), kb.len());
        let w = q + 1;
        let mut f = vec![0u32; (p + 1) * w];
        for i in 1..=p {
            f[i * w] = f[(i - 1) * w] + a.size[ka[i - 1] as usize];
        }
        for j in 1..=q {
            f[j] = f[j - 1] + b.size[kb[j - 1] as usize];
        }
        for i in 1..=p {
            for j in 1..=q {
                let sub = self.dist(ka[i - 1], kb[j - 1]);
                let del = f[(i - 1) * w + j] + a.size[ka[i - 1] as usize];
                let ins = f[i * w + j - 1] + b.size[kb[j - 1] as usize];
                f[i * w + j] = del.min(ins).min(f[(i - 1) * w + j - 1] + sub);
            }
        }
        let v = u32::from(a.label[x as usize] != b.label[y as usize]) + f[p * w + q];
        self.memo.insert(key, v);
        v
    }
}

pub fn median(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}
