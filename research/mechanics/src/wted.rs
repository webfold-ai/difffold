//! A banded Zhang-Shasha tree edit distance with arbitrary per-node costs, a lexicographic secondary
//! objective packed into the low bits, a traceback, and a count of optimal mappings.
//!
//! Costs are `primary * k + secondary` with `secondary < k`. Every unmapped node must cost at least
//! `m0` primary units, which makes the shift bound `|i - j| <= cap / m0` exact (the same argument as
//! `difffold::ted`).

use difffold::ted::PostTree;

/// A cost that can never be part of an accepted mapping.
pub const FORBID: u64 = u64::MAX / 8;

pub trait Costs {
    /// Cost of mapping node `x` of the first tree to node `y` of the second (1-based postorder).
    fn pair(&self, x: usize, y: usize) -> u64;
    /// Cost of deleting node `x` of the first tree.
    fn del(&self, x: usize) -> u64;
    /// Cost of inserting node `y` of the second tree.
    fn ins(&self, y: usize) -> u64;
}

#[derive(Clone, Copy)]
pub struct Params {
    pub k: u64,
    pub m0: u64,
}

#[derive(Clone, Copy)]
struct Geo {
    w: usize,
    t: usize,
    inf: u64,
}

fn adiff(x: usize, y: usize) -> usize {
    x.abs_diff(y)
}

fn bidx(g: Geo, x: usize, y: usize) -> usize {
    x * g.w + (y + g.t - x)
}

fn cell(g: Geo, fd: &[u64], p: usize, q: usize) -> u64 {
    if adiff(p, q) <= g.t {
        fd[bidx(g, p, q)]
    } else {
        g.inf
    }
}

fn cellf(g: Geo, f: &[f64], p: usize, q: usize) -> f64 {
    if adiff(p, q) <= g.t {
        f[bidx(g, p, q)]
    } else {
        0.0
    }
}

fn add(g: Geo, a: u64, b: u64) -> u64 {
    let s = a.saturating_add(b);
    if s >= g.inf {
        g.inf
    } else {
        s
    }
}

pub struct Solved {
    pub value: u64,
    /// Number of optimal mappings (only with counting on).
    pub count: f64,
    g: Geo,
    td: Vec<u64>,
}

/// Bytes the tables of a solve would take.
pub fn bytes_needed(n: usize, m: usize, cap: u64, p: Params, counting: bool) -> u128 {
    let t = (cap / p.m0) as u128;
    let w = 2 * t + 1;
    let per = if counting { 8 + 8 + 8 + 8 } else { 8 };
    ((n + 1) as u128 * w * per * 2) + (n.max(m) as u128 + 1) * w * if counting { 16 } else { 8 }
}

#[allow(clippy::too_many_arguments)]
fn fill<C: Costs>(
    a: &PostTree,
    b: &PostTree,
    c: &C,
    g: Geo,
    tabs: &mut Tabs,
    fd: &mut [u64],
    nfd: &mut [f64],
    (i0, j0): (usize, usize),
    stop: bool,
    counting: bool,
) {
    let (t, inf) = (g.t, g.inf);
    let li = a.lml[i0 - 1] as usize;
    let lj = b.lml[j0 - 1] as usize;
    let si = i0 - li + 1;
    let sj = j0 - lj + 1;
    fd[bidx(g, 0, 0)] = 0;
    if counting {
        nfd[bidx(g, 0, 0)] = 1.0;
    }
    let mut acc = 0u64;
    for q in 1..=sj.min(t) {
        acc = add(g, acc, c.ins(lj + q - 1));
        fd[bidx(g, 0, q)] = acc;
        if counting {
            nfd[bidx(g, 0, q)] = if acc < inf { 1.0 } else { 0.0 };
        }
    }
    acc = 0;
    for p in 1..=si.min(t) {
        acc = add(g, acc, c.del(li + p - 1));
        fd[bidx(g, p, 0)] = acc;
        if counting {
            nfd[bidx(g, p, 0)] = if acc < inf { 1.0 } else { 0.0 };
        }
    }
    for p in 1..=si {
        let qlo = p.saturating_sub(t).max(1);
        let qhi = sj.min(p + t);
        let x = li + p - 1;
        let lx = a.lml[x - 1] as usize;
        let mut row_min = if p <= t { fd[bidx(g, p, 0)] } else { inf };
        if qlo > qhi {
            break;
        }
        let dx = c.del(x);
        for q in qlo..=qhi {
            let y = lj + q - 1;
            let ly = b.lml[y - 1] as usize;
            let delv = add(g, cell(g, fd, p - 1, q), dx);
            let insv = add(g, cell(g, fd, p, q - 1), c.ins(y));
            let leaf = lx == li && ly == lj;
            let in_band = adiff(x, y) <= t;
            let (v, cnt);
            if leaf {
                let pc = c.pair(x, y);
                let ren = add(g, cell(g, fd, p - 1, q - 1), pc);
                v = delv.min(insv).min(ren).min(inf);
                if in_band {
                    tabs.td[bidx(g, x, y)] = v;
                    if counting {
                        tabs.tdm[bidx(g, x, y)] = ren;
                        tabs.ntdm[bidx(g, x, y)] = if ren < inf {
                            cellf(g, nfd, p - 1, q - 1)
                        } else {
                            0.0
                        };
                    }
                }
                cnt = if counting && v < inf {
                    count3(
                        g,
                        fd,
                        nfd,
                        c,
                        (p, q),
                        (x, y),
                        v,
                        delv,
                        insv,
                        ren,
                        cellf(g, nfd, p - 1, q - 1),
                    )
                } else {
                    0.0
                };
            } else if counting {
                let (tdm, ntdm) = if in_band {
                    (tabs.tdm[bidx(g, x, y)], tabs.ntdm[bidx(g, x, y)])
                } else {
                    (inf, 0.0)
                };
                let sub = add(g, cell(g, fd, lx - li, ly - lj), tdm);
                v = delv.min(insv).min(sub).min(inf);
                let nsub = cellf(g, nfd, lx - li, ly - lj) * ntdm;
                cnt = if v < inf {
                    count3(g, fd, nfd, c, (p, q), (x, y), v, delv, insv, sub, nsub)
                } else {
                    0.0
                };
            } else {
                let tdv = if in_band { tabs.td[bidx(g, x, y)] } else { inf };
                let sub = add(g, cell(g, fd, lx - li, ly - lj), tdv);
                v = delv.min(insv).min(sub).min(inf);
                cnt = 0.0;
            }
            fd[bidx(g, p, q)] = v;
            if counting {
                nfd[bidx(g, p, q)] = cnt;
            }
            row_min = row_min.min(v);
        }
        if stop && row_min >= inf {
            break;
        }
    }
}

/// Disjoint count of optimal mappings: x deleted, or x mapped and y inserted, or x mapped to y.
#[allow(clippy::too_many_arguments)]
fn count3<C: Costs>(
    g: Geo,
    fd: &[u64],
    nfd: &[f64],
    c: &C,
    (p, q): (usize, usize),
    (x, y): (usize, usize),
    v: u64,
    delv: u64,
    insv: u64,
    subv: u64,
    nsub: f64,
) -> f64 {
    let mut n = 0.0;
    if delv == v {
        n += cellf(g, nfd, p - 1, q);
    }
    if insv == v {
        // Mappings of (F, G - y) with y unmapped, minus those that also leave x unmapped.
        let mut b = cellf(g, nfd, p, q - 1);
        let both = add(g, cell(g, fd, p - 1, q - 1), c.del(x));
        if both == cell(g, fd, p, q - 1) {
            b -= cellf(g, nfd, p - 1, q - 1);
        }
        n += b;
    }
    if subv == v {
        n += nsub;
    }
    let _ = y;
    n
}

struct Tabs {
    td: Vec<u64>,
    tdm: Vec<u64>,
    ntdm: Vec<f64>,
}

/// Solve with a primary budget `cap` (in primary units). `None` when the optimum exceeds it.
pub fn solve<C: Costs>(
    a: &PostTree,
    b: &PostTree,
    c: &C,
    p: Params,
    cap: u64,
    counting: bool,
) -> Option<Solved> {
    let (n, m) = (a.len(), b.len());
    let t = (cap / p.m0) as usize;
    let inf = (cap + 1) * p.k;
    if adiff(n, m) > t {
        return None;
    }
    let g = Geo {
        w: 2 * t + 1,
        t,
        inf,
    };
    let mut tabs = Tabs {
        td: vec![inf; (n + 1) * g.w],
        tdm: if counting {
            vec![inf; (n + 1) * g.w]
        } else {
            Vec::new()
        },
        ntdm: if counting {
            vec![0.0; (n + 1) * g.w]
        } else {
            Vec::new()
        },
    };
    let rows = n.max(m) + 1;
    let mut fd = vec![inf; rows * g.w];
    let mut nfd = if counting {
        vec![0.0; rows * g.w]
    } else {
        Vec::new()
    };
    for &i0 in &a.keyroots {
        let i0 = i0 as usize;
        let li = a.lml[i0 - 1] as usize;
        for &j0 in &b.keyroots {
            let j0 = j0 as usize;
            let lj = b.lml[j0 - 1] as usize;
            if adiff(li, lj) > 2 * t {
                continue;
            }
            fill(
                a,
                b,
                c,
                g,
                &mut tabs,
                &mut fd,
                &mut nfd,
                (i0, j0),
                true,
                counting,
            );
        }
    }
    if adiff(n, m) > t {
        return None;
    }
    let value = tabs.td[bidx(g, n, m)];
    if value >= inf {
        return None;
    }
    // The count of the whole-tree window is the last cell written for (n, m); recompute it.
    let mut count = 0.0;
    if counting {
        let mut fd2 = vec![inf; rows * g.w];
        let mut nfd2 = vec![0.0; rows * g.w];
        fill(
            a,
            b,
            c,
            g,
            &mut tabs,
            &mut fd2,
            &mut nfd2,
            (n, m),
            false,
            true,
        );
        count = nfd2[bidx(g, n, m)];
    }
    Some(Solved {
        value,
        count,
        g,
        td: tabs.td,
    })
}

/// Doubling driver. Returns the solution and the cap that succeeded; an error past `cap_max` or `mem_max`.
#[allow(clippy::too_many_arguments)] // Flat arguments mirror `solve`.
pub fn solve_auto<C: Costs>(
    a: &PostTree,
    b: &PostTree,
    c: &C,
    p: Params,
    cap0: u64,
    cap_max: u64,
    mem_max: u128,
    counting: bool,
) -> Result<(Solved, u64), String> {
    let mut cap = cap0.max(1);
    loop {
        let capc = cap.min(cap_max);
        if bytes_needed(a.len(), b.len(), capc, p, counting) > mem_max {
            return Err(format!("memory: cap {capc}"));
        }
        if let Some(s) = solve(a, b, c, p, capc, counting) {
            return Ok((s, capc));
        }
        if capc >= cap_max {
            return Err("no mapping within cap".into());
        }
        cap = cap.saturating_mul(2);
    }
}

impl Solved {
    /// One optimal mapping (1-based postorder pairs), ties broken toward matching.
    pub fn mapping<C: Costs>(
        &self,
        a: &PostTree,
        b: &PostTree,
        c: &C,
        prefer_match: bool,
    ) -> Vec<(u32, u32)> {
        let g = self.g;
        let (n, m) = (a.len(), b.len());
        let mut td = self.td.clone();
        let mut tabs = Tabs {
            td: std::mem::take(&mut td),
            tdm: Vec::new(),
            ntdm: Vec::new(),
        };
        let mut to_b = vec![0usize; n + 1];
        let mut stack = vec![(n, m)];
        while let Some((i, j)) = stack.pop() {
            let li = a.lml[i - 1] as usize;
            let lj = b.lml[j - 1] as usize;
            let si = i - li + 1;
            let sj = j - lj + 1;
            let mut fd = vec![g.inf; (si + 1) * g.w];
            let mut nf = Vec::new();
            fill(
                a,
                b,
                c,
                g,
                &mut tabs,
                &mut fd,
                &mut nf,
                (i, j),
                false,
                false,
            );
            let (mut p, mut q) = (si, sj);
            while p + q > 0 {
                let v = cell(g, &fd, p, q);
                let x = li + p.max(1) - 1;
                let y = lj + q.max(1) - 1;
                let lx = a.lml[x - 1] as usize;
                let ly = b.lml[y - 1] as usize;
                let leaf = p > 0 && q > 0 && lx == li && ly == lj;
                let diag_ok = if p > 0 && q > 0 {
                    if leaf {
                        let pc = c.pair(x, y);
                        pc < g.inf && add(g, cell(g, &fd, p - 1, q - 1), pc) == v
                    } else {
                        let tdv = if adiff(x, y) <= g.t {
                            tabs.td[bidx(g, x, y)]
                        } else {
                            g.inf
                        };
                        add(g, cell(g, &fd, lx - li, ly - lj), tdv) == v
                    }
                } else {
                    false
                };
                let del_ok = p > 0 && add(g, cell(g, &fd, p - 1, q), c.del(x)) == v;
                let ins_ok = q > 0 && add(g, cell(g, &fd, p, q - 1), c.ins(y)) == v;
                let go_diag = if prefer_match && diag_ok {
                    true
                } else if del_ok || ins_ok {
                    false
                } else {
                    diag_ok
                };
                if go_diag {
                    if leaf {
                        to_b[x] = y;
                        p -= 1;
                        q -= 1;
                    } else {
                        stack.push((x, y));
                        p = lx - li;
                        q = ly - lj;
                    }
                } else if del_ok {
                    p -= 1;
                } else {
                    q -= 1;
                }
            }
        }
        (1..=n)
            .filter(|&x| to_b[x] != 0)
            .map(|x| (x as u32, to_b[x] as u32))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// A random tree as postorder child lists.
    fn random_tree(r: &mut Rng, n: usize) -> PostTree {
        let mut parent = vec![usize::MAX; n];
        for (i, p) in parent.iter_mut().enumerate().skip(1) {
            *p = r.below(i as u64) as usize;
        }
        let mut kids: Vec<Vec<usize>> = vec![Vec::new(); n];
        for i in 1..n {
            kids[parent[i]].push(i);
        }
        let mut post = Vec::new();
        let mut stack = vec![(0usize, 0usize)];
        while let Some((v, k)) = stack.pop() {
            if k < kids[v].len() {
                stack.push((v, k + 1));
                stack.push((kids[v][k], 0));
            } else {
                post.push(v);
            }
        }
        let mut pos = vec![0u32; n];
        for (i, &v) in post.iter().enumerate() {
            pos[v] = i as u32;
        }
        let pk: Vec<Vec<u32>> = post
            .iter()
            .map(|&v| kids[v].iter().map(|&c| pos[c]).collect())
            .collect();
        PostTree::from_kids((0..n).map(|_| r.below(3) as u32).collect(), &pk)
    }

    struct Mat {
        pair: Vec<Vec<u64>>,
        del: Vec<u64>,
        ins: Vec<u64>,
    }
    impl Costs for Mat {
        fn pair(&self, x: usize, y: usize) -> u64 {
            self.pair[x - 1][y - 1]
        }
        fn del(&self, x: usize) -> u64 {
            self.del[x - 1]
        }
        fn ins(&self, y: usize) -> u64 {
            self.ins[y - 1]
        }
    }

    fn legal(a: &PostTree, b: &PostTree, pr: &[(usize, usize)]) -> bool {
        for (i, &(x1, y1)) in pr.iter().enumerate() {
            for &(x2, y2) in &pr[i + 1..] {
                let (lo, hi) = if x1 < x2 {
                    ((x1, y1), (x2, y2))
                } else {
                    ((x2, y2), (x1, y1))
                };
                if lo.1 >= hi.1 {
                    return false;
                }
                let anc_a = a.lml[hi.0 - 1] as usize <= lo.0;
                let anc_b = b.lml[hi.1 - 1] as usize <= lo.1;
                if anc_a != anc_b {
                    return false;
                }
            }
        }
        true
    }

    /// Brute force: (min cost, number of optimal mappings).
    fn brute(a: &PostTree, b: &PostTree, c: &Mat) -> (u64, f64) {
        #[allow(clippy::too_many_arguments)]
        fn rec(
            x: usize,
            a: &PostTree,
            b: &PostTree,
            c: &Mat,
            used: &mut Vec<bool>,
            cur: &mut Vec<(usize, usize)>,
            cost: u64,
            best: &mut (u64, f64),
        ) {
            let (n, m) = (a.len(), b.len());
            if x > n {
                let mut tot = cost;
                for y in 1..=m {
                    if !used[y - 1] {
                        tot += c.ins(y);
                    }
                }
                if tot < best.0 {
                    *best = (tot, 1.0);
                } else if tot == best.0 {
                    best.1 += 1.0;
                }
                return;
            }
            rec(x + 1, a, b, c, used, cur, cost + c.del(x), best);
            for y in 1..=m {
                if used[y - 1] || c.pair(x, y) >= FORBID {
                    continue;
                }
                cur.push((x, y));
                if legal(a, b, cur) {
                    used[y - 1] = true;
                    rec(x + 1, a, b, c, used, cur, cost + c.pair(x, y), best);
                    used[y - 1] = false;
                }
                cur.pop();
            }
        }
        let mut best = (u64::MAX, 0.0);
        rec(
            1,
            a,
            b,
            c,
            &mut vec![false; b.len()],
            &mut Vec::new(),
            0,
            &mut best,
        );
        best
    }

    #[test]
    fn matches_brute_force_value_count_and_mapping() {
        let mut r = Rng(0x1234_5678_9abc_def1);
        let k = 64;
        let mut multi = 0;
        for round in 0..300 {
            let n = 1 + r.below(6) as usize;
            let m = 1 + r.below(6) as usize;
            let a = random_tree(&mut r, n);
            let b = random_tree(&mut r, m);
            let c = Mat {
                pair: (0..n)
                    .map(|_| {
                        (0..m)
                            .map(|_| {
                                if r.below(8) == 0 {
                                    FORBID
                                } else {
                                    r.below(4) * k + r.below(3)
                                }
                            })
                            .collect()
                    })
                    .collect(),
                del: (0..n).map(|_| (1 + r.below(2)) * k + r.below(3)).collect(),
                ins: (0..m).map(|_| (1 + r.below(2)) * k + r.below(3)).collect(),
            };
            let (bv, bc) = brute(&a, &b, &c);
            let p = Params { k, m0: 1 };
            let cap = bv / k + 2;
            let s = solve(&a, &b, &c, p, cap, true).expect("solvable");
            assert_eq!(s.value, bv, "value, round {round}");
            assert_eq!(s.count, bc, "count, round {round}");
            multi += usize::from(bc > 1.0);
            let s2 = solve(&a, &b, &c, p, cap, false).expect("solvable");
            assert_eq!(s2.value, bv);
            for pm in [true, false] {
                let mp = s.mapping(&a, &b, &c, pm);
                let pr: Vec<(usize, usize)> =
                    mp.iter().map(|&(x, y)| (x as usize, y as usize)).collect();
                assert!(legal(&a, &b, &pr), "legal mapping, round {round}");
                let mut tot = 0;
                let (mut ua, mut ub) = (vec![false; n], vec![false; m]);
                for &(x, y) in &pr {
                    tot += c.pair(x, y);
                    ua[x - 1] = true;
                    ub[y - 1] = true;
                }
                for x in 1..=n {
                    if !ua[x - 1] {
                        tot += c.del(x);
                    }
                }
                for y in 1..=m {
                    if !ub[y - 1] {
                        tot += c.ins(y);
                    }
                }
                assert_eq!(tot, bv, "mapping cost, round {round}");
            }
        }
        assert!(multi > 20, "the test must exercise ties: {multi}");
    }
}
