// Extraction-friendly copies of the pure cores of `src/ted.rs`, for Charon and Aeneas.
// 
// Stock Aeneas cannot translate the whole of `src/ted.rs` (see `proof/README.md`). This file holds
// faithful copies of `PostTree::from_kids`, `label_lower_bound`, `fill_window` and `within_td`, with
// only the constructs Aeneas cannot handle removed: the `Stats` counters (diagnostics), the `kids`
// field kept for `mirror`, closures (`map_or`, `tdi`, `in_band`, `fdi`, `get`, `filter`), `for` loops
// over ranges (rewritten as `while`), `usize::max`/`min`/`abs_diff` (small helper functions), `vec![x; n]`
// (push loops), `then_some` and `u32::from(bool)` (`if`). The arithmetic, the control flow and the order of
// the writes are those of the real functions. `tests/ted_core.rs` compiles the real `src/ted.rs` and checks
// every function here against it on random inputs, so the copy is tied to the shipped code.
// 
// Preconditions a proof must carry, because Aeneas makes every `+` overflow-checked: `tau < u32::MAX`,
// `kids[i]` holds only indices below `i` (postorder), and the sizes keep `(n + 1) * (2 * tau + 1)` and
// the like below `usize::MAX`.

/// The postorder tree without the `kids` field of the real `PostTree`, which only `mirror` reads.
pub struct PostTree {
    pub label: Vec<u32>,
    pub lml: Vec<u32>,
    pub keyroots: Vec<u32>,
}

/// `PostTree::from_kids`.
pub fn from_kids(label: Vec<u32>, kids: &[Vec<u32>]) -> PostTree {
    let n = label.len();
    let mut lml: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < n {
        lml.push(0);
        i += 1;
    }
    i = 0;
    while i < n {
        let v = if kids[i].len() == 0 {
            i as u32 + 1
        } else {
            let k = kids[i][0];
            lml[k as usize]
        };
        lml[i] = v;
        i += 1;
    }
    let mut seen: Vec<bool> = Vec::new();
    i = 0;
    while i < n + 2 {
        seen.push(false);
        i += 1;
    }
    let mut keyroots: Vec<u32> = Vec::new();
    i = n;
    while i > 0 {
        i -= 1;
        let l = lml[i] as usize;
        if !seen[l] {
            seen[l] = true;
            keyroots.push(i as u32 + 1);
        }
    }
    keyroots.reverse();
    PostTree { label, lml, keyroots }
}

/// The larger of two `usize`.
pub fn umax(x: usize, y: usize) -> usize {
    if x >= y {
        x
    } else {
        y
    }
}

/// The smaller of two `usize`.
pub fn umin(x: usize, y: usize) -> usize {
    if x <= y {
        x
    } else {
        y
    }
}

/// `usize::abs_diff`.
pub fn adiff(x: usize, y: usize) -> usize {
    if x >= y {
        x - y
    } else {
        y - x
    }
}

/// The smaller of two `u32`.
pub fn min32(x: u32, y: u32) -> u32 {
    if x <= y {
        x
    } else {
        y
    }
}

/// `label_lower_bound`. The `match` on `cmp` is an `if` chain.
pub fn label_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    let mut la = a.label.clone();
    let mut lb = b.label.clone();
    la.sort_unstable();
    lb.sort_unstable();
    let mut i = 0;
    let mut j = 0;
    let mut common = 0u32;
    while i < la.len() && j < lb.len() {
        if la[i] < lb[j] {
            i += 1;
        } else if la[i] > lb[j] {
            j += 1;
        } else {
            common += 1;
            i += 1;
            j += 1;
        }
    }
    umax(a.label.len(), b.label.len()) as u32 - common
}

/// The band index `x * w + (y + t - x)` of both `td` and `fd`.
pub fn bidx(w: usize, t: usize, x: usize, y: usize) -> usize {
    x * w + (y + t - x)
}

/// The `get` closure of `fill_window`: the cell, or `inf` outside the band.
pub fn get(fd: &[u32], w: usize, t: usize, inf: u32, pp: usize, qq: usize) -> u32 {
    if adiff(pp, qq) <= t {
        fd[bidx(w, t, pp, qq)]
    } else {
        inf
    }
}

/// `fill_window`, with `(i0, j0)` as two parameters.
pub fn fill_window(a: &PostTree, b: &PostTree, td: &mut [u32], fd: &mut [u32], i0: usize, j0: usize, tau: u32) {
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    let li = a.lml[i0 - 1] as usize;
    let lj = b.lml[j0 - 1] as usize;
    let si = i0 - li + 1;
    let sj = j0 - lj + 1;
    fd[bidx(w, t, 0, 0)] = 0;
    let lim_q = umin(sj, t);
    let mut q = 1;
    while q <= lim_q {
        fd[bidx(w, t, 0, q)] = q as u32;
        q += 1;
    }
    let lim_p = umin(si, t);
    let mut p = 1;
    while p <= lim_p {
        fd[bidx(w, t, p, 0)] = p as u32;
        p += 1;
    }
    p = 1;
    while p <= si {
        let qlo = umax(p.saturating_sub(t), 1);
        let qhi = umin(sj, p + t);
        let x = li + p - 1;
        let lx = a.lml[x - 1] as usize;
        let mut row_min = if p <= t { fd[bidx(w, t, p, 0)] } else { inf };
        q = qlo;
        while q <= qhi {
            let y = lj + q - 1;
            let ly = b.lml[y - 1] as usize;
            let del = get(fd, w, t, inf, p - 1, q) + 1;
            let ins = get(fd, w, t, inf, p, q - 1) + 1;
            let v = if lx == li && ly == lj {
                let ren = if a.label[x - 1] != b.label[y - 1] { 1 } else { 0 };
                let diag = get(fd, w, t, inf, p - 1, q - 1) + ren;
                let v = min32(min32(min32(del, ins), diag), inf);
                if adiff(x, y) <= t {
                    td[bidx(w, t, x, y)] = v;
                }
                v
            } else {
                let tdv = if adiff(x, y) <= t { td[bidx(w, t, x, y)] } else { inf };
                let sub = get(fd, w, t, inf, lx - li, ly - lj) + tdv;
                min32(min32(min32(del, ins), sub), inf)
            };
            fd[bidx(w, t, p, q)] = v;
            row_min = min32(row_min, v);
            q += 1;
        }
        if qlo > qhi || row_min > tau {
            break;
        }
        p += 1;
    }
}

/// `within_td`, without the `Stats` argument.
pub fn within_td(a: &PostTree, b: &PostTree, tau: u32) -> (Option<u32>, Vec<u32>) {
    let n = a.label.len();
    let m = b.label.len();
    if adiff(n, m) as u32 > tau {
        return (None, Vec::new());
    }
    if n == 0 || m == 0 {
        let d = umax(n, m) as u32;
        if d <= tau {
            return (Some(d), Vec::new());
        } else {
            return (None, Vec::new());
        }
    }
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    let mut td: Vec<u32> = Vec::new();
    let mut k = 0;
    while k < (n + 1) * w {
        td.push(inf);
        k += 1;
    }
    let rows = umax(n, m) + 1;
    let mut fd: Vec<u32> = Vec::new();
    k = 0;
    while k < rows * w {
        fd.push(inf);
        k += 1;
    }
    let mut ia = 0;
    while ia < a.keyroots.len() {
        let i0 = a.keyroots[ia] as usize;
        let li = a.lml[i0 - 1] as usize;
        let mut ib = 0;
        while ib < b.keyroots.len() {
            let j0 = b.keyroots[ib] as usize;
            let lj = b.lml[j0 - 1] as usize;
            if adiff(li, lj) <= 2 * t {
                fill_window(a, b, &mut td, &mut fd, i0, j0, tau);
            }
            ib += 1;
        }
        ia += 1;
    }
    let d = if adiff(n, m) <= t { td[bidx(w, t, n, m)] } else { inf };
    if d <= tau {
        (Some(d), td)
    } else {
        (None, td)
    }
}
