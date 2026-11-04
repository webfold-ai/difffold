// Extraction-friendly copy of the pure pieces of the line search in `src/lines.rs`.
//
// Aeneas rejects closures that sit in recursive groups, and `lines.rs` keeps its helpers private, so
// this file holds copies: `common_prefix` and `common_suffix` verbatim; `snake` and `snake_back` take the
// two id lists instead of the `Search` state (`n` and `m` are the list lengths, which is what
// `middle` stores in `Search`); `line_start` and `suffix_on_line_start` write their `map_or` closures as
// `match` (and the two `starts` tests as nested `if`, because Aeneas mistypes a `bool` let); `count_block`, `count_byte` and `count_lines` are verbatim. The newline helpers `nl_mask`,
// `word`, `first_nl` and `last_nl` come from `lines_core.rs`, which this file is `include!`d after.
// No `//!` comments, so `tests/myers_core.rs` can `include!` it.
// `tests/myers_core.rs` checks every function here against the real `src/lines.rs` on random input.

pub fn common_prefix<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    let n = a.len().min(b.len());
    if n == 0 {
        0
    } else if n == 1 {
        usize::from(a[0] == b[0])
    } else {
        let h = n / 2;
        if a[..h] == b[..h] {
            h + common_prefix(&a[h..], &b[h..])
        } else {
            common_prefix(&a[..h], &b[..h])
        }
    }
}

pub fn common_suffix<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    let n = a.len().min(b.len());
    if n == 0 {
        0
    } else if n == 1 {
        usize::from(a[a.len() - 1] == b[b.len() - 1])
    } else {
        let h = n / 2;
        if a[a.len() - h..] == b[b.len() - h..] {
            h + common_suffix(&a[..a.len() - h], &b[..b.len() - h])
        } else {
            common_suffix(&a[a.len() - h..], &b[b.len() - h..])
        }
    }
}

pub fn snake(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
    let n = a.len() as i32;
    let m = b.len() as i32;
    if x >= n || y >= m || a[x as usize] != b[y as usize] {
        0
    } else {
        common_prefix(&a[x as usize..], &b[y as usize..]) as i32
    }
}

pub fn snake_back(a: &[u32], b: &[u32], x: i32, y: i32) -> i32 {
    let n = a.len() as i32;
    let m = b.len() as i32;
    if x >= n || y >= m || a[(n - 1 - x) as usize] != b[(m - 1 - y) as usize] {
        0
    } else {
        common_suffix(&a[..(n - x) as usize], &b[..(m - y) as usize]) as i32
    }
}

pub fn line_start(t: &[u8], p: usize) -> usize {
    match last_nl(&t[..p]) {
        Some(i) => i + 1,
        None => 0,
    }
}

pub fn shrink_suffix(ro: &[u8], q: usize) -> usize {
    match first_nl(&ro[ro.len() - q..]) {
        Some(k) => q - k - 1,
        None => 0,
    }
}

pub fn suffix_on_line_start(ro: &[u8], rn: &[u8], q: usize) -> usize {
    if q == 0 {
        q
    } else if q < ro.len() && ro[ro.len() - q - 1] != b'\n' {
        shrink_suffix(ro, q)
    } else if q < rn.len() && rn[rn.len() - q - 1] != b'\n' {
        shrink_suffix(ro, q)
    } else {
        q
    }
}

pub fn count_block(t: &[u8]) -> usize {
    if t.is_empty() {
        0
    } else {
        nl_mask(word(t)).count_ones() as usize + count_block(&t[t.len().min(8)..])
    }
}

pub fn count_byte(t: &[u8], _b: u8) -> usize {
    if t.len() <= 64 {
        count_block(t)
    } else {
        count_byte(&t[..t.len() / 2], b'\n') + count_byte(&t[t.len() / 2..], b'\n')
    }
}

pub fn count_lines(t: &[u8]) -> usize {
    count_byte(t, b'\n') + usize::from(!t.is_empty() && t[t.len() - 1] != b'\n')
}
