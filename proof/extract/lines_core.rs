// Extraction-friendly copy of the newline-search helpers of `src/lines.rs`.
//
// Aeneas rejects the real `first_nl` and `last_nl`: they recurse through the closure arguments of
// `Option::or_else` and `Option::map`, and Aeneas reports "Mixed-recursive declaration groups are
// not supported" (a function mutually recursive with the `FnOnce::call_once` impl of its own
// closure). The only change here is that the two closures are written as `match` on the recursive
// result. The bodies of `nl_mask`, `word`, `first_in_block` and `last_in_block` are verbatim (they
// are copied only because `lines.rs` keeps them private). No `//!` comments, so the agreement test
// can `include!` this file.
// `tests/agree.rs` in `proof/extract-lines` checks the copy against the real file on random input.

pub fn nl_mask(w: u64) -> u64 {
    const LOW7: u64 = 0x7F7F_7F7F_7F7F_7F7F;
    let x = w ^ 0x0A0A_0A0A_0A0A_0A0A;
    !(((x & LOW7) + LOW7) | x | LOW7)
}

pub fn word(t: &[u8]) -> u64 {
    match t.len() {
        0 => 0,
        n if n >= 8 => u64::from_le_bytes([t[0], t[1], t[2], t[3], t[4], t[5], t[6], t[7]]),
        n => word(&t[..n - 1]) | (u64::from(t[n - 1]) << (8 * (n - 1))),
    }
}

pub fn first_in_block(t: &[u8], at: usize) -> Option<usize> {
    if at >= t.len() {
        None
    } else {
        let m = nl_mask(word(&t[at..]));
        if m != 0 {
            Some(at + (m.trailing_zeros() / 8) as usize)
        } else {
            first_in_block(t, at + 8)
        }
    }
}

pub fn first_nl(t: &[u8]) -> Option<usize> {
    if t.len() <= 64 {
        first_in_block(t, 0)
    } else {
        match first_nl(&t[..t.len() / 2]) {
            Some(i) => Some(i),
            None => match first_nl(&t[t.len() / 2..]) {
                Some(i) => Some(i + t.len() / 2),
                None => None,
            },
        }
    }
}

pub fn last_in_block(t: &[u8]) -> Option<usize> {
    match t.len() {
        0 => None,
        n if t[n - 1] == b'\n' => Some(n - 1),
        n => last_in_block(&t[..n - 1]),
    }
}

pub fn last_nl(t: &[u8]) -> Option<usize> {
    if t.len() <= 64 {
        last_in_block(t)
    } else {
        match last_nl(&t[t.len() / 2..]) {
            Some(i) => Some(i + t.len() / 2),
            None => last_nl(&t[..t.len() / 2]),
        }
    }
}
