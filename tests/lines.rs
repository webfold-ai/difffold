//! The line differ must return a minimal script: cost = n + m - 2 * LCS, and replay must hold.
use difffold::lines::{diff_ids, diff_text, replay_ok};

fn lcs(a: &[u32], b: &[u32]) -> usize {
    let mut t = vec![vec![0usize; b.len() + 1]; a.len() + 1];
    for i in 1..=a.len() {
        for j in 1..=b.len() {
            t[i][j] = if a[i - 1] == b[j - 1] { t[i - 1][j - 1] + 1 } else { t[i - 1][j].max(t[i][j - 1]) };
        }
    }
    t[a.len()][b.len()]
}

#[test]
fn minimal_on_random_small_inputs() {
    let mut s = 0x1234_5678_9abc_def0u64;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for round in 0..40_000 {
        let alpha = 2 + (next() % 5) as u32;
        let (n, m) = ((next() % 14) as usize, (next() % 14) as usize);
        let a: Vec<u32> = (0..n).map(|_| (next() % u64::from(alpha)) as u32).collect();
        let b: Vec<u32> = (0..m).map(|_| (next() % u64::from(alpha)) as u32).collect();
        let d = diff_ids(&a, &b, alpha as usize);
        assert_eq!(d.cost(), n + m - 2 * lcs(&a, &b), "round {round}: a={a:?} b={b:?}");
        let ka: Vec<u32> = a.iter().zip(&d.deleted).filter(|(_, &x)| !x).map(|(v, _)| *v).collect();
        let kb: Vec<u32> = b.iter().zip(&d.inserted).filter(|(_, &x)| !x).map(|(v, _)| *v).collect();
        assert_eq!(ka, kb, "kept lines must agree: a={a:?} b={b:?}");
    }
}

#[test]
fn text_replay_and_final_newline() {
    let old = b"a\nb\nc\n";
    let new = b"a\nB\nc";
    let d = diff_text(old, new);
    assert!(replay_ok(old, new, &d));
    assert_eq!(d.cost(), 4, "b -> B and c\\n -> c are two replacements");
    assert_eq!(diff_text(b"", b"").cost(), 0);
    assert_eq!(diff_text(b"x\n", b"").cost(), 1);
}

#[test]
fn text_level_fuzz_matches_id_level() {
    let mut s = 0xdead_beef_cafe_f00du64;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let pieces: [&[u8]; 6] = [b"a\n", b"b\n", b"c\n", b"ab\n", b"\n", b"tail"];
    for _ in 0..20_000 {
        let mk = |next: &mut dyn FnMut() -> u64| {
            let n = (next() % 9) as usize;
            let mut t = Vec::new();
            for _ in 0..n {
                t.extend_from_slice(pieces[(next() % 6) as usize]);
            }
            t
        };
        let (a, b) = (mk(&mut next), mk(&mut next));
        let d = diff_text(&a, &b);
        assert!(replay_ok(&a, &b, &d), "replay a={a:?} b={b:?}");
        // Reference: split exactly and run the id-level search.
        let split = |t: &[u8]| -> Vec<Vec<u8>> {
            let mut out = Vec::new();
            let mut st = 0;
            for (i, &c) in t.iter().enumerate() {
                if c == b'\n' {
                    out.push(t[st..=i].to_vec());
                    st = i + 1;
                }
            }
            if st < t.len() {
                out.push(t[st..].to_vec());
            }
            out
        };
        let (la, lb) = (split(&a), split(&b));
        let mut ids = std::collections::HashMap::new();
        let mut id = |l: &Vec<u8>| {
            let n = ids.len() as u32;
            *ids.entry(l.clone()).or_insert(n)
        };
        let ia: Vec<u32> = la.iter().map(&mut id).collect();
        let ib: Vec<u32> = lb.iter().map(&mut id).collect();
        assert_eq!(d.cost(), n_cost(&ia, &ib), "a={a:?} b={b:?}");
    }
}

fn n_cost(a: &[u32], b: &[u32]) -> usize {
    a.len() + b.len() - 2 * lcs(a, b)
}

#[test]
fn histogram_is_valid_and_never_beats_minimal() {
    use difffold::lines::diff_histogram_ids;
    let mut s = 0x0123_4567_89ab_cdefu64;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let mut worse = 0;
    for _ in 0..30_000 {
        let alpha = 2 + (next() % 8) as u32;
        let (n, m) = ((next() % 30) as usize, (next() % 30) as usize);
        let a: Vec<u32> = (0..n).map(|_| (next() % u64::from(alpha)) as u32).collect();
        let b: Vec<u32> = (0..m).map(|_| (next() % u64::from(alpha)) as u32).collect();
        let d = diff_histogram_ids(&a, &b, alpha as usize);
        let ka: Vec<u32> = a.iter().zip(&d.deleted).filter(|(_, &x)| !x).map(|(v, _)| *v).collect();
        let kb: Vec<u32> = b.iter().zip(&d.inserted).filter(|(_, &x)| !x).map(|(v, _)| *v).collect();
        assert_eq!(ka, kb, "histogram kept lines must agree: a={a:?} b={b:?}");
        let min = n + m - 2 * lcs(&a, &b);
        assert!(d.cost() >= min);
        worse += usize::from(d.cost() > min);
    }
    eprintln!("histogram strictly worse than minimal in {worse} of 30000 random cases");
}
