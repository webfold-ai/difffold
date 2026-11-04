//! Adversarial inputs for the line differ: worst-case edit distance, degenerate shapes, odd bytes.
//! Each case checks replay and, where affordable, minimality against a DP reference.
use difffold::lines::{diff_ids, diff_text, replay_ok};
use std::time::Instant;

fn lcs(a: &[u32], b: &[u32]) -> usize {
    let mut prev = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        let mut cur = vec![0usize; b.len() + 1];
        for j in 1..=b.len() {
            cur[j] = if a[i - 1] == b[j - 1] {
                prev[j - 1] + 1
            } else {
                prev[j].max(cur[j - 1])
            };
        }
        prev = cur;
    }
    prev[b.len()]
}

fn text(ids: &[u32]) -> Vec<u8> {
    ids.iter()
        .flat_map(|i| format!("line{i}\n").into_bytes())
        .collect()
}

fn small_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    // The default test thread stack is 2 MiB. The sweep recursion must fit for every input the DP
    // reference below can also handle.
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn reversed_sequence_maximal_distance() {
    // Every line occurs on both sides, LCS = 1, so D is about 2N.
    small_stack(|| {
        let n = 3000u32;
        let a: Vec<u32> = (0..n).collect();
        let b: Vec<u32> = (0..n).rev().collect();
        let t = Instant::now();
        let d = diff_ids(&a, &b, n as usize);
        eprintln!("reversed n={n}: {:?}", t.elapsed());
        assert_eq!(d.cost(), a.len() + b.len() - 2 * lcs(&a, &b));
    });
}

#[test]
fn two_symbol_random_high_distance() {
    small_stack(|| {
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let a: Vec<u32> = (0..4000).map(|_| (next() & 1) as u32).collect();
        let b: Vec<u32> = (0..4000).map(|_| (next() & 1) as u32).collect();
        let t = Instant::now();
        let d = diff_ids(&a, &b, 2);
        eprintln!("binary random n=4000: {:?}", t.elapsed());
        assert_eq!(d.cost(), a.len() + b.len() - 2 * lcs(&a, &b));
    });
}

#[test]
fn all_distinct_lines_collapse_before_search() {
    let a: Vec<u32> = (0..200_000).collect();
    let b: Vec<u32> = (200_000..400_000).collect();
    let t = Instant::now();
    let d = diff_ids(&a, &b, 400_000);
    eprintln!("200k distinct vs 200k distinct: {:?}", t.elapsed());
    assert_eq!(d.cost(), 400_000);
}

#[test]
fn all_equal_lines_vs_one_changed() {
    let a = vec![0u32; 100_000];
    let mut b = a.clone();
    b[50_000] = 1;
    let d = diff_ids(&a, &b, 2);
    assert_eq!(d.cost(), 2);
}

#[test]
fn huge_single_line() {
    let mut old = vec![b'x'; 8 << 20];
    let mut new = old.clone();
    new[(8 << 20) - 1] = b'y';
    old.push(b'\n');
    new.push(b'\n');
    let t = Instant::now();
    let d = diff_text(&old, &new);
    eprintln!("8 MiB single line: {:?}", t.elapsed());
    assert_eq!(d.cost(), 2);
    assert!(replay_ok(&old, &new, &d));
}

#[test]
fn odd_bytes_and_line_endings() {
    let cases: [(&[u8], &[u8]); 8] = [
        (b"a\r\nb\r\n", b"a\nb\n"),
        (b"a\nb", b"a\nb\n"),
        (b"\0\0\n\xff\xfe\n", b"\0\n\xff\xfe\n"),
        (b"\n\n\n", b"\n\n"),
        (b"", b"\n"),
        (b"\n", b""),
        (b"a\rb\n", b"a\nb\n"),
        (b"same\n", b"same\n"),
    ];
    for (a, b) in cases {
        let d = diff_text(a, b);
        assert!(replay_ok(a, b, &d), "a={a:?} b={b:?}");
    }
    assert_eq!(
        diff_text(b"a\r\nb\r\n", b"a\nb\n").cost(),
        4,
        "CRLF differs from LF byte for byte"
    );
    assert_eq!(diff_text(b"same\n", b"same\n").cost(), 0);
}

#[test]
fn many_duplicate_lines_with_blocks_moved() {
    small_stack(|| {
        // Two copies of a long repeated block with the halves swapped.
        let blk: Vec<u32> = (0..1500).map(|i| i % 7).collect();
        let mut a = blk.clone();
        a.extend((0..1500).map(|i| 7 + i % 5));
        let mut b: Vec<u32> = (0..1500).map(|i| 7 + i % 5).collect();
        b.extend(blk);
        let t = Instant::now();
        let d = diff_ids(&a, &b, 12);
        eprintln!("swapped repeated blocks: {:?}", t.elapsed());
        assert_eq!(d.cost(), a.len() + b.len() - 2 * lcs(&a, &b));
    });
}

#[test]
fn text_level_texts_with_repeated_lines_round_trip() {
    let a: Vec<u32> = (0..2000).map(|i| (i * 7919) % 31).collect();
    let b: Vec<u32> = (0..2000).map(|i| (i * 104_729 + 3) % 29).collect();
    let (ta, tb) = (text(&a), text(&b));
    let d = diff_text(&ta, &tb);
    assert!(replay_ok(&ta, &tb, &d));
}
