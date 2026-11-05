//! Correctness tests for `difffold::levenshtein`. Every implementation is checked against the full
//! dynamic program, which is the reference oracle. The tests are exhaustive on small alphabets and
//! randomised on long inputs. They are tested, not proved.

use difffold::levenshtein::{
    histogram_lower_bound_u32, levenshtein, levenshtein_full_dp, levenshtein_within,
    levenshtein_within_band, levenshtein_within_myers_banded, levenshtein_within_myers_multi,
    levenshtein_within_myers_single, levenshtein_within_u32, levenshtein_within_wavefront,
};

type Within = fn(&[u32], &[u32], u32) -> Option<u32>;

/// Every bounded implementation under test. Each must agree with the oracle on every input.
fn implementations() -> Vec<(&'static str, Within)> {
    vec![
        ("band", levenshtein_within_band::<u32>),
        ("myers_single", levenshtein_within_myers_single::<u32>),
        ("myers_multi", levenshtein_within_myers_multi::<u32>),
        ("dispatch", levenshtein_within::<u32>),
        ("u32_path", levenshtein_within_u32),
        ("wavefront", levenshtein_within_wavefront::<u32>),
        ("myers_banded", levenshtein_within_myers_banded::<u32>),
    ]
}

/// The expected answer of a bounded query, derived from the oracle distance.
fn expected(d: usize, limit: u32) -> Option<u32> {
    let d = u32::try_from(d).expect("test distances fit u32");
    (d <= limit).then_some(d)
}

/// Checks one pair against every implementation at every limit in `limits`.
fn check_pair(a: &[u32], b: &[u32], limits: &[u32]) {
    let d = levenshtein_full_dp(a, b);
    assert_eq!(
        levenshtein(a, b),
        u32::try_from(d).unwrap(),
        "exact levenshtein a={a:?} b={b:?}"
    );
    for &limit in limits {
        let want = expected(d, limit);
        for (name, f) in implementations() {
            assert_eq!(
                f(a, b, limit),
                want,
                "{name}: a={a:?} b={b:?} limit={limit} oracle={d}"
            );
        }
    }
}

/// All sequences of length at most `max_len` over the alphabet `0..alpha`, shortest first.
fn all_sequences(alpha: u32, max_len: usize) -> Vec<Vec<u32>> {
    let mut out = vec![Vec::new()];
    let mut frontier = vec![Vec::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for s in &frontier {
            for c in 0..alpha {
                let mut t = s.clone();
                t.push(c);
                next.push(t);
            }
        }
        out.extend(next.iter().cloned());
        frontier = next;
    }
    out
}

/// Small deterministic generator (xorshift64*). Tests seed it explicitly so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// A random sequence over an alphabet described by `alpha`: a dense range `0..alpha`, or, when
/// `alpha == 0`, sparse random `u32` ids that are almost surely distinct.
fn random_seq(rng: &mut Rng, len: usize, alpha: usize) -> Vec<u32> {
    (0..len)
        .map(|_| {
            if alpha == 0 {
                rng.next_u64() as u32
            } else {
                rng.below(alpha) as u32
            }
        })
        .collect()
}

/// Applies `edits` random unit edits (substitute, insert or delete) to `s`.
fn mutate(rng: &mut Rng, s: &[u32], edits: usize, alpha: usize) -> Vec<u32> {
    let mut t = s.to_vec();
    for _ in 0..edits {
        let fresh = random_seq(rng, 1, alpha)[0];
        match rng.below(3) {
            0 if !t.is_empty() => {
                let i = rng.below(t.len());
                t[i] = fresh;
            }
            1 => {
                let i = rng.below(t.len() + 1);
                t.insert(i, fresh);
            }
            _ if !t.is_empty() => {
                let i = rng.below(t.len());
                t.remove(i);
            }
            _ => t.push(fresh),
        }
    }
    t
}

/// Limits probing the threshold around a known distance `d`, plus the extremes.
fn threshold_limits(d: usize, longest: usize) -> Vec<u32> {
    let d = u32::try_from(d).unwrap();
    let mut v = vec![0, 1, d.saturating_sub(1), d, d + 1, 2 * d + 1, d / 2];
    v.push(u32::try_from(longest + 5).unwrap());
    v.sort_unstable();
    v.dedup();
    v
}

#[test]
fn exhaustive_alphabet3_length6() {
    let seqs = all_sequences(3, 6);
    let limits: Vec<u32> = (0..=7).collect();
    // Unordered pairs (including equal ones). Symmetry is tested on the random cases.
    for (i, a) in seqs.iter().enumerate() {
        for b in &seqs[i..] {
            check_pair(a, b, &limits);
        }
    }
}

#[test]
fn exhaustive_alphabet4_length5() {
    let seqs = all_sequences(4, 5);
    let limits: Vec<u32> = (0..=6).collect();
    for (i, a) in seqs.iter().enumerate() {
        for b in &seqs[i..] {
            check_pair(a, b, &limits);
        }
    }
}

#[test]
fn empty_and_identical_inputs() {
    let empty: [u32; 0] = [];
    check_pair(&empty, &empty, &[0, 1]);
    check_pair(&empty, &[7, 7, 7], &[0, 2, 3, 4]);
    let s = [4u32, 1, 4, 1, 5];
    check_pair(&s, &s, &[0, 1, 5]);
    assert_eq!(levenshtein_within(&s, &s, 0), Some(0));
}

#[test]
fn substitution_costs_one_not_two() {
    // Regression: a token absent from the other side must be substituted for cost 1. One-sided
    // token elimination would price this as a deletion plus an insertion, i.e. 2.
    assert_eq!(levenshtein(&[1u32], &[2u32]), 1);
    assert_eq!(levenshtein_within(&[1u32], &[2u32], 0), None);
    assert_eq!(levenshtein_within(&[1u32], &[2u32], 1), Some(1));
    check_pair(&[1], &[2], &[0, 1, 2]);
    check_pair(&[1, 2, 3], &[1, 9, 3], &[0, 1, 2]);
}

#[test]
fn length_difference_rejection() {
    let a: Vec<u32> = (0..10).collect();
    let b: Vec<u32> = (0..20).collect();
    assert_eq!(levenshtein_within(&a, &b, 9), None);
    assert_eq!(levenshtein_within(&a, &b, 10), Some(10));
    check_pair(&a, &b, &[0, 9, 10, 11]);
}

#[test]
fn long_equal_prefix_and_suffix_hide_a_small_middle() {
    let mut rng = Rng(0x5EED_0001);
    let x = random_seq(&mut rng, 1000, 4);
    let y = random_seq(&mut rng, 1000, 4);
    let mut a = x.clone();
    a.extend([1, 2, 3]);
    a.extend(&y);
    let mut b = x;
    b.extend([1, 9, 3]);
    b.extend(&y);
    assert_eq!(levenshtein(&a, &b), 1);
    check_pair(&a, &b, &[0, 1, 2]);
}

#[test]
fn random_long_sequences_across_alphabets() {
    // Lengths up to 3000 over alphabets 2, 4, 256 and sparse `u32` ids. Each pair is a mutated copy
    // (small distance) or an independent sample (large distance), probed at every threshold.
    let mut rng = Rng(0xD1FF_F00D_1234_5678);
    for &alpha in &[2usize, 4, 256, 0] {
        for round in 0..6 {
            let len = 1 + rng.below(3000);
            let base = random_seq(&mut rng, len, alpha);
            let edits = 1 + rng.below(60);
            let other = if round % 2 == 0 {
                mutate(&mut rng, &base, edits, alpha)
            } else {
                let len_b = 1 + rng.below(3000);
                random_seq(&mut rng, len_b, alpha)
            };
            let d = levenshtein_full_dp(&base, &other);
            let longest = base.len().max(other.len());
            let limits = threshold_limits(d, longest);
            check_pair(&base, &other, &limits);
            check_pair(&other, &base, &limits);
        }
    }
}

#[test]
fn single_word_pattern_against_long_text() {
    // The single-word kernel serves a pattern of at most 64 tokens. Here the shorter side is that
    // pattern and the longer side is a text of up to 3000 tokens, which exercises the long scan.
    let mut rng = Rng(0x5146_1E0D_0064);
    for &alpha in &[2usize, 4, 256, 0] {
        for _ in 0..8 {
            let pat_len = 1 + rng.below(64);
            let pattern = random_seq(&mut rng, pat_len, alpha);
            let text_len = 1 + rng.below(3000);
            let text = if rng.below(2) == 0 {
                random_seq(&mut rng, text_len, alpha)
            } else {
                let edits = rng.below(40);
                mutate(&mut rng, &pattern, edits, alpha)
            };
            let d = levenshtein_full_dp(&pattern, &text);
            let limits = threshold_limits(d, pattern.len().max(text.len()));
            check_pair(&pattern, &text, &limits);
            check_pair(&text, &pattern, &limits);
        }
    }
}

#[test]
fn multiword_boundary_lengths() {
    // Word boundaries of a 64-bit bit-parallel block: pattern lengths straddling 64, 128 and 192.
    let mut rng = Rng(0xB0_0000_0001);
    for &len in &[63usize, 64, 65, 127, 128, 129, 191, 192, 193] {
        for &alpha in &[2usize, 4, 0] {
            let a = random_seq(&mut rng, len, alpha);
            let edits = 1 + rng.below(8);
            let b = mutate(&mut rng, &a, edits, alpha);
            let len_c = len + rng.below(5);
            let c = random_seq(&mut rng, len_c, alpha);
            let d_ab = levenshtein_full_dp(&a, &b);
            let limits = threshold_limits(d_ab, len.max(b.len()));
            check_pair(&a, &b, &limits);
            let longest = a.len().max(c.len());
            check_pair(
                &a,
                &c,
                &threshold_limits(levenshtein_full_dp(&a, &c), longest),
            );
        }
    }
}

#[test]
fn indel_distance_differs_from_levenshtein_on_a_relabel() {
    // The existing line engine measures indel (LCS) distance: deletions and insertions, each 1, and
    // no substitution. A relabel is therefore two edits there and one edit here.
    let old = [1u32, 2, 3];
    let new = [1u32, 9, 3];
    let indel = difffold::lines::diff_ids(&old, &new, 10).cost();
    assert_eq!(
        indel, 2,
        "indel distance prices a relabel as delete plus insert"
    );
    assert_eq!(
        levenshtein(&old, &new),
        1,
        "Levenshtein prices a relabel as one substitution"
    );

    let single = [1u32];
    let other = [2u32];
    assert_eq!(difffold::lines::diff_ids(&single, &other, 3).cost(), 2);
    assert_eq!(levenshtein(&single, &other), 1);
}

#[test]
fn generic_non_integer_tokens() {
    let a = ["alpha", "beta", "gamma", "delta"];
    let b = ["alpha", "BETA", "gamma"];
    assert_eq!(levenshtein(&a, &b), 2);
    assert_eq!(levenshtein_within(&a, &b, 1), None);
    assert_eq!(levenshtein_within(&a, &b, 2), Some(2));
    assert_eq!(levenshtein_within_band(&a, &b, 2), Some(2));
}

/// Checks one bounded kernel against the oracle at every limit in `limits`.
fn check_kernel(name: &str, f: Within, a: &[u32], b: &[u32], limits: &[u32]) {
    let d = levenshtein_full_dp(a, b);
    for &limit in limits {
        assert_eq!(
            f(a, b, limit),
            expected(d, limit),
            "{name}: a={a:?} b={b:?} limit={limit} oracle={d}"
        );
    }
}

#[test]
fn wavefront_exhaustive_alphabet3_length6() {
    let seqs = all_sequences(3, 6);
    let limits: Vec<u32> = (0..=7).collect();
    for (i, a) in seqs.iter().enumerate() {
        for b in &seqs[i..] {
            check_kernel(
                "wavefront",
                levenshtein_within_wavefront::<u32>,
                a,
                b,
                &limits,
            );
            check_kernel(
                "wavefront",
                levenshtein_within_wavefront::<u32>,
                b,
                a,
                &limits,
            );
        }
    }
}

#[test]
fn wavefront_exhaustive_alphabet4_length5() {
    let seqs = all_sequences(4, 5);
    let limits: Vec<u32> = (0..=6).collect();
    for (i, a) in seqs.iter().enumerate() {
        for b in &seqs[i..] {
            check_kernel(
                "wavefront",
                levenshtein_within_wavefront::<u32>,
                a,
                b,
                &limits,
            );
        }
    }
}

#[test]
fn banded_bit_parallel_exhaustive_small() {
    // A single block per pattern. The band still shifts across columns, so the window logic runs.
    let seqs = all_sequences(3, 6);
    let limits: Vec<u32> = (0..=7).collect();
    for (i, a) in seqs.iter().enumerate() {
        for b in &seqs[i..] {
            check_kernel(
                "myers_banded",
                levenshtein_within_myers_banded::<u32>,
                a,
                b,
                &limits,
            );
            check_kernel(
                "myers_banded",
                levenshtein_within_myers_banded::<u32>,
                b,
                a,
                &limits,
            );
        }
    }
}

#[test]
fn banded_bit_parallel_multiword_boundary_lengths() {
    // Pattern lengths on both sides of each 64-token block boundary, against mutated and independent
    // texts, probed at thresholds around the distance and at the fixed bounds 1, 8, 32 and 128.
    let mut rng = Rng(0xBA4D_0000_0064);
    for &len in &[63usize, 64, 65, 127, 128, 129, 191, 192, 193] {
        for &alpha in &[2usize, 4, 256, 0] {
            let a = random_seq(&mut rng, len, alpha);
            let edits = 1 + rng.below(12);
            let b = mutate(&mut rng, &a, edits, alpha);
            let c_len = len + rng.below(9);
            let c = random_seq(&mut rng, c_len, alpha);
            for other in [&b, &c] {
                let d = levenshtein_full_dp(&a, other);
                let mut limits = threshold_limits(d, a.len().max(other.len()));
                limits.extend([1, 8, 32, 128]);
                limits.sort_unstable();
                limits.dedup();
                check_kernel(
                    "myers_banded",
                    levenshtein_within_myers_banded::<u32>,
                    &a,
                    other,
                    &limits,
                );
                check_kernel(
                    "myers_banded",
                    levenshtein_within_myers_banded::<u32>,
                    other,
                    &a,
                    &limits,
                );
                check_pair(&a, other, &limits);
            }
        }
    }
}

#[test]
fn random_long_pairs_threshold_regimes() {
    // Distances below, equal to, one above, and far above the bound, across alphabets 2, 4, 256 and sparse.
    let mut rng = Rng(0x7E61_0E5A_0042);
    for &alpha in &[2usize, 4, 256, 0] {
        for round in 0..6 {
            let len = 200 + rng.below(1800);
            let base = random_seq(&mut rng, len, alpha);
            let other = if round % 3 == 2 {
                let other_len = 200 + rng.below(1800);
                random_seq(&mut rng, other_len, alpha)
            } else {
                let edits = 1 + rng.below(100);
                mutate(&mut rng, &base, edits, alpha)
            };
            let d = levenshtein_full_dp(&base, &other);
            let longest = base.len().max(other.len());
            let mut limits = Vec::new();
            if d >= 1 {
                limits.push(u32::try_from(d - 1).unwrap()); // d > k
            }
            limits.push(u32::try_from(d).unwrap()); // d == k
            limits.push(u32::try_from(d + 1).unwrap()); // d < k
            limits.push(u32::try_from(d.saturating_sub(10)).unwrap()); // d >> k when d is large
            limits.push(u32::try_from(d / 2 + 1).unwrap());
            limits.push(u32::try_from(longest + 1).unwrap());
            limits.sort_unstable();
            limits.dedup();
            check_pair(&base, &other, &limits);
            check_pair(&other, &base, &limits);
            for &k in &[1u32, 8, 32, 128] {
                check_kernel(
                    "wavefront",
                    levenshtein_within_wavefront::<u32>,
                    &base,
                    &other,
                    &[k],
                );
                check_kernel(
                    "myers_banded",
                    levenshtein_within_myers_banded::<u32>,
                    &base,
                    &other,
                    &[k],
                );
            }
        }
    }
}

#[test]
fn histogram_bound_never_exceeds_distance_exhaustive() {
    // Dense ids take the counting path. Sparse ids take the sorting path, selected by large ids.
    let sparse = |x: u32| x.wrapping_mul(1_000_003).wrapping_add(7_000_000);
    for (alpha, max_len) in [(3u32, 6usize), (4, 5)] {
        let seqs = all_sequences(alpha, max_len);
        for a in &seqs {
            for b in &seqs {
                let d = levenshtein_full_dp(a, b);
                assert!(
                    histogram_lower_bound_u32(a, b) <= d,
                    "dense a={a:?} b={b:?}"
                );
                let sa: Vec<u32> = a.iter().map(|&x| sparse(x)).collect();
                let sb: Vec<u32> = b.iter().map(|&x| sparse(x)).collect();
                assert_eq!(
                    histogram_lower_bound_u32(&sa, &sb),
                    histogram_lower_bound_u32(a, b)
                );
                assert!(
                    histogram_lower_bound_u32(&sa, &sb) <= d,
                    "sparse a={a:?} b={b:?}"
                );
            }
        }
    }
}

#[test]
fn histogram_bound_never_exceeds_distance_random() {
    let mut rng = Rng(0x4157_0004_0001);
    for &alpha in &[2usize, 4, 256, 0] {
        for _ in 0..60 {
            let a_len = rng.below(300);
            let a = random_seq(&mut rng, a_len, alpha);
            let b = if rng.below(2) == 0 {
                let edits = rng.below(30);
                mutate(&mut rng, &a, edits, alpha)
            } else {
                let b_len = rng.below(300);
                random_seq(&mut rng, b_len, alpha)
            };
            let d = levenshtein_full_dp(&a, &b);
            let lb = histogram_lower_bound_u32(&a, &b);
            assert!(lb <= d, "alpha={alpha} lb={lb} d={d} a={a:?} b={b:?}");
            assert!(histogram_lower_bound_u32(&b, &a) <= d);
        }
    }
    assert_eq!(histogram_lower_bound_u32(&[1, 2, 2], &[2, 1, 2]), 0);
    assert_eq!(histogram_lower_bound_u32(&[1, 2, 3], &[4, 5, 6]), 3);
}
