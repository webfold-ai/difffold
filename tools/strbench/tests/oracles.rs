//! Checks the three library adapters and the bounded oracle against the full dynamic program.

use strbench::{
    alphabet, difffold, edlib, edlib_bytes, oracle_bounded, oracle_full, random_seq, rapidfuzz,
    wfa, wfa_bytes, Answer, Rng,
};

fn expected(d: usize, k: usize) -> Answer {
    if d <= k {
        Answer::Dist(d)
    } else {
        Answer::Exceeds
    }
}

#[test]
fn bounded_oracle_matches_full_dp() {
    let mut rng = Rng::new(7);
    let sym = alphabet(&mut rng, 3, false);
    for _ in 0..2000 {
        let n = rng.below(20);
        let m = rng.below(20);
        let a = random_seq(&mut rng, n, &sym);
        let b = random_seq(&mut rng, m, &sym);
        let d = oracle_full(&a, &b);
        for k in [0usize, 1, 2, 3, 5, 8, 32, 128] {
            assert_eq!(
                oracle_bounded(&a, &b, k),
                expected(d, k),
                "k={k} n={n} m={m}"
            );
        }
    }
}

#[test]
fn adapters_match_full_dp_on_dense_and_sparse_symbols() {
    let mut rng = Rng::new(21);
    for i in 0..1500 {
        let sigma = [2usize, 4, 256][i % 3];
        let sparse = i % 5 == 4;
        let symbols = alphabet(&mut rng, if sparse { 512 } else { sigma }, sparse);
        let n = 1 + rng.below(40);
        let m = 1 + rng.below(40);
        let a = random_seq(&mut rng, n, &symbols);
        let b = random_seq(&mut rng, m, &symbols);
        let d = oracle_full(&a, &b);
        assert_eq!(rapidfuzz(&a, &b, None), Answer::Dist(d));
        if let (Some(e8a), Some(e8b)) = (edlib_bytes(&a), edlib_bytes(&b)) {
            assert_eq!(edlib(&e8a, &e8b, None), Answer::Dist(d));
            for k in [0usize, 1, 4, 32] {
                assert_eq!(edlib(&e8a, &e8b, Some(k)), expected(d, k), "edlib k={k}");
            }
        }
        if let (Some(wa), Some(wb)) = (wfa_bytes(&a), wfa_bytes(&b)) {
            assert_eq!(wfa(&wa, &wb, None), Answer::Dist(d));
            for k in [0usize, 1, 4, 32] {
                assert_eq!(wfa(&wa, &wb, Some(k)), expected(d, k), "wfa k={k}");
            }
        }
        for k in [0usize, 1, 4, 32] {
            assert_eq!(
                rapidfuzz(&a, &b, Some(k)),
                expected(d, k),
                "rapidfuzz k={k}"
            );
        }
        assert_eq!(difffold(&a, &b, None), Answer::Dist(d));
        for k in [0usize, 1, 4, 32] {
            assert_eq!(difffold(&a, &b, Some(k)), expected(d, k), "difffold k={k}");
        }
    }
}
