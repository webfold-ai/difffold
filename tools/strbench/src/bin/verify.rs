//! Checks every tool against the full dynamic-programming oracle on many small random pairs.
//!
//! Usage: `verify [pairs] [seed]`. Exits non-zero on the first run with any disagreement.

use std::process::ExitCode;

use strbench::{
    alphabet, edlib, edlib_bytes, oracle_full, random_seq, rapidfuzz, wfa, wfa_bytes, Answer, Rng,
};

/// One adapter under test, called with an optional bound.
type Query<'a> = Box<dyn Fn(Option<usize>) -> Answer + 'a>;

fn expect_bounded(d: usize, k: usize) -> Answer {
    if d <= k {
        Answer::Dist(d)
    } else {
        Answer::Exceeds
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let pairs: usize = args.get(1).map_or(5000, |s| s.parse().expect("pairs"));
    let seed: u64 = args.get(2).map_or(1, |s| s.parse().expect("seed"));
    let mut rng = Rng::new(seed);
    let ks = [0usize, 1, 2, 4, 8, 32, 128];

    let mut checked = 0u64;
    let mut failures = 0u64;
    for p in 0..pairs {
        // Alphabets 2, 4 and 256 are dense. Every fourth pair uses sparse u32 ids, which only RapidFuzz accepts.
        let sigma = [2usize, 4, 256][p % 3];
        let sparse = p % 4 == 3;
        let symbols = if sparse {
            alphabet(&mut rng, 512, true)
        } else {
            alphabet(&mut rng, sigma, false)
        };
        let n = 1 + rng.below(40);
        let m = 1 + rng.below(40);
        let a = random_seq(&mut rng, n, &symbols);
        let b = random_seq(&mut rng, m, &symbols);
        let want = oracle_full(&a, &b);

        let rf = rapidfuzz(&a, &b, None);
        checked += 1;
        if rf != Answer::Dist(want) {
            failures += 1;
            eprintln!("rapidfuzz exact n={n} m={m} got={rf:?} want={want} a={a:?} b={b:?}");
        }
        for &k in &ks {
            let want_b = expect_bounded(want, k);
            let got = rapidfuzz(&a, &b, Some(k));
            checked += 1;
            if got != want_b {
                failures += 1;
                eprintln!("rapidfuzz k={k} n={n} m={m} got={got:?} want={want_b:?}");
            }
        }

        let (Some(a8), Some(b8)) = (edlib_bytes(&a), edlib_bytes(&b)) else {
            continue;
        };
        let mut checks: Vec<(&str, Query<'_>)> = vec![("edlib", Box::new(|k| edlib(&a8, &b8, k)))];
        if let (Some(wa), Some(wb)) = (wfa_bytes(&a), wfa_bytes(&b)) {
            checks.push(("wfa", Box::new(move |k| wfa(&wa, &wb, k))));
        }
        for (name, f) in &checks {
            let got = f(None);
            checked += 1;
            if got != Answer::Dist(want) {
                failures += 1;
                eprintln!("{name} exact n={n} m={m} got={got:?} want={want} a={a:?} b={b:?}");
            }
            for &k in &ks {
                let want_b = expect_bounded(want, k);
                let got = f(Some(k));
                checked += 1;
                if got != want_b {
                    failures += 1;
                    eprintln!(
                        "{name} k={k} n={n} m={m} got={got:?} want={want_b:?} a={a:?} b={b:?}"
                    );
                }
            }
        }
    }
    println!("pairs={pairs} checks={checked} failures={failures}");
    println!("note: empty-input pairs are excluded; the bench never uses them");
    if failures == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
