//! The Charon/Aeneas extraction rewrites two closures of `first_nl` and `last_nl` as `match` (Aeneas
//! rejects the mutually recursive closure impls). Everything else in the extracted line core is the real
//! `src/lines.rs`, included by `#[path]`. This test checks the rewritten copy against the real functions
//! on random inputs, including lengths beyond the 64-byte block so the halving recursion is exercised.
#[allow(dead_code, clippy::all)]
mod copy {
    include!("../proof/extract/lines_core.rs");
}
use difffold::lines::proof_api;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn first_and_last_newline_copies_agree_with_the_real_functions() {
    let mut r = Rng(0xA5A5_5A5A_1234_5678);
    for round in 0..60_000 {
        // Mix short and long inputs and sparse and dense newlines.
        let len = match r.next() % 4 {
            0 => (r.next() % 70) as usize,
            1 => (r.next() % 400) as usize,
            2 => (r.next() % 5000) as usize,
            _ => 0,
        };
        let density = 1 + r.next() % 40;
        let t: Vec<u8> = (0..len)
            .map(|_| {
                if r.next() % density == 0 {
                    b'\n'
                } else {
                    (r.next() % 255) as u8 | 1
                }
            })
            .collect();
        assert_eq!(
            copy::first_nl(&t),
            proof_api::first_nl(&t),
            "first_nl round {round} len {len}"
        );
        assert_eq!(
            copy::last_nl(&t),
            proof_api::last_nl(&t),
            "last_nl round {round} len {len}"
        );
    }
}
