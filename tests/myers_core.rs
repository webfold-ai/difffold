//! The Charon/Aeneas extraction of the line search uses the closure-free copies in
//! `proof/extract/myers_core.rs`. This test checks every function there against the real `src/lines.rs`
//! (through `proof_api`) on random input. It is the only link between the copy and the source:
//! there is no proof of equality.
#[allow(dead_code, clippy::all)]
mod copy {
    include!("../proof/extract/lines_core.rs");
    include!("../proof/extract/myers_core.rs");
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

fn ids(r: &mut Rng, len: usize, alpha: u64) -> Vec<u32> {
    (0..len).map(|_| (r.next() % alpha) as u32).collect()
}

#[test]
fn snake_copies_agree_with_the_real_functions() {
    let mut r = Rng(0x1357_9BDF_2468_ACE1);
    for round in 0..40_000 {
        let alpha = 1 + r.next() % 4;
        let (n, m) = ((r.next() % 40) as usize, (r.next() % 40) as usize);
        // Sometimes make the lists share a long stretch so the runs are long.
        let mut a = ids(&mut r, n, alpha);
        let mut b = ids(&mut r, m, alpha);
        if r.next() % 3 == 0 && n > 0 && m > 0 {
            let k = (r.next() % (n.min(m) as u64 + 1)) as usize;
            let (ao, bo) = ((r.next() % (n - k + 1) as u64) as usize, (r.next() % (m - k + 1) as u64) as usize);
            let common: Vec<u32> = ids(&mut r, k, 50);
            a[ao..ao + k].copy_from_slice(&common);
            b[bo..bo + k].copy_from_slice(&common);
        }
        for _ in 0..6 {
            let x = (r.next() % (n as u64 + 3)) as i32;
            let y = (r.next() % (m as u64 + 3)) as i32;
            assert_eq!(copy::snake(&a, &b, x, y), proof_api::snake(&a, &b, x, y), "snake round {round}");
            assert_eq!(copy::snake_back(&a, &b, x, y), proof_api::snake_back(&a, &b, x, y), "snake_back round {round}");
        }
    }
}

#[test]
fn line_helpers_copies_agree_with_the_real_functions() {
    let mut r = Rng(0xC0FF_EE00_DEAD_BEEF);
    for round in 0..40_000 {
        let len = match r.next() % 4 {
            0 => (r.next() % 30) as usize,
            1 => (r.next() % 200) as usize,
            2 => (r.next() % 3000) as usize,
            _ => 0,
        };
        let density = 1 + r.next() % 12;
        let t: Vec<u8> = (0..len).map(|_| if r.next() % density == 0 { b'\n' } else { (r.next() % 3) as u8 + b'a' }).collect();
        assert_eq!(copy::count_lines(&t), proof_api::count_lines(&t), "count_lines round {round} len {len}");
        let p = if len == 0 { 0 } else { (r.next() % (len as u64 + 1)) as usize };
        assert_eq!(copy::line_start(&t, p), proof_api::line_start(&t, p), "line_start round {round}");
        // Two texts that share a suffix of length q, as `diff_text_with` calls it.
        let k = (r.next() % (len as u64 + 1)) as usize;
        let mut other: Vec<u8> = (0..(r.next() % 40) as usize).map(|_| if r.next() % density == 0 { b'\n' } else { (r.next() % 3) as u8 + b'a' }).collect();
        other.extend_from_slice(&t[len - k..]);
        let q = copy::common_suffix(&t, &other);
        assert_eq!(
            copy::suffix_on_line_start(&t, &other, q),
            proof_api::suffix_on_line_start(&t, &other, q),
            "suffix_on_line_start round {round}"
        );
    }
}
