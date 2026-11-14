//! The `imara-diff` baseline, over both of its APIs.
//!
//! 0.2 computes a `Diff` from interned input and prints it through a `UnifiedDiffPrinter`; 0.1
//! drives a sink (`Counter`, `UnifiedDiffBuilder`) from `diff`. `imara-02` (default) selects the
//! first and `imara-01` the second; with neither, every function answers `None` and the rows are
//! left out. Costs are insertions plus removals, as for the other baselines.

#[derive(Clone, Copy)]
pub enum Algo {
    Myers,
    MyersMinimal,
    Histogram,
}

#[cfg(feature = "imara-02")]
mod api {
    use super::Algo;
    use imara_diff::{Algorithm, BasicLineDiffPrinter, Diff, InternedInput, UnifiedDiffConfig};

    fn algorithm(a: Algo) -> Algorithm {
        match a {
            Algo::Myers => Algorithm::Myers,
            Algo::MyersMinimal => Algorithm::MyersMinimal,
            Algo::Histogram => Algorithm::Histogram,
        }
    }

    pub fn cost(a: Algo, before: &str, after: &str) -> Option<usize> {
        let input = InternedInput::new(before, after);
        let diff = Diff::compute(algorithm(a), &input);
        Some((diff.count_additions() + diff.count_removals()) as usize)
    }

    pub fn patch_len(a: Algo, before: &str, after: &str) -> Option<usize> {
        let input = InternedInput::new(before, after);
        let diff = Diff::compute(algorithm(a), &input);
        let printer = BasicLineDiffPrinter(&input.interner);
        let patch = diff
            .unified_diff(&printer, UnifiedDiffConfig::default(), &input)
            .to_string();
        Some(patch.len())
    }
}

#[cfg(all(feature = "imara-01", not(feature = "imara-02")))]
mod api {
    use super::Algo;
    use imara_diff_01::intern::InternedInput;
    use imara_diff_01::sink::Counter;
    use imara_diff_01::{diff, Algorithm, UnifiedDiffBuilder};

    fn algorithm(a: Algo) -> Algorithm {
        match a {
            Algo::Myers => Algorithm::Myers,
            Algo::MyersMinimal => Algorithm::MyersMinimal,
            Algo::Histogram => Algorithm::Histogram,
        }
    }

    pub fn cost(a: Algo, before: &str, after: &str) -> Option<usize> {
        let input = InternedInput::new(before, after);
        let c = diff(algorithm(a), &input, Counter::default());
        Some((c.insertions + c.removals) as usize)
    }

    pub fn patch_len(a: Algo, before: &str, after: &str) -> Option<usize> {
        let input = InternedInput::new(before, after);
        Some(diff(algorithm(a), &input, UnifiedDiffBuilder::new(&input)).len())
    }
}

#[cfg(not(any(feature = "imara-01", feature = "imara-02")))]
mod api {
    use super::Algo;

    pub fn cost(_: Algo, _: &str, _: &str) -> Option<usize> {
        None
    }

    pub fn patch_len(_: Algo, _: &str, _: &str) -> Option<usize> {
        None
    }
}

pub use api::{cost, patch_len};
