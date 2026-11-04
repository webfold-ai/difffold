//! Checks shared by the libFuzzer targets and by `cargo test -p difffold-fuzz`.
//!
//! Each check panics when a contract in `SPEC.md` is violated. Random inputs therefore either pass
//! silently or abort, and the same code runs both under cargo-fuzz and in the ordinary test suite.

use difffold::diff::{diff, diff_checked};
use difffold::intern::{Arena, Id};
use difffold::lines::{diff_text_with, replay_ok, Algo};

/// Maximum nesting depth decoded from the input. Keeps trees small enough to fuzz quickly.
const MAX_DEPTH: u32 = 4;
/// Maximum number of nodes decoded per tree.
const MAX_NODES: u32 = 96;

/// Decodes one ordered tree from `bytes`, one byte per node. Low 3 bits: label. Bits 3-4: child
/// count (capped at 3, and 0 at `MAX_DEPTH` or when the node budget is spent). Missing bytes read as
/// zero, so every input decodes to some tree.
fn decode(arena: &mut Arena, bytes: &[u8], pos: &mut usize, depth: u32, budget: &mut u32) -> Id {
    let b = bytes.get(*pos).copied().unwrap_or(0);
    *pos += 1;
    *budget = budget.saturating_sub(1);
    let label = u32::from(b & 0x07);
    let nkids = if depth >= MAX_DEPTH || *budget == 0 { 0 } else { usize::from((b >> 3) & 0x03) };
    let kids: Vec<Id> = (0..nkids).map(|_| decode(arena, bytes, pos, depth + 1, budget)).collect();
    arena.mk(label, &kids)
}

/// Splits `data` into a before-tree and an after-tree. The first byte chooses the cut point.
fn trees(arena: &mut Arena, data: &[u8]) -> (Id, Id) {
    let (head, rest) = data.split_first().map_or((0u8, &[][..]), |(h, r)| (*h, r));
    let cut = usize::from(head) % (rest.len() + 1);
    let (a, b) = rest.split_at(cut);
    let (mut pa, mut pb) = (0usize, 0usize);
    let (mut ba, mut bb) = (MAX_NODES, MAX_NODES);
    let ta = decode(arena, a, &mut pa, 0, &mut ba);
    let tb = decode(arena, b, &mut pb, 0, &mut bb);
    (ta, tb)
}

/// Tree contracts on two decoded trees:
/// * C3: `diff_checked` asserts that the script's cost equals the distance and that replaying it on
///   the before-tree rebuilds the after-tree id for id.
/// * C5: the distance is symmetric.
/// * C6: the distance is zero exactly when the two trees are equal.
pub fn check_tree(data: &[u8]) {
    let mut arena = Arena::new();
    let (a, b) = trees(&mut arena, data);
    let forward = diff_checked(&mut arena, a, b);
    let backward = diff_checked(&mut arena, b, a);
    assert_eq!(forward.cost, backward.cost, "C5: dist(x, y) != dist(y, x)");
    assert_eq!(forward.cost == 0, a == b, "C6: dist = 0 iff the trees are equal");
    // The unchecked entry point must agree with the checked one.
    assert_eq!(diff(&arena, a, b).cost, forward.cost, "checked and unchecked distances differ");
}

/// Line-diff contract: for both algorithms, the reported deletions and insertions must rebuild the
/// new text from the old one (`replay_ok`). The first byte chooses where the two texts split.
pub fn check_lines(data: &[u8]) {
    let Some((head, rest)) = data.split_first() else {
        return;
    };
    let cut = usize::from(*head) % (rest.len() + 1);
    let (old, new) = rest.split_at(cut);
    for algo in [Algo::Minimal, Algo::Histogram] {
        let d = diff_text_with(old, new, algo);
        assert!(replay_ok(old, new, &d), "replay failed for {algo:?}");
    }
}

#[cfg(test)]
mod tests {
    use super::{check_lines, check_tree};

    /// Deterministic xorshift, so the test is reproducible without a random-number dependency.
    fn bytes(seed: &mut u64, len: usize) -> Vec<u8> {
        (0..len)
            .map(|_| {
                *seed ^= *seed << 13;
                *seed ^= *seed >> 7;
                *seed ^= *seed << 17;
                (*seed >> 24) as u8
            })
            .collect()
    }

    #[test]
    fn random_trees_satisfy_the_contracts() {
        let mut seed = 0x5EED_1234_ABCD_0001u64;
        for n in 0..4000usize {
            let len = n % 97;
            check_tree(&bytes(&mut seed, len));
        }
    }

    #[test]
    fn random_texts_replay() {
        let mut seed = 0x5EED_9876_FEED_0002u64;
        for n in 0..4000usize {
            let len = n % 200;
            check_lines(&bytes(&mut seed, len));
        }
    }

    #[test]
    fn empty_and_single_byte_inputs_are_accepted() {
        check_tree(&[]);
        check_tree(&[0]);
        check_lines(&[]);
        check_lines(&[0]);
    }
}
