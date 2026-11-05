import RealText
import RealIntern
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- The line identification of `diff_text_with`: the real `intern_seeded` with a given hash seed. The
production `intern` is `intern_seeded` with `random_seed()`, whose source (`RandomState`) Aeneas cannot
model, so the seed is a parameter here; `histogram` is irrelevant to `Algo::Minimal` and is arbitrary. -/
def seededIds (seed : U64) (hist : Slice U32 → Slice U32 → Usize → Result lines.LineDiff) :
    lines.LineIds Unit :=
  { intern := fun a b => lines.intern_seeded a b seed, histogram := hist }

/-- The real interner meets the contract `diff_text_minimal` needs, for every seed. -/
theorem seeded_exact (seed : U64) (hist : Slice U32 → Slice U32 → Usize → Result lines.LineDiff) :
    LineIdsExact (seededIds seed hist) := by
  intro a b hN
  exact intern_seeded_spec a b seed hN

/-- End to end: `diff_text` (the `Algo::Minimal` path of `diff_text_with`) returns flags of a minimal line
edit script that turns `old` into `new`. -/
theorem diff_text_minimal_seeded (seed : U64)
    (hist : Slice U32 → Slice U32 → Usize → Result lines.LineDiff)
    (old new : Slice U8) (B : Nat) (hB : B + 8 ≤ Usize.max) (ho : old.val.length ≤ B) (hn : new.val.length ≤ B)
    (hlines : (Myers.lines (bytes old.val)).length + (Myers.lines (bytes new.val)).length ≤ 2 ^ 28) :
    lines.diff_text_core (seededIds seed hist) old new lines.Algo.Minimal ⦃ r => ∃ da di,
      r.deleted.val = da ∧ r.inserted.val = di ∧
      Myers.MinL (Myers.lines (bytes old.val)) (Myers.lines (bytes new.val)) da di ∧
      (Myers.applyS (Myers.lines (bytes old.val)) (Myers.lines (bytes new.val)) da di).flatten =
        bytes new.val ⦄ :=
  diff_text_minimal (seededIds seed hist) (seeded_exact seed hist) old new B hB ho hn hlines

end difffold_myers_extract
