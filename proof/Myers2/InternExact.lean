import Aeneas
open Aeneas Aeneas.Std
namespace difffold_myers_extract

/-- The contract of the line interner (`intern` in `src/lines.rs`). `la`, `lb` are the byte contents of the
lines of the two sides, `ia`, `ib` the ids assigned to them and `n` the number of distinct ids. It says:
one id per line; every id is below `n`; two lines (on either side) have equal ids exactly when their bytes
are equal; and every id below `n` is used by some line (the ids are dense in `0..n`). -/
def InternExact (la lb : List (List U8)) (ia ib : List U32) (n : Nat) : Prop :=
  ia.length = la.length ∧ ib.length = lb.length ∧
  (∀ x ∈ ia, x.val < n) ∧ (∀ x ∈ ib, x.val < n) ∧
  (∀ i j : Nat, ia[i]? = ia[j]? ↔ la[i]? = la[j]?) ∧
  (∀ i j : Nat, ia[i]? = ib[j]? ↔ la[i]? = lb[j]?) ∧
  (∀ i j : Nat, ib[i]? = ib[j]? ↔ lb[i]? = lb[j]?) ∧
  (∀ k, k < n → ∃ x ∈ ia ++ ib, x.val = k)

end difffold_myers_extract
