import FillSpec
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

/-- **Optimality over the extracted code.** Under the model's admissibility of the heuristic
(`h <= B`, the remaining-cost bound), the Aeneas translation of `kernel::fill` returns a result exactly
when the grid's optimum `F*(n, m)` is at most `tau`, and the value it stores in the last row's last
cell is that optimum. When it returns `none`, the optimum exceeds `tau`.

What this does not cover: that `hK` of the extracted `suffix_sums` outputs satisfies the admissibility
hypothesis (the model proves it for `hLists` in `Link.lean`), that the oracle's `pair_cost` is the
recursive Selkow distance, and anything about `diff.rs` beyond the kernel call. -/
theorem fill_optimal (C : Ctx O inst) (o : O) (c : kernel.Counters)
    (hmsmall : C.g.m < 2 ^ 27) (hnsmall : C.g.n < 2 ^ 27) (hsum : sumU C.sb.val < 2 ^ 27)
    (htau0 : hK C.ra C.rb C.on 0 0 ≤ C.tau.val) (hInv : C.Inv o)
    (hadm : ∀ i j, i ≤ C.g.n → j ≤ C.g.m → C.h i j ≤ C.g.B i j) :
    kernel.fill inst o C.sa C.sb C.ra C.rb C.tau C.on c ⦃ r =>
      C.Inv r.2.1 ∧
      (∀ rows, r.1 = some rows →
        rowSem rows.val[C.g.n]! C.g.m = C.g.F C.g.n C.g.m ∧ C.g.F C.g.n C.g.m ≤ C.tau.val) ∧
      (r.1 = none → C.tau.val < C.g.F C.g.n C.g.m) ⦄ := by
  refine WP.spec_mono (fill_spec C o c hmsmall hnsmall hsum htau0 hInv) ?_
  intro r ⟨hI, hsome, hnone⟩
  refine ⟨hI, ?_, ?_⟩
  · intro rows hr
    obtain ⟨_, _, x, hx, hrs⟩ := hsome rows hr
    obtain ⟨h1, h2⟩ := Grid.result_is_min hadm hx
    exact ⟨by rw [hrs]; exact h1, by omega⟩
  · intro hr
    have hp := hnone hr
    have hdec := Grid.decision (g := C.g) (h := C.h) (tau := C.tau.val) hadm
    by_contra hle
    have : C.g.F C.g.n C.g.m ≤ C.tau.val := by omega
    have := hdec.2 this
    rw [hp] at this
    simp at this

end difffold_kernel_extract
