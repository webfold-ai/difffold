import RowCells
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

/-- `row_cells` builds row `i` of the model from the row above: the same conclusion as the loop, with the
loop's starting state (an empty row at the previous row's first column) discharged. -/
theorem row_cells_spec (C : Ctx O inst) (prev : kernel.Row) (o : O) (i : Std.Usize) (c : kernel.Counters)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ C.g.n) (hmlt : C.sb.val.length < Std.Usize.max)
    (hvpos : 0 < prev.v.length) (hspan : prev.lo.val + prev.v.length ≤ C.g.m + 1)
    (hprev : ∀ j' ≤ C.g.m, rowSem prev j' = enc (C.g.P C.h C.tau.val (i.val - 1) j'))
    (hInv : C.Inv o)
    (hnone : ∀ j' < prev.lo.val, C.g.P C.h C.tau.val i.val j' = none) :
    kernel.row_cells inst o prev i C.sa C.sb C.ra C.rb C.tau C.on c ⦃ r =>
      C.Inv r.2.1 ∧ 0 < r.1.length ∧ prev.lo.val + r.1.length ≤ C.g.m + 1 ∧
      (∀ t < r.1.length, r.1.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (prev.lo.val + t))) ∧
      (∀ j', prev.lo.val + r.1.length ≤ j' → j' ≤ C.g.m → C.g.P C.h C.tau.val i.val j' = none) ⦄ := by
  unfold kernel.row_cells
  have hmv : (Slice.len C.sb).val = C.g.m := by rw [C.hm]; simp [Slice.len]
  step as ⟨i2, hi2v⟩
  step as ⟨phi, hphiv⟩
  have hnew : (alloc.vec.Vec.new Std.U32).length = 0 := by simp [alloc.vec.Vec.new]
  have hlo : prev.lo.val ≤ C.g.m := by omega
  have hphi : phi.val + 1 = prev.lo.val + prev.v.length := by
    have : (alloc.vec.Vec.len prev.v).val = prev.v.length := by simp [alloc.vec.Vec.len]
    omega
  exact row_cells_loop_spec C prev.lo prev.v o i c (Slice.len C.sb) phi (alloc.vec.Vec.new Std.U32) prev.lo
    hi1 hi2 hmv (by rw [hmv, C.hm]; exact hmlt) hphi hvpos hspan hprev hInv (le_refl _) hlo (by rw [hnew]; omega)
    (by intro t ht; rw [hnew] at ht; omega) hnone
