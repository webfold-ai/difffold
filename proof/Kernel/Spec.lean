import DifffoldKernel
open Aeneas Aeneas.Std Result
namespace difffold_kernel_extract

/-- `adiff` returns the absolute difference. Stated over the Aeneas-extracted `kernel::adiff`. -/
@[step] theorem adiff_spec (x y : Std.U32) :
    kernel.adiff x y ⦃ r => r.val = (if x.val ≥ y.val then x.val - y.val else y.val - x.val) ⦄ := by
  unfold kernel.adiff
  split
  · step*
  · step*

/-- `umin` returns the smaller value. -/
@[step] theorem umin_spec (x y : Std.U32) :
    kernel.umin x y ⦃ r => r.val = Nat.min x.val y.val ∧ r.val ≤ x.val ∧ r.val ≤ y.val ⦄ := by
  unfold kernel.umin
  split
  · simp_all
  · simp_all
    omega

/-- `Row.at` reads a held column and returns `INF` for any column outside the span. -/
theorem row_at_spec (r : kernel.Row) (j : Std.Usize) :
    kernel.Row.at r j ⦃ x =>
      (j.val < r.lo.val ∨ r.lo.val + r.v.length ≤ j.val → x = kernel.INF) ∧
      (r.lo.val ≤ j.val → j.val < r.lo.val + r.v.length → x = r.v[j.val - r.lo.val]!) ⦄ := by
  unfold kernel.Row.at
  split
  · step*
  · step*
    have hb : j.val - r.lo.val < r.v.length := by scalar_tac
    refine ⟨fun h => ?_, fun _ _ => ?_⟩
    · rcases h with h | h <;> scalar_tac
    · simp [x_post, k_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb]

end difffold_kernel_extract
