import DifffoldKernel
import Spec
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract

/-- `kernel::INF` as a natural number. -/
def INFn : Nat := 1073741823

@[simp] theorem kernel_INF_val : kernel.INF.val = INFn := by
  unfold kernel.INF INFn; rfl

theorem getElem_bang_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i]'h := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- What a `Row` says about column `j`: the held value, or `INF` outside its span. -/
def rowSem (r : kernel.Row) (j : Nat) : Nat :=
  if j < r.lo.val then INFn
  else if j - r.lo.val < r.v.length then r.v.val[j - r.lo.val]!.val else INFn

/-- What a raw (untrimmed) row starting at column `plo` says about column `j`. -/
def rawSem (v : alloc.vec.Vec Std.U32) (plo : Nat) (j : Nat) : Nat :=
  if j < plo then INFn
  else if j - plo < v.length then v.val[j - plo]!.val else INFn

/-- `Row::at` computes `rowSem`. -/
@[step] theorem row_at_val (r : kernel.Row) (j : Std.Usize) :
    kernel.Row.at r j ⦃ x => x.val = rowSem r j.val ⦄ := by
  unfold kernel.Row.at rowSem
  split
  · step*
    simp_all
  · step*
    · rename_i h1 h2 h3
      have hb : j.val - r.lo.val < r.v.length := by scalar_tac
      have hlt : ¬ (j.val < r.lo.val) := by scalar_tac
      simp only [hlt, if_false, hb, if_true]
      simp [x_post, k_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb]
    · rename_i h1 h2
      have hlt : ¬ (j.val < r.lo.val) := by scalar_tac
      have hb : ¬ (j.val - r.lo.val < r.v.length) := by scalar_tac
      simp [hlt, hb]

end difffold_kernel_extract
