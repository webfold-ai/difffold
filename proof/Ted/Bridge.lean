import FromKids
import LabelLB
import Driver
import Oriented
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! From the output of `from_kids_spec` to the `Keys` facts the driver needs. -/

theorem keyroot_facts (C : Ctx) (a : ted.PostTree) (hA : WfL C.la) (n2 : a.lml.length = C.n)
    (la_eq : ∀ u, 1 ≤ u → u ≤ C.n → C.la u = (a.lml.val[u - 1]!).val)
    (hsort : a.keyroots.val.Pairwise (fun x y => x.val < y.val))
    (hkr : ∀ v, InKR a.keyroots.val v ↔ LastWithLml a.lml.val a.lml.length v) :
    (vals a.keyroots.val).Pairwise (· < ·) ∧
    (∀ x, 1 ≤ x → x ≤ C.n → krf C.la C.n x ∈ vals a.keyroots.val) ∧
    (∀ v ∈ vals a.keyroots.val, Ctx.IsKr C.la C.n v) := by
  have hmem : ∀ v, v ∈ vals a.keyroots.val ↔ InKR a.keyroots.val v := by
    intro v; simp [vals, InKR, List.mem_map]
  refine ⟨?_, ?_, ?_⟩
  · simpa [vals, List.pairwise_map] using hsort
  · intro x hx1 hxn
    have hk := Ctx.krf_isKr C.la C.n x hx1 hxn (hA.1 x hx1).2
    rw [hmem, hkr]
    obtain ⟨h1, h2, h3⟩ := hk
    refine ⟨h1, by rw [n2]; exact h2, fun j hj1 hj2 => ?_⟩
    rw [n2] at hj2
    have e1 := la_eq (j + 1) (by omega) (by omega)
    have e2 := la_eq (krf C.la C.n x) h1 h2
    have := h3 (j + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at e1
    intro heq
    exact this (by rw [e1, e2, heq])
  · intro v hv
    rw [hmem, hkr] at hv
    obtain ⟨h1, h2, h3⟩ := hv
    rw [n2] at h2 h3
    refine ⟨h1, h2, fun u hu hun => ?_⟩
    have e1 := la_eq u (by omega) hun
    have e2 := la_eq v h1 h2
    have := h3 (u - 1) (by omega) (by omega)
    rw [e1, e2]; exact this

end difffold_lines_extract
