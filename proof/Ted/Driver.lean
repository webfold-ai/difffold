import DifffoldTed
import Basic
import Cell
import Truth
import Window
import LabelLB
import Kr
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The driver of `within_td`: the nested loops over the keyroot pairs. -/

namespace Ctx

/-- The window of the keyroot pair `(i0, j0)`. -/
def win (C : Ctx) (i0 j0 : Nat) : Ctx :=
  { C with i0 := i0, j0 := j0, li := C.la i0, lj := C.lb j0 }

/-- Table entries only: never below the capped truth, never above `inf`, exact for `before` pairs that fit
the budget. -/
def GInv (C : Ctx) (td : List Std.U32) (before : Nat → Nat → Prop) : Prop :=
  ∀ x y, 1 ≤ x → x ≤ C.n → 1 ≤ y → y ≤ C.m →
    (min (TD C.la C.lb C.ren x y) C.inf ≤ rd td C.w C.t C.inf x y ∧ rd td C.w C.t C.inf x y ≤ C.inf) ∧
    (before x y → TD C.la C.lb C.ren x y + adf (C.la x) (C.lb y) ≤ C.t →
      rd td C.w C.t C.inf x y = TD C.la C.lb C.ren x y)

theorem TdInv_eq (C : Ctx) (td : List Std.U32) (p q : Nat) : C.TdInv td p q ↔ C.GInv td (C.Done p q) := Iff.rfl

/-- Pairs whose window `(kr x, kr y)` comes before the keyroot pair at positions `(ia, ib)`. -/
def WB (C : Ctx) (KA KB : List Nat) (ia ib : Nat) (x y : Nat) : Prop :=
  krf C.la C.n x ∈ KA.take ia ∨
    (KA[ia]? = some (krf C.la C.n x) ∧ krf C.lb C.m y ∈ KB.take ib)


theorem win_good (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) {i0 j0 : Nat} (h1 : 1 ≤ i0) (h2 : i0 ≤ C.n)
    (h3 : 1 ≤ j0) (h4 : j0 ≤ C.m) : (C.win i0 j0).Good :=
  ⟨hA, hB, h1, h2, h3, h4, rfl, rfl⟩

/-- A keyroot of the first tree: last node with its leftmost leaf. -/
def IsKr (la : Nat → Nat) (n v : Nat) : Prop := 1 ≤ v ∧ v ≤ n ∧ ∀ u, v < u → u ≤ n → la u ≠ la v

theorem krf_isKr (la : Nat → Nat) (n x : Nat) (hx1 : 1 ≤ x) (hx : x ≤ n) (hle : la x ≤ x) :
    IsKr la n (krf la n x) := by
  obtain ⟨a1, a2, a3, a4⟩ := krf_spec la n x hx
  refine ⟨by omega, a2, fun u hu hu2 => ?_⟩
  rw [a3]; exact a4 u hu hu2

theorem krf_of_isKr (la : Nat → Nat) (n x : Nat) (hx : x ≤ n) (hk : IsKr la n x) : krf la n x = x :=
  krf_self la n x hx hk.2.2

/-- The window of `(i0, j0)` only has to trust pairs whose own window comes earlier in the loop order. -/
theorem done_wb (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) {KA KB : List Nat} {ia ib i0 j0 : Nat}
    (hsA : KA.Pairwise (· < ·)) (hsB : KB.Pairwise (· < ·))
    (hmA : ∀ x, 1 ≤ x → x ≤ C.n → krf C.la C.n x ∈ KA) (hmB : ∀ y, 1 ≤ y → y ≤ C.m → krf C.lb C.m y ∈ KB)
    (hia : ia < KA.length) (hib : ib < KB.length) (hi0 : KA[ia] = i0) (hj0 : KB[ib] = j0)
    (hk0 : IsKr C.la C.n i0) (hl0 : IsKr C.lb C.m j0) (hn0 : j0 ≤ C.m)
    {x y : Nat} (hx1 : 1 ≤ x) (hxn : x ≤ C.n) (hy1 : 1 ≤ y) (hym : y ≤ C.m)
    (hd : (C.win i0 j0).Done 1 1 x y) : C.WB KA KB ia ib x y := by
  obtain ⟨hda, hdb, hdx, hdy, hd3⟩ := hd
  simp only [Ctx.win] at hda hdb hdx hdy hd3
  have hnl : ¬ (C.la x = C.la i0 ∧ C.lb y = C.lb j0) := by
    rcases hd3 with h | ⟨h, h2 | ⟨h2, h3⟩⟩
    · exact h
    · exfalso; omega
    · exfalso; omega
  unfold Ctx.WB
  by_cases hxe : C.la x = C.la i0
  · -- the node lies on the left path of `i0`, so the keyroots agree
    have hyne : C.lb y ≠ C.lb j0 := fun h => hnl ⟨hxe, h⟩
    have hkx : krf C.la C.n x = i0 := by
      rw [krf_congr C.la C.n x i0 hxn hk0.2.1 hxe]; exact krf_of_isKr C.la C.n i0 hk0.2.1 hk0
    refine Or.inr ⟨by rw [hkx, ← hi0]; simp [List.getElem?_eq_getElem hia], ?_⟩
    apply mem_take_of_lt hsB hib (hmB y hy1 hym)
    have hlt := kr_lt C.lb C.m (fun u hu => (hB.1 u hu).2) hB.2 (x := y) (u := j0) hy1 hn0 hdy hdb hyne
    rw [← hj0] at hlt; exact hlt
  · have hlt := kr_lt C.la C.n (fun u hu => (hA.1 u hu).2) hA.2 (x := x) (u := i0) hx1 hk0.2.1 hdx hda hxe
    left
    apply mem_take_of_lt hsA hia (hmA x hx1 hxn)
    rw [hi0]; exact hlt


/-- A pair that newly counts as before after the window `(ia, ib)` has been processed is a leaf pair of that
window. -/
theorem wb_new (C : Ctx) {KA KB : List Nat} {ia ib i0 j0 : Nat} (hsB : KB.Pairwise (· < ·))
    (hia : ia < KA.length) (hib : ib < KB.length) (hi0 : KA[ia] = i0) (hj0 : KB[ib] = j0)
    {x y : Nat} (h1 : C.WB KA KB ia (ib + 1) x y) (h2 : ¬ C.WB KA KB ia ib x y) :
    krf C.la C.n x = i0 ∧ krf C.lb C.m y = j0 := by
  unfold Ctx.WB at h1 h2
  rcases h1 with h | ⟨hk, hy⟩
  · exact absurd (Or.inl h) h2
  · rw [take_succ_mem hib] at hy
    rcases hy with hy | hy
    · exact absurd (Or.inr ⟨hk, hy⟩) h2
    · rw [List.getElem?_eq_getElem hia] at hk
      have := Option.some.inj hk
      exact ⟨by omega, by omega⟩

theorem leaf_not_wb (C : Ctx) {KA KB : List Nat} {ia ib i0 j0 : Nat} (hsA : KA.Pairwise (· < ·))
    (hsB : KB.Pairwise (· < ·)) (hia : ia < KA.length) (hib : ib < KB.length) (hi0 : KA[ia] = i0)
    (hj0 : KB[ib] = j0) (hn : i0 ≤ C.n) (hm : j0 ≤ C.m) (hk0 : IsKr C.la C.n i0) (hl0 : IsKr C.lb C.m j0)
    {x y : Nat} (hx : x ≤ C.n) (hy : y ≤ C.m) (hlx : C.la x = C.la i0) (hly : C.lb y = C.lb j0) :
    ¬ C.WB KA KB ia ib x y := by
  have hkx : krf C.la C.n x = i0 := by
    rw [krf_congr C.la C.n x i0 hx hn hlx]; exact krf_of_isKr C.la C.n i0 hn hk0
  have hky : krf C.lb C.m y = j0 := by
    rw [krf_congr C.lb C.m y j0 hy hm hly]; exact krf_of_isKr C.lb C.m j0 hm hl0
  unfold Ctx.WB
  rintro (h | ⟨_, h⟩)
  · rw [hkx] at h
    have := lt_of_mem_take hsA hia h
    omega
  · rw [hky] at h
    have := lt_of_mem_take hsB hib h
    omega


theorem inv_step (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) {KA KB : List Nat} {ia ib i0 j0 : Nat}
    (hsA : KA.Pairwise (· < ·)) (hsB : KB.Pairwise (· < ·)) (hia : ia < KA.length) (hib : ib < KB.length)
    (hi0 : KA[ia] = i0) (hj0 : KB[ib] = j0) (hk0 : IsKr C.la C.n i0) (hl0 : IsKr C.lb C.m j0)
    {td td' : List Std.U32} (hF : (C.win i0 j0).Frame td td')
    (hT' : (C.win i0 j0).TdInv td' ((C.win i0 j0).si + 1) 1) (hG : C.GInv td (C.WB KA KB ia ib)) :
    C.GInv td' (C.WB KA KB ia (ib + 1)) := by
  intro x y hx1 hxn hy1 hym
  have hT := hT' x y hx1 hxn hy1 hym
  refine ⟨hT.1, fun hw hb => ?_⟩
  by_cases hold : C.WB KA KB ia ib x y
  · have hnl : ¬ ((C.win i0 j0).LeafPair x y ∧ x ≤ (C.win i0 j0).i0 ∧ y ≤ (C.win i0 j0).j0) := by
      rintro ⟨⟨h1, h2⟩, _⟩
      exact leaf_not_wb C hsA hsB hia hib hi0 hj0 hk0.2.1 hl0.2.1 hk0 hl0 hxn hym h1 h2 hold
    have := hF x y hnl
    exact this.trans ((hG x y hx1 hxn hy1 hym).2 hold hb)
  · obtain ⟨hkx, hky⟩ := wb_new C hsB hia hib hi0 hj0 hw hold
    have hkx' := krf_spec C.la C.n x hxn
    have hky' := krf_spec C.lb C.m y hym
    have hlx : C.la x = C.la i0 := by rw [← hkx, hkx'.2.2.1]
    have hly : C.lb y = C.lb j0 := by rw [← hky, hky'.2.2.1]
    have hxi : x ≤ i0 := by omega
    have hyj : y ≤ j0 := by omega
    have hle := (hA.1 i0 hk0.1).2
    have hlex := (hA.1 x hx1).2
    have hley := (hB.1 y hy1).2
    refine hT.2 ?_ hb
    refine ⟨by simp only [Ctx.win]; omega, by simp only [Ctx.win]; omega, hxi, hyj, Or.inr ⟨⟨hlx, hly⟩, Or.inl ?_⟩⟩
    simp only [Ctx.win, Ctx.si]
    omega

theorem skip_step (C : Ctx) {KA KB : List Nat} {ia ib i0 j0 : Nat} (hsB : KB.Pairwise (· < ·))
    (hia : ia < KA.length) (hib : ib < KB.length) (hi0 : KA[ia] = i0) (hj0 : KB[ib] = j0)
    {td : List Std.U32} (hskip : 2 * C.t < adf (C.la i0) (C.lb j0)) (hG : C.GInv td (C.WB KA KB ia ib)) :
    C.GInv td (C.WB KA KB ia (ib + 1)) := by
  intro x y hx1 hxn hy1 hym
  refine ⟨(hG x y hx1 hxn hy1 hym).1, fun hw hb => ?_⟩
  by_cases hold : C.WB KA KB ia ib x y
  · exact (hG x y hx1 hxn hy1 hym).2 hold hb
  · obtain ⟨hkx, hky⟩ := wb_new C hsB hia hib hi0 hj0 hw hold
    have hkx' := krf_spec C.la C.n x hxn
    have hky' := krf_spec C.lb C.m y hym
    have hlx : C.la x = C.la i0 := by rw [← hkx, hkx'.2.2.1]
    have hly : C.lb y = C.lb j0 := by rw [← hky, hky'.2.2.1]
    rw [hlx, hly] at hb
    omega

end Ctx

end difffold_lines_extract
