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


theorem Ctx.Link.win {C : Ctx} {a b : ted.PostTree} (hK : C.Link a b) (i0 j0 : Nat) : (C.win i0 j0).Link a b :=
  ⟨hK.n1, hK.n2, hK.n3, hK.m1, hK.m2, hK.m3, hK.la_eq, hK.lb_eq, hK.ren_eq, hK.nbig, hK.mbig, hK.wbig, hK.tbig⟩

/-- The facts the driver needs about the two trees and their keyroot lists. -/
structure Ctx.Keys (C : Ctx) (a b : ted.PostTree) : Prop where
  hA : WfL C.la
  hB : WfL C.lb
  sA : (vals a.keyroots.val).Pairwise (· < ·)
  sB : (vals b.keyroots.val).Pairwise (· < ·)
  mA : ∀ x, 1 ≤ x → x ≤ C.n → krf C.la C.n x ∈ vals a.keyroots.val
  mB : ∀ y, 1 ≤ y → y ≤ C.m → krf C.lb C.m y ∈ vals b.keyroots.val
  kA : ∀ v ∈ vals a.keyroots.val, Ctx.IsKr C.la C.n v
  kB : ∀ v ∈ vals b.keyroots.val, Ctx.IsKr C.lb C.m v

/-- The loop over the keyroots of the second tree for a fixed keyroot `i0` of the first. -/
theorem within_inner_spec (C : Ctx) (a b : ted.PostTree) (hK : C.Link a b) (hKe : C.Keys a b)
    (hw : C.w = 2 * C.t + 1) (tau : Std.U32) (t : Std.Usize) (ia : Nat)
    (hia : ia < (vals a.keyroots.val).length) (i0 li : Std.Usize) (st : ted.Stats)
    (td fd : alloc.vec.Vec Std.U32) (ib : Std.Usize)
    (htau : tau.val = C.t) (ht : t.val = C.t) (hi0 : (vals a.keyroots.val)[ia] = i0.val)
    (hli : li.val = C.la i0.val) (hib : ib.val ≤ (vals b.keyroots.val).length)
    (htdlen : (C.n + 1) * C.w ≤ td.val.length) (hfdlen : (C.n + 1) * C.w ≤ fd.val.length)
    (hTB : Ctx.FdB td.val C.inf) (hFB : Ctx.FdB fd.val C.inf)
    (hG : C.GInv td.val (C.WB (vals a.keyroots.val) (vals b.keyroots.val) ia ib.val)) :
    ted.within_td_loop0_loop0 a.label a.lml a.keyroots a.kids a.kind b tau st t td fd i0 li ib ⦃ r =>
      r.2.2.2.2.2.2.1.val.length = td.val.length ∧ r.2.2.2.2.2.2.2.val.length = fd.val.length ∧
      Ctx.FdB r.2.2.2.2.2.2.1.val C.inf ∧ Ctx.FdB r.2.2.2.2.2.2.2.val C.inf ∧
      C.GInv r.2.2.2.2.2.2.1.val (C.WB (vals a.keyroots.val) (vals b.keyroots.val) ia (vals b.keyroots.val).length) ⦄ := by
  unfold ted.within_td_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun s => (vals b.keyroots.val).length - s.2.2.2.val)
    (inv := fun s => s.2.2.2.val ≤ (vals b.keyroots.val).length ∧ s.2.1.val.length = td.val.length ∧
      s.2.2.1.val.length = fd.val.length ∧ Ctx.FdB s.2.1.val C.inf ∧ Ctx.FdB s.2.2.1.val C.inf ∧
      C.GInv s.2.1.val (C.WB (vals a.keyroots.val) (vals b.keyroots.val) ia s.2.2.2.val))
  · intro s hs
    obtain ⟨st1, td1, fd1, ib1⟩ := s
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 ⊢
    unfold ted.within_td_loop0_loop0.body
    have hlenv : (alloc.vec.Vec.len b.keyroots).val = (vals b.keyroots.val).length := by
      rw [alloc.vec.Vec.len_val, vals_length]
    by_cases hq : ib1 < alloc.vec.Vec.len b.keyroots
    · simp only [if_pos hq]
      have hibl : ib1.val < (vals b.keyroots.val).length := by
        have : ib1.val < (alloc.vec.Vec.len b.keyroots).val := hq
        omega
      have hkb : ib1.val < b.keyroots.val.length := by rw [vals_length] at hibl; exact hibl
      step as ⟨i1, hi1⟩
      have hJ : (UScalar.cast .Usize i1).val = (vals b.keyroots.val)[ib1.val]'hibl := by
        rw [U32.cast_Usize_val_eq, hi1, vals_getElem _ _ hkb]
      generalize hj0g : UScalar.cast .Usize i1 = j0 at hJ
      simp only [lift, bind_tc_ok]
      have hJmem : (vals b.keyroots.val)[ib1.val]'hibl ∈ vals b.keyroots.val := List.getElem_mem hibl
      have hkJ := hKe.kB _ hJmem
      have hJ1 : 1 ≤ j0.val := by rw [hJ]; exact hkJ.1
      have hJm : j0.val ≤ C.m := by rw [hJ]; exact hkJ.2.1
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < b.lml.val.length := by have : b.lml.val.length = C.m := hK.m2; omega
      step as ⟨i3, hi3⟩
      have hljv : (UScalar.cast .Usize i3).val = C.lb j0.val := by
        have e : j0.val - 1 = i2.val := by omega
        have h := hK.lb_eq j0.val hJ1 hJm
        rw [e] at h
        rw [U32.cast_Usize_val_eq, hi3, ← getU_eq _ _ hi2b, ← h]
      generalize hljg : UScalar.cast .Usize i3 = lj at hljv
      step as ⟨i4, hi4⟩
      have h2t : 2 * t.val < 2 ^ 32 := by have := hK.tbig; omega
      step as ⟨i5, hi5⟩
      have hi4v : i4.val = adf (C.la i0.val) (C.lb j0.val) := by
        rw [hi4, hli, hljv]; unfold adf; split <;> omega
      have hi5v : i5.val = 2 * C.t := by omega
      have hj0eq : (vals b.keyroots.val)[ib1.val]'hibl = j0.val := hJ.symm
      split
      · rename_i hs
        have hskip : 2 * C.t < adf (C.la i0.val) (C.lb j0.val) := by
          have : i5.val < i4.val := hs
          omega
        step as ⟨ib2, hib2⟩
        have hG' := Ctx.skip_step C (KA := vals a.keyroots.val) (KB := vals b.keyroots.val) hKe.sB hia hibl hi0 hj0eq
          (td := td1.val) hskip h6
        refine ⟨by omega, h2, h3, h4, h5, ?_, by omega⟩
        rw [hib2]; exact hG'
      · rename_i hs
        simp only [lift, bind_tc_ok, alloc.vec.Vec.deref_mut]
        have hia1 : 1 ≤ i0.val := (hKe.kA _ (by rw [← hi0]; exact List.getElem_mem hia)).1
        have hia2 : i0.val ≤ C.n := (hKe.kA _ (by rw [← hi0]; exact List.getElem_mem hia)).2.1
        have hkI : Ctx.IsKr C.la C.n i0.val := hKe.kA _ (by rw [← hi0]; exact List.getElem_mem hia)
        have hkJ' : Ctx.IsKr C.lb C.m j0.val := by rw [hJ]; exact hkJ
        have hGood := Ctx.win_good C hKe.hA hKe.hB hia1 hia2 hJ1 hJm
        have hli1 : 1 ≤ C.la i0.val := (hKe.hA.1 _ hia1).1
        have hlj1 : 1 ≤ C.lb j0.val := (hKe.hB.1 _ hJ1).1
        have hsi : (C.win i0.val j0.val).si ≤ C.n := by
          have := (hKe.hA.1 _ hia1).2
          simp only [Ctx.win, Ctx.si]; omega
        have hmw : ((C.win i0.val j0.val).si + 1) * C.w ≤ (C.n + 1) * C.w := Nat.mul_le_mul_right _ (by omega)
        have hTin : (C.win i0.val j0.val).TdInv td1.val 1 1 := by
          intro x y hx1 hxn hy1 hym
          have := h6 x y hx1 hxn hy1 hym
          refine ⟨this.1, fun hd hb => this.2 ?_ hb⟩
          exact Ctx.done_wb C hKe.hA hKe.hB hKe.sA hKe.sB hKe.mA hKe.mB hia hibl hi0 hj0eq hkI hkJ' hJm hx1 hxn hy1 hym hd
        step with fill_window_spec (C.win i0.val j0.val) hGood a b (hK.win _ _) hw hli1 hlj1 td1.slice fd1.slice
          { cells := st1.cells, windows := core.num.U64.wrapping_add st1.windows 1#u64, skipped := st1.skipped,
            attempts := st1.attempts, mirrored := st1.mirrored } i0 j0 tau rfl rfl htau
          (by have := Nat.le_trans hmw hfdlen; rw [← h3] at this; exact this) (by have := htdlen; rw [← h2] at this; exact this) h5 h4 hTin as ⟨r, hr1, hr2, hr3, hr4, hr5, hr6⟩
        obtain ⟨s2, s3, st2⟩ := r
        dsimp only at hr1 hr2 hr3 hr4 hr5 hr6
        have hnew := Ctx.inv_step C hKe.hA hKe.hB (KA := vals a.keyroots.val) (KB := vals b.keyroots.val)
          hKe.sA hKe.sB hia hibl hi0 hj0eq hkI hkJ' (td := td1.val) (td' := s2.val) hr4 hr3 h6
        step as ⟨ib2, hib2⟩
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, by omega⟩
        · show s2.val.length = td.val.length; rw [hr1]; exact h2
        · show s3.val.length = fd.val.length; rw [hr5]; exact h3
        · show Ctx.FdB s2.val C.inf; exact hr2
        · show Ctx.FdB s3.val C.inf; exact hr6
        · show C.GInv s2.val _; rw [hib2]; exact hnew
    · simp only [if_neg hq]
      have hib1 : ib1.val = (vals b.keyroots.val).length := by
        have : ¬ ib1.val < (alloc.vec.Vec.len b.keyroots).val := hq
        omega
      simp only [WP.spec_ok]
      rw [hib1] at h6
      exact ⟨h2, h3, h4, h5, h6⟩
  · exact ⟨hib, rfl, rfl, hTB, hFB, hG⟩

end difffold_lines_extract
