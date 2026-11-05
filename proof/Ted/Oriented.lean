import DifffoldTed
import Basic
import Cell
import Truth
import Window
import LabelLB
import Kr
import Driver
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The doubling loop `ted_oriented`: it returns the exact distance. -/

/-- The context with another threshold. -/
def Ctx.withT (C : Ctx) (T : Nat) : Ctx := { C with t := T }

theorem Ctx.ted_withT (C : Ctx) (T : Nat) : (C.withT T).ted = C.ted := rfl

theorem Ctx.Keys.withT {C : Ctx} {a b : ted.PostTree} (hKe : C.Keys a b) (T : Nat) : (C.withT T).Keys a b :=
  ⟨hKe.hA, hKe.hB, hKe.sA, hKe.sB, hKe.mA, hKe.mB, hKe.kA, hKe.kB⟩

theorem ted_le_cap (C : Ctx) (hn : 1 ≤ C.n) (hm : 1 ≤ C.m) : C.ted ≤ C.n + C.m := by
  have := D_size C.la C.lb C.ren _ 1 C.n 1 C.m (by omega) (by omega) rfl
  unfold Ctx.ted; omega


@[step] theorem dbl32_spec (x : Std.U32) :
    ted.dbl32 x ⦃ r => r.val = if x.val ≥ 2147483648 then 4294967295 else 2 * x.val ⦄ := by
  unfold ted.dbl32
  split
  · rename_i h
    simp only [WP.spec_ok]
    have : x.val ≥ 2147483648 := h
    simp [this, core.num.U32.MAX, U32.rMax]
  · rename_i h
    have : ¬ x.val ≥ 2147483648 := h
    have hU32 : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max, Std.U32.numBits]
    have hb : 2 * x.val ≤ Std.U32.max := by rw [hU32]; omega
    step as ⟨r, hr⟩
    simp [this]; omega

theorem ted_oriented_loop_spec (C : Ctx) (a b : ted.PostTree) (hKe : C.Keys a b)
    (hL : ∀ T, T ≤ C.n + C.m → (C.withT T).Link a b)
    (hbigm : ∀ T, T ≤ C.n + C.m → (C.m + 1) * (2 * T + 1) < 2 ^ 32)
    (hn1 : 1 ≤ C.n) (hm1 : 1 ≤ C.m) (hra : C.la C.n = 1) (hrb : C.lb C.m = 1)
    (n m : Std.Usize) (hnv : n.val = C.n) (hmv : m.val = C.m) (cap : Std.U32) (hcap : cap.val = C.n + C.m)
    (st : ted.Stats) (tau : Std.U32) (htau : 1 ≤ tau.val) :
    ted.ted_oriented_loop a b st n m cap tau ⦃ r => r.1.val = C.ted ⦄ := by
  unfold ted.ted_oriented_loop
  apply loop.spec_decr_nat
    (measure := fun s => C.n + C.m + 1 - min s.2.val (C.n + C.m))
    (inv := fun s => 1 ≤ s.2.val)
  · intro s hs
    obtain ⟨st1, tau0⟩ := s
    dsimp only at hs ⊢
    unfold ted.ted_oriented_loop.body
    have hted := ted_le_cap C hn1 hm1
    have hnb : C.n < 2 ^ 31 := (hL 0 (by omega)).nbig
    have hmb : C.m < 2 ^ 31 := (hL 0 (by omega)).mbig
    simp only [lift, bind_tc_ok]
    have hc64 : (UScalar.cast .U64 tau0).val = tau0.val := by
      rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
      exact Nat.mod_eq_of_lt (by have := tau0.hBounds; simp [UScalar.max] at this; omega)
    generalize (UScalar.cast .U64 tau0) = i at hc64
    have htau0b : tau0.val < 2 ^ 32 := by have := tau0.hBounds; simp [UScalar.max] at this; omega
    have hU64 : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, UScalar.max, Std.U64.numBits]
    have hi3b : i.val * 3 ≤ Std.U64.max := by rw [hU64]; omega
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = max C.n C.m := by omega
    have hi2c : (UScalar.cast .U64 i2).val = i2.val := by
      rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
      exact Nat.mod_eq_of_lt (by have := hi2.symm; omega)
    generalize (UScalar.cast .U64 i2) = i3 at hi2c
    by_cases hc : i1 ≥ i3
    · simp only [if_pos hc, bind_tc_ok]
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = min (cap).val cap.val := hi5
      have hT : i5.val ≤ C.n + C.m := by omega
      refine WP.spec_bind (within_td_spec (C.withT i5.val) a b (hL _ hT) (hKe.withT _) rfl i5 _ rfl hn1 hm1 hra hrb
        (hbigm _ hT)) ?_
      rintro ⟨⟨o, td⟩, st2⟩ hpost
      cases o with
      | none =>
        have hlt : i5.val < C.ted := hpost.1
        show (do let tau2 ← ted.dbl32 cap; ok (cont (st2, tau2))) ⦃ _ ⦄
        step as ⟨tau2, htau2⟩
        have hd : tau2.val = if (cap).val ≥ 2147483648 then 4294967295 else 2 * (cap).val := htau2
        exfalso; omega
      | some d =>
        show ok (done (d, st2)) ⦃ _ ⦄
        simp only [WP.spec_ok]
        exact hpost.1.1
    · simp only [if_neg hc, bind_tc_ok]
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = min (tau0).val cap.val := hi5
      have hT : i5.val ≤ C.n + C.m := by omega
      refine WP.spec_bind (within_td_spec (C.withT i5.val) a b (hL _ hT) (hKe.withT _) rfl i5 _ rfl hn1 hm1 hra hrb
        (hbigm _ hT)) ?_
      rintro ⟨⟨o, td⟩, st2⟩ hpost
      cases o with
      | none =>
        have hlt : i5.val < C.ted := hpost.1
        show (do let tau2 ← ted.dbl32 tau0; ok (cont (st2, tau2))) ⦃ _ ⦄
        step as ⟨tau2, htau2⟩
        have hd : tau2.val = if (tau0).val ≥ 2147483648 then 4294967295 else 2 * (tau0).val := htau2
        have hcl : tau0.val < C.n + C.m := by omega
        have hdd := hd
        refine ⟨by split at hdd <;> omega, ?_⟩
        split at hdd <;> omega
      | some d =>
        show ok (done (d, st2)) ⦃ _ ⦄
        simp only [WP.spec_ok]
        exact hpost.1.1
  · exact htau


@[step] theorem max32_spec (x y : Std.U32) : ted.max32 x y ⦃ r => r.val = max x.val y.val ⦄ := by
  unfold ted.max32
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

/-- `ted_oriented` returns the exact distance of two non-empty trees. -/
theorem ted_oriented_spec (C : Ctx) (a b : ted.PostTree) (hKe : C.Keys a b)
    (hL : ∀ T, T ≤ C.n + C.m → (C.withT T).Link a b)
    (hbigm : ∀ T, T ≤ C.n + C.m → (C.m + 1) * (2 * T + 1) < 2 ^ 32)
    (hn1 : 1 ≤ C.n) (hm1 : 1 ≤ C.m) (hra : C.la C.n = 1) (hrb : C.lb C.m = 1)
    (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31) (st : ted.Stats) :
    ted.ted_oriented a b st ⦃ r => r.1.val = C.ted ⦄ := by
  unfold ted.ted_oriented
  have hK0 := hL 0 (by omega)
  have hnb : C.n < 2 ^ 31 := hK0.nbig
  have hmb : C.m < 2 ^ 31 := hK0.mbig
  have hlenA : (alloc.vec.Vec.len a.label).val = C.n := by rw [alloc.vec.Vec.len_val]; exact hK0.n1
  have hlenB : (alloc.vec.Vec.len b.label).val = C.m := by rw [alloc.vec.Vec.len_val]; exact hK0.m1
  simp only [ted.PostTree.len, bind_tc_ok]
  step as ⟨i, hi⟩
  have hcap : (UScalar.cast .U32 i).val = C.n + C.m := by
    rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  generalize hcg : UScalar.cast .U32 i = cap at hcap
  simp only [lift, bind_tc_ok]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = C.n - C.m + (C.m - C.n) := by omega
  have hi2 : (UScalar.cast .U32 i1).val = i1.val := by
    rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
    exact Nat.mod_eq_of_lt (by omega)
  generalize UScalar.cast .U32 i1 = i2 at hi2
  step with label_lower_bound_spec a b (by rw [hK0.n1]; exact hnb) (by rw [hK0.m1]; exact hmb)
    (by intro j hj; exact hla j (by have := hK0.n1; show _ < a.label.length; omega)) as ⟨i3, hi3⟩
  step as ⟨tau, htau⟩
  step as ⟨tau1, htau1⟩
  refine WP.spec_mono (ted_oriented_loop_spec C a b hKe hL hbigm hn1 hm1 hra hrb _ _ hlenA hlenB cap hcap st tau1 ?_) ?_
  · omega
  · intro r hr; exact hr


/-- The distance the code computes is the minimum cost of a valid tree edit mapping (Tai): one to one,
preserving postorder and the descendant relation, with cost = unmapped nodes + relabel costs. -/
theorem ted_eq_min_mapping (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) :
    (∀ M : List (Nat × Nat), Valid C.la C.lb M → InRange 1 C.n 1 C.m M →
      C.ted ≤ Cost C.ren 1 C.n 1 C.m M) ∧
    ∃ M : List (Nat × Nat), Valid C.la C.lb M ∧ InRange 1 C.n 1 C.m M ∧ Cost C.ren 1 C.n 1 C.m M = C.ted := by
  have hcA : Closed C.la 1 C.n := fun u hu _ => (hA.1 u hu).1
  have hcB : Closed C.lb 1 C.m := fun u hu _ => (hB.1 u hu).1
  refine ⟨fun M hv hr => D_le_cost hA hB _ 1 C.n 1 C.m M (Nat.le_refl _) (Nat.le_refl _) hcA hcB rfl hv hr, ?_⟩
  exact exists_map hA hB _ 1 C.n 1 C.m (Nat.le_refl _) (Nat.le_refl _) hcA hcB rfl

end difffold_lines_extract
