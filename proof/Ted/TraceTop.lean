import TraceOuter
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The traceback as a whole, and the mapping built from it. -/

theorem ted_le_sum (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) :
    TED a b ≤ a.label.length + b.label.length := by
  have h := (D_size (la := laOf a) (lb := laOf b) (ren := rcost a b) _ 1 a.label.length 1 b.label.length
    (by omega) (by omega) rfl).2.2
  unfold TED
  omega

theorem Pto_replicate (n k : Nat) : Pto n (List.replicate k (0#usize)) = [] := by
  unfold Pto
  rw [List.filterMap_eq_nil_iff]
  intro x _
  have h0 : ((List.replicate k (0#usize))[x]!).val = 0 := by
    by_cases hk : x < k
    · simp [hk]
    · simp [hk, UScalar.default_val]
  show (if ((List.replicate k (0#usize))[x]!).val = 0 then none else _) = none
  rw [if_pos h0]

set_option maxHeartbeats 1600000 in
theorem traceback_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (cost : Std.U32) (prefer_match : Bool) (hcost : cost.val = TED a b) :
    ted.traceback a b cost prefer_match ⦃ r => r.length = a.label.length + 1 ∧
      Sol (laOf a) (laOf b) (rcost a b) 1 a.label.length 1 b.label.length (Pto a.label.length r.val) ⦄ := by
  unfold ted.traceback
  have hT : cost.val ≤ a.label.length + b.label.length := by rw [hcost]; exact ted_le_sum a b hA hB
  have tt : TT a b cost.val := ⟨hA, hB, hna, hnb, hT, by rw [hcost]⟩
  have hUM : 2 ^ 32 ≤ Std.Usize.max + 1 := by scalar_tac
  have hlenA : (alloc.vec.Vec.len a.label).val = a.label.length := by rw [alloc.vec.Vec.len_val]
  have hlenB : (alloc.vec.Vec.len b.label).val = b.label.length := by rw [alloc.vec.Vec.len_val]
  simp only [ted.Stats.Insts.CoreDefaultDefault.default, core.default.DefaultBool.default,
    core.default.DefaultU64.default, core.default.DefaultU32.default, bind_tc_ok]
  have hw : (mkCtx a b cost.val).w = 2 * (mkCtx a b cost.val).t + 1 := rfl
  have hbigm : ((mkCtx a b cost.val).m + 1) * (mkCtx a b cost.val).w < 2 ^ 32 := by
    show (b.label.length + 1) * (2 * cost.val + 1) < 2 ^ 32
    have : (b.label.length + 1) * (2 * cost.val + 1) ≤ 2 ^ 14 * 2 ^ 16 := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine WP.spec_bind (within_td_spec (mkCtx a b cost.val) a b (mkCtx_link a b hA hB hna hnb cost.val hT)
    (mkCtx_keys a b hA hB cost.val) hw cost _ rfl hA.pos hB.pos
    hA.root hB.root hbigm) ?_
  rintro ⟨⟨o, td⟩, st1⟩ hpost
  obtain ⟨_, hG, hL⟩ := hpost
  have hted : (mkCtx a b cost.val).ted ≤ (mkCtx a b cost.val).t := by
    show TED a b ≤ cost.val
    rw [hcost]
  have hGt := hG hted
  obtain ⟨hlen, hFB⟩ := hL hted
  step as ⟨t, ht⟩
  step as ⟨inf, hinf⟩
  step as ⟨i, hi⟩
  step as ⟨w, hw'⟩
  step as ⟨i1, hi1⟩
  step as ⟨to_b, hto1, hto2⟩
  step as ⟨stack_i, hsi⟩
  step as ⟨stack_j, hsj⟩
  have htv : t.val = cost.val := by rw [ht, U32.cast_Usize_val_eq]
  have hwv : w.val = 2 * cost.val + 1 := by omega
  have hi1v : i1.val = a.label.length + 1 := by omega
  have h1v : (1#usize).val = 1 := by simp
  have hSi : stack_i.val = [a.label.len] := by rw [hsi]; simp [alloc.vec.Vec.new]
  have hSj : stack_j.val = [b.label.len] := by rw [hsj]; simp [alloc.vec.Vec.new]
  have hstk1 : stk stack_i.val stack_j.val 1 = [(a.label.length, b.label.length)] := by
    rw [hSi, hSj]
    unfold stk
    simp [hlenA, hlenB]
  have hA1 := hA.root
  have hB1 := hB.root
  have hroot : TD (laOf a) (laOf b) (rcost a b) a.label.length b.label.length = cost.val := by
    unfold TD
    rw [hA1, hB1, hcost]
    rfl
  have hS : OS a b cost.val td to_b stack_i stack_j (1#usize).val := by
    refine ⟨hlen, hFB, hGt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hto2, hi1v]
    · show stack_i.val.length = stack_j.val.length
      rw [hSi, hSj]; rfl
    · rw [h1v]; show 1 ≤ stack_i.val.length
      rw [hSi]; simp
    · show stack_i.val.length ≤ _
      rw [hSi]; have : 1 ≤ a.label.val.length := hA.pos; simp; omega
    · rw [h1v, hstk1]
      intro w hw
      rw [List.mem_singleton] at hw
      subst hw
      refine ⟨hA.pos, Nat.le_refl _, hB.pos, Nat.le_refl _, ?_⟩
      show TD (laOf a) (laOf b) (rcost a b) a.label.length b.label.length +
        adf (laOf a a.label.length) (laOf b b.label.length) ≤ cost.val
      rw [hroot, hA1, hB1]
      show cost.val + 0 ≤ cost.val
      omega
    · rw [h1v, hstk1]
      unfold ssum
      simp [hA1, hB1]
      have : 1 ≤ a.label.val.length := hA.pos
      have : 1 ≤ b.label.val.length := hB.pos
      omega
    · rw [h1v, hstk1, hto1, Pto_replicate]
      exact oinv_init hA1 hB1
  exact outer_spec a b prefer_match tt cost rfl t w inf htv hwv (by omega) st1 td to_b stack_i stack_j 1#usize hS

end difffold_lines_extract
