import WalkFacts
import TraceInv
import Mirror2
import Stats
import Check
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The small helpers of the traceback. -/

@[step] theorem eq32_spec (x y : Std.U32) : ted.eq32 x y ⦃ r => r = decide (x.val = y.val) ⦄ := by
  unfold ted.eq32
  split
  · rename_i h
    simp only [WP.spec_ok]
    have : x.val = y.val := by rw [h]
    simp [this]
  · rename_i h
    simp only [WP.spec_ok]
    have : x.val ≠ y.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [this]

theorem is_leaf_case_spec (p q lx ly li lj : Std.Usize) :
    ted.is_leaf_case p q lx ly li lj ⦃ r => r = true ↔
      (0 < p.val ∧ 0 < q.val ∧ lx.val = li.val ∧ ly.val = lj.val) ⦄ := by
  unfold ted.is_leaf_case
  by_cases h1 : p > 0#usize
  · by_cases h2 : q > 0#usize
    · by_cases h3 : lx = li
      · by_cases h4 : ly = lj
        · simp only [if_pos h1, if_pos h2, if_pos h3, WP.spec_ok]
          have a1 : 0 < p.val := h1
          have a2 : 0 < q.val := h2
          have a3 : lx.val = li.val := by rw [h3]
          have a4 : ly.val = lj.val := by rw [h4]
          simp [a1, a2, a3, a4, h4]
        · simp only [if_pos h1, if_pos h2, if_pos h3, WP.spec_ok]
          have a4 : ¬ ly.val = lj.val := fun e => h4 (UScalar.eq_of_val_eq e)
          simp [h4, a4]
      · simp only [if_pos h1, if_pos h2, if_neg h3, WP.spec_ok]
        have a3 : ¬ lx.val = li.val := fun e => h3 (UScalar.eq_of_val_eq e)
        simp [a3]
    · simp only [if_pos h1, if_neg h2, WP.spec_ok]
      have a2 : ¬ 0 < q.val := h2
      simp [a2]
  · simp only [if_neg h1, WP.spec_ok]
    have a1 : ¬ 0 < p.val := h1
    simp [a1]

theorem choose_diag_spec (prefer diag_ok del_ok ins_ok : Bool) :
    ted.choose_diag prefer diag_ok del_ok ins_ok ⦃ r => r = ((prefer && diag_ok) || (!del_ok && !ins_ok)) ⦄ := by
  unfold ted.choose_diag
  cases prefer <;> cases diag_ok <;> cases del_ok <;> cases ins_ok <;> simp

theorem del_test_spec (fd : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32) (p q : Std.Usize) (v : Std.U32)
    (hw : w.val = 2 * t.val + 1) (hlen : (p.val + 1) * w.val ≤ fd.val.length)
    (hbig : (p.val + 1) * w.val < 2 ^ 32) (hinf : inf.val + 1 < 2 ^ 32)
    (hFB : Ctx.FdB fd.val inf.val) :
    ted.del_test fd w t inf (p, q) v ⦃ r => (r = true ↔
      (0 < p.val ∧ rd fd.val w.val t.val inf.val (p.val - 1) q.val + 1 = v.val)) ⦄ := by
  unfold ted.del_test
  show (if p > 0#usize then _ else _) ⦃ _ ⦄
  by_cases h1 : p > 0#usize
  · rw [if_pos h1]
    have a1 : 0 < p.val := h1
    step as ⟨i, hi⟩
    step as ⟨g, hg⟩
    rw [hi] at hg
    have hm : (p.val - 1 + 1) * w.val ≤ (p.val + 1) * w.val := Nat.mul_le_mul_right _ (by omega)
    have hgle := rd_le fd.val w.val t.val inf.val (p.val - 1) q.val hw (by omega) hFB
    step as ⟨i2, hi2⟩
    step as ⟨r, hr⟩
    rw [hr]
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨a1, by omega⟩
    · intro h; omega
  · rw [if_neg h1]
    simp only [WP.spec_ok]
    have a1 : ¬ 0 < p.val := h1
    simp [a1]

theorem ins_test_spec (fd : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32) (p q : Std.Usize) (v : Std.U32)
    (hw : w.val = 2 * t.val + 1) (hlen : (p.val + 1) * w.val ≤ fd.val.length)
    (hbig : (p.val + 1) * w.val < 2 ^ 32) (hinf : inf.val + 1 < 2 ^ 32)
    (hFB : Ctx.FdB fd.val inf.val) :
    ted.ins_test fd w t inf (p, q) v ⦃ r => (r = true ↔
      (0 < q.val ∧ rd fd.val w.val t.val inf.val p.val (q.val - 1) + 1 = v.val)) ⦄ := by
  unfold ted.ins_test
  show (if q > 0#usize then _ else _) ⦃ _ ⦄
  by_cases h1 : q > 0#usize
  · rw [if_pos h1]
    have a1 : 0 < q.val := h1
    step as ⟨i, hi⟩
    step as ⟨g, hg⟩
    rw [hi] at hg
    have hgle := rd_le fd.val w.val t.val inf.val p.val (q.val - 1) hw hlen hFB
    step as ⟨i2, hi2⟩
    step as ⟨r, hr⟩
    rw [hr]
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨a1, by omega⟩
    · intro h; omega
  · rw [if_neg h1]
    simp only [WP.spec_ok]
    have a1 : ¬ 0 < q.val := h1
    simp [a1]

theorem diag_test_spec (a b : ted.PostTree) (fd td : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32)
    (li lj p q x y lx ly : Std.Usize) (leaf_case : Bool) (v : Std.U32)
    (hw : w.val = 2 * t.val + 1) (hinf : 2 * inf.val + 2 < 2 ^ 32)
    (hlen : (p.val + 1) * w.val ≤ fd.val.length) (hbig : (p.val + 1) * w.val < 2 ^ 32)
    (hlen2 : (lx.val - li.val + 1) * w.val ≤ fd.val.length) (hbig2 : (lx.val - li.val + 1) * w.val < 2 ^ 32)
    (hlent : (x.val + 1) * w.val ≤ td.val.length) (hbigt : (x.val + 1) * w.val < 2 ^ 32)
    (hFB : Ctx.FdB fd.val inf.val) (hTB : Ctx.FdB td.val inf.val)
    (hx : 1 ≤ x.val ∧ x.val ≤ a.label.length) (hy : 1 ≤ y.val ∧ y.val ≤ b.label.length)
    (hka : a.kind.length = a.label.length) (hkb : b.kind.length = b.label.length)
    (hll : li.val ≤ lx.val) (hll' : lj.val ≤ ly.val) :
    ted.diag_test a b fd td w t inf (li, lj) (p, q) (x, y) (lx, ly) leaf_case v ⦃ r => (r = true ↔
      (0 < p.val ∧ 0 < q.val ∧
        ((leaf_case = true → rcost a b x.val y.val < 2 ∧
          rd fd.val w.val t.val inf.val (p.val - 1) (q.val - 1) + rcost a b x.val y.val = v.val) ∧
        (leaf_case = false →
          rd fd.val w.val t.val inf.val (lx.val - li.val) (ly.val - lj.val) +
            rd td.val w.val t.val inf.val x.val y.val = v.val)))) ⦄ := by
  unfold ted.diag_test
  show (if p > 0#usize then _ else _) ⦃ _ ⦄
  by_cases h1 : p > 0#usize
  · by_cases h2 : q > 0#usize
    · have a1 : 0 < p.val := h1
      have a2 : 0 < q.val := h2
      rw [if_pos h1, if_pos h2]
      have hU : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max, UScalar.max, UScalarTy.numBits, Std.U32.numBits]
      by_cases hl : leaf_case = true
      · rw [if_pos hl]
        step with relabel_cost_spec a b x y hx.1 hy.1 (by omega) (by omega) (by omega) (by omega) as ⟨rc, hrc⟩
        by_cases h3 : rc < 2#u32
        · rw [if_pos h3]
          have a3 : rc.val < 2 := h3
          step as ⟨i, hi⟩
          step as ⟨i1, hi1⟩
          have hm : (p.val - 1 + 1) * w.val ≤ (p.val + 1) * w.val := Nat.mul_le_mul_right _ (by omega)
          step as ⟨i2, hi2⟩
          rw [hi, hi1] at hi2
          have hr1 := rd_le fd.val w.val t.val inf.val (p.val - 1) (q.val - 1) hw (by omega) hFB
          have hb : i2.val + rc.val ≤ Std.U32.max := by rw [hU]; omega
          step as ⟨i3, hi3⟩
          step as ⟨r, hr⟩
          rw [hr, decide_eq_true_iff]
          constructor
          · intro h
            refine ⟨a1, a2, fun _ => ⟨by rw [← hrc]; exact a3, ?_⟩, fun h' => absurd (hl.symm.trans h') (by simp)⟩
            rw [← hrc, ← hi2]; omega
          · intro h
            have := (h.2.2.1 hl).2
            rw [← hrc] at this
            omega
        · rw [if_neg h3]
          simp only [WP.spec_ok]
          have a3 : ¬ rc.val < 2 := h3
          simp only [Bool.false_eq_true, false_iff]
          intro h
          have := (h.2.2.1 hl).1
          rw [← hrc] at this
          exact a3 this
      · have hlf : leaf_case = false := by simpa using hl
        rw [if_neg hl]
        step as ⟨tdv, htdv⟩
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        have hlen2' : (i.val + 1) * w.val ≤ fd.val.length := by rw [hi]; exact hlen2
        have hbig2' : (i.val + 1) * w.val < 2 ^ 32 := by rw [hi]; exact hbig2
        step as ⟨i2, hi2⟩
        have hr1 := rd_le fd.val w.val t.val inf.val (lx.val - li.val) (ly.val - lj.val) hw hlen2 hFB
        have hr2 := rd_le td.val w.val t.val inf.val x.val y.val hw hlent hTB
        rw [hi, hi1] at hi2
        have hb : i2.val + tdv.val ≤ Std.U32.max := by rw [hU]; omega
        step as ⟨i3, hi3⟩
        step as ⟨r, hr⟩
        rw [hr, decide_eq_true_iff]
        constructor
        · intro h
          refine ⟨a1, a2, fun h' => absurd h' hl, fun _ => ?_⟩
          rw [← htdv, ← hi2]; omega
        · intro h
          have := h.2.2.2 hlf
          omega
    · rw [if_pos h1, if_neg h2]
      simp only [WP.spec_ok]
      have a2 : ¬ 0 < q.val := h2
      simp [a2]
  · rw [if_neg h1]
    simp only [WP.spec_ok]
    have a1 : ¬ 0 < p.val := h1
    simp [a1]

theorem getG_snoc {α : Type} [Inhabited α] (l : List α) (x : α) (i : Nat) (h : i = l.length) :
    (l ++ [x])[i]! = x := by
  subst h; simp [List.getElem!_eq_getElem?_getD]

theorem push_slot_spec (stack_i stack_j : alloc.vec.Vec Std.Usize) (top x y : Std.Usize)
    (hl : stack_i.length = stack_j.length) (ht : top.val ≤ stack_i.length)
    (hmax : stack_i.length + 1 ≤ Std.Usize.max) :
    ted.push_slot stack_i stack_j top x y ⦃ r =>
      r.1.length = r.2.length ∧ top.val + 1 ≤ r.1.length ∧
      (∀ k < top.val, r.1.val[k]! = stack_i.val[k]! ∧ r.2.val[k]! = stack_j.val[k]!) ∧
      (r.1.val[top.val]!).val = x.val ∧ (r.2.val[top.val]!).val = y.val ∧
      (stack_i.length ≤ r.1.length ∧ r.1.length ≤ stack_i.length + 1) ⦄ := by
  unfold ted.push_slot
  have hlen := alloc.vec.Vec.len_val stack_i
  have hl' : stack_i.val.length = stack_j.val.length := hl
  have ht' : top.val ≤ stack_i.val.length := ht
  by_cases h : top = alloc.vec.Vec.len stack_i
  · rw [if_pos h]
    have htop : top.val = stack_i.val.length := by rw [h]; exact hlen
    have hmax2 : stack_j.length + 1 ≤ Std.Usize.max := hl ▸ hmax
    step as ⟨si, hsi⟩
    step as ⟨sj, hsj⟩
    have e1 : si.val = stack_i.val ++ [x] := hsi
    have e2 : sj.val = stack_j.val ++ [y] := hsj
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show si.val.length = sj.val.length
      rw [e1, e2, List.length_append, List.length_append, List.length_singleton, List.length_singleton]; omega
    · show top.val + 1 ≤ si.val.length
      rw [e1, List.length_append, List.length_singleton]; omega
    · intro k hk
      rw [e1, e2]
      have hk1 : k < stack_i.val.length := by omega
      have hk2 : k < stack_j.val.length := by omega
      constructor
      · rw [getG_eq _ _ (by rw [List.length_append]; simp; omega), getG_eq _ _ hk1, List.getElem_append_left hk1]
      · rw [getG_eq _ _ (by rw [List.length_append]; simp; omega), getG_eq _ _ hk2, List.getElem_append_left hk2]
    · rw [e1, getG_snoc _ _ _ htop]
    · rw [e2, getG_snoc _ _ _ (by omega)]
    · show stack_i.val.length ≤ si.val.length ∧ si.val.length ≤ stack_i.val.length + 1
      rw [e1, List.length_append, List.length_singleton]; omega
  · rw [if_neg h]
    have htop : top.val < stack_i.val.length := by
      have : top.val ≠ (alloc.vec.Vec.len stack_i).val := fun e => h (UScalar.eq_of_val_eq e)
      have hlen2 : (alloc.vec.Vec.len stack_i).val = stack_i.val.length := hlen
      omega
    step as ⟨old, imb, ho, himb⟩
    step as ⟨old2, imb2, ho2, himb2⟩
    have e1 : (imb x).val = stack_i.val.set top.val x := by rw [himb, alloc.vec.Vec.set_val_eq]
    have e2 : (imb2 y).val = stack_j.val.set top.val y := by rw [himb2, alloc.vec.Vec.set_val_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (imb x).val.length = (imb2 y).val.length
      rw [e1, e2, List.length_set, List.length_set]; exact hl'
    · show top.val + 1 ≤ (imb x).val.length
      rw [e1, List.length_set]; omega
    · intro k hk
      rw [e1, e2]
      exact ⟨getG_set_ne _ _ _ _ (by omega), getG_set_ne _ _ _ _ (by omega)⟩
    · rw [e1, getG_set_eq _ _ _ htop]
    · rw [e2, getG_set_eq _ _ _ (by omega)]
    · show stack_i.val.length ≤ (imb x).val.length ∧ (imb x).val.length ≤ stack_i.val.length + 1
      rw [e1, List.length_set]; omega

end difffold_lines_extract
