import DifffoldTed
import Overlap
import Basic
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Theorems over the Aeneas extraction of the real `label_lower_bound` of `src/ted.rs` (counting version).
It returns `max(n, m)` minus the size of the label multiset overlap (`Ted.overlap`, `Overlap.lean`). -/

/-- The values of a list of `u32`. -/
def vals (l : List Std.U32) : List Nat := l.map (fun x => x.val)

theorem vals_length (l : List Std.U32) : (vals l).length = l.length := by simp [vals]

theorem vals_getElem (l : List Std.U32) (i : Nat) (h : i < l.length) :
    (vals l)[i]'(by simpa [vals_length] using h) = (l[i]'h).val := by
  simp [vals]

theorem count_take_succ (l : List Std.U32) (i : Nat) (h : i < l.length) (x : Nat) :
    (vals (l.take (i + 1))).count x = (vals (l.take i)).count x + if (l[i]'h).val = x then 1 else 0 := by
  have e : vals (l.take (i + 1)) = vals (l.take i) ++ [(l[i]'h).val] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    simp only [vals, List.map_append]
    simp
  rw [e, List.count_append]
  by_cases hh : (l[i]'h).val = x <;> simp [hh]


/-- Loop 0 finds a bound on the labels of `a`. -/
@[step] theorem llb_top_loop_spec (a : ted.PostTree) (top i : Std.Usize)
    (hA : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (hi : i.val ≤ a.label.length) (htop : top.val ≤ 2 ^ 31)
    (hlt : ∀ j < i.val, (a.label.val[j]!).val < top.val) :
    ted.label_lower_bound_loop0 a top i ⦃ r =>
      r = (a.label, a.lml, a.keyroots, a.kids, a.kind, r.2.2.2.2.2) ∧
      r.2.2.2.2.2.val ≤ 2 ^ 31 ∧ ∀ j < a.label.length, (a.label.val[j]!).val < r.2.2.2.2.2.val ⦄ := by
  unfold ted.label_lower_bound_loop0
  apply loop.spec_decr_nat
    (measure := fun p => a.label.length - p.2.val)
    (inv := fun p => p.2.val ≤ a.label.length ∧ p.1.val ≤ 2 ^ 31 ∧
      ∀ j < p.2.val, (a.label.val[j]!).val < p.1.val)
  · intro p hp
    obtain ⟨tp, c⟩ := p
    obtain ⟨hc, ht, hl⟩ := hp
    unfold ted.label_lower_bound_loop0.body
    dsimp only at hc ht hl ⊢
    have hlen := alloc.vec.Vec.len_val a.label
    split
    · rename_i hci
      have hci' : c.val < a.label.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨l, hl'⟩
      have hlv : l.val = (a.label.val[c.val]!).val := by
        rw [hl', U32.cast_Usize_val_eq, hi2, getU_eq _ _ hci']
      have hAc := hA c.val hci'
      split
      · rename_i hlt'
        have hge : tp.val ≤ l.val := by scalar_tac
        step as ⟨top1, htop1⟩
        step as ⟨i3, hi3⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        intro j hj
        by_cases hjc : j = c.val
        · subst hjc; omega
        · have := hl j (by omega); omega
      · rename_i hlt'
        have hge : l.val < tp.val := by scalar_tac
        step as ⟨i3, hi3⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        intro j hj
        by_cases hjc : j = c.val
        · subst hjc; omega
        · have := hl j (by omega); omega
    · rename_i hci
      have hc2 : a.label.length ≤ c.val := by scalar_tac
      refine ⟨rfl, ht, ?_⟩
      intro j hj; exact hl j (by omega)
  · exact ⟨hi, htop, hlt⟩


/-- Loop 1 counts the labels of `a` into `cnt`. -/
@[step] theorem llb_count_loop_spec (v cnt : alloc.vec.Vec Std.U32) (i : Std.Usize) (top : Nat)
    (hv : ∀ j < v.length, (v.val[j]!).val < top) (hlen : v.length < 2 ^ 31)
    (hcnt : cnt.length = top) (hi : i.val ≤ v.length)
    (hinv : ∀ x < top, (cnt.val[x]!).val = (vals (v.val.take i.val)).count x) :
    ted.label_lower_bound_loop1 v i cnt ⦃ r =>
      r.length = top ∧ ∀ x < top, (r.val[x]!).val = (vals v.val).count x ⦄ := by
  unfold ted.label_lower_bound_loop1
  apply loop.spec_decr_nat
    (measure := fun p => v.length - p.1.val)
    (inv := fun p => p.1.val ≤ v.length ∧ p.2.length = top ∧
      ∀ x < top, (p.2.val[x]!).val = (vals (v.val.take p.1.val)).count x)
  · intro p hp
    obtain ⟨c, o⟩ := p
    obtain ⟨hc, hl, hI⟩ := hp
    unfold ted.label_lower_bound_loop1.body
    dsimp only at hc hl hI ⊢
    have hlenv := alloc.vec.Vec.len_val v
    split
    · rename_i hci
      have hci' : c.val < v.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨l, hl'⟩
      have hlv : l.val = (v.val[c.val]!).val := by
        rw [hl', U32.cast_Usize_val_eq, hi2, getU_eq _ _ hci']
      have hlt := hv c.val hci'
      have hlc : l.val < o.val.length := by
        have : o.length = top := hl
        have : l.val < top := by omega
        have h3 : o.val.length = top := hl
        omega
      step as ⟨i3, imb, hi3, himb⟩
      have hb : l.val < o.val.length := hlc
      have e : (o.val[l.val]'hb) = o.val[l.val]! := (getU_eq _ _ hb).symm
      have hi3v : i3.val = (vals (v.val.take c.val)).count l.val := by
        rw [hi3, e]; exact hI l.val (by omega)
      have hcle : (vals (v.val.take c.val)).count l.val ≤ c.val := by
        have := List.count_le_length (a := l.val) (l := vals (v.val.take c.val))
        rw [vals_length, List.length_take] at this
        omega
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      have hset : (imb i4).val = o.val.set l.val i4 := by
        rw [himb, alloc.vec.Vec.set_val_eq]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
      · intro x hx
        rw [hset]
        have hsucc := count_take_succ v.val c.val hci' x
        have hi5' : i5.val = c.val + 1 := by omega
        rw [hi5']
        rw [hsucc]
        by_cases hxl : x = l.val
        · subst hxl
          rw [getU_set_eq _ _ _ hb]
          have hvl : (v.val[c.val]'hci').val = l.val := by rw [hlv, getU_eq _ _ hci']
          simp [hi4, hi3v, hvl]
        · rw [getU_set_ne _ _ _ _ hxl, hI x hx]
          have : ¬ (v.val[c.val]'hci').val = x := by
            intro h; apply hxl; rw [hlv, ← h, getU_eq _ _ hci']
          simp [this]
    · rename_i hci
      have hc2 : v.length ≤ c.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hl, ?_⟩
      intro x hx
      rw [hI x hx]
      have : c.val = v.length := by omega
      rw [this]
      simp [vals]
  · exact ⟨hi, hcnt, hinv⟩


/-- Loop 2 consumes the counts with the labels of `b`; `C` collects the matched labels. -/
@[step] theorem llb_consume_loop_spec (b : ted.PostTree) (top i : Std.Usize) (cnt : alloc.vec.Vec Std.U32)
    (common : Std.U32) (A : List Nat)
    (hAtop : ∀ x ∈ A, x < top.val) (hcnt : cnt.length = top.val) (hb : b.label.length < 2 ^ 31)
    (hi : i.val ≤ b.label.length) (hcom : common.val ≤ i.val)
    (hinv : ∃ C : List Nat, (∀ x, C.count x = min (A.count x) ((vals (b.label.val.take i.val)).count x)) ∧
      C.length = common.val ∧ ∀ x < top.val, (cnt.val[x]!).val = A.count x - C.count x) :
    ted.label_lower_bound_loop2 b top i cnt common ⦃ r =>
      r = (b.label, b.lml, b.keyroots, b.kids, b.kind, r.2.2.2.2.2) ∧
      ∃ C : List Nat, (∀ x, C.count x = min (A.count x) ((vals b.label.val).count x)) ∧
        C.length = r.2.2.2.2.2.val ⦄ := by
  unfold ted.label_lower_bound_loop2
  apply loop.spec_decr_nat
    (measure := fun p => b.label.length - p.1.val)
    (inv := fun p => p.1.val ≤ b.label.length ∧ p.2.2.val ≤ p.1.val ∧ p.2.1.length = top.val ∧
      ∃ C : List Nat, (∀ x, C.count x = min (A.count x) ((vals (b.label.val.take p.1.val)).count x)) ∧
        C.length = p.2.2.val ∧ ∀ x < top.val, (p.2.1.val[x]!).val = A.count x - C.count x)
  · intro p hp
    obtain ⟨c, o, m⟩ := p
    obtain ⟨hc, hm, hl, C, hC, hCl, hCc⟩ := hp
    unfold ted.label_lower_bound_loop2.body
    dsimp only at hc hm hl hC hCl hCc ⊢
    have hlenv := alloc.vec.Vec.len_val b.label
    split
    · rename_i hci
      have hci' : c.val < b.label.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨l, hl'⟩
      have hlv : l.val = (b.label.val[c.val]!).val := by
        rw [hl', U32.cast_Usize_val_eq, hi2, getU_eq _ _ hci']
      have hsucc := count_take_succ b.label.val c.val hci'
      have hbl : (b.label.val[c.val]'hci').val = l.val := by rw [hlv, getU_eq _ _ hci']
      have hso : ∀ x, (vals (b.label.val.take (c.val + 1))).count x =
          (vals (b.label.val.take c.val)).count x + if l.val = x then 1 else 0 := by
        intro x; rw [hsucc x, hbl]
      have hlen' : o.val.length = top.val := hl
      split
      · rename_i hlt'
        have hlt2 : l.val < top.val := hlt'
        have hlo : l.val < o.val.length := by omega
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = A.count l.val - C.count l.val := by
          rw [hi3, ← getU_eq _ _ hlo]; exact hCc l.val hlt2
        split
        · rename_i hpos
          have hpos' : 0 < i3.val := hpos
          step as ⟨pr, hpr1, hpr2⟩
          obtain ⟨i4, imb⟩ := pr
          dsimp only at hpr1 hpr2 ⊢
          step as ⟨i5, hi5⟩
          step as ⟨common2, hcm2⟩
          step as ⟨i6, hi6⟩
          have hset : (imb i5).val = o.val.set l.val i5 := by
            rw [hpr2, alloc.vec.Vec.set_val_eq]
          have hi4v : i4.val = i3.val := by
            rw [hpr1, hi3]
          have hCl' : C.count l.val < A.count l.val := by omega
          have hi6' : i6.val = c.val + 1 := by omega
          refine ⟨by omega, by omega, ?_, ⟨l.val :: C, ?_, ?_, ?_⟩, by omega⟩
          · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
          · intro x
            rw [hi6', hso x, List.count_cons, hC x]
            have hCx := hC l.val
            by_cases hxl : l.val = x
            · subst hxl; simp; omega
            · simp [hxl]
          · simp [hCl]; omega
          · intro x hx
            rw [hset]
            by_cases hxl : x = l.val
            · subst hxl
              rw [getU_set_eq _ _ _ hlo]
              simp [List.count_cons]; omega
            · rw [getU_set_ne _ _ _ _ hxl, hCc x hx]
              simp [List.count_cons, Ne.symm hxl]
        · rename_i hz
          have hz' : i3.val = 0 := by have : ¬ 0 < i3.val := hz; omega
          step as ⟨i6, hi6⟩
          have hi6' : i6.val = c.val + 1 := by omega
          refine ⟨by omega, by omega, hl, ⟨C, ?_, hCl, hCc⟩, by omega⟩
          · intro x
            rw [hi6', hso x, hC x]
            by_cases hxl : l.val = x
            · subst hxl
              have := hC l.val
              omega
            · simp [hxl]
      · rename_i hlt'
        have hge : top.val ≤ l.val := by have : ¬ l.val < top.val := hlt'; omega
        have hA0 : A.count l.val = 0 := List.count_eq_zero.mpr (fun h => by have := hAtop _ h; omega)
        step as ⟨i6, hi6⟩
        have hi6' : i6.val = c.val + 1 := by omega
        refine ⟨by omega, by omega, hl, ⟨C, ?_, hCl, hCc⟩, by omega⟩
        intro x
        rw [hi6', hso x, hC x]
        by_cases hxl : l.val = x
        · subst hxl; omega
        · simp [hxl]
    · rename_i hci
      have hc2 : b.label.length ≤ c.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨trivial, C, ?_, hCl⟩
      intro x
      rw [hC x]
      have : c.val = b.label.length := by omega
      rw [this]
      congr 3
      simp [List.take_of_length_le]
  · exact ⟨hi, hcom, hcnt, hinv⟩


/-- `label_lower_bound` returns `max(n, m)` minus the size of the label multiset overlap. Hypotheses: fewer
than `2^31` nodes, and labels of `a` below `2^31` (the count table is indexed by label). -/
theorem label_lower_bound_spec (a b : ted.PostTree)
    (ha : a.label.length < 2 ^ 31) (hb : b.label.length < 2 ^ 31)
    (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31) :
    ted.label_lower_bound a b ⦃ r =>
      r.val = max a.label.length b.label.length - overlap (vals a.label.val) (vals b.label.val) ⦄ := by
  unfold ted.label_lower_bound
  obtain ⟨r0, he0, hr0, hr1, hr2⟩ : ∃ r0, ted.label_lower_bound_loop0 a 0#usize 0#usize = ok r0 ∧
      r0 = (a.label, a.lml, a.keyroots, a.kids, a.kind, r0.2.2.2.2.2) ∧ r0.2.2.2.2.2.val ≤ 2 ^ 31 ∧
      ∀ j < a.label.length, (a.label.val[j]!).val < r0.2.2.2.2.2.val := by
    obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists
      (llb_top_loop_spec a 0#usize 0#usize hla (by simp) (by simp) (by simp))
    exact ⟨r, hr, hh⟩
  obtain ⟨v, v1, v2, v3, v4, top⟩ := r0
  simp only [Prod.mk.injEq] at hr0
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := hr0
  subst e1 e2 e3 e4 e5
  dsimp only at hr1 hr2
  rw [he0]
  simp only [bind_tc_ok]
  have hlenA := alloc.vec.Vec.len_val a.label
  have hlenB := alloc.vec.Vec.len_val b.label
  step as ⟨cnt, hcnt, hcntl⟩
  have hcnt0 : ∀ x < top.val, (cnt.val[x]!).val = (vals (a.label.val.take 0)).count x := by
    intro x hx
    rw [hcnt]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, hx, vals]
  obtain ⟨cnt1, he1, hc1l, hc1⟩ : ∃ cnt1, ted.label_lower_bound_loop1 a.label 0#usize cnt = ok cnt1 ∧
      cnt1.length = top.val ∧ ∀ x < top.val, (cnt1.val[x]!).val = (vals a.label.val).count x := by
    obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists
      (llb_count_loop_spec a.label cnt 0#usize top.val hr2 ha hcntl (by simp) hcnt0)
    exact ⟨r, hr, hh⟩
  rw [he1]
  simp only [bind_tc_ok]
  obtain ⟨r2, he2, hr2e, C, hC, hCl⟩ : ∃ r2, ted.label_lower_bound_loop2 b top 0#usize cnt1 0#u32 = ok r2 ∧
      r2 = (b.label, b.lml, b.keyroots, b.kids, b.kind, r2.2.2.2.2.2) ∧
      ∃ C : List Nat, (∀ x, C.count x = min ((vals a.label.val).count x) ((vals b.label.val).count x)) ∧
        C.length = r2.2.2.2.2.2.val := by
    have hAtop : ∀ x ∈ vals a.label.val, x < top.val := by
      intro x hx
      simp only [vals, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
      have := hr2 j hj
      rwa [getU_eq _ _ hj] at this
    obtain ⟨r, hr, hh, C, hC, hCl⟩ := WP.spec_imp_exists
      (llb_consume_loop_spec b top 0#usize cnt1 0#u32 (vals a.label.val) hAtop hc1l hb (by simp) (by simp)
        ⟨[], by intro x; simp [vals], by simp, by intro x hx; rw [hc1 x hx]; simp⟩)
    exact ⟨r, hr, hh, C, hC, hCl⟩
  obtain ⟨v5, v6, v7, v8, v9, common⟩ := r2
  simp only [Prod.mk.injEq] at hr2e
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := hr2e
  subst f1 f2 f3 f4 f5
  rw [he2]
  simp only [bind_tc_ok, ted.PostTree.len]
  step as ⟨i2, hi2⟩
  have hc3 : (UScalar.cast .U32 i2).val = max a.label.length b.label.length := by
    rw [UScalar.cast_val_eq]
    simp only [UScalarTy.numBits]
    rw [hi2, hlenA, hlenB, Nat.mod_eq_of_lt (by omega)]
  have hcv : common.val = overlap (vals a.label.val) (vals b.label.val) := by
    rw [← hCl]; exact (length_of_counts hC)
  have hle : overlap (vals a.label.val) (vals b.label.val) ≤ max a.label.length b.label.length := by
    have := overlap_le_left (vals a.label.val) (vals b.label.val)
    rw [vals_length] at this
    exact Nat.le_trans this (Nat.le_max_left _ _)
  have hsub : common.val ≤ (UScalar.cast .U32 i2).val := by omega
  step as ⟨r, hr⟩
  subst hr
  step as ⟨s, hs⟩
  rw [hs, hc3, hcv]


end difffold_lines_extract
