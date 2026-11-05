import Check
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! `replay_core` accepts exactly the legal tree edit mappings and returns their cost. -/

def NotOps (v : ted.Replay) : Prop := ∀ c, v ≠ ted.Replay.Ops c

theorem replay_loop0_spec (pairs : Slice (Std.U32 × Std.U32)) (n m : Std.Usize) (nn mm : Nat)
    (hn : n.val = nn) (hm : m.val = mm) :
    ∀ (to_b to_a : alloc.vec.Vec Std.Usize) (verdict : ted.Replay) (i : Std.Usize),
    i.val ≤ pairs.val.length →
    Rng nn mm ((Mp pairs.val).take i.val) → IInj ((Mp pairs.val).take i.val) →
    TbO nn to_b.val ((Mp pairs.val).take i.val) →
    TbO mm to_a.val (((Mp pairs.val).take i.val).map Prod.swap) →
    ted.replay_core_loop0 pairs n m to_b to_a verdict true i ⦃ r =>
      (r.2.2.2 = true → Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val) ∧ TbO nn r.1.val (Mp pairs.val) ∧
        TbO mm r.2.1.val ((Mp pairs.val).map Prod.swap)) ∧
      (r.2.2.2 = false → NotOps r.2.2.1 ∧ ¬ (Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val))) ⦄ := by
  intro to_b to_a verdict i hi hR hI hB hA
  unfold ted.replay_core_loop0
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.2.2.1 = true then pairs.val.length - s.2.2.2.2.val + 1 else 0)
    (inv := fun s => s.2.2.2.2.val ≤ pairs.val.length ∧
      (s.2.2.2.1 = true → Rng nn mm ((Mp pairs.val).take s.2.2.2.2.val) ∧ IInj ((Mp pairs.val).take s.2.2.2.2.val) ∧
        TbO nn s.1.val ((Mp pairs.val).take s.2.2.2.2.val) ∧
        TbO mm s.2.1.val (((Mp pairs.val).take s.2.2.2.2.val).map Prod.swap)) ∧
      (s.2.2.2.1 = false → NotOps s.2.2.1 ∧ ¬ (Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val))))
  · intro s hs
    obtain ⟨to_b1, to_a1, verdict1, ok1, idx⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.replay_core_loop0.body
    cases ok1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, WP.spec_ok]
      exact ⟨fun h => h.elim, fun _ => hs3 rfl⟩
    | true =>
      obtain ⟨hR1, hI1, hB1, hA1⟩ := hs2 rfl
      simp only [if_true]
      have hlen : (Mp pairs.val).length = pairs.val.length := by simp [Mp]
      by_cases hlt : idx < Slice.len pairs
      · rw [if_pos hlt]
        have hlt' : idx.val < pairs.val.length := by
          have : idx.val < (Slice.len pairs).val := hlt
          simpa using this
        obtain ⟨pr, hpr, hpr2⟩ := WP.spec_imp_exists (Slice.index_usize_spec pairs idx hlt')
        rw [hpr]
        simp only [bind_tc_ok]
        obtain ⟨a2, a3⟩ := pr
        simp only [lift, bind_tc_ok]
        show (if UScalar.cast UScalarTy.Usize a2 = 0#usize then _ else _) ⦃ _ ⦄
        have hxv : (UScalar.cast UScalarTy.Usize a2).val = a2.val := U32.cast_Usize_val_eq a2
        have hyv : (UScalar.cast UScalarTy.Usize a3).val = a3.val := U32.cast_Usize_val_eq a3
        generalize UScalar.cast UScalarTy.Usize a2 = x at hxv ⊢
        generalize UScalar.cast UScalarTy.Usize a3 = y at hyv ⊢
        have hlenM : (Mp pairs.val).length = pairs.val.length := by simp [Mp]
        have hc := Mp_getN pairs.val idx.val hlt'
        have hc1 : ((Mp pairs.val)[idx.val]!).1 = x.val := by rw [hc.1, ← hpr2]; simp [hxv]
        have hc2 : ((Mp pairs.val)[idx.val]!).2 = y.val := by rw [hc.2, ← hpr2]; simp [hyv]
        have hmem : (Mp pairs.val)[idx.val]! ∈ Mp pairs.val := by
          rw [getG_eq _ _ (by omega)]; exact List.getElem_mem _
        have htl : ((Mp pairs.val).take idx.val).length = idx.val := by simp; omega
        have hRfail : (x.val = 0 ∨ x.val > nn ∨ y.val = 0 ∨ y.val > mm) → ¬ (Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val)) := by
          rintro h ⟨hRng, _⟩
          have := hRng _ hmem
          rw [hc1, hc2] at this
          omega
        have hI2 : ∀ j < idx.val, ((Mp pairs.val)[j]!) = ((Mp pairs.val).take idx.val)[j]! := fun j hj =>
          (getN_take _ _ _ hj).symm
        by_cases c1 : x = 0#usize
        · rw [if_pos c1]
          simp only [WP.spec_ok]
          refine ⟨⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), hRfail (Or.inl ?_)⟩⟩, by simp⟩
          rw [c1]; rfl
        rw [if_neg c1]
        by_cases c2 : x > n
        · rw [if_pos c2]
          simp only [WP.spec_ok]
          refine ⟨⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), hRfail (Or.inr (Or.inl ?_))⟩⟩, by simp⟩
          have : x.val > n.val := c2
          omega
        rw [if_neg c2]
        by_cases c3 : y = 0#usize
        · rw [if_pos c3]
          simp only [WP.spec_ok]
          refine ⟨⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), hRfail (Or.inr (Or.inr (Or.inl ?_)))⟩⟩, by simp⟩
          rw [c3]; rfl
        rw [if_neg c3]
        by_cases c4 : y > m
        · rw [if_pos c4]
          simp only [WP.spec_ok]
          refine ⟨⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), hRfail (Or.inr (Or.inr (Or.inr ?_)))⟩⟩, by simp⟩
          have : y.val > m.val := c4
          omega
        rw [if_neg c4]
        have hx1 : 1 ≤ x.val := by
          have : x ≠ 0#usize := c1
          have h0 : x.val ≠ 0 := fun h => this (UScalar.eq_of_val_eq (by simpa using h))
          omega
        have hxn : x.val ≤ nn := by have : ¬ x.val > n.val := c2; omega
        have hy1 : 1 ≤ y.val := by
          have : y ≠ 0#usize := c3
          have h0 : y.val ≠ 0 := fun h => this (UScalar.eq_of_val_eq (by simpa using h))
          omega
        have hym : y.val ≤ mm := by have : ¬ y.val > m.val := c4; omega
        have hbl : to_b1.length = nn + 1 := hB1.1
        have hal : to_a1.length = mm + 1 := hA1.1
        have hbl' : to_b1.val.length = nn + 1 := hB1.1
        have hal' : to_a1.val.length = mm + 1 := hA1.1
        step as ⟨i4, hi4⟩
        have hi4' : i4.val = (to_b1.val[x.val]!).val := by rw [hi4, getG_eq _ _ (by omega)]
        by_cases c5 : i4 != 0#usize
        · rw [if_pos c5]
          simp only [WP.spec_ok]
          refine ⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), ?_⟩, by simp⟩
          have hne : i4.val ≠ 0 := by
            intro h0; apply (by simpa using c5 : i4 ≠ 0#usize)
            exact UScalar.eq_of_val_eq (by simpa using h0)
          rintro ⟨_, hInj⟩
          have hex : ∃ j < idx.val, ((Mp pairs.val)[j]!).1 = x.val := by
            refine Classical.byContradiction fun hno => ?_
            apply hne
            rw [hi4']
            apply hB1.2.2 x.val hxn
            intro j hj
            rw [htl] at hj
            rw [getN_take _ _ _ hj]
            intro heq; exact hno ⟨j, hj, heq⟩
          obtain ⟨j, hj, hjx⟩ := hex
          have := (hInj j idx.val (by omega) (by omega) (by omega)).1
          rw [hjx, hc1] at this; exact this rfl
        rw [if_neg c5]
        have hi4z : i4.val = 0 := by simpa using c5
        step as ⟨i5, hi5⟩
        have hi5' : i5.val = (to_a1.val[y.val]!).val := by rw [hi5, getG_eq _ _ (by omega)]
        by_cases c6 : i5 != 0#usize
        · rw [if_pos c6]
          simp only [WP.spec_ok]
          refine ⟨hs1, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), ?_⟩, by simp⟩
          have hne : i5.val ≠ 0 := by
            intro h0; apply (by simpa using c6 : i5 ≠ 0#usize)
            exact UScalar.eq_of_val_eq (by simpa using h0)
          rintro ⟨_, hInj⟩
          have hex : ∃ j < idx.val, ((Mp pairs.val)[j]!).2 = y.val := by
            refine Classical.byContradiction fun hno => ?_
            apply hne
            rw [hi5']
            apply hA1.2.2 y.val hym
            intro j hj
            have hj' : j < idx.val := by rw [List.length_map, htl] at hj; exact hj
            rw [getN_swap _ _ (by omega), getN_take _ _ _ hj']
            intro heq; exact hno ⟨j, hj', heq⟩
          obtain ⟨j, hj, hjx⟩ := hex
          have := (hInj j idx.val (by omega) (by omega) (by omega)).2
          rw [hjx, hc2] at this; exact this rfl
        rw [if_neg c6]
        have hi5z : i5.val = 0 := by simpa using c6
        step as ⟨old, imb, ho, himb⟩
        step as ⟨old1, imb1, ho1, himb1⟩
        step as ⟨i6, hi6⟩
        have hsetb : (imb y).val = to_b1.val.set x.val y := by rw [himb, alloc.vec.Vec.set_val_eq]
        have hseta : (imb1 x).val = to_a1.val.set y.val x := by rw [himb1, alloc.vec.Vec.set_val_eq]
        have hq : (Mp pairs.val)[idx.val]! = (x.val, y.val) := Prod.ext hc1 hc2
        have hPm : ∀ j < idx.val, ((Mp pairs.val).take idx.val)[j]! ∈ (Mp pairs.val).take idx.val := fun j hj => by
          rw [getG_eq _ _ (by omega)]; exact List.getElem_mem _
        have hnewB : ∀ j < ((Mp pairs.val).take idx.val).length, (((Mp pairs.val).take idx.val)[j]!).1 ≠ x.val := by
          intro j hj heq
          rw [htl] at hj
          have h1 := hB1.2.1 j (by rw [htl]; exact hj)
          rw [heq, ← hi4'] at h1
          have := hR1 _ (hPm j hj)
          omega
        have hnewA : ∀ j < (((Mp pairs.val).take idx.val).map Prod.swap).length,
            ((((Mp pairs.val).take idx.val).map Prod.swap)[j]!).1 ≠ y.val := by
          intro j hj heq
          rw [List.length_map, htl] at hj
          have h1 := hA1.2.1 j (by rw [List.length_map, htl]; exact hj)
          rw [getN_swap _ _ (by rw [htl]; exact hj)] at h1 heq
          simp only [Prod.fst_swap, Prod.snd_swap] at h1 heq
          rw [heq, ← hi5'] at h1
          have := hR1 _ (hPm j hj)
          omega
        refine ⟨by omega, fun _ => ?_, fun h => by simp at h, by simp; omega⟩
        rw [hi6, take_succ_eq _ _ (by omega), hq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hR1 p hp
          · have : p = (x.val, y.val) := by simpa using hp
            rw [this]; exact ⟨hx1, hxn, hy1, hym⟩
        · apply iinj_snoc _ _ hI1
          · exact hnewB
          · intro j hj heq
            have h1 := hnewA j (by simpa using hj)
            rw [getN_swap _ _ (by simpa using hj)] at h1
            exact h1 heq
        · rw [hsetb]
          have := TbO_snoc nn to_b1.val _ x.val y hB1 hxn hnewB
          exact this
        · rw [hseta]
          have := TbO_snoc mm to_a1.val _ y.val x hA1 hym hnewA
          simpa using this
      · rw [if_neg hlt]
        simp only [WP.spec_ok]
        have hlt' : idx.val = pairs.val.length := by
          have : ¬ idx.val < (Slice.len pairs).val := hlt
          simp at this; omega
        have hall : (Mp pairs.val).take idx.val = Mp pairs.val := by
          rw [hlt']; simp [Mp]
        rw [hall] at hR1 hI1 hB1
        rw [hall] at hA1
        exact ⟨fun _ => ⟨hR1, hI1, hB1, hA1⟩, fun h => by simp at h⟩
  · refine ⟨hi, fun _ => ⟨hR, hI, hB, hA⟩, fun h => by simp at h⟩


/-! Counting the mapped nodes. -/

def CA (M : List (Nat × Nat)) (x : Nat) : Nat := M.countP (fun p => decide (p.1 ≤ x))

theorem countP_sum {α : Type} (P : α → Bool) (l : List α) : l.countP P = (l.map (fun a => if P a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a r ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; split <;> omega

theorem ca_zero {nn mm : Nat} {M : List (Nat × Nat)} (hR : Rng nn mm M) : CA M 0 = 0 := by
  unfold CA
  rw [List.countP_eq_zero]
  intro p hp
  have := (hR p hp).1
  simp; omega

theorem ca_succ {nn mm : Nat} {tb : List Std.Usize} {M : List (Nat × Nat)} (hR : Rng nn mm M) (hI : IInj M)
    (hT : TbO nn tb M) {x : Nat} (hx1 : 1 ≤ x) (hxn : x ≤ nn) :
    CA M x = CA M (x - 1) + (if (tb[x]!).val = 0 then 0 else 1) := by
  unfold CA
  rw [countP_sum, countP_sum]
  have hsplit : (M.map (fun p => if decide (p.1 ≤ x) = true then 1 else 0)).sum =
      (M.map (fun p => if decide (p.1 ≤ x - 1) = true then 1 else 0)).sum +
      (M.map (fun p => if p.1 = x then (fun _ : Nat × Nat => 1) p else 0)).sum := by
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p hp
    by_cases h1 : p.1 ≤ x - 1
    · simp [h1, show p.1 ≤ x by omega, show p.1 ≠ x by omega]
    · by_cases h2 : p.1 = x
      · simp [h2, show ¬ x ≤ x - 1 by omega]
      · simp [h1, show ¬ p.1 ≤ x by omega, h2]
  rw [hsplit]
  congr 1
  by_cases h0 : (tb[x]!).val = 0
  · rw [if_pos h0]
    apply sum_ite_zero
    intro p hp heq
    have := tb_val hT hp
    rw [heq, h0] at this
    have := hR p hp
    omega
  · rw [if_neg h0]
    obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hxn h0
    exact sum_ite_unique M (iinj_nodup hI) (fun _ => 1) x pq hpq
      (fun p hp hpx => iinj_fst hI hp hpq (by omega)) hpq1

theorem replay_loop1_spec (n : Std.Usize) (nn mm : Nat) (hn : n.val = nn) (to_b : alloc.vec.Vec Std.Usize)
    (M : List (Nat × Nat)) (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M) :
    ∀ (cnt : alloc.vec.Vec Std.Usize) (x : Std.Usize), 1 ≤ x.val → x.val ≤ nn + 1 → cnt.length = nn + 1 →
    (∀ x', x' < x.val → (cnt.val[x']!).val = CA M x') →
    ted.replay_core_loop1 n to_b cnt x ⦃ r => r.length = nn + 1 ∧ ∀ x', x' ≤ nn → (r.val[x']!).val = CA M x' ⦄ := by
  intro cnt x hx1 hx2 hcl hc
  unfold ted.replay_core_loop1
  apply loop.spec_decr_nat
    (measure := fun s => nn + 1 - s.2.val)
    (inv := fun s => 1 ≤ s.2.val ∧ s.2.val ≤ nn + 1 ∧ s.1.length = nn + 1 ∧
      ∀ x', x' < s.2.val → (s.1.val[x']!).val = CA M x')
  · intro s hs
    obtain ⟨cnt1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.replay_core_loop1.body
    by_cases hle : x1 <= n
    · rw [if_pos hle]
      have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
      have hcl' : cnt1.val.length = nn + 1 := hs3
      have hbl : to_b.val.length = nn + 1 := hT.1
      have hbl' : to_b.length = nn + 1 := hT.1
      step as ⟨i, hi⟩
      step as ⟨c, hc'⟩
      have hc'' : c.val = CA M (x1.val - 1) := by
        rw [hc', ← hs4 (x1.val - 1) (by omega), getG_eq _ _ (by omega : x1.val - 1 < cnt1.val.length)]
        congr 2 <;> omega
      have hcle : CA M (x1.val - 1) ≤ nn := le_trans List.countP_le_length (mlen_le hR hI)
      have hcb : c.val + 1 ≤ Std.Usize.max := by scalar_tac
      step as ⟨i1, hi1⟩
      have hi1' : i1.val = (to_b.val[x1.val]!).val := by rw [hi1, getG_eq _ _ (by omega)]
      have hca := ca_succ hR hI hT hs1 hle'
      by_cases c1 : i1 != 0#usize
      · have hi0 : i1.val ≠ 0 := by
          intro h0; apply (by simpa using c1 : i1 ≠ 0#usize)
          exact UScalar.eq_of_val_eq (by simpa using h0)
        simp only [c1, if_true, bind_tc_ok]
        step as ⟨c1', hc1'⟩
        step as ⟨old, imb, ho, himb⟩
        step as ⟨x2, hx2'⟩
        have hset : (imb c1').val = cnt1.val.set x1.val c1' := by rw [himb, alloc.vec.Vec.set_val_eq]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs3
        · intro x' hx'
          rw [hset]
          by_cases hxx : x' = x1.val
          · subst hxx
            rw [getG_set_eq _ _ _ (by omega), hca, if_neg (by rw [← hi1']; exact hi0)]
            omega
          · rw [getG_set_ne _ _ _ _ hxx]
            exact hs4 x' (by omega)
      · have hi0 : i1.val = 0 := by simpa using c1
        have c1f : (i1 != 0#usize) = false := by
          have : i1 = 0#usize := UScalar.eq_of_val_eq (by simpa using hi0)
          rw [this]; rfl
        simp only [c1f, Bool.false_eq_true, if_false, bind_tc_ok]
        step as ⟨old, imb, ho, himb⟩
        step as ⟨x2, hx2'⟩
        have hset : (imb c).val = cnt1.val.set x1.val c := by rw [himb, alloc.vec.Vec.set_val_eq]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs3
        · intro x' hx'
          rw [hset]
          by_cases hxx : x' = x1.val
          · subst hxx
            rw [getG_set_eq _ _ _ (by omega), hca, if_pos (by rw [← hi1']; exact hi0)]
            omega
          · rw [getG_set_ne _ _ _ _ hxx]
            exact hs4 x' (by omega)
    · rw [if_neg hle]
      simp only [WP.spec_ok]
      have : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
      refine ⟨hs3, fun x' hx' => hs4 x' (by omega)⟩
  · exact ⟨hx1, hx2, hcl, hc⟩

theorem replay_loop2_spec (n : Std.Usize) (nn mm : Nat) (hn : n.val = nn) (to_b : alloc.vec.Vec Std.Usize)
    (M : List (Nat × Nat)) (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M) :
    ∀ (cnt : alloc.vec.Vec Std.Usize) (x : Std.Usize), 1 ≤ x.val → x.val ≤ nn + 1 → cnt.length = nn + 1 →
    (∀ x', x' < x.val → (cnt.val[x']!).val = CA M x') →
    ted.replay_core_loop2 n to_b cnt x ⦃ r => r.length = nn + 1 ∧ ∀ x', x' ≤ nn → (r.val[x']!).val = CA M x' ⦄ := by
  intro cnt x hx1 hx2 hcl hc
  unfold ted.replay_core_loop2
  apply loop.spec_decr_nat
    (measure := fun s => nn + 1 - s.2.val)
    (inv := fun s => 1 ≤ s.2.val ∧ s.2.val ≤ nn + 1 ∧ s.1.length = nn + 1 ∧
      ∀ x', x' < s.2.val → (s.1.val[x']!).val = CA M x')
  · intro s hs
    obtain ⟨cnt1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.replay_core_loop2.body
    by_cases hle : x1 <= n
    · rw [if_pos hle]
      have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
      have hcl' : cnt1.val.length = nn + 1 := hs3
      have hbl : to_b.val.length = nn + 1 := hT.1
      have hbl' : to_b.length = nn + 1 := hT.1
      step as ⟨i, hi⟩
      step as ⟨c, hc'⟩
      have hc'' : c.val = CA M (x1.val - 1) := by
        rw [hc', ← hs4 (x1.val - 1) (by omega), getG_eq _ _ (by omega : x1.val - 1 < cnt1.val.length)]
        congr 2 <;> omega
      have hcle : CA M (x1.val - 1) ≤ nn := le_trans List.countP_le_length (mlen_le hR hI)
      have hcb : c.val + 1 ≤ Std.Usize.max := by scalar_tac
      step as ⟨i1, hi1⟩
      have hi1' : i1.val = (to_b.val[x1.val]!).val := by rw [hi1, getG_eq _ _ (by omega)]
      have hca := ca_succ hR hI hT hs1 hle'
      by_cases c1 : i1 != 0#usize
      · have hi0 : i1.val ≠ 0 := by
          intro h0; apply (by simpa using c1 : i1 ≠ 0#usize)
          exact UScalar.eq_of_val_eq (by simpa using h0)
        simp only [c1, if_true, bind_tc_ok]
        step as ⟨c1', hc1'⟩
        step as ⟨old, imb, ho, himb⟩
        step as ⟨x2, hx2'⟩
        have hset : (imb c1').val = cnt1.val.set x1.val c1' := by rw [himb, alloc.vec.Vec.set_val_eq]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs3
        · intro x' hx'
          rw [hset]
          by_cases hxx : x' = x1.val
          · subst hxx
            rw [getG_set_eq _ _ _ (by omega), hca, if_neg (by rw [← hi1']; exact hi0)]
            omega
          · rw [getG_set_ne _ _ _ _ hxx]
            exact hs4 x' (by omega)
      · have hi0 : i1.val = 0 := by simpa using c1
        have c1f : (i1 != 0#usize) = false := by
          have : i1 = 0#usize := UScalar.eq_of_val_eq (by simpa using hi0)
          rw [this]; rfl
        simp only [c1f, Bool.false_eq_true, if_false, bind_tc_ok]
        step as ⟨old, imb, ho, himb⟩
        step as ⟨x2, hx2'⟩
        have hset : (imb c).val = cnt1.val.set x1.val c := by rw [himb, alloc.vec.Vec.set_val_eq]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs3
        · intro x' hx'
          rw [hset]
          by_cases hxx : x' = x1.val
          · subst hxx
            rw [getG_set_eq _ _ _ (by omega), hca, if_pos (by rw [← hi1']; exact hi0)]
            omega
          · rw [getG_set_ne _ _ _ _ hxx]
            exact hs4 x' (by omega)
    · rw [if_neg hle]
      simp only [WP.spec_ok]
      have : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
      refine ⟨hs3, fun x' hx' => hs4 x' (by omega)⟩
  · exact ⟨hx1, hx2, hcl, hc⟩

/-! Legal mappings in terms of subtree sizes. -/

theorem countP_split {α : Type} (l : List α) (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (h : ∀ a ∈ l, R a ↔ (P a ∨ Q a)) (hd : ∀ a ∈ l, ¬ (P a ∧ Q a)) :
    l.countP (fun a => decide (R a)) = l.countP (fun a => decide (P a)) + l.countP (fun a => decide (Q a)) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) (fun b hb => hd b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    have hda := hd a (List.mem_cons_self ..)
    by_cases hP : P a
    · have : ¬ Q a := fun hq => hda ⟨hP, hq⟩
      simp [hP, this, ha.mpr (Or.inl hP)]; omega
    · by_cases hQ : Q a
      · simp [hP, hQ, ha.mpr (Or.inr hQ)]; omega
      · have : ¬ R a := fun hr => by rcases ha.mp hr with h | h <;> contradiction
        simp [hP, hQ, this]; omega

def SizeOk (la lb : Nat → Nat) (M : List (Nat × Nat)) : Prop :=
  ∀ p ∈ M, M.countP (fun q => decide (la p.1 ≤ q.1 ∧ q.1 ≤ p.1)) =
    M.countP (fun q => decide (lb p.2 ≤ q.2 ∧ q.2 ≤ p.2))

theorem valid_to_size {la lb : Nat → Nat} {nn mm : Nat} {M : List (Nat × Nat)} (hA : WfL la) (hB : WfL lb)
    (hR : Rng nn mm M) (hv : Valid la lb M) : SizeOk la lb M := by
  intro p hp
  apply List.countP_congr
  intro q hq
  simp only [decide_eq_true_eq]
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hR p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hR q hq
  obtain ⟨e, o, a⟩ := hv.2 q hq p hp
  have hlp := (hA.1 p.1 hp1).2
  have hlp' := (hB.1 p.2 hp3).2
  rcases Nat.lt_trichotomy q.1 p.1 with h | h | h
  · have h2 := o.mp h
    have ha := a
    simp only [Anc] at ha
    constructor
    · rintro ⟨h1, _⟩; exact ⟨(ha.mp ⟨h, h1⟩).2, by omega⟩
    · rintro ⟨h1, _⟩; exact ⟨(ha.mpr ⟨h2, h1⟩).2, by omega⟩
  · have h2 := e.mp h
    constructor
    · intro _; omega
    · intro _; omega
  · have h2 : p.2 < q.2 := ((hv.2 p hp q hq).2.1).mp h
    constructor
    · rintro ⟨_, h1⟩; omega
    · rintro ⟨_, h1⟩; omega

theorem block_mem_iff (f : Nat × Nat → Nat) (l : Nat → Nat) (M : List (Nat × Nat)) (p q : Nat × Nat)
    (hl : l (f q) ≤ f q) (hpq : f p ≤ f q) (hp : p ∈ M) :
    l (f q) ≤ f p ↔ M.countP (fun s => decide (f p ≤ f s ∧ f s ≤ f q)) ≤
      M.countP (fun s => decide (l (f q) ≤ f s ∧ f s ≤ f q)) := by
  constructor
  · intro h
    apply List.countP_mono_left
    intro s _ hs
    simp only [decide_eq_true_eq] at hs ⊢
    omega
  · intro h
    refine Classical.byContradiction fun hlt => ?_
    have hlt' : f p < l (f q) := by omega
    have hsplit : M.countP (fun s => decide (f p ≤ f s ∧ f s ≤ f q)) =
        M.countP (fun s => decide (l (f q) ≤ f s ∧ f s ≤ f q)) +
        M.countP (fun s => decide (f p ≤ f s ∧ f s < l (f q))) :=
      countP_split M (fun s => l (f q) ≤ f s ∧ f s ≤ f q) (fun s => f p ≤ f s ∧ f s < l (f q))
        (fun s => f p ≤ f s ∧ f s ≤ f q)
        (fun s _ => by constructor <;> intro h' <;> omega)
        (fun s _ => by intro h'; omega)
    have hpos : 0 < M.countP (fun s => decide (f p ≤ f s ∧ f s < l (f q))) := by
      rw [List.countP_pos_iff]
      exact ⟨p, hp, by simp; omega⟩
    omega

theorem size_to_valid {la lb : Nat → Nat} {nn mm : Nat} {M : List (Nat × Nat)} (hA : WfL la) (hB : WfL lb)
    (hR : Rng nn mm M) (hI : IInj M) (hPo : PostOrd M) (hS : SizeOk la lb M) : Valid la lb M := by
  refine ⟨iinj_nodup hI, fun p hp q hq => ?_⟩
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hR p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hR q hq
  have e1 : p.1 = q.1 ↔ p.2 = q.2 :=
    ⟨fun e => by have := iinj_fst hI hp hq e; rw [this], fun e => by have := iinj_snd hI hp hq e; rw [this]⟩
  have e2 : p.1 < q.1 ↔ p.2 < q.2 := by
    refine ⟨hPo p hp q hq, fun h => ?_⟩
    rcases Nat.lt_trichotomy p.1 q.1 with h' | h' | h'
    · exact h'
    · have := e1.mp h'; omega
    · have := hPo q hq p hp h'; omega
  have hlq := (hA.1 q.1 hq1).2
  have hlq' := (hB.1 q.2 hq3).2
  -- the equivalence of the orders on the elements of `M`
  have hord : ∀ s ∈ M, (p.1 ≤ s.1 ↔ p.2 ≤ s.2) ∧ (s.1 ≤ q.1 ↔ s.2 ≤ q.2) := by
    intro s hs
    have key : ∀ u ∈ M, ∀ v ∈ M, (u.1 ≤ v.1 ↔ u.2 ≤ v.2) := by
      intro u hu v hv
      rcases Nat.lt_trichotomy u.1 v.1 with h | h | h
      · have := hPo u hu v hv h; omega
      · have := (hI |> fun _ => (⟨fun e => by have := iinj_fst hI hu hv e; rw [this], fun e => by have := iinj_snd hI hu hv e; rw [this]⟩ : u.1 = v.1 ↔ u.2 = v.2)).mp h; omega
      · have := hPo v hv u hu h; omega
    exact ⟨key p hp s hs, key s hs q hq⟩
  have hCI : M.countP (fun s => decide (p.1 ≤ s.1 ∧ s.1 ≤ q.1)) = M.countP (fun s => decide (p.2 ≤ s.2 ∧ s.2 ≤ q.2)) := by
    apply List.countP_congr
    intro s hs
    simp only [decide_eq_true_eq]
    have := hord s hs
    omega
  have hSq := hS q hq
  refine ⟨e1, e2, ?_⟩
  simp only [Anc]
  rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
  · have h2 := e2.mp h
    have b1 := block_mem_iff Prod.fst la M p q hlq (by omega) hp
    have b2 := block_mem_iff Prod.snd lb M p q hlq' (by omega) hp
    constructor
    · rintro ⟨_, h3⟩
      exact ⟨h2, b2.mpr (by rw [← hCI, ← hSq]; exact b1.mp h3)⟩
    · rintro ⟨_, h3⟩
      exact ⟨h, b1.mpr (by rw [hCI, hSq]; exact b2.mp h3)⟩
  · constructor <;> intro hh <;> omega
  · have h2 : q.2 < p.2 := by
      have := hPo q hq p hp h; exact this
    constructor <;> intro hh <;> omega

theorem postup_unmapped {M : List (Nat × Nat)} {x prev : Nat} (hU : PostUp M x prev) (hnone : ∀ p ∈ M, p.1 ≠ x) :
    PostUp M (x + 1) prev := by
  refine ⟨fun p hp q hq h1 h2 => ?_, fun p hp h1 => ?_, fun hne => ?_⟩
  · have : q.1 < x := by have := hnone q hq; omega
    exact hU.1 p hp q hq h1 this
  · have : p.1 < x := by have := hnone p hp; omega
    exact hU.2.1 p hp this
  · obtain ⟨p, hp, h1, h2⟩ := hU.2.2 hne
    exact ⟨p, hp, by omega, h2⟩

theorem postup_mapped {M : List (Nat × Nat)} (hI : IInj M) {x prev : Nat} (hU : PostUp M x prev) {pq : Nat × Nat}
    (hpq : pq ∈ M) (hx : pq.1 = x) (hy : prev < pq.2) : PostUp M (x + 1) pq.2 := by
  refine ⟨fun p hp q hq h1 h2 => ?_, fun p hp h1 => ?_, fun _ => ⟨pq, hpq, by omega, rfl⟩⟩
  · by_cases hq1 : q.1 < x
    · exact hU.1 p hp q hq h1 hq1
    · have hqq : q = pq := iinj_fst hI hq hpq (by omega)
      rw [hqq]
      have := hU.2.1 p hp (by omega)
      omega
  · by_cases hp1 : p.1 < x
    · have := hU.2.1 p hp hp1; omega
    · have hpp : p = pq := iinj_fst hI hp hpq (by omega)
      rw [hpp]

theorem postup_fail {M : List (Nat × Nat)} {x prev : Nat} (hU : PostUp M x prev) {pq : Nat × Nat}
    (hpq : pq ∈ M) (hx : pq.1 = x) (hy : pq.2 ≤ prev) (hy1 : 1 ≤ pq.2) : ¬ PostOrd M := by
  intro hPo
  obtain ⟨pp, hpp, hpp1, hpp2⟩ := hU.2.2 (by omega)
  have := hPo pp hpp pq hpq (by omega)
  omega

theorem ca_le {nn mm : Nat} {M : List (Nat × Nat)} (hR : Rng nn mm M) (hI : IInj M) (x : Nat) : CA M x ≤ x := by
  unfold CA
  rw [List.countP_eq_length_filter]
  have hnd : (M.filter (fun p => decide (p.1 ≤ x))).Nodup := (iinj_nodup hI).filter _
  have := len_le_of_inj Prod.fst (M.filter (fun p => decide (p.1 ≤ x))) 1 x hnd
    (fun p hp => by
      have hp' := List.mem_filter.mp hp
      have := hR p hp'.1
      have h2 : p.1 ≤ x := by simpa using hp'.2
      exact ⟨this.1, h2⟩)
    (fun p hp q hq e => iinj_fst hI (List.mem_filter.mp hp).1 (List.mem_filter.mp hq).1 e)
  omega

theorem ca_diff (M : List (Nat × Nat)) (l x : Nat) (hl : 1 ≤ l) (hlx : l ≤ x + 1) :
    CA M x = CA M (l - 1) + M.countP (fun q => decide (l ≤ q.1 ∧ q.1 ≤ x)) := by
  unfold CA
  exact countP_split M (fun q => q.1 ≤ l - 1) (fun q => l ≤ q.1 ∧ q.1 ≤ x) (fun q => q.1 ≤ x)
    (fun s _ => by constructor <;> intro h' <;> omega) (fun s _ => by intro h'; omega)

def CB (M : List (Nat × Nat)) (y : Nat) : Nat := M.countP (fun p => decide (p.2 ≤ y))

theorem ca_swap (M : List (Nat × Nat)) (y : Nat) : CA (M.map Prod.swap) y = CB M y := by
  unfold CA CB
  rw [List.countP_map]
  rfl

theorem cb_diff (M : List (Nat × Nat)) (l y : Nat) (hl : 1 ≤ l) (hly : l ≤ y + 1) :
    CB M y = CB M (l - 1) + M.countP (fun q => decide (l ≤ q.2 ∧ q.2 ≤ y)) := by
  unfold CB
  exact countP_split M (fun q => q.2 ≤ l - 1) (fun q => l ≤ q.2 ∧ q.2 ≤ y) (fun q => q.2 ≤ y)
    (fun s _ => by constructor <;> intro h' <;> omega) (fun s _ => by intro h'; omega)

theorem cb_mono (M : List (Nat × Nat)) {y y' : Nat} (h : y ≤ y') : CB M y ≤ CB M y' := by
  unfold CB
  apply List.countP_mono_left
  intro q _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  omega

theorem ca_mono (M : List (Nat × Nat)) {y y' : Nat} (h : y ≤ y') : CA M y ≤ CA M y' := by
  unfold CA
  apply List.countP_mono_left
  intro q _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  omega

def SizeAt (la lb : Nat → Nat) (M : List (Nat × Nat)) (p : Nat × Nat) : Prop :=
  M.countP (fun q => decide (la p.1 ≤ q.1 ∧ q.1 ≤ p.1)) = M.countP (fun q => decide (lb p.2 ≤ q.2 ∧ q.2 ≤ p.2))

theorem replay_loop3_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (n : Std.Usize) (nn mm : Nat)
    (hn : n.val = nn) (hnn : nn = a.label.length) (hmm : mm = b.label.length) (hna : nn < 2 ^ 14)
    (to_b cnt_a cnt_b : alloc.vec.Vec Std.Usize) (M : List (Nat × Nat))
    (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M)
    (hla : cnt_a.length = nn + 1) (hlb : cnt_b.length = mm + 1)
    (hCA : ∀ x', x' ≤ nn → (cnt_a.val[x']!).val = CA M x') (hCB : ∀ y', y' ≤ mm → (cnt_b.val[y']!).val = CB M y') :
    ∀ (verdict : ted.Replay) (x : Std.Usize) (ops : Std.U32) (prev : Std.Usize), 1 ≤ x.val → x.val ≤ nn + 1 →
    PostUp M x.val prev.val → (∀ p ∈ M, p.1 < x.val → SizeAt (laOf a) (laOf b) M p) →
    ops.val = (x.val - 1 - CA M (x.val - 1)) + RSum a b M x.val →
    ted.replay_core_loop3 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind n to_b
      verdict true cnt_a x cnt_b ops prev ⦃ r =>
      (r.2.1 = true → PostOrd M ∧ SizeOk (laOf a) (laOf b) M ∧ r.2.2.val = (nn - CA M nn) + RSum a b M (nn + 1)) ∧
      (r.2.1 = false → NotOps r.1 ∧ ¬ (PostOrd M ∧ SizeOk (laOf a) (laOf b) M)) ⦄ := by
  intro verdict x ops prev hx1 hx2 hU hSz hops
  unfold ted.replay_core_loop3
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.1 = true then nn + 1 - s.2.2.1.val + 1 else 0)
    (inv := fun s => 1 ≤ s.2.2.1.val ∧ s.2.2.1.val ≤ nn + 1 ∧
      (s.2.1 = true → PostUp M s.2.2.1.val s.2.2.2.2.val ∧ (∀ p ∈ M, p.1 < s.2.2.1.val → SizeAt (laOf a) (laOf b) M p) ∧
        s.2.2.2.1.val = (s.2.2.1.val - 1 - CA M (s.2.2.1.val - 1)) + RSum a b M s.2.2.1.val) ∧
      (s.2.1 = false → NotOps s.1 ∧ ¬ (PostOrd M ∧ SizeOk (laOf a) (laOf b) M)))
  · intro s hs
    obtain ⟨verdict1, ok1, x1, ops1, prev1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.replay_core_loop3.body
    cases ok1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, WP.spec_ok]
      exact ⟨fun h => h.elim, fun _ => hs4 rfl⟩
    | true =>
      obtain ⟨hU1, hSz1, hops1⟩ := hs3 rfl
      simp only [if_true]
      by_cases hle : x1 <= n
      · rw [if_pos hle]
        have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
        have hbl : to_b.val.length = nn + 1 := hT.1
        have hbl' : to_b.length = nn + 1 := hT.1
        have hlml : a.lml.length = a.label.length := hA.n2
        have hlmlb : b.lml.length = b.label.length := hB.n2
        have hcal : cnt_a.val.length = nn + 1 := hla
        have hcbl : cnt_b.val.length = mm + 1 := hlb
        step as ⟨y, hy⟩
        have hy' : y.val = (to_b.val[x1.val]!).val := by rw [hy, getG_eq _ _ (by omega)]
        have hca := ca_succ hR hI hT hs1 hle'
        have hrs := rsum_succ a b hR hI hT hle'
        have hcale := ca_le hR hI (x1.val - 1)
        have hcmM := mlen_le hR hI
        have hrsb := rsum_le a b M x1.val
        have hopsb : ops1.val + 1 ≤ Std.U32.max := by
          have hU : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max, UScalar.max, UScalarTy.numBits, Std.U32.numBits]
          rw [hU]; omega
        by_cases c0 : y = 0#usize
        · rw [if_pos c0]
          have hy0 : y.val = 0 := by rw [c0]; rfl
          have hnone : ∀ p ∈ M, p.1 ≠ x1.val := by
            intro p hp heq
            have := tb_val hT hp
            rw [heq, ← hy'] at this
            have := hR p hp
            omega
          step as ⟨ops2, hops2⟩
          step as ⟨x2, hx2'⟩
          refine ⟨by omega, by omega, fun _ => ⟨by rw [hx2']; exact postup_unmapped hU1 hnone, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
          · intro p hp h1
            rw [hx2'] at h1
            have := hnone p hp
            exact hSz1 p hp (by omega)
          · rw [hx2', hops2]
            rw [if_pos (by rw [← hy']; exact hy0)] at hca hrs
            have e : x1.val + 1 - 1 = x1.val := by omega
            rw [e, hca, hrs, hops1]
            omega
        · rw [if_neg c0]
          have hy0 : y.val ≠ 0 := fun h => c0 (UScalar.eq_of_val_eq (by simpa using h))
          obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hle' (by rw [← hy']; exact hy0)
          have hpqy : pq.2 = y.val := by rw [hpq2, hy']
          obtain ⟨_, _, hq3, hq4⟩ := hR pq hpq
          by_cases c1 : y <= prev1
          · rw [if_pos c1]
            simp only [WP.spec_ok]
            have hyp : y.val ≤ prev1.val := c1
            exact ⟨hs1, hs2, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h),
              fun ⟨hPo, _⟩ => postup_fail hU1 hpq hpq1 (by omega) hq3 hPo⟩, by simp⟩
          · rw [if_neg c1]
            have hyp : prev1.val < y.val := by have : ¬ y.val ≤ prev1.val := c1; omega
            have hyr : y.val ≤ mm := by rw [← hpqy]; exact hq4
            have hlx := hA.wfl.1 x1.val hs1
            have hly := hB.wfl.1 y.val (by omega)
            have hlxv : laOf a x1.val = (a.lml.val[x1.val - 1]!).val := laOf_eq1 a _ hs1 (by omega)
            have hlyv : laOf b y.val = (b.lml.val[y.val - 1]!).val := laOf_eq1 b _ (by omega) (by omega)
            have hlmlv : a.lml.val.length = a.label.length := hA.n2
            have hlmlbv : b.lml.val.length = b.label.length := hB.n2
            step as ⟨i, hi⟩
            step as ⟨i1, hi1⟩
            step as ⟨i2, hi2⟩
            step as ⟨i3, hi3⟩
            have hi3v : i3.val = laOf a x1.val := by
              rw [hi3, U32.cast_Usize_val_eq, hi2, hlxv, getG_eq _ _ (by omega)]
              congr 2
            step as ⟨i4, hi4⟩
            step as ⟨i5, hi5⟩
            have hiv : i.val = CA M x1.val := by
              rw [hi, ← hCA x1.val hle', getG_eq _ _ (by omega)]
            have hi5v : i5.val = CA M (laOf a x1.val - 1) := by
              rw [hi5, ← hCA (laOf a x1.val - 1) (by omega), getG_eq _ _ (by omega)]
              congr 2; omega
            have hle5 : i5.val ≤ i.val := by
              rw [hiv, hi5v]; exact ca_mono M (by omega)
            step as ⟨sa, hsa⟩
            have hsav : sa.val = M.countP (fun q => decide (laOf a x1.val ≤ q.1 ∧ q.1 ≤ x1.val)) := by
              have := ca_diff M (laOf a x1.val) x1.val hlx.1 (by omega)
              omega
            step as ⟨i6, hi6⟩
            step as ⟨i7, hi7⟩
            step as ⟨i8, hi8⟩
            step as ⟨i9, hi9⟩
            have hi9v : i9.val = laOf b y.val := by
              rw [hi9, U32.cast_Usize_val_eq, hi8, hlyv, getG_eq _ _ (by omega)]
              congr 2
            step as ⟨i10, hi10⟩
            step as ⟨i11, hi11⟩
            have hi6v : i6.val = CB M y.val := by
              rw [hi6, ← hCB y.val hyr, getG_eq _ _ (by omega)]
            have hi11v : i11.val = CB M (laOf b y.val - 1) := by
              rw [hi11, ← hCB (laOf b y.val - 1) (by omega), getG_eq _ _ (by omega)]
              congr 2; omega
            have hle11 : i11.val ≤ i6.val := by
              rw [hi6v, hi11v]; exact cb_mono M (by omega)
            step as ⟨sb, hsb⟩
            have hsbv : sb.val = M.countP (fun q => decide (laOf b y.val ≤ q.2 ∧ q.2 ≤ y.val)) := by
              have := cb_diff M (laOf b y.val) y.val hly.1 (by omega)
              omega
            by_cases c2 : sa != sb
            · rw [if_pos c2]
              simp only [WP.spec_ok]
              have hne : sa.val ≠ sb.val := by
                intro h0; apply (by simpa using c2 : sa ≠ sb)
                exact UScalar.eq_of_val_eq h0
              refine ⟨hs1, hs2, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), fun ⟨_, hSzAll⟩ => ?_⟩, by simp⟩
              have := hSzAll pq hpq
              unfold SizeAt at this
              rw [hpq1, hpqy] at this
              rw [hsav, hsbv] at hne
              exact hne this
            · rw [if_neg c2]
              have heq : sa.val = sb.val := by simpa using c2
              have hrc := relabel_cost_spec a b x1 y hs1 (by omega) (by rw [hnn] at hle'; omega)
                (by rw [hA.n3, ← hnn]; omega) (by omega) (by rw [hB.n3, ← hmm]; omega)
              obtain ⟨c, hcc, hcv⟩ := WP.spec_imp_exists hrc
              rw [hcc]
              simp only [bind_tc_ok]
              have hrcb : c.val ≤ 2 := by rw [hcv]; exact rcost_le a b _ _
              have hopsb2 : ops1.val + c.val ≤ Std.U32.max := by
                have hU : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max, UScalar.max, UScalarTy.numBits, Std.U32.numBits]
                rw [hU]; omega
              step as ⟨ops2, hops2⟩
              step as ⟨x2, hx2'⟩
              refine ⟨by omega, by omega, fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
              · rw [hx2']
                have := postup_mapped hI hU1 hpq hpq1 (by omega)
                rw [hpqy] at this
                exact this
              · intro p hp h1
                rw [hx2'] at h1
                by_cases hp1 : p.1 < x1.val
                · exact hSz1 p hp hp1
                · have hpp : p = pq := iinj_fst hI hp hpq (by omega)
                  rw [hpp]
                  unfold SizeAt
                  rw [hpq1, hpqy, ← hsav, ← hsbv]
                  exact heq
              · rw [hx2', hops2]
                have e : x1.val + 1 - 1 = x1.val := by omega
                rw [e]
                rw [if_neg (by rw [← hy']; exact hy0)] at hca hrs
                have hmap : (to_b.val[x1.val]!).val = y.val := hy'.symm
                rw [hmap] at hrs
                rw [hca, hrs, hops1, hcv]
                omega
      · rw [if_neg hle]
        simp only [WP.spec_ok]
        have hx : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
        refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h⟩
        · intro p hp q hq h1
          exact hU1.1 p hp q hq h1 (by have := hR q hq; omega)
        · intro p hp
          exact hSz1 p hp (by have := hR p hp; omega)
        · rw [hops1, hx]; simp
  · exact ⟨hx1, hx2, fun _ => ⟨hU, hSz, hops⟩, fun h => by simp at h⟩

end difffold_lines_extract
