import Mirror2
import Stats
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! `check_core` accepts exactly the legal tree edit mappings. -/

theorem preorder_loop_spec (a : ted.PostTree) (hW : PT.Wf a) (n : Std.Usize) (depth pre : alloc.vec.Vec Std.Usize)
    (x : Std.Usize) (hn : n.val = a.label.length) (hx : x.val ≤ a.label.length)
    (hdl : depth.length = a.label.length) (hpl : pre.length = a.label.length)
    (hD : ∀ c, 1 ≤ c → c ≤ a.label.length → (depth.val[c - 1]!).val = dep (laOf a) a.label.length c)
    (hP : ∀ y < x.val, (pre.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1)) :
    ted.preorder_loop a.lml n depth pre x ⦃ r =>
      r.length = a.label.length ∧ ∀ y < a.label.length, (r.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1) ⦄ := by
  unfold ted.preorder_loop
  apply loop.spec_decr_nat
    (measure := fun s => a.label.length - s.2.val)
    (inv := fun s => s.2.val ≤ a.label.length ∧ s.1.length = a.label.length ∧
      ∀ y < s.2.val, (s.1.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1))
  · intro s hs
    obtain ⟨pre1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.preorder_loop.body
    by_cases hxn : x1 < n
    · rw [if_pos hxn]
      have hxn' : x1.val < a.label.length := by have : x1.val < n.val := hxn; omega
      have hlml : a.lml.val.length = a.label.length := hW.n2
      have hlml' : a.lml.length = a.label.length := hW.n2
      have hdl' : depth.val.length = a.label.length := hdl
      step as ⟨i, hi⟩
      have hi' : i.val = laOf a (x1.val + 1) := by
        rw [laOf_eq a _ hxn', hi, getG_eq _ _ (by omega)]
      step as ⟨l, hl⟩
      have hl' : l.val = laOf a (x1.val + 1) := by rw [hl, U32.cast_Usize_val_eq]; exact hi'
      step as ⟨d, hd⟩
      have hd' : d.val = dep (laOf a) a.label.length (x1.val + 1) := by
        rw [hd]
        have := hD (x1.val + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at this
        rw [← this, getG_eq _ _ (by omega)]
      have hpre := pre_le_n hW.wfl (n := a.label.length) (u := x1.val + 1) (by omega) (by omega)
      unfold Ted.pre at hpre
      step as ⟨v1, hv1⟩
      step as ⟨old, imb, ho, himb⟩
      have hset : (imb v1).val = pre1.val.set x1.val v1 := by
        rw [himb, alloc.vec.Vec.set_val_eq]
      step as ⟨x2, hx2⟩
      have hp1 : pre1.val.length = a.label.length := hs2
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs2
      · intro y hy
        rw [hset]
        by_cases hyx : y = x1.val
        · subst hyx
          rw [getG_set_eq _ _ _ (by omega)]
          unfold Ted.pre; omega
        · rw [getG_set_ne _ _ _ _ hyx]
          exact hs3 y (by omega)
    · rw [if_neg hxn]
      simp only [WP.spec_ok]
      have : x1.val = a.label.length := by
        have : ¬ x1.val < n.val := hxn
        omega
      refine ⟨hs2, ?_⟩
      intro y hy
      exact hs3 y (by omega)
  · exact ⟨hx, hpl, hP⟩

theorem preorder_spec (a : ted.PostTree) (hW : PT.Wf a) :
    ted.preorder a ⦃ r => r.length = a.label.length ∧
      ∀ x, 1 ≤ x → x ≤ a.label.length → (r.val[x - 1]!).val = Ted.pre (laOf a) a.label.length x ⦄ := by
  unfold ted.preorder
  have hlenv := alloc.vec.Vec.len_val a.label
  refine WP.spec_bind (depths_spec a hW) ?_
  rintro depth ⟨hdl, hD⟩
  step as ⟨pre, hpre, hpl⟩
  refine WP.spec_mono (preorder_loop_spec a hW a.label.len depth pre 0#usize hlenv (by simp) hdl
    (by rw [hpl]; exact hlenv) hD (by simp)) ?_
  rintro r ⟨h1, h2⟩
  refine ⟨h1, fun x hx1 hx2 => ?_⟩
  have := h2 (x - 1) (by omega)
  have e : x - 1 + 1 = x := by omega
  rw [e] at this; exact this

/-- The pairs as natural numbers. -/
def Mp (pairs : List (Std.U32 × Std.U32)) : List (Nat × Nat) := pairs.map (fun p => (p.1.val, p.2.val))

/-- A list of pairs is one to one, by position. -/
def IInj (M : List (Nat × Nat)) : Prop :=
  ∀ i j, i < M.length → j < M.length → i ≠ j → (M[i]!).1 ≠ (M[j]!).1 ∧ (M[i]!).2 ≠ (M[j]!).2

/-- The lookup table of a list of pairs. -/
def TbO (n : Nat) (tb : List Std.Usize) (P : List (Nat × Nat)) : Prop :=
  tb.length = n + 1 ∧ (∀ i < P.length, (tb[(P[i]!).1]!).val = (P[i]!).2) ∧
  ∀ x ≤ n, (∀ i < P.length, (P[i]!).1 ≠ x) → (tb[x]!).val = 0

theorem getN_take (M : List (Nat × Nat)) (i j : Nat) (h : j < i) : (M.take i)[j]! = M[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_take, h]

theorem take_succ_eq (M : List (Nat × Nat)) (i : Nat) (h : i < M.length) :
    M.take (i + 1) = M.take i ++ [M[i]!] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp [getG_eq M i h]

theorem iinj_snoc (P : List (Nat × Nat)) (q : Nat × Nat) (h : IInj P)
    (h1 : ∀ i < P.length, (P[i]!).1 ≠ q.1) (h2 : ∀ i < P.length, (P[i]!).2 ≠ q.2) : IInj (P ++ [q]) := by
  intro i j hi hj hij
  simp only [List.length_append, List.length_singleton] at hi hj
  have e : ∀ k, k < P.length → (P ++ [q])[k]! = P[k]! := by
    intro k hk
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hk]
  have eq : (P ++ [q])[P.length]! = q := by
    simp [List.getElem!_eq_getElem?_getD]
  by_cases hi' : i < P.length
  · by_cases hj' : j < P.length
    · rw [e i hi', e j hj']; exact h i j hi' hj' hij
    · have : j = P.length := by omega
      subst this; rw [e i hi', eq]; exact ⟨h1 i hi', h2 i hi'⟩
  · have hi2 : i = P.length := by omega
    subst hi2
    have hj' : j < P.length := by omega
    rw [e j hj', eq]; exact ⟨fun h => h1 j hj' h.symm, fun h => h2 j hj' h.symm⟩

def NotCost (v : ted.Check) : Prop := ∀ c, v ≠ ted.Check.Cost c

theorem Mp_getN (pairs : List (Std.U32 × Std.U32)) (i : Nat) (h : i < pairs.length) :
    ((Mp pairs)[i]!).1 = (pairs[i]'h).1.val ∧ ((Mp pairs)[i]!).2 = (pairs[i]'h).2.val := by
  have : (Mp pairs).length = pairs.length := by simp [Mp]
  rw [getG_eq _ _ (by omega)]
  simp [Mp]

theorem TbO_snoc (n : Nat) (tb : List Std.Usize) (P : List (Nat × Nat)) (x : Nat) (yU : Std.Usize)
    (h : TbO n tb P) (hx : x ≤ n) (hnew : ∀ i < P.length, (P[i]!).1 ≠ x) :
    TbO n (tb.set x yU) (P ++ [(x, yU.val)]) := by
  obtain ⟨hl, h1, h2⟩ := h
  have hxl : x < tb.length := by omega
  have e : ∀ k, k < P.length → (P ++ [(x, yU.val)])[k]! = P[k]! := by
    intro k hk
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hk]
  have eq : (P ++ [(x, yU.val)])[P.length]! = (x, yU.val) := by
    simp [List.getElem!_eq_getElem?_getD]
  refine ⟨by simpa using hl, ?_, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hi' : i < P.length
    · rw [e i hi', getG_set_ne _ _ _ _ (hnew i hi')]
      exact h1 i hi'
    · have : i = P.length := by omega
      subst this; rw [eq]
      simp only
      rw [getG_set_eq _ _ _ hxl]
  · intro x' hx' hall
    have hne : x' ≠ x := by
      intro h'
      apply hall P.length (by simp)
      rw [eq]; exact h'.symm
    rw [getG_set_ne _ _ _ _ hne]
    apply h2 x' hx'
    intro i hi
    have := hall i (by simp; omega)
    rwa [e i hi] at this

theorem getN_swap (P : List (Nat × Nat)) (i : Nat) (h : i < P.length) : (P.map Prod.swap)[i]! = (P[i]!).swap := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem check_loop0_spec (pairs : Slice (Std.U32 × Std.U32)) (n m : Std.Usize) (nn mm : Nat)
    (hn : n.val = nn) (hm : m.val = mm) :
    ∀ (to_b to_a : alloc.vec.Vec Std.Usize) (verdict : ted.Check) (i : Std.Usize),
    i.val ≤ pairs.val.length →
    Rng nn mm ((Mp pairs.val).take i.val) → IInj ((Mp pairs.val).take i.val) →
    TbO nn to_b.val ((Mp pairs.val).take i.val) →
    TbO mm to_a.val (((Mp pairs.val).take i.val).map Prod.swap) →
    ted.check_core_loop0 pairs n m to_b to_a verdict true i ⦃ r =>
      (r.2.2 = true → Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val) ∧ TbO nn r.1.val (Mp pairs.val)) ∧
      (r.2.2 = false → NotCost r.2.1 ∧ ¬ (Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val))) ⦄ := by
  intro to_b to_a verdict i hi hR hI hB hA
  unfold ted.check_core_loop0
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.2.2.1 = true then pairs.val.length - s.2.2.2.2.val + 1 else 0)
    (inv := fun s => s.2.2.2.2.val ≤ pairs.val.length ∧
      (s.2.2.2.1 = true → Rng nn mm ((Mp pairs.val).take s.2.2.2.2.val) ∧ IInj ((Mp pairs.val).take s.2.2.2.2.val) ∧
        TbO nn s.1.val ((Mp pairs.val).take s.2.2.2.2.val) ∧
        TbO mm s.2.1.val (((Mp pairs.val).take s.2.2.2.2.val).map Prod.swap)) ∧
      (s.2.2.2.1 = false → NotCost s.2.2.1 ∧ ¬ (Rng nn mm (Mp pairs.val) ∧ IInj (Mp pairs.val))))
  · intro s hs
    obtain ⟨to_b1, to_a1, verdict1, ok1, idx⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.check_core_loop0.body
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
        exact ⟨fun _ => ⟨hR1, hI1, hB1⟩, fun h => by simp at h⟩
  · refine ⟨hi, fun _ => ⟨hR, hI, hB, hA⟩, fun h => by simp at h⟩

/-! Legal mappings are the one to one maps that preserve the postorder and the preorder. -/

def PostOrd (M : List (Nat × Nat)) : Prop := ∀ p ∈ M, ∀ q ∈ M, p.1 < q.1 → p.2 < q.2
def PreOrd (la lb : Nat → Nat) (n m : Nat) (M : List (Nat × Nat)) : Prop :=
  ∀ p ∈ M, ∀ q ∈ M, Ted.pre la n p.1 < Ted.pre la n q.1 → Ted.pre lb m p.2 < Ted.pre lb m q.2

theorem iinj_fst {M : List (Nat × Nat)} (h : IInj M) {p q : Nat × Nat} (hp : p ∈ M) (hq : q ∈ M)
    (e : p.1 = q.1) : p = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  by_cases hij : i = j
  · subst hij; rfl
  · have := (h i j hi hj hij).1
    rw [getG_eq _ _ hi, getG_eq _ _ hj] at this
    exact absurd e this

theorem iinj_snd {M : List (Nat × Nat)} (h : IInj M) {p q : Nat × Nat} (hp : p ∈ M) (hq : q ∈ M)
    (e : p.2 = q.2) : p = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  by_cases hij : i = j
  · subst hij; rfl
  · have := (h i j hi hj hij).2
    rw [getG_eq _ _ hi, getG_eq _ _ hj] at this
    exact absurd e this

theorem iinj_nodup {M : List (Nat × Nat)} (h : IInj M) : M.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij hh
  have := (h i j hi hj (by omega)).1
  rw [getG_eq _ _ hi, getG_eq _ _ hj, hh] at this
  exact this rfl

theorem valid_to_iinj {la lb : Nat → Nat} {M : List (Nat × Nat)} (h : Valid la lb M) : IInj M := by
  intro i j hi hj hij
  have hnd := h.1
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  have hne : M[i] ≠ M[j] := by
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · exact hnd i j hi hj hlt
    · exact fun e => hnd j i hj hi hgt e.symm
  have hmi : M[i] ∈ M := List.getElem_mem hi
  have hmj : M[j] ∈ M := List.getElem_mem hj
  have hh := (h.2 _ hmi _ hmj).1
  rw [getG_eq _ _ hi, getG_eq _ _ hj]
  constructor
  · intro e; apply hne; exact Prod.ext e (hh.mp e)
  · intro e; apply hne; exact Prod.ext (hh.mpr e) e

theorem anc_iff_orders {la : Nat → Nat} {n : Nat} (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (hun : u ≤ n)
    (hv : 1 ≤ v) (hvn : v ≤ n) :
    Anc la u v ↔ u < v ∧ Ted.pre la n v < Ted.pre la n u := by
  constructor
  · intro h
    exact ⟨h.1, (P_anc hA hu h.1 hvn h.2).1⟩
  · rintro ⟨h1, h2⟩
    by_cases hc : la v ≤ u
    · exact ⟨h1, hc⟩
    · have := P_un hA hu h1 hvn (by omega)
      have := pre_le_Qp hA hu (n := n)
      omega

theorem valid_of_orders {la lb : Nat → Nat} {n m : Nat} (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)}
    (hr : Rng n m M) (hI : IInj M) (hPo : PostOrd M) (hPr : PreOrd la lb n m M) : Valid la lb M := by
  apply validQ_to_valid hA hB hr
  refine ⟨iinj_nodup hI, fun p hp q hq => ?_⟩
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hq
  have e1 : p.1 = q.1 ↔ p.2 = q.2 :=
    ⟨fun e => by have := iinj_fst hI hp hq e; rw [this], fun e => by have := iinj_snd hI hp hq e; rw [this]⟩
  have t1 := hPr p hp q hq
  have t2 := hPr q hq p hp
  have t3 : Ted.pre la n p.1 = Ted.pre la n q.1 → Ted.pre lb m p.2 = Ted.pre lb m q.2 := fun h => by
    rw [e1.mp (pre_inj hA hp1 hp2 hq1 hq2 h)]
  have t4 : Ted.pre lb m p.2 = Ted.pre lb m q.2 → Ted.pre la n p.1 = Ted.pre la n q.1 := fun h => by
    rw [e1.mpr (pre_inj hB hp3 hp4 hq3 hq4 h)]
  have hpre : Ted.pre la n p.1 < Ted.pre la n q.1 ↔ Ted.pre lb m p.2 < Ted.pre lb m q.2 := by omega
  have hpre' : Ted.pre la n q.1 < Ted.pre la n p.1 ↔ Ted.pre lb m q.2 < Ted.pre lb m p.2 := by omega
  have hpost : p.1 < q.1 ↔ p.2 < q.2 := by
    refine ⟨hPo p hp q hq, fun h => ?_⟩
    rcases Nat.lt_trichotomy p.1 q.1 with h' | h' | h'
    · exact h'
    · have := e1.mp h'; omega
    · have := hPo q hq p hp h'; omega
  refine ⟨e1, hpre, ?_⟩
  rw [anc_iff_orders hA hp1 hp2 hq1 hq2, anc_iff_orders hB hp3 hp4 hq3 hq4]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hpost.mp h1, hpre'.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hpost.mpr h1, hpre'.mpr h2⟩

theorem tb_nonzero {n : Nat} {tb : List Std.Usize} {M : List (Nat × Nat)} (hT : TbO n tb M) {x : Nat} (hx : x ≤ n)
    (h : (tb[x]!).val ≠ 0) : ∃ p ∈ M, p.1 = x ∧ p.2 = (tb[x]!).val := by
  refine Classical.byContradiction fun hno => ?_
  apply h
  apply hT.2.2 x hx
  intro i hi heq
  apply hno
  refine ⟨M[i]!, ?_, heq, ?_⟩
  · rw [getG_eq _ _ hi]; exact List.getElem_mem _
  · rw [← hT.2.1 i hi, heq]

theorem tb_val {n : Nat} {tb : List Std.Usize} {M : List (Nat × Nat)} (hT : TbO n tb M) {p : Nat × Nat}
    (hp : p ∈ M) : (tb[p.1]!).val = p.2 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have := hT.2.1 i hi
  rwa [getG_eq _ _ hi] at this

def PostUp (M : List (Nat × Nat)) (x prev : Nat) : Prop :=
  (∀ p ∈ M, ∀ q ∈ M, p.1 < q.1 → q.1 < x → p.2 < q.2) ∧ (∀ p ∈ M, p.1 < x → p.2 ≤ prev) ∧
  (prev ≠ 0 → ∃ p ∈ M, p.1 < x ∧ p.2 = prev)

theorem check_loop1_spec (n : Std.Usize) (nn mm : Nat) (hn : n.val = nn) (to_b : alloc.vec.Vec Std.Usize)
    (M : List (Nat × Nat)) (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M) :
    ∀ (verdict : ted.Check) (prev x : Std.Usize), 1 ≤ x.val → x.val ≤ nn + 1 → PostUp M x.val prev.val →
    ted.check_core_loop1 n to_b verdict true prev x ⦃ r =>
      (r.2 = true → PostOrd M) ∧ (r.2 = false → NotCost r.1 ∧ ¬ PostOrd M) ⦄ := by
  intro verdict prev x hx1 hx2 hU
  unfold ted.check_core_loop1
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.1 = true then nn + 1 - s.2.2.2.val + 1 else 0)
    (inv := fun s => 1 ≤ s.2.2.2.val ∧ s.2.2.2.val ≤ nn + 1 ∧
      (s.2.1 = true → PostUp M s.2.2.2.val s.2.2.1.val) ∧ (s.2.1 = false → NotCost s.1 ∧ ¬ PostOrd M))
  · intro s hs
    obtain ⟨verdict1, ok1, prev1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.check_core_loop1.body
    cases ok1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, WP.spec_ok]
      exact ⟨fun h => h.elim, fun _ => hs4 rfl⟩
    | true =>
      have hU1 := hs3 rfl
      simp only [if_true]
      by_cases hle : x1 <= n
      · rw [if_pos hle]
        have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
        have hbl : to_b.val.length = nn + 1 := hT.1
        have hbl' : to_b.length = nn + 1 := hT.1
        step as ⟨y, hy⟩
        have hy' : y.val = (to_b.val[x1.val]!).val := by rw [hy, getG_eq _ _ (by omega)]
        by_cases c1 : y != 0#usize
        · rw [if_pos c1]
          have hy0 : y.val ≠ 0 := by
            intro h0; apply (by simpa using c1 : y ≠ 0#usize)
            exact UScalar.eq_of_val_eq (by simpa using h0)
          obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hle' (by rw [← hy']; exact hy0)
          by_cases c2 : y <= prev1
          · rw [if_pos c2]
            simp only [WP.spec_ok]
            refine ⟨hs1, hs2, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), ?_⟩, by simp⟩
            intro hPo
            have hy2 : y.val ≤ prev1.val := c2
            obtain ⟨pp, hpp, hpp1, hpp2⟩ := hU1.2.2 (by omega)
            have := hPo pp hpp pq hpq (by omega)
            omega
          · rw [if_neg c2]
            have hy2 : prev1.val < y.val := by have : ¬ y.val ≤ prev1.val := c2; omega
            simp only [c1, if_true, bind_tc_ok]
            step as ⟨x2, hx2⟩
            refine ⟨by omega, by omega, fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
            · intro p hp q hq h1 h2
              by_cases hq1 : q.1 < x1.val
              · exact hU1.1 p hp q hq h1 hq1
              · have hq2 : q.1 = x1.val := by omega
                have hqq : q = pq := iinj_fst hI hq hpq (by omega)
                have hpqy : pq.2 = y.val := by rw [hpq2, hy']
                rw [hqq, hpqy]
                have := hU1.2.1 p hp (by omega)
                omega
            · intro p hp h1
              by_cases hp1 : p.1 < x1.val
              · have := hU1.2.1 p hp hp1; omega
              · have hq2 : p.1 = x1.val := by omega
                have hpp : p = pq := iinj_fst hI hp hpq (by omega)
                have hpqy : pq.2 = y.val := by rw [hpq2, hy']
                rw [hpp, hpqy]
            · intro _
              exact ⟨pq, hpq, by omega, by omega⟩
        · rw [if_neg c1]
          have hy0 : y.val = 0 := by simpa using c1
          have c1' : (y != 0#usize) = false := by
            have : y = 0#usize := UScalar.eq_of_val_eq (by simpa using hy0)
            rw [this]; rfl
          simp only [c1', Bool.false_eq_true, if_false, bind_tc_ok]
          step as ⟨x2, hx2⟩
          have hnone : ∀ p ∈ M, p.1 ≠ x1.val := by
            intro p hp heq
            have := tb_val hT hp
            rw [heq] at this
            have hpr := hR p hp
            omega
          refine ⟨by omega, by omega, fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
          · intro p hp q hq h1 h2
            have : q.1 < x1.val := by have := hnone q hq; omega
            exact hU1.1 p hp q hq h1 this
          · intro p hp h1
            have : p.1 < x1.val := by have := hnone p hp; omega
            exact hU1.2.1 p hp this
          · intro hne
            obtain ⟨p, hp, h1, h2⟩ := hU1.2.2 hne
            exact ⟨p, hp, by omega, h2⟩
      · rw [if_neg hle]
        simp only [WP.spec_ok]
        have hx : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
        refine ⟨fun _ => ?_, fun h => by simp at h⟩
        intro p hp q hq h1
        exact hU1.1 p hp q hq h1 (by have := hR q hq; omega)
  · exact ⟨hx1, hx2, fun _ => hU, fun h => by simp at h⟩

theorem check_loop2_spec {la : Nat → Nat} (hA : WfL la) (n : Std.Usize) (nn : Nat) (hn : n.val = nn)
    (pa : alloc.vec.Vec Std.Usize) (hpl : pa.length = nn)
    (hpa : ∀ x, 1 ≤ x → x ≤ nn → (pa.val[x - 1]!).val = Ted.pre la nn x) :
    ∀ (x : Std.Usize) (at0 : alloc.vec.Vec Std.Usize), 1 ≤ x.val → x.val ≤ nn + 1 → at0.length = nn + 1 →
    (∀ x', 1 ≤ x' → x' < x.val → (at0.val[Ted.pre la nn x']!).val = x') →
    ted.check_core_loop2 n x pa at0 ⦃ r => r.length = nn + 1 ∧
      ∀ x', 1 ≤ x' → x' ≤ nn → (r.val[Ted.pre la nn x']!).val = x' ⦄ := by
  intro x at0 hx1 hx2 hal hat
  unfold ted.check_core_loop2
  apply loop.spec_decr_nat
    (measure := fun s => nn + 1 - s.1.val)
    (inv := fun s => 1 ≤ s.1.val ∧ s.1.val ≤ nn + 1 ∧ s.2.length = nn + 1 ∧
      ∀ x', 1 ≤ x' → x' < s.1.val → (s.2.val[Ted.pre la nn x']!).val = x')
  · intro s hs
    obtain ⟨x1, at1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.check_core_loop2.body
    by_cases hle : x1 <= n
    · rw [if_pos hle]
      have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
      have hpl' : pa.val.length = nn := hpl
      have hal' : at1.val.length = nn + 1 := hs3
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1' : i1.val = Ted.pre la nn x1.val := by
        rw [hi1, ← hpa x1.val hs1 hle']
        rw [← getG_eq _ _ (by omega)]
        congr 2
      have hpre := pre_le_n hA (n := nn) (u := x1.val) hs1 hle'
      step as ⟨old, imb, ho, himb⟩
      step as ⟨x2, hx2⟩
      have hset : (imb x1).val = at1.val.set i1.val x1 := by rw [himb, alloc.vec.Vec.set_val_eq]
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs3
      · intro x' h1 h2
        rw [hset]
        by_cases hxx : x' = x1.val
        · subst hxx
          rw [← hi1', getG_set_eq _ _ _ (by omega)]
        · have hlt : x' < x1.val := by omega
          have hne : Ted.pre la nn x' ≠ i1.val := by
            intro h
            rw [hi1'] at h
            exact hxx (pre_inj hA h1 (by omega) hs1 hle' h)
          rw [getG_set_ne _ _ _ _ hne]
          exact hs4 x' h1 hlt
    · rw [if_neg hle]
      simp only [WP.spec_ok]
      have : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
      refine ⟨hs3, ?_⟩
      intro x' h1 h2
      exact hs4 x' h1 (by omega)
  · exact ⟨hx1, hx2, hal, hat⟩

theorem pre_surj {la : Nat → Nat} {n : Nat} (hA : WfL la) {k : Nat} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ x, 1 ≤ x ∧ x ≤ n ∧ Ted.pre la n x = k := by
  obtain ⟨x, h1, h2, h3⟩ := pim_surj hA (n := n) (y := n + 1 - k) (by omega) (by omega)
  refine ⟨x, h1, h2, ?_⟩
  have := pre_le_n hA h1 h2
  unfold pim at h3; omega

def PreUp (la lb : Nat → Nat) (n m : Nat) (M : List (Nat × Nat)) (k prev : Nat) : Prop :=
  (∀ p ∈ M, ∀ q ∈ M, Ted.pre la n p.1 < Ted.pre la n q.1 → Ted.pre la n q.1 < k →
      Ted.pre lb m p.2 < Ted.pre lb m q.2) ∧
  (∀ p ∈ M, Ted.pre la n p.1 < k → Ted.pre lb m p.2 ≤ prev) ∧
  (prev ≠ 0 → ∃ p ∈ M, Ted.pre la n p.1 < k ∧ Ted.pre lb m p.2 = prev)

theorem check_loop3_spec {la lb : Nat → Nat} (hA : WfL la) (hB : WfL lb) (n : Std.Usize) (nn mm : Nat)
    (hn : n.val = nn) (to_b pb at0 : alloc.vec.Vec Std.Usize) (M : List (Nat × Nat))
    (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M)
    (hpl : pb.length = mm) (hpb : ∀ y, 1 ≤ y → y ≤ mm → (pb.val[y - 1]!).val = Ted.pre lb mm y)
    (hal : at0.length = nn + 1) (hat : ∀ x, 1 ≤ x → x ≤ nn → (at0.val[Ted.pre la nn x]!).val = x) :
    ∀ (verdict : ted.Check) (prev k : Std.Usize), 1 ≤ k.val → k.val ≤ nn + 1 →
    PreUp la lb nn mm M k.val prev.val →
    ted.check_core_loop3 n to_b verdict true pb at0 prev k ⦃ r =>
      (r.2 = true → PreOrd la lb nn mm M) ∧ (r.2 = false → NotCost r.1 ∧ ¬ PreOrd la lb nn mm M) ⦄ := by
  intro verdict prev k hk1 hk2 hU
  unfold ted.check_core_loop3
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.1 = true then nn + 1 - s.2.2.2.val + 1 else 0)
    (inv := fun s => 1 ≤ s.2.2.2.val ∧ s.2.2.2.val ≤ nn + 1 ∧
      (s.2.1 = true → PreUp la lb nn mm M s.2.2.2.val s.2.2.1.val) ∧ (s.2.1 = false → NotCost s.1 ∧ ¬ PreOrd la lb nn mm M))
  · intro s hs
    obtain ⟨verdict1, ok1, prev1, k1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.check_core_loop3.body
    cases ok1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, WP.spec_ok]
      exact ⟨fun h => h.elim, fun _ => hs4 rfl⟩
    | true =>
      have hU1 := hs3 rfl
      simp only [if_true]
      by_cases hle : k1 <= n
      · rw [if_pos hle]
        have hle' : k1.val ≤ nn := by have : k1.val ≤ n.val := hle; omega
        obtain ⟨x0, hx01, hx0n, hx0k⟩ := pre_surj hA (n := nn) hs1 hle'
        have hal' : at0.val.length = nn + 1 := hal
        have hbl : to_b.val.length = nn + 1 := hT.1
        have hbl' : to_b.length = nn + 1 := hT.1
        have hpl' : pb.val.length = mm := hpl
        step as ⟨x, hx⟩
        have hxv : x.val = x0 := by
          rw [hx]
          have := hat x0 hx01 hx0n
          rw [hx0k, getG_eq _ _ (by omega : k1.val < at0.val.length)] at this
          exact this
        step as ⟨y, hy⟩
        have hy' : y.val = (to_b.val[x0]!).val := by
          rw [hy, getG_eq to_b.val x0 (by omega)]
          congr 2
        by_cases c1 : y != 0#usize
        · rw [if_pos c1]
          have hy0 : y.val ≠ 0 := by
            intro h0; apply (by simpa using c1 : y ≠ 0#usize)
            exact UScalar.eq_of_val_eq (by simpa using h0)
          obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hx0n (by rw [← hy']; exact hy0)
          have hpqy : pq.2 = y.val := by rw [hpq2, hy']
          obtain ⟨_, _, hq3, hq4⟩ := hR pq hpq
          have hyr : 1 ≤ y.val ∧ y.val ≤ mm := by rw [← hpqy]; exact ⟨hq3, hq4⟩
          have hpre_pq : Ted.pre la nn pq.1 = k1.val := by rw [hpq1, hx0k]
          step as ⟨j, hj⟩
          step as ⟨i1, hi1⟩
          have hi1' : i1.val = Ted.pre lb mm y.val := by
            rw [hi1, ← hpb y.val hyr.1 hyr.2, getG_eq _ _ (by omega)]
            congr 2
          by_cases c2 : i1 <= prev1
          · rw [if_pos c2]
            simp only [WP.spec_ok]
            refine ⟨hs1, hs2, fun h => by simp at h, fun _ => ⟨(fun c h => nomatch h), ?_⟩, by simp⟩
            intro hPo
            have hy2 : i1.val ≤ prev1.val := c2
            obtain ⟨pp, hpp, hpp1, hpp2⟩ := hU1.2.2 (by
              have := pre_pos hB (n := mm) (u := y.val) hyr.1; omega)
            have := hPo pp hpp pq hpq (by omega)
            rw [hpqy] at this
            omega
          · rw [if_neg c2]
            have hy2 : prev1.val < i1.val := by have : ¬ i1.val ≤ prev1.val := c2; omega
            simp only [c1, if_true, bind_tc_ok]
            step as ⟨i1b, hi1b⟩
            have hi1bb : i1b.val = i1.val := by rw [hi1b, hi1]
            step as ⟨k2, hk2'⟩
            refine ⟨by omega, by omega, fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
            · intro p hp q hq h1 h2
              by_cases hq1 : Ted.pre la nn q.1 < k1.val
              · exact hU1.1 p hp q hq h1 hq1
              · have hq2 : Ted.pre la nn q.1 = k1.val := by omega
                have hqq : q = pq := by
                  have := pre_inj hA (hR q hq).1 (hR q hq).2.1 (hR pq hpq).1 (hR pq hpq).2.1 (by omega)
                  exact iinj_fst hI hq hpq this
                rw [hqq, hpqy, ← hi1']
                have := hU1.2.1 p hp (by omega)
                omega
            · intro p hp h1
              by_cases hp1 : Ted.pre la nn p.1 < k1.val
              · have := hU1.2.1 p hp hp1; omega
              · have hq2 : Ted.pre la nn p.1 = k1.val := by omega
                have hpp : p = pq := by
                  have := pre_inj hA (hR p hp).1 (hR p hp).2.1 (hR pq hpq).1 (hR pq hpq).2.1 (by omega)
                  exact iinj_fst hI hp hpq this
                rw [hpp, hpqy]; omega
            · intro _
              exact ⟨pq, hpq, by omega, by rw [hpqy]; omega⟩
        · rw [if_neg c1]
          have hy0 : y.val = 0 := by simpa using c1
          have c1' : (y != 0#usize) = false := by
            have : y = 0#usize := UScalar.eq_of_val_eq (by simpa using hy0)
            rw [this]; rfl
          simp only [c1', Bool.false_eq_true, if_false, bind_tc_ok]
          step as ⟨k2, hk2'⟩
          have hnone : ∀ p ∈ M, p.1 ≠ x0 := by
            intro p hp heq
            have := tb_val hT hp
            rw [heq, ← hy'] at this
            have hpr := hR p hp
            omega
          have hnone' : ∀ p ∈ M, Ted.pre la nn p.1 ≠ k1.val := by
            intro p hp heq
            have := pre_inj hA (hR p hp).1 (hR p hp).2.1 hx01 hx0n (by omega)
            exact hnone p hp this
          refine ⟨by omega, by omega, fun _ => ⟨?_, ?_, ?_⟩, fun h => by simp at h, by simp; omega⟩
          · intro p hp q hq h1 h2
            have : Ted.pre la nn q.1 < k1.val := by have := hnone' q hq; omega
            exact hU1.1 p hp q hq h1 this
          · intro p hp h1
            have : Ted.pre la nn p.1 < k1.val := by have := hnone' p hp; omega
            exact hU1.2.1 p hp this
          · intro hne
            obtain ⟨p, hp, h1, h2⟩ := hU1.2.2 hne
            exact ⟨p, hp, by omega, h2⟩
      · rw [if_neg hle]
        simp only [WP.spec_ok]
        have hx : k1.val = nn + 1 := by have : ¬ k1.val ≤ n.val := hle; omega
        refine ⟨fun _ => ?_, fun h => by simp at h⟩
        intro p hp q hq h1
        exact hU1.1 p hp q hq h1 (by
          have := pre_le_n hA (n := nn) (u := q.1) (hR q hq).1 (hR q hq).2.1; omega)
  · exact ⟨hk1, hk2, fun _ => hU, fun h => by simp at h⟩

def RSum (a b : ted.PostTree) (M : List (Nat × Nat)) (x : Nat) : Nat :=
  (M.map (fun p => if p.1 < x then rcost a b p.1 p.2 else 0)).sum

theorem sum_ite_zero (M : List (Nat × Nat)) (g : Nat × Nat → Nat) (x : Nat) (h : ∀ p ∈ M, p.1 ≠ x) :
    (M.map (fun p => if p.1 = x then g p else 0)).sum = 0 := by
  induction M with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [if_neg (h a (List.mem_cons_self ..)), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem sum_ite_unique (M : List (Nat × Nat)) (hnd : M.Nodup) (g : Nat × Nat → Nat) (x : Nat) (q : Nat × Nat)
    (hq : q ∈ M) (hu : ∀ p ∈ M, p.1 = x → p = q) (hqx : q.1 = x) :
    (M.map (fun p => if p.1 = x then g p else 0)).sum = g q := by
  induction M with
  | nil => simp at hq
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hnd' := List.nodup_cons.mp hnd
    by_cases ha : a = q
    · subst ha
      rw [if_pos hqx]
      have : (rest.map (fun p => if p.1 = x then g p else 0)).sum = 0 := by
        apply sum_ite_zero
        intro p hp hpx
        have := hu p (List.mem_cons_of_mem _ hp) hpx
        exact hnd'.1 (this ▸ hp)
      omega
    · have hax : a.1 ≠ x := fun h => ha (hu a (List.mem_cons_self ..) h)
      rw [if_neg hax]
      have hq' : q ∈ rest := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h.symm ha
        · exact h
      rw [ih hnd'.2 hq' (fun p hp => hu p (List.mem_cons_of_mem _ hp))]
      omega

theorem rsum_succ (a b : ted.PostTree) {nn mm : Nat} {to_b : List Std.Usize} {M : List (Nat × Nat)}
    (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b M) {x : Nat} (hx : x ≤ nn) :
    RSum a b M (x + 1) = RSum a b M x +
      (if (to_b[x]!).val = 0 then 0 else rcost a b x (to_b[x]!).val) := by
  have hsplit : (M.map (fun p => if p.1 < x + 1 then rcost a b p.1 p.2 else 0)).sum =
      (M.map (fun p => if p.1 < x then rcost a b p.1 p.2 else 0)).sum +
      (M.map (fun p => if p.1 = x then rcost a b p.1 p.2 else 0)).sum := by
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p hp
    by_cases h1 : p.1 < x
    · simp [h1, show p.1 < x + 1 by omega, show p.1 ≠ x by omega]
    · by_cases h2 : p.1 = x
      · simp [h2]
      · simp [h1, h2, show ¬ p.1 < x + 1 by omega]
  unfold RSum
  rw [hsplit]
  congr 1
  by_cases h0 : (to_b[x]!).val = 0
  · rw [if_pos h0]
    apply sum_ite_zero
    intro p hp heq
    have := tb_val hT hp
    rw [heq, h0] at this
    have := hR p hp
    omega
  · rw [if_neg h0]
    obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hx h0
    rw [sum_ite_unique M (iinj_nodup hI) (fun p => rcost a b p.1 p.2) x pq hpq
      (fun p hp hpx => iinj_fst hI hp hpq (by omega)) hpq1]
    rw [← hpq2, hpq1]

theorem rcost_le (a b : ted.PostTree) (x y : Nat) : rcost a b x y ≤ 2 := by
  unfold rcost; split <;> try omega
  split <;> omega

theorem rsum_le (a b : ted.PostTree) (M : List (Nat × Nat)) (x : Nat) : RSum a b M x ≤ 2 * M.length := by
  unfold RSum
  induction M with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := rcost_le a b p.1 p.2
    split <;> omega

theorem mlen_le {nn mm : Nat} {M : List (Nat × Nat)} (hR : Rng nn mm M) (hI : IInj M) : M.length ≤ nn := by
  have := len_le_of_inj Prod.fst M 1 nn (iinj_nodup hI)
    (fun p hp => ⟨(hR p hp).1, (hR p hp).2.1⟩)
    (fun p hp q hq e => iinj_fst hI hp hq e)
  omega

theorem check_loop4_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (n : Std.Usize) (nn mm : Nat)
    (hn : n.val = nn) (hnn : nn = a.label.length) (hmm : mm = b.label.length) (hna : nn < 2 ^ 14)
    (to_b : alloc.vec.Vec Std.Usize) (M : List (Nat × Nat))
    (hR : Rng nn mm M) (hI : IInj M) (hT : TbO nn to_b.val M) :
    ∀ (x : Std.Usize) (relabels : Std.U32), 1 ≤ x.val → x.val ≤ nn + 1 → relabels.val = RSum a b M x.val →
    ted.check_core_loop4 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind n to_b x relabels
      ⦃ r => r.val = (M.map (fun p => rcost a b p.1 p.2)).sum ⦄ := by
  intro x relabels hx1 hx2 hrl
  unfold ted.check_core_loop4
  apply loop.spec_decr_nat
    (measure := fun s => nn + 1 - s.1.val)
    (inv := fun s => 1 ≤ s.1.val ∧ s.1.val ≤ nn + 1 ∧ s.2.val = RSum a b M s.1.val)
  · intro s hs
    obtain ⟨x1, rl⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.check_core_loop4.body
    by_cases hle : x1 <= n
    · rw [if_pos hle]
      have hle' : x1.val ≤ nn := by have : x1.val ≤ n.val := hle; omega
      have hbl : to_b.val.length = nn + 1 := hT.1
      have hbl' : to_b.length = nn + 1 := hT.1
      step as ⟨y, hy⟩
      have hy' : y.val = (to_b.val[x1.val]!).val := by rw [hy, getG_eq _ _ (by omega)]
      have hrs := rsum_succ a b hR hI hT hle'
      by_cases c1 : y != 0#usize
      · have hy0 : y.val ≠ 0 := by
          intro h0; apply (by simpa using c1 : y ≠ 0#usize)
          exact UScalar.eq_of_val_eq (by simpa using h0)
        obtain ⟨pq, hpq, hpq1, hpq2⟩ := tb_nonzero hT hle' (by rw [← hy']; exact hy0)
        have hpqy : pq.2 = y.val := by rw [hpq2, hy']
        obtain ⟨_, _, hq3, hq4⟩ := hR pq hpq
        simp only [c1, if_true, bind_tc_ok]
        have hc := relabel_cost_spec a b x1 y hs1 (by omega) (by rw [hnn] at hle'; omega) (by rw [hA.n3, ← hnn]; omega)
          (by rw [← hpqy, ← hmm]; omega) (by rw [hB.n3, ← hmm]; omega)
        obtain ⟨c, hcc, hcv⟩ := WP.spec_imp_exists hc
        rw [hcc]
        simp only [bind_tc_ok]
        have hrb : c.val ≤ 2 := by
          rw [hcv]; unfold rcost; split <;> try omega
          split <;> omega
        have hsumb : RSum a b M x1.val ≤ 2 * M.length := rsum_le a b M x1.val
        have hlenM : M.length ≤ nn := mlen_le hR hI
        have hbound : rl.val + c.val ≤ Std.U32.max := by
          have hU : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max, UScalar.max, UScalarTy.numBits, Std.U32.numBits]
          rw [hU]; omega
        step as ⟨rl2, hrl2⟩
        step as ⟨x2, hx2'⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        rw [hx2', hrl2, hs3, hrs, if_neg (by rw [← hy']; exact hy0), ← hy', hcv]
      · have hy0 : y.val = 0 := by simpa using c1
        have c1' : (y != 0#usize) = false := by
          have : y = 0#usize := UScalar.eq_of_val_eq (by simpa using hy0)
          rw [this]; rfl
        simp only [c1', Bool.false_eq_true, if_false, bind_tc_ok]
        step as ⟨x2, hx2'⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        rw [hx2', hs3, hrs, if_pos (by rw [← hy']; exact hy0)]
        rfl
    · rw [if_neg hle]
      simp only [WP.spec_ok]
      have hx : x1.val = nn + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
      rw [hs3, hx]
      unfold RSum
      congr 1
      apply List.map_congr_left
      intro p hp
      have := hR p hp
      simp [show p.1 < nn + 1 by omega]
  · refine ⟨hx1, hx2, hrl⟩

theorem valid_to_postord {la lb : Nat → Nat} {M : List (Nat × Nat)} (h : Valid la lb M) : PostOrd M :=
  fun p hp q hq hlt => ((h.2 p hp q hq).2.1).mp hlt

theorem valid_to_preord {la lb : Nat → Nat} {n m : Nat} {M : List (Nat × Nat)} (hA : WfL la) (hB : WfL lb)
    (hr : Rng n m M) (h : Valid la lb M) : PreOrd la lb n m M :=
  fun p hp q hq hlt => (((valid_to_validQ hA hB hr h).2 p hp q hq).2.1).mp hlt

def CheckPost (a b : ted.PostTree) (M : List (Nat × Nat)) (r : ted.Check) : Prop :=
  (∀ c, r = ted.Check.Cost c → Rng a.label.length b.label.length M ∧ Valid (laOf a) (laOf b) M ∧
    c.val = Cost (rcost a b) 1 a.label.length 1 b.label.length M) ∧
  ((Rng a.label.length b.label.length M ∧ Valid (laOf a) (laOf b) M) → ∃ c, r = ted.Check.Cost c)

theorem checkpost_fail (a b : ted.PostTree) (M : List (Nat × Nat)) (r : ted.Check) (hNC : NotCost r)
    (hnot : ¬ (Rng a.label.length b.label.length M ∧ Valid (laOf a) (laOf b) M)) : CheckPost a b M r :=
  ⟨fun c h => absurd h (hNC c), fun h => absurd h hnot⟩

theorem tbo_nil (n : Nat) (tb : List Std.Usize) (h : tb = List.replicate (n + 1) 0#usize) : TbO n tb [] := by
  refine ⟨by simp [h], by simp, fun x hx _ => ?_⟩
  rw [h, getG_eq _ _ (by simp; omega)]
  simp

theorem check_core_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (pairs : Slice (Std.U32 × Std.U32)) :
    ted.check_core a b pairs ⦃ r => CheckPost a b (Mp pairs.val) r ⦄ := by
  unfold ted.check_core
  have hlenA := alloc.vec.Vec.len_val a.label
  have hlenB := alloc.vec.Vec.len_val b.label
  simp only []
  step as ⟨i, hi⟩
  step as ⟨to_b, hto_b, hto_bl⟩
  step as ⟨i1, hi1⟩
  step as ⟨to_a, hto_a, hto_al⟩
  have hto_b' : to_b.val = List.replicate (a.label.length + 1) 0#usize := by rw [hto_b, hi, hlenA]
  have hto_a' : to_a.val = List.replicate (b.label.length + 1) 0#usize := by rw [hto_a, hi1, hlenB]
  refine WP.spec_bind (check_loop0_spec pairs a.label.len b.label.len a.label.length b.label.length hlenA hlenB
    to_b to_a (ted.Check.Cost 0#u32) 0#usize (by simp)
    (fun p hp => by simp at hp) (fun i j hi => by simp at hi) (tbo_nil _ _ hto_b')
    (by simpa using tbo_nil _ _ hto_a')) ?_
  rintro ⟨to_b1, verdict, ok1⟩ ⟨hP1, hP2⟩
  dsimp only at hP1 hP2
  show (if ok1 = true then _ else _) ⦃ _ ⦄
  by_cases hok1 : ok1 = true
  · rw [if_pos hok1]
    obtain ⟨hR, hI, hT⟩ := hP1 hok1
    refine WP.spec_bind (check_loop1_spec a.label.len a.label.length b.label.length hlenA to_b1 (Mp pairs.val)
      hR hI hT verdict 0#usize 1#usize (by simp) (by simp) ?_) ?_
    · have h1v : (1#usize).val = 1 := rfl
      have h0v : (0#usize).val = 0 := rfl
      refine ⟨fun p hp q hq h1 h2 => ?_, fun p hp h1 => ?_, fun h => absurd rfl h⟩
      · have := (hR q hq).1; omega
      · have := (hR p hp).1; omega
    rintro ⟨verdict1, ok2⟩ ⟨hQ1, hQ2⟩
    dsimp only at hQ1 hQ2
    show (if ok2 = true then _ else _) ⦃ _ ⦄
    by_cases hok2 : ok2 = true
    · rw [if_pos hok2]
      have hPo := hQ1 hok2
      refine WP.spec_bind (preorder_spec a hA) ?_
      rintro pa ⟨hpal, hpa⟩
      refine WP.spec_bind (preorder_spec b hB) ?_
      rintro pb ⟨hpbl, hpb⟩
      step as ⟨i2, hi2⟩
      step as ⟨at0, hat0, hat0l⟩
      have h1v : (1#usize).val = 1 := rfl
      have hat0' : at0.length = a.label.length + 1 := by rw [hat0l, hi2, hlenA]
      refine WP.spec_bind (check_loop2_spec hA.wfl a.label.len a.label.length hlenA pa hpal hpa 1#usize at0
        (by simp) (by simp) hat0' (fun x' h1 h2 => by omega)) ?_
      rintro at1 ⟨hat1l, hat1⟩
      refine WP.spec_bind (check_loop3_spec hA.wfl hB.wfl a.label.len a.label.length b.label.length hlenA to_b1 pb at1
        (Mp pairs.val) hR hI hT hpbl hpb hat1l hat1 verdict1 0#usize 1#usize (by simp) (by simp) ?_) ?_
      · have h0v : (0#usize).val = 0 := rfl
        refine ⟨fun p hp q hq h1 h2 => ?_, fun p hp h1 => ?_, fun h => absurd rfl h⟩
        · have := pre_pos hA.wfl (n := a.label.length) (u := q.1) (hR q hq).1; omega
        · have := pre_pos hA.wfl (n := a.label.length) (u := p.1) (hR p hp).1; omega
      rintro ⟨verdict2, ok3⟩ ⟨hS1, hS2⟩
      dsimp only at hS1 hS2
      show (if ok3 = true then _ else _) ⦃ _ ⦄
      by_cases hok3 : ok3 = true
      · rw [if_pos hok3]
        have hPr := hS1 hok3
        have hVal := valid_of_orders hA.wfl hB.wfl hR hI hPo hPr
        have hrs0 : RSum a b (Mp pairs.val) 1 = 0 := by
          unfold RSum
          have : (Mp pairs.val).map (fun p => if p.1 < 1 then rcost a b p.1 p.2 else 0) =
              (Mp pairs.val).map (fun _ => 0) :=
            List.map_congr_left (fun p hp => by
              have := (hR p hp).1; simp [show ¬ p.1 < 1 by omega])
          rw [this]; simp
        have h0u : (0#u32).val = 0 := rfl
        refine WP.spec_bind (check_loop4_spec a b hA hB a.label.len a.label.length b.label.length hlenA rfl rfl
          hna to_b1 (Mp pairs.val) hR hI hT 1#usize 0#u32 (by simp) (by simp) (by rw [h0u, h1v]; exact hrs0.symm)) ?_
        intro relabels hrel
        simp only [lift, bind_tc_ok]
        have hMl : (Mp pairs.val).length ≤ a.label.length := mlen_le hR hI
        have hlp : (Slice.len pairs).val = (Mp pairs.val).length := by simp [Mp]
        have hcnt : (UScalar.cast UScalarTy.U32 (Slice.len pairs)).val = (Mp pairs.val).length := by
          rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
          rw [hlp]; exact Nat.mod_eq_of_lt (by omega)
        have hc4 : (UScalar.cast UScalarTy.U32 a.label.len).val = a.label.length := by
          rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
          rw [hlenA]; exact Nat.mod_eq_of_lt (by omega)
        have hc6 : (UScalar.cast UScalarTy.U32 b.label.len).val = b.label.length := by
          rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
          rw [hlenB]; exact Nat.mod_eq_of_lt (by omega)
        have hmM : (Mp pairs.val).length ≤ b.label.length := by
          have := len_le_of_inj Prod.snd (Mp pairs.val) 1 b.label.length (iinj_nodup hI)
            (fun p hp => ⟨(hR p hp).2.2.1, (hR p hp).2.2.2⟩) (fun p hp q hq e => iinj_snd hI hp hq e)
          omega
        generalize UScalar.cast UScalarTy.U32 (Slice.len pairs) = cnt at hcnt ⊢
        generalize UScalar.cast UScalarTy.U32 a.label.len = i4 at hc4 ⊢
        generalize UScalar.cast UScalarTy.U32 b.label.len = i6 at hc6 ⊢
        step as ⟨i5, hi5⟩
        step as ⟨i7, hi7⟩
        have hrb : relabels.val ≤ 2 * a.label.length := by
          have := rsum_le a b (Mp pairs.val) (a.label.length + 1)
          have hsm : (Mp pairs.val).map (fun p => rcost a b p.1 p.2) =
              (Mp pairs.val).map (fun p => if p.1 < a.label.length + 1 then rcost a b p.1 p.2 else 0) :=
            List.map_congr_left (fun p hp => by have := (hR p hp).2.1; simp [show p.1 < a.label.length + 1 by omega])
          unfold RSum at this
          rw [← hsm] at this
          omega
        step as ⟨i8, hi8⟩
        step as ⟨i9, hi9⟩
        refine ⟨fun c h => ?_, fun _ => ⟨i9, rfl⟩⟩
        injection h with h'
        subst h'
        refine ⟨hR, hVal, ?_⟩
        unfold Cost
        omega
      · rw [if_neg hok3]
        have hok3' : ok3 = false := by simpa using hok3
        obtain ⟨hNC, hnot⟩ := hS2 hok3'
        simp only [WP.spec_ok]
        exact checkpost_fail a b _ _ hNC (fun ⟨hr, hv⟩ => hnot (valid_to_preord hA.wfl hB.wfl hr hv))
    · rw [if_neg hok2]
      have hok2' : ok2 = false := by simpa using hok2
      obtain ⟨hNC, hnot⟩ := hQ2 hok2'
      simp only [WP.spec_ok]
      exact checkpost_fail a b _ _ hNC (fun ⟨_, hv⟩ => hnot (valid_to_postord hv))
  · rw [if_neg hok1]
    have hok1' : ok1 = false := by simpa using hok1
    obtain ⟨hNC, hnot⟩ := hP2 hok1'
    simp only [WP.spec_ok]
    exact checkpost_fail a b _ _ hNC (fun ⟨hr, hv⟩ => hnot ⟨hr, valid_to_iinj hv⟩)

end difffold_lines_extract
