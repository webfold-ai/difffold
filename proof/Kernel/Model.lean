import SuffixSums
import Defs
import Difffold.Prune
import Difffold.Decision
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

/-- A model cell as a kernel word: a pruned cell is `INF`. -/
def enc : Option Nat → Nat
  | none => INFn
  | some v => v

/-- The model grid for the extracted size lists and a pair-cost function. -/
def gridOf (sa sb : Slice Std.U32) (dd : Nat → Nat → Nat) : Grid where
  n := sa.val.length
  m := sb.val.length
  sa := fun i => sa.val[i]!.val
  sb := fun j => sb.val[j]!.val
  dd := dd

/-- The kernel's bound: `|R_a(i) - R_b(j)|` when pruning is on, `0` otherwise. -/
def hK (ra rb : Slice Std.U32) (on : Bool) (i j : Nat) : Nat :=
  if on then
    (if ra.val[i]!.val ≥ rb.val[j]!.val then ra.val[i]!.val - rb.val[j]!.val
     else rb.val[j]!.val - ra.val[i]!.val)
  else 0

/-- Once a cell of row 0 is pruned, so is every cell to its right. -/
theorem P0_none_from (g : Grid) (h : Nat → Nat → Nat) (tau j : Nat)
    (hn : g.P h tau 0 j = none) : ∀ k, g.P h tau 0 (j + k) = none := by
  intro k
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    have : j + (k + 1) = (j + k) + 1 := by omega
    rw [this]
    simp [Grid.P, ih, oadd, keep]

theorem sumU_take_succ (l : List Std.U32) (t : Nat) (h : t < l.length) :
    sumU (l.take (t + 1)) = sumU (l.take t) + (l[t]'h).val := by
  unfold sumU
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append, List.sum_append]
  simp

theorem sumU_take_le (l : List Std.U32) (t : Nat) : sumU (l.take t) ≤ sumU l := by
  have h2 : sumU l = sumU (l.take t) + sumU (l.drop t) := by
    conv_lhs => rw [← List.take_append_drop t l]
    simp [sumU, List.sum_append]
  omega

/-- One step of the prefix-sum invariant. -/
theorem step_sum (sb : Slice Std.U32) (v : alloc.vec.Vec Std.U32) (j : Nat) (hj1 : 1 ≤ j)
    (hj : j ≤ sb.val.length) (hlen : v.length = j)
    (h4 : ∀ t < j, v.val[t]!.val = sumU (sb.val.take t)) :
    v.val[j - 1]!.val + sb.val[j - 1]!.val = sumU (sb.val.take j) := by
  have hb : j - 1 < sb.val.length := by omega
  rw [h4 (j - 1) (by omega)]
  have := sumU_take_succ sb.val (j - 1) hb
  rw [show j - 1 + 1 = j by omega] at this
  rw [this, getElem_bang_eq _ _ hb]

theorem hK_le (ra rb : Slice Std.U32) (on : Bool) (i j : Nat)
    (hra : ∀ i < ra.val.length, ra.val[i]!.val ≤ 2 ^ 27) (hrb : ∀ i < rb.val.length, rb.val[i]!.val ≤ 2 ^ 27)
    (hi : i < ra.val.length) (hj : j < rb.val.length) : hK ra rb on i j ≤ 2 ^ 27 := by
  have := hra i hi; have := hrb j hj
  unfold hK
  by_cases hon : on
  · simp only [hon, if_true]; split <;> omega
  · simp [hon]

/-- The model's recurrence at a cell of row 0. -/
theorem P0_succ (g : Grid) (h : Nat → Nat → Nat) (tau j v : Nat) (hv : g.P h tau 0 j = some v) :
    g.P h tau 0 (j + 1) = if v + g.sb j + h 0 (j + 1) ≤ tau then some (v + g.sb j) else none := by
  simp [Grid.P, hv, oadd, keep]

/-- `bound` computes `|ra[i] - rb[j]|`. -/
@[step] theorem bound_spec (ra rb : Slice Std.U32) (i j : Std.Usize)
    (hi : i.val < ra.val.length) (hj : j.val < rb.val.length) :
    kernel.bound ra rb i j ⦃ r => r.val = hK ra rb true i.val j.val ⦄ := by
  unfold kernel.bound
  step*
  have e1 : i1.val = ra.val[i.val]!.val := by rw [i1_post, getElem_bang_eq _ _ hi]
  have e2 : i2.val = rb.val[j.val]!.val := by rw [i2_post, getElem_bang_eq _ _ hj]
  simp only [hK, if_true, e1, e2] at *
  assumption

/-- `hh` computes `hK`. -/
@[step] theorem hh_spec (ra rb : Slice Std.U32) (on : Bool) (i j : Std.Usize)
    (hi : i.val < ra.val.length) (hj : j.val < rb.val.length) :
    kernel.hh ra rb on i j ⦃ r => r.val = hK ra rb on i.val j.val ⦄ := by
  unfold kernel.hh
  split
  · rename_i hon
    step*
  · rename_i hon
    have : on = false := by simpa using hon
    subst this
    simp [hK]

/-- Loop of `first_row`: extend row 0 while the cell fits under the threshold. -/
theorem first_row_loop_spec (g : Grid) (sb ra rb : Slice Std.U32) (on : Bool) (tau : Std.U32) (m : Std.Usize)
    (v0 : alloc.vec.Vec Std.U32) (j0 : Std.Usize)
    (hgsb : ∀ j, g.sb j = sb.val[j]!.val) (hm : m.val = sb.val.length) (hsum : sumU sb.val < 2 ^ 27)
    (hra : ∀ i < ra.val.length, ra.val[i]!.val ≤ 2 ^ 27) (hrb : ∀ i < rb.val.length, rb.val[i]!.val ≤ 2 ^ 27)
    (hra0 : 0 < ra.val.length) (hrbm : m.val < rb.val.length) (htau : tau.val < INFn)
    (hj0 : 1 ≤ j0.val) (hj1 : j0.val ≤ m.val + 1) (hlen : v0.length = j0.val)
    (hpre : ∀ t < j0.val, v0.val[t]!.val = sumU (sb.val.take t))
    (hP : ∀ t < j0.val, g.P (hK ra rb on) tau.val 0 t = some v0.val[t]!.val) :
    kernel.first_row_loop sb ra rb on tau m v0 j0 ⦃ r =>
      1 ≤ r.length ∧ r.length ≤ m.val + 1 ∧
      (∀ t < r.length, r.val[t]!.val = sumU (sb.val.take t)) ∧
      (∀ t < r.length, g.P (hK ra rb on) tau.val 0 t = some r.val[t]!.val) ∧
      (r.length ≤ m.val → g.P (hK ra rb on) tau.val 0 r.length = none) ⦄ := by
  unfold kernel.first_row_loop
  apply loop.spec_decr_nat
    (measure := fun p => m.val + 1 - p.2.val)
    (inv := fun p => 1 ≤ p.2.val ∧ p.2.val ≤ m.val + 1 ∧ p.1.length = p.2.val ∧
      (∀ t < p.2.val, p.1.val[t]!.val = sumU (sb.val.take t)) ∧
      (∀ t < p.2.val, g.P (hK ra rb on) tau.val 0 t = some p.1.val[t]!.val))
  · intro p hp
    obtain ⟨v, j⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    dsimp only at h1 h2 h3 h4 h5 ⊢
    unfold kernel.first_row_loop.body
    split
    · have hjm : j.val ≤ m.val := by scalar_tac
      have hjrb : j.val < rb.val.length := by omega
      have hsj := step_sum sb v j.val h1 (by omega) h3 h4
      have hle := sumU_take_le sb.val j.val
      have hbj := hK_le ra rb on 0 j.val hra hrb hra0 hjrb
      step*
      · have hi' : i.val = j.val - 1 := by scalar_tac
        have e1 : i1.val = v.val[i.val]!.val := by rw [i1_post, getElem_bang_eq _ _ (by scalar_tac)]
        have e2 : i2.val = sb.val[i.val]!.val := by rw [i2_post, getElem_bang_eq _ _ (by scalar_tac)]
        rw [hi'] at e1 e2
        scalar_tac
      · have hi' : i.val = j.val - 1 := by scalar_tac
        have e1 : i1.val = v.val[i.val]!.val := by rw [i1_post, getElem_bang_eq _ _ (by scalar_tac)]
        have e2 : i2.val = sb.val[i.val]!.val := by rw [i2_post, getElem_bang_eq _ _ (by scalar_tac)]
        rw [hi'] at e1 e2
        scalar_tac
      · have hi' : i.val = j.val - 1 := by scalar_tac
        have e1 : i1.val = v.val[i.val]!.val := by rw [i1_post, getElem_bang_eq _ _ (by scalar_tac)]
        have e2 : i2.val = sb.val[i.val]!.val := by rw [i2_post, getElem_bang_eq _ _ (by scalar_tac)]
        rw [hi'] at e1 e2
        have hgt : tau.val < i4.val := by scalar_tac
        refine ⟨by omega, by omega, fun t ht => h4 t (by omega), fun t ht => h5 t (by omega), fun _ => ?_⟩
        have hP' := h5 (j.val - 1) (by omega)
        have hs := P0_succ g (hK ra rb on) tau.val (j.val - 1) (v.val[j.val - 1]!.val) hP'
        rw [show j.val - 1 + 1 = j.val by omega] at hs
        rw [h3, hs]
        have hn : ¬ (v.val[j.val - 1]!.val + g.sb (j.val - 1) + hK ra rb on 0 j.val ≤ tau.val) := by
          rw [hgsb]; omega
        rw [if_neg hn]
      · have hi' : i.val = j.val - 1 := by scalar_tac
        have e1 : i1.val = v.val[i.val]!.val := by rw [i1_post, getElem_bang_eq _ _ (by scalar_tac)]
        have e2 : i2.val = sb.val[i.val]!.val := by rw [i2_post, getElem_bang_eq _ _ (by scalar_tac)]
        rw [hi'] at e1 e2
        have hle' : i4.val ≤ tau.val := by scalar_tac
        have hlen1 : v01.length = v.length + 1 := by simp [alloc.vec.Vec.length, v01_post]
        have hP' := h5 (j.val - 1) (by omega)
        have hs := P0_succ g (hK ra rb on) tau.val (j.val - 1) (v.val[j.val - 1]!.val) hP'
        rw [show j.val - 1 + 1 = j.val by omega] at hs
        have hy : v.val[j.val - 1]!.val + g.sb (j.val - 1) + hK ra rb on 0 j.val ≤ tau.val := by
          rw [hgsb]; omega
        rw [if_pos hy] at hs
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rcases Nat.lt_or_ge t v.length with h | h
          · have := h4 t (by omega)
            simpa [v01_post, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h] using this
          · have ht' : t = j.val := by omega
            have h6 : (v01.val)[v.val.length]!.val = f.val := by
              rw [v01_post]; simp [List.getElem!_eq_getElem?_getD]
            have h7 : v.val.length = j.val := h3
            rw [h7] at h6
            rw [ht', h6, f_post, e1, e2, hsj]
        · intro t ht
          rcases Nat.lt_or_ge t v.length with h | h
          · have := h5 t (by omega)
            rw [this]
            simp [v01_post, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]
          · have ht' : t = j.val := by omega
            have h6 : (v01.val)[v.val.length]!.val = f.val := by
              rw [v01_post]; simp [List.getElem!_eq_getElem?_getD]
            have h7 : v.val.length = j.val := h3
            rw [h7] at h6
            rw [ht', h6, hs, f_post, e1, e2, hgsb]
    · rename_i hnot
      refine ⟨by omega, by omega, fun t ht => h4 t (by omega), fun t ht => h5 t (by omega), fun hle => by exfalso; scalar_tac⟩
  · exact ⟨hj0, hj1, hlen, hpre, hP⟩

/-- `first_row` is the model's row 0: it agrees with `P` on every column, is non-empty, starts at
column 0, and holds only words `<= INF`. -/
theorem first_row_spec (g : Grid) (sb ra rb : Slice Std.U32) (on : Bool) (tau : Std.U32)
    (hgsb : ∀ j, g.sb j = sb.val[j]!.val) (hsum : sumU sb.val < 2 ^ 27)
    (hra : ∀ i < ra.val.length, ra.val[i]!.val ≤ 2 ^ 27) (hrb : ∀ i < rb.val.length, rb.val[i]!.val ≤ 2 ^ 27)
    (hra0 : 0 < ra.val.length) (hrbm : sb.val.length < rb.val.length) (htau : tau.val < INFn)
    (htau0 : hK ra rb on 0 0 ≤ tau.val) :
    kernel.first_row sb ra rb on tau ⦃ r =>
      r.lo.val = 0 ∧ 0 < r.v.length ∧ r.v.length ≤ sb.val.length + 1 ∧
      (∀ t < r.v.length, r.v.val[t]!.val ≤ INFn) ∧
      (∀ j, j ≤ sb.val.length → rowSem r j = enc (g.P (hK ra rb on) tau.val 0 j)) ∧
      (∀ j, sb.val.length < j → rowSem r j = INFn) ⦄ := by
  unfold kernel.first_row
  have hlenx : (Slice.len sb).val = sb.val.length := by simp [Slice.len]
  step as ⟨v0, hv0⟩
  have hv0len : v0.length = 1 := by simp [alloc.vec.Vec.length, hv0, alloc.vec.Vec.new]
  have hv00 : v0.val[0]!.val = 0 := by
    rw [hv0]; simp [alloc.vec.Vec.new, List.getElem!_eq_getElem?_getD]
  have hP0 : g.P (hK ra rb on) tau.val 0 0 = some 0 := by
    simp [Grid.P, keep, htau0]
  step with first_row_loop_spec g sb ra rb on tau (Slice.len sb) v0 1#usize hgsb hlenx hsum hra hrb hra0
    (by omega) htau (by simp) (by scalar_tac) (by simpa using hv0len)
    (by intro t ht; have ht' : t = 0 := by scalar_tac
        subst ht'; rw [hv00]; simp [sumU])
    (by intro t ht; have ht' : t = 0 := by scalar_tac
        subst ht'; rw [hP0, hv00]) as ⟨v01, hl1, hl2, hl3, hl4, hl5⟩
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_⟩
  · intro t ht
    have := hl3 t ht
    have h2 := sumU_take_le sb.val t
    unfold INFn; omega
  · intro j hj
    unfold rowSem
    simp only [Nat.not_lt_zero, if_false]
    show (if j - 0 < v01.length then v01.val[j - 0]!.val else INFn) = _
    by_cases hjl : j < v01.length
    · rw [if_pos (by omega)]
      have := hl4 j hjl
      rw [this]; simp [enc]
    · rw [if_neg (by omega)]
      have hn : g.P (hK ra rb on) tau.val 0 v01.length = none := hl5 (by omega)
      have := P0_none_from g (hK ra rb on) tau.val v01.length hn (j - v01.length)
      rw [show v01.length + (j - v01.length) = j by omega] at this
      rw [this]; simp [enc]
  · intro j hj
    unfold rowSem
    simp only [Nat.not_lt_zero, if_false]
    show (if j - 0 < v01.length then v01.val[j - 0]!.val else INFn) = _
    rw [if_neg (by omega)]

end difffold_kernel_extract
