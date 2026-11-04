import DifffoldKernel
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract

/-- Sum of a list of `U32` values as a natural number. -/
def sumU (l : List Std.U32) : Nat := (l.map (fun v => v.val)).sum

theorem sumU_cons (a : Std.U32) (l : List Std.U32) : sumU (a :: l) = a.val + sumU l := by
  simp [sumU]

theorem sumU_nil : sumU ([] : List Std.U32) = 0 := by simp [sumU]

/-- Loop 0 of `suffix_sums` pushes zeros until the vector has `n + 1` entries. -/
@[step] theorem suffix_sums_loop0_spec (n : Std.Usize) (out : alloc.vec.Vec Std.U32) (k : Std.Usize)
    (hn : n.val < 2 ^ 31) (hk : k.val ≤ n.val + 1) (hlen : out.length = k.val)
    (hz : ∀ i < out.length, out.val[i]!.val = 0) :
    kernel.suffix_sums_loop0 n out k ⦃ r => r.length = n.val + 1 ∧ ∀ i < r.length, r.val[i]!.val = 0 ⦄ := by
  unfold kernel.suffix_sums_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val + 1 - p.2.val)
    (inv := fun p => p.2.val ≤ n.val + 1 ∧ p.1.length = p.2.val ∧ ∀ i < p.1.length, p.1.val[i]!.val = 0)
  · intro p hp
    obtain ⟨o, c⟩ := p
    obtain ⟨hc, hl, hzz⟩ := hp
    unfold kernel.suffix_sums_loop0.body
    dsimp only at hc hl hzz ⊢
    split
    · step*
      have hlen1 : out1.length = o.length + 1 := by simp [alloc.vec.Vec.length, out1_post]
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      intro i hi
      rcases Nat.lt_or_ge i o.length with h | h
      · have := hzz i h
        simpa [out1_post, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h] using this
      · have hi' : i = o.length := by omega
        subst hi'
        simp [out1_post, List.getElem!_eq_getElem?_getD, alloc.vec.Vec.length] at *
    · rename_i hnot
      refine ⟨?_, hzz⟩
      scalar_tac
  · exact ⟨hk, hlen, hz⟩

theorem sumU_drop_succ (l : List Std.U32) (i : Nat) (h : i < l.length) :
    sumU (l.drop i) = (l[i]'h).val + sumU (l.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h, sumU_cons]

theorem sumU_drop_le (l : List Std.U32) (i : Nat) : sumU (l.drop i) ≤ sumU l := by
  have := List.take_append_drop i l
  have h2 : sumU l = sumU (l.take i) + sumU (l.drop i) := by
    conv_lhs => rw [← List.take_append_drop i l]
    simp [sumU, List.map_append, List.sum_append]
  omega

/-- Loop 1 of `suffix_sums` fills the vector from the back. -/
@[step] theorem suffix_sums_loop1_spec (x : Slice Std.U32) (out : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hs : sumU x.val < 2 ^ 32) (hn : x.val.length < 2 ^ 31)
    (hi : i.val ≤ x.val.length) (hlen : out.length = x.val.length + 1)
    (hinv : ∀ idx, i.val ≤ idx → idx ≤ x.val.length → out.val[idx]!.val = sumU (x.val.drop idx)) :
    kernel.suffix_sums_loop1 x out i ⦃ r =>
      r.length = x.val.length + 1 ∧
      ∀ idx, idx ≤ x.val.length → r.val[idx]!.val = sumU (x.val.drop idx) ⦄ := by
  unfold kernel.suffix_sums_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.2.val)
    (inv := fun p => p.2.val ≤ x.val.length ∧ p.1.length = x.val.length + 1 ∧
      ∀ idx, p.2.val ≤ idx → idx ≤ x.val.length → p.1.val[idx]!.val = sumU (x.val.drop idx))
  · intro p hp
    obtain ⟨o, c⟩ := p
    obtain ⟨hc, hl, hinv'⟩ := hp
    unfold kernel.suffix_sums_loop1.body
    dsimp only at hc hl hinv' ⊢
    split
    · have hl' : o.val.length = x.val.length + 1 := hl
      have hcpos : c.val ≥ 1 := by scalar_tac
      step*
      · -- no overflow in `i3 + i4`
        have hk : i1.val < x.val.length := by omega
        have hi2 : i2.val = c.val := by omega
        have hb2 : i2.val < o.val.length := by omega
        have e3 : i3.val = sumU (x.val.drop c.val) := by
          have h0 := hinv' c.val le_rfl hc
          have e : i3.val = (o.val)[i2.val]!.val := by
            rw [i3_post]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb2]
          rw [e, hi2]; exact h0
        have e4 : i4.val = (x.val[i1.val]'hk).val := by rw [i4_post]
        have hsum : i3.val + i4.val = sumU (x.val.drop i1.val) := by
          rw [sumU_drop_succ x.val i1.val hk, e3, e4]
          have : i1.val + 1 = c.val := by omega
          rw [this]; ring
        have hle := sumU_drop_le x.val i1.val
        scalar_tac
      · have hk : i1.val < x.val.length := by omega
        have hi2 : i2.val = c.val := by omega
        have hb2 : i2.val < o.val.length := by omega
        have e3 : i3.val = sumU (x.val.drop c.val) := by
          have h0 := hinv' c.val le_rfl hc
          have e : i3.val = (o.val)[i2.val]!.val := by
            rw [i3_post]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb2]
          rw [e, hi2]; exact h0
        have e4 : i4.val = (x.val[i1.val]'hk).val := by rw [i4_post]
        have hsum : i3.val + i4.val = sumU (x.val.drop i1.val) := by
          rw [sumU_drop_succ x.val i1.val hk, e3, e4]
          have : i1.val + 1 = c.val := by omega
          rw [this]; ring
        subst index_mut_back_post
        have hset := alloc.vec.Vec.set_val_eq o i1 s
        have hb1 : i1.val < o.val.length := by omega
        refine ⟨by omega, ?_, ?_, by omega⟩
        · rw [alloc.vec.Vec.set_length]; exact hl
        · intro idx h1 h2
          by_cases hidx : idx = i1.val
          · subst hidx
            have e : ((o.set i1 s).val)[i1.val]! = s := by
              rw [hset]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_set, hb1]
            rw [e, s_post, hsum]
          · have hge : c.val ≤ idx := by omega
            have e : ((o.set i1 s).val)[idx]! = (o.val)[idx]! := by
              rw [hset]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_set, Ne.symm hidx]
            rw [e]; exact hinv' idx hge h2
    · rename_i hnot
      refine ⟨hl, fun idx hidx => hinv' idx (by scalar_tac) hidx⟩
  · exact ⟨hi, hlen, hinv⟩

/-- `suffix_sums x` returns `n + 1` values, the `i`-th being the sum of `x[i..]`.
Preconditions carried by the extracted checked arithmetic: the list is short enough to push to and
the total fits a `u32`. Stated over the Aeneas translation of the shipped `kernel::suffix_sums`. -/
theorem suffix_sums_spec (x : Slice Std.U32) (hs : sumU x.val < 2 ^ 32) (hn : x.val.length < 2 ^ 31) :
    kernel.suffix_sums x ⦃ out =>
      out.length = x.val.length + 1 ∧
      ∀ idx, idx ≤ x.val.length → out.val[idx]!.val = sumU (x.val.drop idx) ⦄ := by
  unfold kernel.suffix_sums
  have hlenx : (Slice.len x).val = x.val.length := by simp [Slice.len]
  step*
  intro idx h1 h2
  have hidx : idx = x.val.length := by omega
  subst hidx
  have hz := out_post1 x.val.length (by omega)
  rw [hz, List.drop_length, sumU_nil]

end difffold_kernel_extract
