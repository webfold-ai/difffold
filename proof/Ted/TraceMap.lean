import TraceTop
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The mapping read off the image table. -/

theorem Pto_succ (k : Nat) (tb : List Std.Usize) :
    Pto (k + 1) tb = Pto k tb ++ (if (tb[k + 1]!).val = 0 then [] else [(k + 1, (tb[k + 1]!).val)]) := by
  unfold Pto
  rw [List.range'_concat, List.filterMap_append]
  congr 1
  have e : 1 + 1 * k = k + 1 := by omega
  rw [e, List.filterMap_cons, List.filterMap_nil]
  by_cases h : (tb[k + 1]!).val = 0
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem Pto_length_le (k : Nat) (tb : List Std.Usize) : (Pto k tb).length ≤ k := by
  induction k with
  | zero => simp [Pto]
  | succ k ih =>
    rw [Pto_succ, List.length_append]
    split <;> simp <;> omega

theorem pairs_loop_spec (to_b : alloc.vec.Vec Std.Usize) (n : Std.Usize) (pairs : alloc.vec.Vec (Std.U32 × Std.U32))
    (x : Std.Usize) (hn : n.val < 2 ^ 14) (hlen : to_b.length = n.val + 1)
    (hy : ∀ k, 1 ≤ k → k ≤ n.val → (to_b.val[k]!).val < 2 ^ 32)
    (hx : 1 ≤ x.val ∧ x.val ≤ n.val + 1) (hp : Mp pairs.val = Pto (x.val - 1) to_b.val) :
    ted.ted_mapping_with_loop to_b n pairs x ⦃ r => Mp r.val = Pto n.val to_b.val ⦄ := by
  unfold ted.ted_mapping_with_loop
  have hUM : 2 ^ 32 ≤ Std.Usize.max + 1 := by scalar_tac
  have hlen' : to_b.val.length = n.val + 1 := hlen
  apply loop.spec_decr_nat
    (measure := fun s => n.val + 1 - s.2.val)
    (inv := fun s => 1 ≤ s.2.val ∧ s.2.val ≤ n.val + 1 ∧ Mp s.1.val = Pto (s.2.val - 1) to_b.val)
  · intro s hs
    obtain ⟨pairs1, x1⟩ := s
    obtain ⟨h1, h2, h3⟩ := hs
    dsimp only at h1 h2 h3 ⊢
    unfold ted.ted_mapping_with_loop.body
    have hl : pairs1.val.length ≤ x1.val - 1 := by
      have e : (Mp pairs1.val).length = pairs1.val.length := by simp [Mp]
      have := Pto_length_le (x1.val - 1) to_b.val
      rw [← h3] at this
      omega
    by_cases hle : x1 ≤ n
    · rw [if_pos hle]
      have hxn : x1.val ≤ n.val := hle
      step as ⟨y, hy'⟩
      have hyv : y.val = (to_b.val[x1.val]!).val := by rw [hy', getG_eq _ _ (by have := hlen'; omega)]
      have hsucc : x1.val - 1 + 1 = x1.val := by omega
      have hsuccP : Pto x1.val to_b.val = Pto (x1.val - 1) to_b.val ++
          (if (to_b.val[x1.val]!).val = 0 then [] else [(x1.val, (to_b.val[x1.val]!).val)]) := by
        have := Pto_succ (x1.val - 1) to_b.val
        rw [hsucc] at this
        exact this
      split
      · rename_i hne
        have hne1 : ¬ y = 0#usize := by simpa using hne
        have hne' : y.val ≠ 0 := fun h0 => hne1 (UScalar.eq_of_val_eq (by simpa using h0))
        have hyb := hy x1.val h1 hxn
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        have hiv : i.val = x1.val := by
          rw [hi, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
          exact Nat.mod_eq_of_lt (by omega)
        have hi1v : i1.val = y.val := by
          rw [hi1, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
          exact Nat.mod_eq_of_lt (by omega)
        step as ⟨pairs2, hpairs2⟩
        step as ⟨x2, hx2⟩
        have hnz : (to_b.val[x1.val]!).val ≠ 0 := by rw [← hyv]; exact hne'
        refine ⟨by omega, by omega, ?_, by omega⟩
        show Mp pairs2.val = Pto (x2.val - 1) to_b.val
        have e2 : x2.val - 1 = x1.val := by omega
        rw [e2, hsuccP, if_neg hnz, hpairs2]
        simp only [Mp, List.map_append, List.map_cons, List.map_nil]
        have h3' : pairs1.val.map (fun p => (p.1.val, p.2.val)) = Pto (x1.val - 1) to_b.val := h3
        rw [h3', hiv, hi1v, hyv]
      · rename_i hne
        have hne1 : y.val = 0 := by simpa using hne
        have hz : (to_b.val[x1.val]!).val = 0 := by rw [← hyv, hne1]
        step as ⟨x2, hx2⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        show Mp pairs1.val = Pto (x2.val - 1) to_b.val
        have e2 : x2.val - 1 = x1.val := by omega
        rw [e2, hsuccP, if_pos hz, List.append_nil]
        exact h3
    · rw [if_neg hle]
      simp only [WP.spec_ok]
      have : x1.val = n.val + 1 := by have : ¬ x1.val ≤ n.val := hle; omega
      rw [h3, this]
      rfl
  · exact ⟨hx.1, hx.2, hp⟩

theorem is_empty_false (a : ted.PostTree) (hA : PT.Wf a) : ted.PostTree.is_empty a = ok false := by
  unfold ted.PostTree.is_empty
  have : alloc.vec.Vec.len a.label ≠ 0#usize := by
    intro h
    have := alloc.vec.Vec.len_val a.label
    have h2 : (alloc.vec.Vec.len a.label).val = 0 := by rw [h]; rfl
    have := hA.pos; omega
  simp [this]

theorem ted_val_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (hlb : ∀ j < b.label.length, (b.label.val[j]!).val < 2 ^ 31) :
    ted.ted a b ⦃ c => c.val = TED a b ⦄ := by
  unfold ted.ted
  refine WP.spec_bind (ted_stats_spec a b hA hB hna hnb hla hlb) ?_
  rintro ⟨c, st⟩ hc
  show ok c ⦃ c => c.val = TED a b ⦄
  simp only [WP.spec_ok]
  exact hc

/-- The mapping returned by `ted_mapping_with` is a legal mapping of the two trees whose cost is their distance. -/
theorem ted_mapping_with_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b)
    (hna : a.label.length < 2 ^ 14) (hnb : b.label.length < 2 ^ 14)
    (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (hlb : ∀ j < b.label.length, (b.label.val[j]!).val < 2 ^ 31) (prefer_match : Bool) :
    ted.ted_mapping_with a b prefer_match ⦃ r => r.cost.val = TED a b ∧
      Valid (laOf a) (laOf b) (Mp r.pairs.val) ∧ InRange 1 a.label.length 1 b.label.length (Mp r.pairs.val) ∧
      Cost (rcost a b) 1 a.label.length 1 b.label.length (Mp r.pairs.val) = TED a b ⦄ := by
  unfold ted.ted_mapping_with
  refine WP.spec_bind (ted_val_spec a b hA hB hna hnb hla hlb) ?_
  intro cost hcost
  simp only [is_empty_false a hA, is_empty_false b hB, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (traceback_spec a b hA hB hna hnb cost prefer_match hcost) ?_
  intro to_b ⟨hlen, hSol⟩
  simp only [ted.PostTree.len, bind_tc_ok]
  have hlenA : (alloc.vec.Vec.len a.label).val = a.label.length := by rw [alloc.vec.Vec.len_val]
  have hy : ∀ k, 1 ≤ k → k ≤ (alloc.vec.Vec.len a.label).val → (to_b.val[k]!).val < 2 ^ 32 := by
    intro k hk1 hk2
    by_cases h0 : (to_b.val[k]!).val = 0
    · rw [h0]; omega
    · have hmem : (k, (to_b.val[k]!).val) ∈ Pto a.label.length to_b.val :=
        mem_Pto.mpr ⟨hk1, by omega, rfl, h0⟩
      have := hSol.2.1 _ hmem
      simp only at this
      omega
  refine WP.spec_bind (pairs_loop_spec to_b (alloc.vec.Vec.len a.label) (alloc.vec.Vec.new (Std.U32 × Std.U32))
    1#usize (by omega) (by rw [hlenA]; exact hlen) hy (by simp) (by simp [Mp, Pto])) ?_
  intro pairs hpairs
  simp only [WP.spec_ok]
  rw [hpairs, hlenA]
  obtain ⟨hv, hr, hc⟩ := hSol
  exact ⟨hcost, hv, hr, by rw [hc]; rfl⟩

end difffold_lines_extract
