import Defs
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract

/-- Loop 0 of `trim_row`: scan forward past pruned cells. -/
@[step] theorem trim_loop0_spec (v : alloc.vec.Vec Std.U32) (first : Std.Usize)
    (hlen : v.length < 2 ^ 31) (hf : first.val ≤ v.length)
    (hz : ∀ t < first.val, INFn ≤ v.val[t]!.val) :
    kernel.trim_row_loop0 v first ⦃ r =>
      r.val ≤ v.length ∧ (∀ t < r.val, INFn ≤ v.val[t]!.val) ∧
      (r.val < v.length → v.val[r.val]!.val < INFn) ⦄ := by
  unfold kernel.trim_row_loop0
  apply loop.spec_decr_nat
    (measure := fun f => v.length - f.val)
    (inv := fun f => f.val ≤ v.length ∧ ∀ t < f.val, INFn ≤ v.val[t]!.val)
  · intro f hf'
    obtain ⟨hf1, hz1⟩ := hf'
    unfold kernel.trim_row_loop0.body
    step*
    · have hfv : f.val < v.val.length := by scalar_tac
      have hi1 : INFn ≤ i1.val := by have hk := kernel_INF_val; scalar_tac
      have e : i1.val = v.val[f.val]!.val := by
        rw [i1_post, getElem_bang_eq _ _ hfv]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro t ht
      rcases Nat.lt_or_ge t f.val with h | h
      · exact hz1 t h
      · have : t = f.val := by scalar_tac
        subst this; omega
    · have hfv : f.val < v.val.length := by scalar_tac
      have hi1 : i1.val < INFn := by have hk := kernel_INF_val; scalar_tac
      have e : i1.val = v.val[f.val]!.val := by
        rw [i1_post, getElem_bang_eq _ _ hfv]
      exact ⟨hf1, hz1, fun _ => by omega⟩
  · exact ⟨hf, hz⟩

/-- Loop 1 of `trim_row`: scan backward past pruned cells. -/
theorem trim_loop1_spec (v : alloc.vec.Vec Std.U32) (first last0 last : Std.Usize)
    (hl0 : last0.val < v.length) (hfl : first.val ≤ last.val) (hll : last.val ≤ last0.val)
    (hfv : v.val[first.val]!.val < INFn)
    (htail : ∀ t, last.val < t → t ≤ last0.val → INFn ≤ v.val[t]!.val) :
    kernel.trim_row_loop1 v last ⦃ r =>
      r.val ≤ last0.val ∧ first.val ≤ r.val ∧ v.val[r.val]!.val < INFn ∧
      (∀ t, r.val < t → t ≤ last0.val → INFn ≤ v.val[t]!.val) ⦄ := by
  unfold kernel.trim_row_loop1
  apply loop.spec_decr_nat
    (measure := fun l => l.val)
    (inv := fun l => l.val ≤ last0.val ∧ first.val ≤ l.val ∧
      ∀ t, l.val < t → t ≤ last0.val → INFn ≤ v.val[t]!.val)
  · intro l hl
    obtain ⟨h1, h2, h3⟩ := hl
    unfold kernel.trim_row_loop1.body
    step*
    · have hlv : l.val < v.val.length := by scalar_tac
      have hi : INFn ≤ i.val := by have hk := kernel_INF_val; scalar_tac
      have e : i.val = v.val[l.val]!.val := by rw [i_post, getElem_bang_eq _ _ hlv]
      have hne : first.val ≠ l.val := by
        intro h; rw [h] at hfv; omega
      scalar_tac
    · have hlv : l.val < v.val.length := by scalar_tac
      have hi : INFn ≤ i.val := by have hk := kernel_INF_val; scalar_tac
      have e : i.val = v.val[l.val]!.val := by rw [i_post, getElem_bang_eq _ _ hlv]
      have hne : first.val ≠ l.val := by
        intro h; rw [h] at hfv; omega
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      intro t ht1 ht2
      by_cases hh : t = l.val
      · subst hh; omega
      · exact h3 t (by scalar_tac) ht2
    · have hlv : l.val < v.val.length := by scalar_tac
      have hi : i.val < INFn := by have hk := kernel_INF_val; scalar_tac
      have e : i.val = v.val[l.val]!.val := by rw [i_post, getElem_bang_eq _ _ hlv]
      exact ⟨h1, h2, by omega, h3⟩
  · exact ⟨hll, hfl, htail⟩

/-- Loop 2 of `trim_row`: copy `v[first ..= last]`. -/
theorem trim_loop2_spec (v kept : alloc.vec.Vec Std.U32) (first last k : Std.Usize)
    (hl : last.val < v.length) (hfk : first.val ≤ k.val) (hkl : k.val ≤ last.val + 1)
    (hkept : kept.length = k.val - first.val)
    (hel : ∀ t < kept.length, kept.val[t]!.val = v.val[first.val + t]!.val) :
    kernel.trim_row_loop2 v last kept k ⦃ r =>
      r.length = last.val + 1 - first.val ∧
      ∀ t < r.length, r.val[t]!.val = v.val[first.val + t]!.val ⦄ := by
  unfold kernel.trim_row_loop2
  apply loop.spec_decr_nat
    (measure := fun p => last.val + 1 - p.2.val)
    (inv := fun p => first.val ≤ p.2.val ∧ p.2.val ≤ last.val + 1 ∧
      p.1.length = p.2.val - first.val ∧
      ∀ t < p.1.length, p.1.val[t]!.val = v.val[first.val + t]!.val)
  · intro p hp
    obtain ⟨kr, kk⟩ := p
    obtain ⟨h1, h2, h3, h4⟩ := hp
    dsimp only at h1 h2 h3 h4 ⊢
    unfold kernel.trim_row_loop2.body
    split
    · step*
      have hkv : kk.val < v.val.length := by scalar_tac
      have e : i.val = v.val[kk.val]!.val := by rw [i_post, getElem_bang_eq _ _ hkv]
      have hlen1 : kept_row1.length = kr.length + 1 := by simp [alloc.vec.Vec.length, kept_row1_post]
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      intro t ht
      rcases Nat.lt_or_ge t kr.length with h | h
      · have := h4 t h
        simpa [kept_row1_post, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h] using this
      · have ht' : t = kr.length := by omega
        subst ht'
        have hf : first.val + kr.length = kk.val := by omega
        have h5 : (kept_row1.val)[kr.val.length]!.val = i.val := by
          rw [kept_row1_post]; simp [List.getElem!_eq_getElem?_getD]
        have h6 : kr.val.length = kr.length := rfl
        rw [h6] at h5
        rw [h5, e, hf]
    · rename_i hnot
      exact ⟨by scalar_tac, h4⟩
  · exact ⟨hfk, hkl, hkept, hel⟩

/-- `trim_row` drops the pruned cells at both ends and preserves what the row says about every
column. `none` means every cell was pruned. -/
theorem trim_row_spec (v : alloc.vec.Vec Std.U32) (plo : Std.Usize)
    (hlen : v.length < 2 ^ 31) (hplo : plo.val < 2 ^ 31)
    (hv : ∀ t < v.length, v.val[t]!.val ≤ INFn) :
    kernel.trim_row v plo ⦃ r =>
      match r with
      | none => ∀ t < v.length, v.val[t]!.val = INFn
      | some row => 0 < row.v.length ∧ plo.val ≤ row.lo.val ∧
          row.lo.val + row.v.length ≤ plo.val + v.length ∧
          ∀ j, rowSem row j = rawSem v plo.val j ⦄ := by
  unfold kernel.trim_row
  step as ⟨first, hfa, hfb, hfc⟩
  split
  · rename_i heq
    have hfl : first.val = v.length := by scalar_tac
    rw [WP.spec_ok]
    intro t ht
    have h1 := hfb t (by omega)
    have h2 := hv t ht
    omega
  · rename_i hne
    have hfl : first.val < v.length := by scalar_tac
    have hfv := hfc hfl
    step as ⟨last0, hlast0⟩
    have hl0 : last0.val < v.length := by scalar_tac
    have hfl0 : first.val ≤ last0.val := by scalar_tac
    step with trim_loop1_spec v first last0 last0 hl0 hfl0 le_rfl hfv (fun t h1 h2 => by omega) as ⟨last1, hl1a, hl1b, hl1c, hl1d⟩
    step with trim_loop2_spec v (alloc.vec.Vec.new Std.U32) first last1 first (by scalar_tac) le_rfl (by scalar_tac) (by simp [alloc.vec.Vec.length, alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.length, alloc.vec.Vec.new]) as ⟨kept, hk1, hk2⟩
    step as ⟨lo, hlo⟩
    have hl0' : last0.val + 1 = v.length := by scalar_tac
    have hk1' : kept.length + first.val = last1.val + 1 := by scalar_tac
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j
    unfold rowSem rawSem
    dsimp only
    by_cases hj1 : j < plo.val
    · have h2 : j < lo.val := by omega
      rw [if_pos h2, if_pos hj1]
    · rw [if_neg hj1]
      by_cases hj2 : j < lo.val
      · have ht : j - plo.val < first.val := by omega
        have h1 := hfb (j - plo.val) ht
        have h2 := hv (j - plo.val) (by omega)
        have hlt : j - plo.val < v.length := by omega
        rw [if_pos hj2, if_pos hlt]; omega
      · rw [if_neg hj2]
        by_cases hj3 : j - lo.val < kept.length
        · have hlt : j - plo.val < v.length := by omega
          rw [if_pos hj3, if_pos hlt, hk2 _ hj3]
          have : first.val + (j - lo.val) = j - plo.val := by omega
          rw [this]
        · rw [if_neg hj3]
          by_cases hlt : j - plo.val < v.length
          · rw [if_pos hlt]
            have h1 := hl1d (j - plo.val) (by omega) (by omega)
            have h2 := hv (j - plo.val) hlt
            omega
          · rw [if_neg hlt]

end difffold_kernel_extract
