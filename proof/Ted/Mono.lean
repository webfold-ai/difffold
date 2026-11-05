import Mapping
/-! Facts about the true distance `Ted.D` used to justify the pruning of the banded algorithm. All of them go
through the mapping characterization of `Ted.D`. -/
namespace Ted
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat}

/-- Removing the last node of the first range: every cell of row `x` is at least some cell of row `x - 1`
that is not further right. This is why a row whose cells all exceed the threshold ends the table. -/
theorem D_row_step (hA : WfL la) (hB : WfL lb) {l x l' y : Nat} (hl : 1 ≤ l) (hl' : 1 ≤ l')
    (hcA : Closed la l x) (hcB : Closed lb l' y) (hxl : l ≤ x) (hyl : l' ≤ y + 1) :
    ∃ y₀, l' ≤ y₀ + 1 ∧ y₀ ≤ y ∧ D la lb ren l (x - 1) l' y₀ ≤ D la lb ren l x l' y := by
  obtain ⟨M, hv, hr, hc⟩ := exists_map (ren := ren) hA hB _ l x l' y hl hl' hcA hcB rfl
  have hcA' : Closed la l (x - 1) := fun u h h' => hcA u h (by omega)
  by_cases hx : ∃ p ∈ M, p.1 = x
  · obtain ⟨p, hpM, hpx⟩ := hx
    have hpM2 := hr p hpM
    obtain ⟨hlenM, hsumM⟩ := erase_stats (fun p => ren p.1 p.2) hpM
    generalize hM' : M.erase p = M' at hlenM hsumM
    have hsub : M'.Sublist M := hM' ▸ List.erase_sublist
    have hv' := valid_sublist hv hsub
    have hmem : ∀ q ∈ M', q.1 < x ∧ q.2 < p.2 ∧ l ≤ q.1 ∧ l' ≤ q.2 := by
      intro q hq
      have hqM : q ∈ M := hsub.subset hq
      have hne : q ≠ p := ((List.Nodup.mem_erase_iff hv.1).mp (hM' ▸ hq)).1
      have hr1 := hr q hqM
      have hlt : q.1 < x := by
        by_cases e : q.1 = x
        · exact absurd (valid_inj hv q hqM p hpM (by omega)) hne
        · omega
      have := ((hv.2 q hqM p hpM).2.1).mp (by omega)
      exact ⟨hlt, this, hr1.1, hr1.2.2.1⟩
    refine ⟨p.2 - 1, by omega, by omega, ?_⟩
    have hr' : InRange l (x - 1) l' (p.2 - 1) M' := by
      intro q hq; have := hmem q hq; omega
    have hcB' : Closed lb l' (p.2 - 1) := fun u h h' => hcB u h (by omega)
    have h1 := D_le_cost (ren := ren) hA hB _ l (x - 1) l' (p.2 - 1) M' hl hl' hcA' hcB' rfl hv' hr'
    have hl1 := valid_len hv' hr'
    have hl2 := valid_len hv hr
    unfold Cost at h1 hc
    omega
  · have hr' : InRange l (x - 1) l' y M := by
      intro p hp
      have := hr p hp
      have hne : p.1 ≠ x := fun e => hx ⟨p, hp, e⟩
      omega
    refine ⟨y, hyl, Nat.le_refl _, ?_⟩
    have h1 := D_le_cost (ren := ren) hA hB _ l (x - 1) l' y M hl hl' hcA' hcB rfl hv hr'
    have hl2 := valid_len hv hr'
    unfold Cost at h1 hc
    omega

/-- Row minima never decrease: every cell of row `x₂` is at least some cell of row `x₁ <= x₂` that is not
further right. -/
theorem D_row_mono (hA : WfL la) (hB : WfL lb) {l l' : Nat} (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    ∀ (k x₁ x₂ y : Nat), x₂ = x₁ + k → l ≤ x₁ + 1 → Closed la l x₂ → Closed lb l' y → l' ≤ y + 1 →
    ∃ y₀, l' ≤ y₀ + 1 ∧ y₀ ≤ y ∧ D la lb ren l x₁ l' y₀ ≤ D la lb ren l x₂ l' y := by
  intro k
  induction k with
  | zero => intro x₁ x₂ y h _ _ _ hy; exact ⟨y, hy, Nat.le_refl _, by rw [h]; exact Nat.le_refl _⟩
  | succ k ih =>
    intro x₁ x₂ y h h1 hcA hcB hy
    obtain ⟨y₁, hy1, hy2, hd⟩ := D_row_step (ren := ren) hA hB hl hl' hcA hcB (by omega) hy
    have hcA' : Closed la l (x₂ - 1) := fun u hu hu' => hcA u hu (by omega)
    have hcB' : Closed lb l' y₁ := fun u hu hu' => hcB u hu (by omega)
    obtain ⟨y₀, h3, h4, h5⟩ := ih x₁ (x₂ - 1) y₁ (by omega) h1 hcA' hcB' hy1
    exact ⟨y₀, h3, by omega, by omega⟩

end Ted
