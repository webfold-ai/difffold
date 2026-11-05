import MirrorD
/-! The parent of a node is its nearest ancestor. Depth goes up by one from a node to its parent, and the
parent relation is carried to the mirror image by `pim`. -/
namespace Ted

/-- `p` is the parent of `c`: the nearest ancestor of `c` (the ancestor with the smallest index). -/
def Par (la : Nat → Nat) (n c p : Nat) : Prop := Anc la c p ∧ p ≤ n ∧ ∀ w, Anc la c w → p ≤ w

section
variable {la : Nat → Nat} {n : Nat}

theorem dep_par (hA : WfL la) {c p : Nat} (hc : 1 ≤ c) (h : Par la n c p) : dep la n c = dep la n p + 1 := by
  obtain ⟨⟨hcp, hlp⟩, hpn, hmin⟩ := h
  have e : n - c = (p - c) + (n - p) := by omega
  have h1 : dep la n c = cn (fun w => decide (la w ≤ c)) (c + 1) (p - c) +
      cn (fun w => decide (la w ≤ c)) (p + 1) (n - p) := by
    unfold dep; rw [e, cn_add]
    have : c + 1 + (p - c) = p + 1 := by omega
    rw [this]
  have h2 : cn (fun w => decide (la w ≤ c)) (p + 1) (n - p) = dep la n p := by
    unfold dep
    apply cn_congr
    intro w hw1 hw2
    by_cases hc' : la w ≤ p
    · have := hA.2 w p hc' (by omega)
      have e1 : decide (la w ≤ c) = true := by simp; omega
      have e2 : decide (la w ≤ p) = true := by simp; omega
      rw [e1, e2]
    · have e1 : decide (la w ≤ c) = false := by simp; omega
      have e2 : decide (la w ≤ p) = false := by simp; omega
      rw [e1, e2]
  have h3 : cn (fun w => decide (la w ≤ c)) (c + 1) (p - c) =
      cn (fun w => decide (la w ≤ c)) (c + 1) (p - c - 1) + 1 := by
    have : p - c = (p - c - 1) + 1 := by omega
    rw [this]; simp only [cn]
    have : c + 1 + (p - c - 1) = p := by omega
    simp [this, hlp]
  have h4 : cn (fun w => decide (la w ≤ c)) (c + 1) (p - c - 1) = 0 := by
    apply cn_zero
    intro w hw1 hw2
    simp only [decide_eq_false_iff_not]
    intro hh
    have := hmin w ⟨by omega, hh⟩
    omega
  omega

theorem min_exists (P : Nat → Prop) : ∀ k, P k → ∃ w, P w ∧ ∀ v, P v → w ≤ v := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h : ∃ v, v < k ∧ P v
    · obtain ⟨v, hv, hPv⟩ := h
      exact ih v hv hPv
    · exact ⟨k, hk, fun v hv => by
        by_cases hlt : v < k
        · exact absurd ⟨v, hlt, hv⟩ h
        · omega⟩

theorem par_exists (hA : WfL la) (hroot : la n = 1) {c : Nat} (hc : 1 ≤ c) (hcn : c < n) :
    ∃ p, Par la n c p := by
  obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := min_exists (fun w => Anc la c w ∧ w ≤ n) n ⟨⟨hcn, by omega⟩, Nat.le_refl _⟩
  refine ⟨p, hp1, hp2, fun w hw => ?_⟩
  by_cases hwn : w ≤ n
  · exact hp3 w ⟨hw, hwn⟩
  · omega

theorem par_unique {c p q : Nat} (h1 : Par la n c p) (h2 : Par la n c q) : p = q :=
  Nat.le_antisymm (h1.2.2 q h2.1) (h2.2.2 p h1.1)

theorem anc_between {c p w : Nat} (h1 : Anc la c p) (h2 : Anc la c w) (hpw : p < w) : Anc la p w :=
  ⟨hpw, by have := h1.1; have := h2.2; omega⟩

theorem par_mirror (hA : WfL la) {la' : Nat → Nat}
    (hla' : ∀ x, 1 ≤ x → x ≤ n → la' (pim la n x) = n + 1 - Qp la n x)
    (hbig : ∀ u, n < u → la' u = u)
    {c p : Nat} (hc : 1 ≤ c) (hcn : c ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n) :
    Par la' n (pim la n c) (pim la n p) ↔ Par la n c p := by
  constructor
  · rintro ⟨ha, _, hmin⟩
    have ha' := (anc_mirror hA hla' hc hcn hp hpn).mp ha
    refine ⟨ha', hpn, fun w hw => ?_⟩
    by_cases hwn : w ≤ n
    · have hw1 : 1 ≤ w := by have := hw.1; omega
      have h2 := (anc_mirror hA hla' hc hcn hw1 hwn).mpr hw
      have h3 := hmin _ h2
      by_cases hlt : w < p
      · have := anc_between hw ha' hlt
        have := (anc_mirror hA hla' hw1 hwn hp hpn).mpr this
        have := this.1
        omega
      · omega
    · omega
  · rintro ⟨ha, _, hmin⟩
    have ha' := (anc_mirror hA hla' hc hcn hp hpn).mpr ha
    refine ⟨ha', (pim_mem hA hp hpn).2, fun w' hw' => ?_⟩
    by_cases hwn : w' ≤ n
    · have hw1 : 1 ≤ w' := by have := hw'.1; omega
      obtain ⟨w, hw1', hwn', rfl⟩ := pim_surj hA hw1 hwn
      have h2 := (anc_mirror hA hla' hc hcn hw1' hwn').mp hw'
      have h3 := hmin w h2
      by_cases hlt : p < w
      · have := anc_between ha h2 hlt
        have := (anc_mirror hA hla' hp hpn hw1' hwn').mpr this
        have := this.1
        omega
      · have : p = w := by omega
        rw [this]; exact Nat.le_refl _
    · have := hbig w' (by omega)
      have h4 := hw'.2
      have h5 := hw'.1
      omega

end
end Ted
