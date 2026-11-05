import Mapping
/-! The keyroot of a node: the last node of the postorder with the same leftmost leaf. Plain Lean. -/
namespace Ted

/-- Some node `k` at or after `x` is the last with its leftmost leaf. -/
theorem kr_exists (la : Nat → Nat) (n : Nat) : ∀ (d x : Nat), n - x = d → x ≤ n →
    ∃ k, x ≤ k ∧ k ≤ n ∧ la k = la x ∧ ∀ v, k < v → v ≤ n → la v ≠ la x := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro x hd hx
  by_cases h : ∃ v, x < v ∧ v ≤ n ∧ la v = la x
  · obtain ⟨v, hv1, hv2, hv3⟩ := h
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (n - v) (by omega) v rfl hv2
    exact ⟨k, by omega, hk2, by rw [hk3, hv3], fun w hw1 hw2 => by rw [← hv3]; exact hk4 w hw1 hw2⟩
  · refine ⟨x, Nat.le_refl _, hx, rfl, fun v hv1 hv2 hv3 => h ⟨v, hv1, hv2, hv3⟩⟩

open Classical in
noncomputable def krf (la : Nat → Nat) (n x : Nat) : Nat :=
  if h : x ≤ n then Classical.choose (kr_exists la n (n - x) x rfl h) else x

theorem krf_spec (la : Nat → Nat) (n x : Nat) (hx : x ≤ n) :
    x ≤ krf la n x ∧ krf la n x ≤ n ∧ la (krf la n x) = la x ∧
      ∀ v, krf la n x < v → v ≤ n → la v ≠ la x := by
  unfold krf
  rw [dif_pos hx]
  exact Classical.choose_spec (kr_exists la n (n - x) x rfl hx)

/-- The keyroot of a node that is itself last with its leftmost leaf is the node. -/
theorem krf_self (la : Nat → Nat) (n x : Nat) (hx : x ≤ n) (hl : ∀ v, x < v → v ≤ n → la v ≠ la x) :
    krf la n x = x := by
  obtain ⟨h1, h2, h3, h4⟩ := krf_spec la n x hx
  by_cases e : krf la n x = x
  · exact e
  · exact absurd h3 (hl _ (by omega) h2)

/-- Same leftmost leaf means same keyroot. -/
theorem krf_congr (la : Nat → Nat) (n x y : Nat) (hx : x ≤ n) (hy : y ≤ n) (h : la x = la y) :
    krf la n x = krf la n y := by
  obtain ⟨a1, a2, a3, a4⟩ := krf_spec la n x hx
  obtain ⟨b1, b2, b3, b4⟩ := krf_spec la n y hy
  by_cases e : krf la n x < krf la n y
  · exact absurd (by rw [b3, ← h, ← a3] : la (krf la n y) = la (krf la n x)) (a4 _ e b2 |> fun hh => by rw [a3] at hh ⊢; sorry)
  · sorry

end Ted
