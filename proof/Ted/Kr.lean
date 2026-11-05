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
  by_cases e1 : krf la n x < krf la n y
  · exact absurd (by rw [b3, h]) (a4 _ e1 b2)
  · by_cases e2 : krf la n y < krf la n x
    · exact absurd (by rw [a3, h]) (b4 _ e2 a2)
    · omega

/-- If `x` lies inside the subtree interval of `u` (`la u <= x <= u`) but has another leftmost leaf, its
keyroot comes before `u`. -/
theorem kr_lt (la : Nat → Nat) (n : Nat) (hle : ∀ u, la u ≤ u) (hlam : ∀ u v, la u ≤ v → v ≤ u → la u ≤ la v) {x u : Nat}
    (hu : u ≤ n) (hxu : x ≤ u) (hx1 : la u ≤ x) (hne : la x ≠ la u) : krf la n x < u := by
  have hx : x ≤ n := by omega
  obtain ⟨a1, a2, a3, a4⟩ := krf_spec la n x hx
  have hgt : la u < la x := by have := hlam u x hx1 hxu; omega
  by_cases e : krf la n x = u
  · have h := a3
    rw [e] at h
    exact absurd h.symm hne
  · by_cases e2 : u < krf la n x
    · -- u lies inside the subtree of the keyroot
      have := hlam (krf la n x) u (by rw [a3]; have := hle x; omega) (by omega)
      rw [a3] at this
      omega
    · omega

section sorted
variable {K : List Nat}

theorem sorted_lt_idx (hs : K.Pairwise (· < ·)) {i j : Nat} (hi : i < K.length) (hj : j < K.length)
    (h : i < j) : K[i] < K[j] := by
  have := List.pairwise_iff_getElem.mp hs i j hi hj h
  exact this

/-- Elements of a strictly sorted list that are smaller than `K[ia]` lie among the first `ia` elements. -/
theorem mem_take_of_lt (hs : K.Pairwise (· < ·)) {ia v : Nat} (hia : ia < K.length) (hv : v ∈ K)
    (hlt : v < K[ia]) : v ∈ K.take ia := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hk2 : k < ia := by
    by_cases e : k < ia
    · exact e
    · by_cases e2 : k = ia
      · subst e2; omega
      · have := sorted_lt_idx hs hia hk (by omega)
        omega
  exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩

theorem lt_of_mem_take (hs : K.Pairwise (· < ·)) {ia v : Nat} (hia : ia < K.length) (hv : v ∈ K.take ia) :
    v < K[ia] := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  simp at hk
  have hk' : k < K.length := by omega
  have := sorted_lt_idx hs hk' hia (by omega)
  simpa using this

theorem take_succ_mem {ia : Nat} (hia : ia < K.length) {v : Nat} :
    v ∈ K.take (ia + 1) ↔ v ∈ K.take ia ∨ v = K[ia] := by
  have e : K.take (ia + 1) = K.take ia ++ [K[ia]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hia]
    rfl
  rw [e, List.mem_append, List.mem_singleton]

end sorted

end Ted
