import Mapping
/-! Optimal mappings of a forest task, and the four ways to build one from smaller ones.

`Sol l x l' y M` says that `M` is a legal mapping of the forests `l .. x` and `l' .. y` whose cost is the
distance `D`. These are the building blocks of the existence proof `exists_map`, stated on their own so that
a traceback through the forest tables can use them one step at a time. -/
namespace Ted

def Sol (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (l x l' y : Nat) (M : List (Nat × Nat)) : Prop :=
  Valid la lb M ∧ InRange l x l' y M ∧ Cost ren l x l' y M = D la lb ren l x l' y

section
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat}

theorem sol_nil {l x l' y : Nat} (hx : x < l ∨ x = 0) (hy : y < l' ∨ y = 0) (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    Sol la lb ren l x l' y [] := by
  refine ⟨⟨by simp, by simp⟩, by simp [InRange], ?_⟩
  rw [D_base1 la lb ren l x l' y hx]
  simp [Cost]; omega

theorem sol_del {l x l' y : Nat} {M : List (Nat × Nat)} (h1 : ¬ (x < l ∨ x = 0))
    (hd : D la lb ren l x l' y = D la lb ren l (x - 1) l' y + 1) (hM : Sol la lb ren l (x - 1) l' y M) :
    Sol la lb ren l x l' y M := by
  obtain ⟨hv, hr, hc⟩ := hM
  refine ⟨hv, fun p hp => by have := hr p hp; omega, ?_⟩
  have := (valid_len hv hr).1
  unfold Cost at hc ⊢; omega

theorem sol_ins {l x l' y : Nat} {M : List (Nat × Nat)} (h2 : ¬ (y < l' ∨ y = 0))
    (hd : D la lb ren l x l' y = D la lb ren l x l' (y - 1) + 1) (hM : Sol la lb ren l x l' (y - 1) M) :
    Sol la lb ren l x l' y M := by
  obtain ⟨hv, hr, hc⟩ := hM
  refine ⟨hv, fun p hp => by have := hr p hp; omega, ?_⟩
  have := (valid_len hv hr).2
  unfold Cost at hc ⊢; omega

theorem sol_leaf (hA : WfL la) (hB : WfL lb) {l x l' y : Nat} {M : List (Nat × Nat)}
    (hl : 1 ≤ l) (hl' : 1 ≤ l') (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hlx : la x = l) (hly : lb y = l')
    (hd : D la lb ren l x l' y = D la lb ren l (x - 1) l' (y - 1) + ren x y)
    (hM : Sol la lb ren l (x - 1) l' (y - 1) M) : Sol la lb ren l x l' y ((x, y) :: M) := by
  obtain ⟨hvm, hrm, hcm⟩ := hM
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_cons]
    exact ⟨fun hm => by have := hrm _ hm; simp at this; omega, hvm.1⟩
  · intro p hp q hq
    rw [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · simp [Anc]
    · have := hrm q hq
      simp only [Anc]
      omega
    · have := hrm p hp
      simp only [Anc]
      omega
    · exact hvm.2 p hp q hq
  · intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp; omega
    · have := hrm p hp; omega
  · have hl3 := valid_len hvm hrm
    unfold Cost at hcm ⊢
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem sol_split (hA : WfL la) (hB : WfL lb) {l x l' y : Nat} {M1 M2 : List (Nat × Nat)}
    (hl : 1 ≤ l) (hl' : 1 ≤ l') (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hcA : Closed la l x) (hcB : Closed lb l' y)
    (hd : D la lb ren l x l' y = D la lb ren l (la x - 1) l' (lb y - 1) + D la lb ren (la x) x (lb y) y)
    (hM1 : Sol la lb ren l (la x - 1) l' (lb y - 1) M1) (hM2 : Sol la lb ren (la x) x (lb y) y M2) :
    Sol la lb ren l x l' y (M1 ++ M2) := by
  obtain ⟨hv1, hr1, hc1⟩ := hM1
  obtain ⟨hv2, hr2, hc2⟩ := hM2
  have hxl : l ≤ x := by omega
  have hyl : l' ≤ y := by omega
  have hlx1 : l ≤ la x := hcA x hxl (Nat.le_refl _)
  have hlx2 : la x ≤ x := (hA.1 x (by omega)).2
  have hly1 : l' ≤ lb y := hcB y hyl (Nat.le_refl _)
  have hly2 : lb y ≤ y := (hB.1 y (by omega)).2
  have hcA2 : Closed la (la x) x := fun u h h' => hA.2 x u h h'
  have hcB2 : Closed lb (lb y) y := fun u h h' => hB.2 y u h h'
  have hl1 := valid_len hv1 hr1
  have hl2 := valid_len hv2 hr2
  have hvM : Valid la lb (M1 ++ M2) := by
    apply valid_append hv1 hv2
    intro p hp q hq
    have a1 := hr1 p hp
    have a2 := hr2 q hq
    have b1 := hcA2 q.1 a2.1 a2.2.1
    have b2 := hcB2 q.2 a2.2.2.1 a2.2.2.2
    refine ⟨by omega, by omega, ?_, ?_⟩
    · simp only [Anc]; omega
    · simp only [Anc]; omega
  refine ⟨hvM, ?_, ?_⟩
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have := hr1 p hp; omega
    · have := hr2 p hp; omega
  · rw [hd, ← hc1, ← hc2]
    unfold Cost
    simp only [List.length_append, List.map_append, List.sum_append]
    omega

end
end Ted
