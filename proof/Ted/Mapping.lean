import Zs
/-! Tree edit mappings on postorder indices, and the theorem that the Zhang-Shasha recursion `Ted.D` is the
minimum cost of a valid mapping.

A tree is given by its leftmost-leaf map `la` (1-based postorder). Node `u` is a proper descendant of `v`
when `u < v` and `la v <= u`. A mapping between the node ranges `l..x` and `l'..y` is a list of pairs that is
one to one and preserves both the postorder and the descendant relation. Its cost is the number of unmapped
nodes of both ranges plus the relabel costs of the pairs. -/
namespace Ted

def Anc (la : Nat → Nat) (u v : Nat) : Prop := u < v ∧ la v ≤ u

def Valid (la lb : Nat → Nat) (M : List (Nat × Nat)) : Prop :=
  M.Nodup ∧ ∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ↔ p.2 = q.2) ∧ (p.1 < q.1 ↔ p.2 < q.2) ∧
    (Anc la p.1 q.1 ↔ Anc lb p.2 q.2)

def InRange (l x l' y : Nat) (M : List (Nat × Nat)) : Prop :=
  ∀ p ∈ M, l ≤ p.1 ∧ p.1 ≤ x ∧ l' ≤ p.2 ∧ p.2 ≤ y

def Cost (ren : Nat → Nat → Nat) (l x l' y : Nat) (M : List (Nat × Nat)) : Nat :=
  (x + 1 - l - M.length) + (y + 1 - l' - M.length) + (M.map (fun p => ren p.1 p.2)).sum

def Closed (la : Nat → Nat) (l x : Nat) : Prop := ∀ u, l ≤ u → u ≤ x → l ≤ la u

/-- Well formed leftmost-leaf maps: `la u` lies in `1 .. u`, and subtrees are intervals that nest. -/
def WfL (la : Nat → Nat) : Prop :=
  (∀ u, 1 ≤ u → 1 ≤ la u ∧ la u ≤ u) ∧ (∀ u v, la u ≤ v → v ≤ u → la u ≤ la v)

theorem nodup_length_le : ∀ (l m : List Nat), l.Nodup → l ⊆ m → l.length ≤ m.length
  | [], m, _, _ => by simp
  | a :: l, m, hnd, hsub => by
    have ha : a ∈ m := hsub (by simp)
    have hnd' := List.nodup_cons.mp hnd
    have hs : l ⊆ m.erase a := by
      intro u hu
      have hum := hsub (List.mem_cons_of_mem a hu)
      have hne : u ≠ a := fun e => hnd'.1 (e ▸ hu)
      exact (List.mem_erase_of_ne hne).mpr hum
    have := nodup_length_le l (m.erase a) hnd'.2 hs
    have h2 := List.length_erase_of_mem ha
    have h3 := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

theorem map_nodup (f : Nat × Nat → Nat) : ∀ (M : List (Nat × Nat)), M.Nodup →
    (∀ p ∈ M, ∀ q ∈ M, f p = f q → p = q) → (M.map f).Nodup
  | [], _, _ => by simp
  | p :: M, hnd, hinj => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, map_nodup f M hnd'.2 (fun a ha b hb e => hinj a (by simp [ha]) b (by simp [hb]) e)⟩
    rintro ⟨q, hq, e⟩
    have := hinj q (by simp [hq]) p (by simp) e
    exact hnd'.1 (this ▸ hq)

/-- A one to one (through `f`) list of pairs with `f` inside `l..x` has at most `x + 1 - l` pairs. -/
theorem len_le_of_inj (f : Nat × Nat → Nat) (M : List (Nat × Nat)) (l x : Nat) (hnd : M.Nodup)
    (hin : ∀ p ∈ M, l ≤ f p ∧ f p ≤ x) (hinj : ∀ p ∈ M, ∀ q ∈ M, f p = f q → p = q) :
    M.length ≤ x + 1 - l := by
  have h1 := map_nodup f M hnd hinj
  have h2 : (M.map f) ⊆ List.range' l (x + 1 - l) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    have := hin p hp
    rw [List.mem_range']
    exact ⟨f p - l, by omega, by omega⟩
  have := nodup_length_le _ _ h1 h2
  simpa using this

section
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat}

theorem valid_sublist {M M' : List (Nat × Nat)} (h : Valid la lb M) (hs : M'.Sublist M) : Valid la lb M' :=
  ⟨h.1.sublist hs, fun p hp q hq => h.2 p (hs.subset hp) q (hs.subset hq)⟩

theorem valid_inj {M : List (Nat × Nat)} (h : Valid la lb M) :
    ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q := by
  intro p hp q hq e
  exact Prod.ext e (((h.2 p hp q hq).1).mp e)

theorem valid_inj2 {M : List (Nat × Nat)} (h : Valid la lb M) :
    ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q := by
  intro p hp q hq e
  exact Prod.ext (((h.2 p hp q hq).1).mpr e) e

theorem valid_len {M : List (Nat × Nat)} {l x l' y : Nat} (h : Valid la lb M) (hr : InRange l x l' y M) :
    M.length ≤ x + 1 - l ∧ M.length ≤ y + 1 - l' :=
  ⟨len_le_of_inj Prod.fst M l x h.1 (fun p hp => ⟨(hr p hp).1, (hr p hp).2.1⟩) (valid_inj h),
   len_le_of_inj Prod.snd M l' y h.1 (fun p hp => ⟨(hr p hp).2.2.1, (hr p hp).2.2.2⟩) (valid_inj2 h)⟩


theorem perm_stats (f : Nat × Nat → Nat) {A B C : List (Nat × Nat)} (h : A.Perm (B ++ C)) :
    A.length = B.length + C.length ∧ (A.map f).sum = (B.map f).sum + (C.map f).sum := by
  refine ⟨by simpa using h.length_eq, ?_⟩
  have := (h.map f).sum_nat
  simpa [List.map_append, List.sum_append] using this

theorem erase_stats (f : Nat × Nat → Nat) {M : List (Nat × Nat)} {a : Nat × Nat} (h : a ∈ M) :
    M.length = (M.erase a).length + 1 ∧ (M.map f).sum = f a + ((M.erase a).map f).sum := by
  have hp := List.perm_cons_erase h
  have := perm_stats f (A := M) (B := [a]) (C := M.erase a) (by simpa using hp)
  simp at this
  omega

theorem clamp_eq (hA : WfL la) {l x : Nat} (hc : Closed la l x) (hl : 1 ≤ l) (hlx : l ≤ x) :
    clampL l x (la x) = la x := by
  have h1 := hc x hlx (Nat.le_refl _)
  have h2 := (hA.1 x (by omega)).2
  unfold clampL; omega

theorem D_le_del (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0)) :
    D la lb ren l x l' y ≤ D la lb ren l (x - 1) l' y + 1 := by
  by_cases hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l'
  · rw [D_leaf la lb ren l x l' y h1 h2 hc]; omega
  · rw [D_nonleaf la lb ren l x l' y h1 h2 hc]; omega

theorem D_le_ins (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0)) :
    D la lb ren l x l' y ≤ D la lb ren l x l' (y - 1) + 1 := by
  by_cases hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l'
  · rw [D_leaf la lb ren l x l' y h1 h2 hc]; omega
  · rw [D_nonleaf la lb ren l x l' y h1 h2 hc]; omega

theorem D_le_leaf (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l') :
    D la lb ren l x l' y ≤ D la lb ren l (x - 1) l' (y - 1) + ren x y := by
  rw [D_leaf la lb ren l x l' y h1 h2 hc]; omega

theorem D_le_nonleaf (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hc : ¬ (clampL l x (la x) = l ∧ clampL l' y (lb y) = l')) :
    D la lb ren l x l' y ≤ D la lb ren l (clampL l x (la x) - 1) l' (clampL l' y (lb y) - 1) +
      D la lb ren (clampL l x (la x)) x (clampL l' y (lb y)) y := by
  rw [D_nonleaf la lb ren l x l' y h1 h2 hc]; omega


theorem D_le_cost (hA : WfL la) (hB : WfL lb) : ∀ (n l x l' y : Nat) (M : List (Nat × Nat)),
    1 ≤ l → 1 ≤ l' → Closed la l x → Closed lb l' y → (x + 1 - l) + (y + 1 - l') = n →
    Valid la lb M → InRange l x l' y M → D la lb ren l x l' y ≤ Cost ren l x l' y M := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro l x l' y M hl hl' hcA hcB hn hv hr
  by_cases h1 : x < l ∨ x = 0
  · have hM : M = [] := by
      cases M with
      | nil => rfl
      | cons p M => exfalso; have := hr p (by simp); omega
    subst hM; rw [D_base1 la lb ren l x l' y h1]; simp [Cost] <;> omega
  by_cases h2 : y < l' ∨ y = 0
  · have hM : M = [] := by
      cases M with
      | nil => rfl
      | cons p M => exfalso; have := hr p (by simp); omega
    subst hM; rw [D_base2 la lb ren l x l' y h1 h2]; simp [Cost] <;> omega
  have hxl : l ≤ x := by omega
  have hyl : l' ≤ y := by omega
  obtain ⟨hlenA, hlenB⟩ := valid_len hv hr
  by_cases hx : ¬ ∃ p ∈ M, p.1 = x
  · have hr' : InRange l (x - 1) l' y M := by
      intro p hp
      have := hr p hp
      have hne : p.1 ≠ x := fun e => hx ⟨p, hp, e⟩
      omega
    have hcA' : Closed la l (x - 1) := fun u h h' => hcA u h (by omega)
    have ihx := ih ((x - 1 + 1 - l) + (y + 1 - l')) (by omega) l (x - 1) l' y M hl hl' hcA' hcB rfl hv hr'
    have hd := D_le_del (la := la) (lb := lb) (ren := ren) l x l' y h1 h2
    have hlen' := (valid_len hv hr').1
    unfold Cost at ihx ⊢; omega
  obtain ⟨p, hpM, hpx⟩ := Classical.not_not.mp hx
  by_cases hy : ¬ ∃ q ∈ M, q.2 = y
  · have hr' : InRange l x l' (y - 1) M := by
      intro p hp
      have := hr p hp
      have hne : p.2 ≠ y := fun e => hy ⟨p, hp, e⟩
      omega
    have hcB' : Closed lb l' (y - 1) := fun u h h' => hcB u h (by omega)
    have ihx := ih ((x + 1 - l) + (y - 1 + 1 - l')) (by omega) l x l' (y - 1) M hl hl' hcA hcB' rfl hv hr'
    have hd := D_le_ins (la := la) (lb := lb) (ren := ren) l x l' y h1 h2
    have hlen' := (valid_len hv hr').2
    unfold Cost at ihx ⊢; omega
  obtain ⟨q, hqM, hqy⟩ := Classical.not_not.mp hy
  have hxy : (x, y) ∈ M := by
    have hp1 := hr p hpM
    have hq1 := hr q hqM
    have hpq := (hv.2 q hqM p hpM).2.1
    by_cases hlt : q.1 < p.1
    · have := hpq.mp hlt; omega
    · have e : q.1 = p.1 := by omega
      have e2 := ((hv.2 q hqM p hpM).1).mp e
      have : q = p := Prod.ext e e2
      subst this
      have : q = (x, y) := Prod.ext hpx hqy
      rw [← this]; exact hqM
  obtain ⟨hlenM, hsumM⟩ := erase_stats (fun p => ren p.1 p.2) hxy
  generalize hM' : M.erase (x, y) = M' at hlenM hsumM
  have hsub : M'.Sublist M := hM' ▸ List.erase_sublist
  have hv' := valid_sublist hv hsub
  have hmem : ∀ p ∈ M', p.1 < x ∧ p.2 < y ∧ l ≤ p.1 ∧ l' ≤ p.2 := by
    intro p hp
    have hpM' : p ∈ M := hsub.subset hp
    have hne : p ≠ (x, y) := ((List.Nodup.mem_erase_iff hv.1).mp (hM' ▸ hp)).1
    have hr1 := hr p hpM'
    have hlt : p.1 < x := by
      by_cases e : p.1 = x
      · exact absurd (valid_inj hv p hpM' (x, y) hxy e) hne
      · omega
    have := ((hv.2 p hpM' (x, y) hxy).2.1).mp hlt
    exact ⟨hlt, this, hr1.1, hr1.2.2.1⟩
  by_cases hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l'
  · have hr' : InRange l (x - 1) l' (y - 1) M' := by
      intro p hp; have := hmem p hp; omega
    have hcA' : Closed la l (x - 1) := fun u h h' => hcA u h (by omega)
    have hcB' : Closed lb l' (y - 1) := fun u h h' => hcB u h (by omega)
    have ihx := ih ((x - 1 + 1 - l) + (y - 1 + 1 - l')) (by omega) l (x - 1) l' (y - 1) M' hl hl' hcA' hcB' rfl hv' hr'
    have hd := D_le_leaf (la := la) (lb := lb) (ren := ren) l x l' y h1 h2 hc
    have hlen' := (valid_len hv' hr').1
    have hlen'' := (valid_len hv' hr').2
    unfold Cost at ihx ⊢
    rw [hlenM, hsumM]
    simp only at hsumM ⊢
    omega
  · have hcl := clamp_eq hA hcA hl hxl
    have hcl' := clamp_eq hB hcB hl' hyl
    rw [hcl, hcl'] at hc
    have hd := D_le_nonleaf (la := la) (lb := lb) (ren := ren) l x l' y h1 h2 (by rw [hcl, hcl']; exact hc)
    rw [hcl, hcl'] at hd
    have hlx1 : l ≤ la x := hcA x hxl (Nat.le_refl _)
    have hlx2 : la x ≤ x := (hA.1 x (by omega)).2
    have hly1 : l' ≤ lb y := hcB y hyl (Nat.le_refl _)
    have hly2 : lb y ≤ y := (hB.1 y (by omega)).2
    -- split the remaining pairs at the left end of the last trees
    let P : Nat × Nat → Bool := fun p => decide (p.1 < la x)
    have hperm := List.filter_append_perm P M'
    obtain ⟨hlenS, hsumS⟩ := perm_stats (fun p => ren p.1 p.2) hperm.symm
    have hM1sub : (M'.filter P).Sublist M' := List.filter_sublist
    have hM2sub : (M'.filter (fun p => !P p)).Sublist M' := List.filter_sublist
    have hv1 := valid_sublist hv' hM1sub
    have hv2 := valid_sublist hv' hM2sub
    have hanc : ∀ p ∈ M', (la x ≤ p.1 ↔ lb y ≤ p.2) := by
      intro p hp
      have hpm := hmem p hp
      have hpM' : p ∈ M := hsub.subset hp
      have := (hv.2 p hpM' (x, y) hxy).2.2
      simp only [Anc] at this
      constructor
      · intro h; exact (this.mp ⟨hpm.1, h⟩).2
      · intro h; exact (this.mpr ⟨hpm.2.1, h⟩).2
    have hr1 : InRange l (la x - 1) l' (lb y - 1) (M'.filter P) := by
      intro p hp
      have hpp := List.mem_filter.mp hp
      have hpm := hmem p hpp.1
      have hlt : p.1 < la x := by simpa [P] using hpp.2
      have : ¬ (la x ≤ p.1) := by omega
      have : ¬ (lb y ≤ p.2) := fun h => this ((hanc p hpp.1).mpr h)
      omega
    have hr2 : InRange (la x) (x - 1) (lb y) (y - 1) (M'.filter (fun p => !P p)) := by
      intro p hp
      have hpp := List.mem_filter.mp hp
      have hpm := hmem p hpp.1
      have hge : ¬ p.1 < la x := by simpa [P] using hpp.2
      have : lb y ≤ p.2 := (hanc p hpp.1).mp (by omega)
      omega
    have hcA1 : Closed la l (la x - 1) := fun u h h' => hcA u h (by omega)
    have hcB1 : Closed lb l' (lb y - 1) := fun u h h' => hcB u h (by omega)
    have hcA2 : Closed la (la x) (x - 1) := fun u h h' => hA.2 x u h (by omega)
    have hcB2 : Closed lb (lb y) (y - 1) := fun u h h' => hB.2 y u h (by omega)
    have ih1 := ih ((la x - 1 + 1 - l) + (lb y - 1 + 1 - l')) (by omega) l (la x - 1) l' (lb y - 1)
      (M'.filter P) hl hl' hcA1 hcB1 rfl hv1 hr1
    have ih2 := ih ((x - 1 + 1 - la x) + (y - 1 + 1 - lb y)) (by omega) (la x) (x - 1) (lb y) (y - 1)
      (M'.filter (fun p => !P p)) (by omega) (by omega) hcA2 hcB2 rfl hv2 hr2
    have hleafTD : D la lb ren (la x) x (lb y) y ≤ D la lb ren (la x) (x - 1) (lb y) (y - 1) + ren x y := by
      apply D_le_leaf (la := la) (lb := lb) (ren := ren) (la x) x (lb y) y (by omega) (by omega)
      unfold clampL; omega
    have hl1 := (valid_len hv1 hr1)
    have hl2 := (valid_len hv2 hr2)
    unfold Cost at ih1 ih2 ⊢
    rw [hlenM, hsumM, hlenS, hsumS]
    simp only at hsumM hsumS ⊢
    omega

theorem valid_append {M₁ M₂ : List (Nat × Nat)} (h1 : Valid la lb M₁) (h2 : Valid la lb M₂)
    (hx : ∀ p ∈ M₁, ∀ q ∈ M₂, p.1 < q.1 ∧ p.2 < q.2 ∧ ¬ Anc la p.1 q.1 ∧ ¬ Anc lb p.2 q.2) :
    Valid la lb (M₁ ++ M₂) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨h1.1, h2.1, ?_⟩
    intro a ha b hb e
    subst e
    have := hx a ha a hb
    omega
  · intro p hp q hq
    rw [List.mem_append] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact h1.2 p hp q hq
    · have := hx p hp q hq
      refine ⟨⟨fun e => by omega, fun e => by omega⟩, ⟨fun _ => this.2.1, fun _ => this.1⟩, ⟨fun a => absurd a this.2.2.1, fun a => absurd a this.2.2.2⟩⟩
    · have := hx q hq p hp
      refine ⟨⟨fun e => by omega, fun e => by omega⟩, ⟨fun a => by omega, fun a => by omega⟩, ⟨fun a => by simp [Anc] at a; omega, fun a => by simp [Anc] at a; omega⟩⟩
    · exact h2.2 p hp q hq

theorem exists_map (hA : WfL la) (hB : WfL lb) : ∀ (n l x l' y : Nat),
    1 ≤ l → 1 ≤ l' → Closed la l x → Closed lb l' y → (x + 1 - l) + (y + 1 - l') = n →
    ∃ M, Valid la lb M ∧ InRange l x l' y M ∧ Cost ren l x l' y M = D la lb ren l x l' y := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro l x l' y hl hl' hcA hcB hn
  by_cases h1 : x < l ∨ x = 0
  · refine ⟨[], ⟨by simp, by simp⟩, by simp [InRange], ?_⟩
    rw [D_base1 la lb ren l x l' y h1]; simp [Cost]; omega
  by_cases h2 : y < l' ∨ y = 0
  · refine ⟨[], ⟨by simp, by simp⟩, by simp [InRange], ?_⟩
    rw [D_base2 la lb ren l x l' y h1 h2]; simp [Cost]; omega
  have hxl : l ≤ x := by omega
  have hyl : l' ≤ y := by omega
  have hcA' : Closed la l (x - 1) := fun u h h' => hcA u h (by omega)
  have hcB' : Closed lb l' (y - 1) := fun u h h' => hcB u h (by omega)
  obtain ⟨Md, hvd, hrd, hcd⟩ := ih ((x - 1 + 1 - l) + (y + 1 - l')) (by omega) l (x - 1) l' y hl hl' hcA' hcB rfl
  obtain ⟨Mi, hvi, hri, hci⟩ := ih ((x + 1 - l) + (y - 1 + 1 - l')) (by omega) l x l' (y - 1) hl hl' hcA hcB' rfl
  have hdel : ∃ M, Valid la lb M ∧ InRange l x l' y M ∧ Cost ren l x l' y M = D la lb ren l (x - 1) l' y + 1 := by
    refine ⟨Md, hvd, fun p hp => by have := hrd p hp; omega, ?_⟩
    have := (valid_len hvd hrd).1
    unfold Cost at hcd ⊢; omega
  have hins : ∃ M, Valid la lb M ∧ InRange l x l' y M ∧ Cost ren l x l' y M = D la lb ren l x l' (y - 1) + 1 := by
    refine ⟨Mi, hvi, fun p hp => by have := hri p hp; omega, ?_⟩
    have := (valid_len hvi hri).2
    unfold Cost at hci ⊢; omega
  by_cases hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l'
  · obtain ⟨Mm, hvm, hrm, hcm⟩ := ih ((x - 1 + 1 - l) + (y - 1 + 1 - l')) (by omega) l (x - 1) l' (y - 1) hl hl' hcA' hcB' rfl
    have hcl := clamp_eq hA hcA hl hxl
    have hcl' := clamp_eq hB hcB hl' hyl
    have hlx : la x = l := by rw [← hcl]; exact hc.1
    have hly : lb y = l' := by rw [← hcl']; exact hc.2
    have hmatch : ∃ M, Valid la lb M ∧ InRange l x l' y M ∧
        Cost ren l x l' y M = D la lb ren l (x - 1) l' (y - 1) + ren x y := by
      refine ⟨(x, y) :: Mm, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨fun hm => by have := hrm _ hm; simp at this; omega, hvm.1⟩
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
    rw [D_leaf la lb ren l x l' y h1 h2 hc]
    obtain ⟨Ma, ha1, ha2, ha3⟩ := hdel
    obtain ⟨Mb, hb1, hb2, hb3⟩ := hins
    obtain ⟨Mc, hc1, hc2, hc3⟩ := hmatch
    by_cases e1 : D la lb ren l (x - 1) l' y + 1 ≤ D la lb ren l x l' (y - 1) + 1 ∧
        D la lb ren l (x - 1) l' y + 1 ≤ D la lb ren l (x - 1) l' (y - 1) + ren x y
    · exact ⟨Ma, ha1, ha2, by rw [ha3]; omega⟩
    · by_cases e2 : D la lb ren l x l' (y - 1) + 1 ≤ D la lb ren l (x - 1) l' (y - 1) + ren x y
      · exact ⟨Mb, hb1, hb2, by rw [hb3]; omega⟩
      · exact ⟨Mc, hc1, hc2, by rw [hc3]; omega⟩
  · have hcl := clamp_eq hA hcA hl hxl
    have hcl' := clamp_eq hB hcB hl' hyl
    have hc' : ¬ (la x = l ∧ lb y = l') := by rw [hcl, hcl'] at hc; exact hc
    have hlx1 : l ≤ la x := hcA x hxl (Nat.le_refl _)
    have hlx2 : la x ≤ x := (hA.1 x (by omega)).2
    have hly1 : l' ≤ lb y := hcB y hyl (Nat.le_refl _)
    have hly2 : lb y ≤ y := (hB.1 y (by omega)).2
    have hcA1 : Closed la l (la x - 1) := fun u h h' => hcA u h (by omega)
    have hcB1 : Closed lb l' (lb y - 1) := fun u h h' => hcB u h (by omega)
    have hcA2 : Closed la (la x) x := fun u h h' => hA.2 x u h h'
    have hcB2 : Closed lb (lb y) y := fun u h h' => hB.2 y u h h'
    obtain ⟨M1, hv1, hr1, hc1⟩ := ih ((la x - 1 + 1 - l) + (lb y - 1 + 1 - l')) (by omega)
      l (la x - 1) l' (lb y - 1) hl hl' hcA1 hcB1 rfl
    obtain ⟨M2, hv2, hr2, hc2⟩ := ih ((x + 1 - la x) + (y + 1 - lb y)) (by omega)
      (la x) x (lb y) y (by omega) (by omega) hcA2 hcB2 rfl
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
    have hrM : InRange l x l' y (M1 ++ M2) := by
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · have := hr1 p hp; omega
      · have := hr2 p hp; omega
    have hcM : Cost ren l x l' y (M1 ++ M2) =
        D la lb ren l (la x - 1) l' (lb y - 1) + D la lb ren (la x) x (lb y) y := by
      rw [← hc1, ← hc2]
      unfold Cost
      simp only [List.length_append, List.map_append, List.sum_append]
      omega
    rw [D_nonleaf la lb ren l x l' y h1 h2 hc, hcl, hcl']
    obtain ⟨Ma, ha1, ha2, ha3⟩ := hdel
    obtain ⟨Mb, hb1, hb2, hb3⟩ := hins
    by_cases e1 : D la lb ren l (x - 1) l' y + 1 ≤ D la lb ren l x l' (y - 1) + 1 ∧
        D la lb ren l (x - 1) l' y + 1 ≤ D la lb ren l (la x - 1) l' (lb y - 1) + D la lb ren (la x) x (lb y) y
    · exact ⟨Ma, ha1, ha2, by rw [ha3]; omega⟩
    · by_cases e2 : D la lb ren l x l' (y - 1) + 1 ≤ D la lb ren l (la x - 1) l' (lb y - 1) + D la lb ren (la x) x (lb y) y
      · exact ⟨Mb, hb1, hb2, by rw [hb3]; omega⟩
      · exact ⟨M1 ++ M2, hvM, hrM, by rw [hcM]; omega⟩

end

end Ted
