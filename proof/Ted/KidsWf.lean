import Kids
import Mirror2
import FromKids
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! `from_kids` builds a well formed tree from valid child lists. -/

/-- Valid child lists (0-based): the children of `j` are smaller than `j` and ascending, they end with `j - 1`, the
subtrees of consecutive children tile (the leftmost leaf of the next child is one past the previous child), and the
last node is the root (its leftmost leaf is the first node). The tiling conditions refer to the solution `L` of the
leftmost-leaf equations, which is unique. -/
structure KidsValid (n : Nat) (kids : List (alloc.vec.Vec Std.U32)) : Prop where
  len : kids.length = n
  lt : ∀ j < n, ∀ c ∈ (kids[j]!).val, c.val < j
  sorted : ∀ j < n, (kids[j]!).val.Pairwise (fun a b => a.val < b.val)
  last : ∀ j < n, (kids[j]!).val ≠ [] → ∃ ks0 m, (kids[j]!).val = ks0 ++ [m] ∧ m.val + 1 = j
  adj : ∀ L : List Std.U32, (∀ j < n, LmlEq kids L j) → ∀ j < n, ∀ pre c c' post,
    (kids[j]!).val = pre ++ c :: c' :: post → (L[c'.val]!).val = c.val + 2
  root : ∀ L : List Std.U32, (∀ j < n, LmlEq kids L j) → 1 ≤ n → (L[n - 1]!).val = 1

theorem map_decomp {α β : Type} (f : α → β) (xs : List α) (pre : List β) (c c' : β) (post : List β)
    (h : xs.map f = pre ++ c :: c' :: post) :
    ∃ pre0 c0 c0' post0, xs = pre0 ++ c0 :: c0' :: post0 ∧ f c0 = c ∧ f c0' = c' := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h
  obtain ⟨c0, r1, rfl, e1, h3⟩ := List.map_eq_cons_iff.mp h2
  obtain ⟨c0', r2, rfl, e2, h4⟩ := List.map_eq_cons_iff.mp h3
  exact ⟨l1, c0, c0', r2, rfl, e1, e2⟩

theorem from_kids_wf (label : alloc.vec.Vec Std.U32) (kids : Slice (alloc.vec.Vec Std.U32))
    (hn : label.length < 2 ^ 14) (hpos : 1 ≤ label.length) (hK : KidsValid label.length kids.val) :
    ted.PostTree.from_kids label kids ⦃ t => PT.Wf t ∧ t.label = label ⦄ := by
  have hlt : ∀ j < label.length, ∀ k, FirstKid kids.val j = some k → k.val < j := by
    intro j hj k hk
    unfold FirstKid at hk
    have hjk : j < kids.val.length := by rw [hK.len]; exact hj
    rw [List.getElem?_eq_getElem hjk] at hk
    simp only [Option.bind_some] at hk
    have hm : k ∈ (kids.val[j]'hjk).val := by
      cases hh : (kids.val[j]'hjk).val with
      | nil => rw [hh] at hk; simp at hk
      | cons x xs => rw [hh] at hk; simp at hk; rw [← hk]; simp
    have := hK.lt j hj k (by rw [getG_eq _ _ hjk]; exact hm)
    exact this
  refine WP.spec_mono (from_kids_spec label kids (by omega) (by rw [hK.len]) hlt) ?_
  rintro t ⟨hlab, hlen, hlml, hsort, hkrt, hkids, hkind⟩
  have hn1 : t.label.length = label.length := by rw [hlab]
  have hLm : ∀ j < label.length, LmlEq kids.val t.lml.val j := fun j hj => (hlml j hj).1
  have hlen' : t.lml.val.length = label.length := hlen
  have hkl : kids.val.length = label.length := hK.len
  have hla : ∀ p, 1 ≤ p → p ≤ label.length → laOf t p = (t.lml.val[p - 1]!).val := fun p h1 h2 =>
    laOf_eq1 t p h1 (by omega)
  have hkd : ∀ p, kdOf t p = (kids.val[p - 1]!).val.map (fun c => c.val + 1) := by
    intro p; unfold kdOf; rw [hkids]
  have hKO : KidsOK label.length (laOf t) (kdOf t) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp1 hp2
      rw [hkd]
      rw [List.pairwise_map]
      exact (hK.sorted (p - 1) (by omega)).imp (fun h => by omega)
    · intro p hp1 hp2 c hc
      rw [hkd, List.mem_map] at hc
      obtain ⟨k, hk, rfl⟩ := hc
      have := hK.lt (p - 1) (by omega) k hk
      omega
    · intro p hp1 hp2 h0
      rw [hkd] at h0
      have h1 : (kids.val[p - 1]!).val = [] := List.map_eq_nil_iff.mp h0
      have h2 := hLm (p - 1) (by omega)
      unfold LmlEq at h2
      have h3 : FirstKid kids.val (p - 1) = none := by
        rw [firstKid_get kids.val (p - 1) (by omega)]
        have : (kids.val[p - 1]'(by omega)).val = [] := by
          rw [← getG_eq kids.val _ (by omega)]; exact h1
        rw [this]; rfl
      rw [h3] at h2
      simp only at h2
      rw [hla p hp1 hp2, h2]; omega
    · intro p c cs hp1 hp2 h0
      rw [hkd] at h0
      obtain ⟨k0, ks, hks, e1, _⟩ := List.map_eq_cons_iff.mp h0
      have hk0 := hK.lt (p - 1) (by omega) k0 (by rw [hks]; simp)
      have h2 := hLm (p - 1) (by omega)
      unfold LmlEq at h2
      have h3 : FirstKid kids.val (p - 1) = some k0 := by
        rw [firstKid_get kids.val (p - 1) (by omega)]
        have : (kids.val[p - 1]'(by omega)).val = k0 :: ks := by
          rw [← getG_eq kids.val _ (by omega)]; exact hks
        rw [this]; rfl
      rw [h3] at h2
      simp only at h2
      have hc1 : 1 ≤ c := by omega
      have hcn : c ≤ label.length := by omega
      rw [hla p hp1 hp2, hla c hc1 hcn, h2]
      have : c - 1 = k0.val := by omega
      rw [this]
    · intro p hp1 hp2 hne
      have h1 : (kids.val[p - 1]!).val ≠ [] := by
        intro h0; apply hne; rw [hkd, h0]; rfl
      obtain ⟨ks0, m, hm, hm2⟩ := hK.last (p - 1) (by omega) h1
      rw [hkd, List.mem_map]
      exact ⟨m, by rw [hm]; simp, by omega⟩
    · intro p hp1 hp2 pre c c' post h0
      rw [hkd] at h0
      obtain ⟨pre0, c0, c0', post0, hd, e1, e2⟩ := map_decomp _ _ _ _ _ _ h0
      have hlt0 := hK.lt (p - 1) (by omega) c0' (by rw [hd]; simp)
      have hlt1 := hK.lt (p - 1) (by omega) c0 (by rw [hd]; simp)
      have := hK.adj t.lml.val hLm (p - 1) (by omega) pre0 c0 c0' post0 hd
      have hc'1 : 1 ≤ c' := by omega
      have hc'n : c' ≤ label.length := by omega
      rw [hla c' hc'1 hc'n]
      have : c' - 1 = c0'.val := by omega
      rw [this]; omega
    · intro u hu1 hu2
      have := (hlml (u - 1) (by omega)).2
      rw [hla u hu1 hu2]
      omega
    · intro u hu
      unfold laOf; rw [hn1, if_neg (by omega)]
    · have := hK.root t.lml.val hLm hpos
      rw [hla label.length hpos (Nat.le_refl _)]
      exact this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hlab⟩
  · rw [hn1]; exact hpos
  · rw [hn1]; exact hlen
  · rw [hn1]; show t.kind.val.length = _; rw [hkind]; simp
  · rw [hn1]; show t.kids.val.length = _; rw [hkids]; exact hkl
  · exact hKO.wfl
  · rw [hn1]; exact hKO.root
  · intro p hp1 hp2; rw [hn1] at hp2; exact hKO.sorted p hp1 hp2
  · intro p c hp1 hp2; rw [hn1] at hp2 ⊢; exact hKO.par_iff hp1 hp2 c
  · exact hsort
  · intro v; rw [hn1]; exact hkrt v

end difffold_lines_extract
