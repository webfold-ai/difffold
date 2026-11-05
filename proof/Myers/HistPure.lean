import SolveLen
/-! Pure lemmas for the soundness of the histogram differ: segments of id lists, and how the flag writes of the
recursive calls assemble into one valid script. Only validity (the kept lines agree), no optimality. -/
namespace Myers

/-- The segment `[lo, hi)` of a list. -/
def sg {α : Type} (l : List α) (lo hi : Nat) : List α := (l.drop lo).take (hi - lo)

theorem sg_length {α : Type} (l : List α) (lo hi : Nat) (h : hi ≤ l.length) : (sg l lo hi).length = hi - lo := by
  simp [sg]; omega

theorem sg_split {α : Type} (l : List α) (lo m hi : Nat) (h1 : lo ≤ m) (h2 : m ≤ hi) :
    sg l lo hi = sg l lo m ++ sg l m hi := by
  unfold sg
  rw [show hi - lo = (m - lo) + (hi - m) by omega, List.take_add, List.drop_drop]
  congr 3 <;> omega

theorem sg_three {α : Type} (l : List α) (lo m1 m2 hi : Nat) (h1 : lo ≤ m1) (h2 : m1 ≤ m2) (h3 : m2 ≤ hi) :
    sg l lo hi = sg l lo m1 ++ sg l m1 m2 ++ sg l m2 hi := by
  rw [sg_split l lo m2 hi (by omega) h3, sg_split l lo m1 m2 h1 h2]

theorem sg_drop {α : Type} (l : List α) (lo hi k : Nat) (hk : k ≤ hi - lo) :
    (sg l lo hi).drop k = sg l (lo + k) hi := by
  unfold sg
  rw [List.drop_take, List.drop_drop, show hi - lo - k = hi - (lo + k) by omega]

theorem sg_take {α : Type} (l : List α) (lo hi k : Nat) (hk : k ≤ hi - lo) :
    (sg l lo hi).take k = sg l lo (lo + k) := by
  unfold sg
  rw [List.take_take, show min k (hi - lo) = k by omega, show lo + k - lo = k by omega]

/-- A script for the segments `A`, `B` and the arrays after the write. -/
def HPost (A B : List Nat) (alo blo : Nat) (D I D' I' : List Bool) : Prop :=
  ∃ da di, Valid A B da di ∧ D' = splice D alo da ∧ I' = splice I blo di

theorem valid_join {L L' M R R' : List Nat} {d1 e1 d2 e2 : List Bool}
    (h1 : Valid L L' d1 e1) (h2 : Valid R R' d2 e2) :
    Valid (L ++ M ++ R) (L' ++ M ++ R')
      (d1 ++ List.replicate M.length false ++ d2) (e1 ++ List.replicate M.length false ++ e2) := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  refine ⟨by simp [a1, b1], by simp [a2, b2], ?_⟩
  rw [kept_append _ _ _ _ (by simp [a1]), kept_append _ _ _ _ a1, kept_rep_false,
    kept_append _ _ _ _ (by simp [a2]), kept_append _ _ _ _ a2, kept_rep_false, a3, b3]

theorem hp_trim {P S A1 B1 : List Nat} {alo blo : Nat} {D I D' I' : List Bool}
    (hDl : alo + (P ++ A1 ++ S).length ≤ D.length) (hIl : blo + (P ++ B1 ++ S).length ≤ I.length)
    (hDf : ∀ j, j < (P ++ A1 ++ S).length → D[alo + j]? = some false)
    (hIf : ∀ j, j < (P ++ B1 ++ S).length → I[blo + j]? = some false)
    (h : HPost A1 B1 (alo + P.length) (blo + P.length) D I D' I') :
    HPost (P ++ A1 ++ S) (P ++ B1 ++ S) alo blo D I D' I' := by
  obtain ⟨da, di, hv, hD, hI⟩ := h
  have hv' := hv
  obtain ⟨a1, a2, a3⟩ := hv
  refine ⟨List.replicate P.length false ++ da ++ List.replicate S.length false,
    List.replicate P.length false ++ di ++ List.replicate S.length false, ?_, ?_, ?_⟩
  · refine ⟨by simp [a1], by simp [a2], ?_⟩
    rw [kept_append _ _ _ _ (by simp [a1]), kept_append _ _ _ _ (by simp), kept_rep_false,
      kept_append _ _ _ _ (by simp [a2]), kept_append _ _ _ _ (by simp), kept_rep_false, a3]
    simp [kept_rep_false]
  · rw [hD, splice_trim D da alo P.length S.length (by simp at hDl ⊢; omega)
      (fun j hj => hDf j (by simp; omega)) (fun j hj => by
        have := hDf (P.length + A1.length + j) (by simp; omega)
        rwa [show alo + (P.length + A1.length + j) = alo + P.length + da.length + j by rw [a1]; omega] at this)]
  · rw [hI, splice_trim I di blo P.length S.length (by simp at hIl ⊢; omega)
      (fun j hj => hIf j (by simp; omega)) (fun j hj => by
        have := hIf (P.length + B1.length + j) (by simp; omega)
        rwa [show blo + (P.length + B1.length + j) = blo + P.length + di.length + j by rw [a2]; omega] at this)]

theorem hp_anchor {L L' M R R' : List Nat} {alo blo : Nat} {D I D2 I2 D3 I3 : List Bool}
    (hDl : alo + (L ++ M ++ R).length ≤ D.length) (hIl : blo + (L' ++ M ++ R').length ≤ I.length)
    (hDf : ∀ j, j < M.length → D[alo + L.length + j]? = some false)
    (hIf : ∀ j, j < M.length → I[blo + L'.length + j]? = some false)
    (h1 : HPost L L' alo blo D I D2 I2)
    (h2 : HPost R R' (alo + L.length + M.length) (blo + L'.length + M.length) D2 I2 D3 I3) :
    HPost (L ++ M ++ R) (L' ++ M ++ R') alo blo D I D3 I3 := by
  obtain ⟨d1, e1, hv1, hD1, hI1⟩ := h1
  obtain ⟨d2, e2, hv2, hD2, hI2⟩ := h2
  refine ⟨d1 ++ List.replicate M.length false ++ d2, e1 ++ List.replicate M.length false ++ e2,
    valid_join hv1 hv2, ?_, ?_⟩
  · have l1 : d1.length = L.length := hv1.1
    have l2 : d2.length = R.length := hv2.1
    simp only [List.length_append] at hDl
    have e : splice D alo (d1 ++ List.replicate M.length false) = splice D alo d1 := by
      have := splice_trim D d1 alo 0 M.length (by simp; omega) (fun j hj => by omega)
        (fun j hj => by rw [show alo + 0 + d1.length + j = alo + L.length + j by omega]; exact hDf j hj)
      simpa using this
    rw [hD2, hD1, show alo + L.length + M.length = alo + (d1 ++ List.replicate M.length false).length by
      simp [l1]; omega, ← e, splice_splice D _ d2 alo (by simp; omega)]
  · have l1 : e1.length = L'.length := hv1.2.1
    have l2 : e2.length = R'.length := hv2.2.1
    simp only [List.length_append] at hIl
    have e : splice I blo (e1 ++ List.replicate M.length false) = splice I blo e1 := by
      have := splice_trim I e1 blo 0 M.length (by simp; omega) (fun j hj => by omega)
        (fun j hj => by rw [show blo + 0 + e1.length + j = blo + L'.length + j by omega]; exact hIf j hj)
      simpa using this
    rw [hI2, hI1, show blo + L'.length + M.length = blo + (e1 ++ List.replicate M.length false).length by
      simp [l1]; omega, ← e, splice_splice I _ e2 blo (by simp; omega)]

theorem hp_all_true {A B : List Nat} {alo blo : Nat} (D I : List Bool) :
    HPost A B alo blo D I (splice D alo (List.replicate A.length true)) (splice I blo (List.replicate B.length true)) :=
  ⟨_, _, ⟨by simp, by simp, by rw [kept_rep_true, kept_rep_true]⟩, rfl, rfl⟩

theorem hp_ins_only {B : List Nat} {alo blo : Nat} (D I : List Bool) :
    HPost [] B alo blo D I D (splice I blo (List.replicate B.length true)) :=
  ⟨[], _, ⟨by simp, by simp, by rw [kept_rep_true]; simp [kept]⟩, (splice_nil D alo).symm, rfl⟩

theorem hp_del_only {A : List Nat} {alo blo : Nat} (D I : List Bool) :
    HPost A [] alo blo D I (splice D alo (List.replicate A.length true)) I :=
  ⟨_, [], ⟨by simp, by simp, by rw [kept_rep_true]; simp [kept]⟩, rfl, (splice_nil I blo).symm⟩

theorem hp_anchor_sg {A B : List Nat} {alo1 ahi1 blo1 bhi1 i0 i1 j0 j1 : Nat} {D I D2 I2 D3 I3 : List Bool}
    (h1 : alo1 ≤ i0) (h2 : i0 ≤ i1) (h3 : i1 ≤ ahi1) (h4 : ahi1 ≤ A.length)
    (h5 : blo1 ≤ j0) (h6 : j0 ≤ j1) (h7 : j1 ≤ bhi1) (h8 : bhi1 ≤ B.length)
    (hM : sg A i0 i1 = sg B j0 j1)
    (hDl : ahi1 ≤ D.length) (hIl : bhi1 ≤ I.length)
    (hDf : ∀ j, j < i1 - i0 → D[i0 + j]? = some false)
    (hIf : ∀ j, j < j1 - j0 → I[j0 + j]? = some false)
    (hp1 : HPost (sg A alo1 i0) (sg B blo1 j0) alo1 blo1 D I D2 I2)
    (hp2 : HPost (sg A i1 ahi1) (sg B j1 bhi1) i1 j1 D2 I2 D3 I3) :
    HPost (sg A alo1 ahi1) (sg B blo1 bhi1) alo1 blo1 D I D3 I3 := by
  have hl1 : (sg A alo1 i0).length = i0 - alo1 := sg_length _ _ _ (by omega)
  have hl2 : (sg A i0 i1).length = i1 - i0 := sg_length _ _ _ (by omega)
  have hl3 : (sg A i1 ahi1).length = ahi1 - i1 := sg_length _ _ _ (by omega)
  have hl1' : (sg B blo1 j0).length = j0 - blo1 := sg_length _ _ _ (by omega)
  have hl3' : (sg B j1 bhi1).length = bhi1 - j1 := sg_length _ _ _ (by omega)
  have eA := sg_three A alo1 i0 i1 ahi1 h1 h2 h3
  have eB := sg_three B blo1 j0 j1 bhi1 h5 h6 h7
  rw [← hM] at eB
  rw [eA, eB]
  have hMl : i1 - i0 = j1 - j0 := by
    have := congrArg List.length hM
    rw [sg_length _ _ _ (by omega), sg_length _ _ _ (by omega)] at this
    exact this
  refine hp_anchor (M := sg A i0 i1) (D2 := D2) (I2 := I2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← eA]; rw [sg_length _ _ _ h4]; omega
  · rw [← eB]; rw [sg_length _ _ _ h8]; omega
  · intro j hj; rw [hl1]; rw [hl2] at hj
    rw [show alo1 + (i0 - alo1) + j = i0 + j by omega]; exact hDf j hj
  · intro j hj; rw [hl1']; rw [hl2] at hj
    rw [show blo1 + (j0 - blo1) + j = j0 + j by omega]; exact hIf j (by omega)
  · exact hp1
  · rw [hl1, hl2, show alo1 + (i0 - alo1) + (i1 - i0) = i1 by omega]
    rw [hl1', show blo1 + (j0 - blo1) + (i1 - i0) = j1 by omega]
    exact hp2

/-- Trimming equal ends: a script for the middle gives one for the whole range. -/
theorem hp_wrap {A B : List Nat} {alo ahi alo1 ahi1 blo bhi blo1 bhi1 : Nat} {D I D' I' : List Bool}
    (h1 : alo ≤ alo1) (h2 : alo1 ≤ ahi1) (h3 : ahi1 ≤ ahi) (h4 : ahi ≤ A.length)
    (h5 : blo ≤ blo1) (h6 : blo1 ≤ bhi1) (h7 : bhi1 ≤ bhi) (h8 : bhi ≤ B.length)
    (hpp : blo1 = blo + (alo1 - alo))
    (hP : sg A alo alo1 = sg B blo blo1) (hS : sg A ahi1 ahi = sg B bhi1 bhi)
    (hDl : ahi ≤ D.length) (hIl : bhi ≤ I.length)
    (hDf : ∀ j, alo ≤ j → j < ahi → D[j]? = some false) (hIf : ∀ j, blo ≤ j → j < bhi → I[j]? = some false)
    (h : HPost (sg A alo1 ahi1) (sg B blo1 bhi1) alo1 blo1 D I D' I') :
    HPost (sg A alo ahi) (sg B blo bhi) alo blo D I D' I' := by
  have hP1 : (sg A alo alo1).length = alo1 - alo := sg_length _ _ _ (by omega)
  have hS1 : (sg A ahi1 ahi).length = ahi - ahi1 := sg_length _ _ _ (by omega)
  have hSl : ahi - ahi1 = bhi - bhi1 := by
    have := congrArg List.length hS
    rw [sg_length _ _ _ (by omega), sg_length _ _ _ (by omega)] at this
    exact this
  rw [sg_three A alo alo1 ahi1 ahi h1 h2 h3, sg_three B blo blo1 bhi1 bhi h5 h6 h7, ← hP, ← hS]
  have hM1 : (sg A alo1 ahi1).length = ahi1 - alo1 := sg_length _ _ _ (by omega)
  have hM2 : (sg B blo1 bhi1).length = bhi1 - blo1 := sg_length _ _ _ (by omega)
  refine hp_trim (P := sg A alo alo1) (S := sg A ahi1 ahi) ?_ ?_ ?_ ?_ ?_
  · simp only [List.length_append]; rw [hP1, hM1, hS1]; omega
  · simp only [List.length_append]; rw [hP1, hM2, hS1]; omega
  · intro j hj
    simp only [List.length_append] at hj
    rw [hP1, hM1, hS1] at hj
    exact hDf _ (by omega) (by omega)
  · intro j hj
    simp only [List.length_append] at hj
    rw [hP1, hM2, hS1] at hj
    exact hIf _ (by omega) (by omega)
  · rw [hP1, ← hpp, show alo + (alo1 - alo) = alo1 by omega]; exact h

end Myers
