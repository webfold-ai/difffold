import Solve
/-! Writing a flag list into a segment of a bigger flag array. -/
namespace Myers

/-- `l` with the segment starting at `i` replaced by `d`. -/
def splice (l : List Bool) (i : Nat) (d : List Bool) : List Bool := l.take i ++ d ++ l.drop (i + d.length)

theorem splice_length (l : List Bool) (i : Nat) (d : List Bool) (h : i + d.length ≤ l.length) :
    (splice l i d).length = l.length := by
  unfold splice; simp; omega

theorem splice_getElem? (l : List Bool) (i : Nat) (d : List Bool) (h : i + d.length ≤ l.length) (j : Nat) :
    (splice l i d)[j]? = if j < i then l[j]? else if j < i + d.length then d[j - i]? else l[j]? := by
  unfold splice
  have hl1 : (l.take i).length = i := by simp; omega
  by_cases h1 : j < i
  · rw [if_pos h1, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega),
      List.getElem?_take, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : j < i + d.length
    · rw [if_pos h2, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hl1]
    · rw [if_neg h2, List.getElem?_append_right (by simp; omega), List.getElem?_drop]
      simp only [List.length_append, hl1]
      congr 1; omega

theorem splice_ext (l l' : List Bool) (i : Nat) (d : List Bool) (h : i + d.length ≤ l.length) :
    l' = splice l i d ↔ l'.length = l.length ∧ (∀ j, j < i → l'[j]? = l[j]?) ∧
      (∀ j, i ≤ j → j < i + d.length → l'[j]? = d[j - i]?) ∧ (∀ j, i + d.length ≤ j → l'[j]? = l[j]?) := by
  constructor
  · rintro rfl
    refine ⟨splice_length l i d h, ?_, ?_, ?_⟩
    · intro j hj; rw [splice_getElem? l i d h, if_pos hj]
    · intro j h1 h2; rw [splice_getElem? l i d h, if_neg (by omega), if_pos h2]
    · intro j hj; rw [splice_getElem? l i d h, if_neg (by omega), if_neg (by omega)]
  · rintro ⟨hl, h1, h2, h3⟩
    apply List.ext_getElem?
    intro j
    rw [splice_getElem? l i d h]
    by_cases a : j < i
    · rw [if_pos a]; exact h1 j a
    · rw [if_neg a]
      by_cases b : j < i + d.length
      · rw [if_pos b]; exact h2 j (by omega) b
      · rw [if_neg b]; exact h3 j (by omega)

/-- Writing the flags of a segment and then those of the next segment is one write. -/
theorem splice_splice (l d1 d2 : List Bool) (i : Nat) (h : i + d1.length + d2.length ≤ l.length) :
    splice (splice l i d1) (i + d1.length) d2 = splice l i (d1 ++ d2) := by
  have hl : (splice l i d1).length = l.length := splice_length l i d1 (by omega)
  have hl2 : (splice (splice l i d1) (i + d1.length) d2).length = l.length := by
    rw [splice_length _ _ _ (by omega), hl]
  refine (splice_ext l _ i (d1 ++ d2) (by simp; omega)).mpr ⟨hl2, ?_, ?_, ?_⟩
  · intro j hj
    rw [splice_getElem? (splice l i d1) (i + d1.length) d2 (by omega), if_pos (by omega),
      splice_getElem? l i d1 (by omega), if_pos hj]
  · intro j h1 h2
    simp only [List.length_append] at h2
    rw [splice_getElem? (splice l i d1) (i + d1.length) d2 (by omega)]
    by_cases a : j < i + d1.length
    · rw [if_pos a, splice_getElem? l i d1 (by omega), if_neg (by omega), if_pos a,
        List.getElem?_append_left (by omega)]
    · rw [if_neg a, if_pos (by omega), List.getElem?_append_right (by omega)]
      congr 1; omega
  · intro j hj
    simp only [List.length_append] at hj
    rw [splice_getElem? (splice l i d1) (i + d1.length) d2 (by omega), if_neg (by omega), if_neg (by omega),
      splice_getElem? l i d1 (by omega), if_neg (by omega), if_neg (by omega)]


theorem splice_trim (l core : List Bool) (i p s : Nat) (hb : i + p + core.length + s ≤ l.length)
    (hf1 : ∀ j, j < p → l[i + j]? = some false)
    (hf2 : ∀ j, j < s → l[i + p + core.length + j]? = some false) :
    splice l i (List.replicate p false ++ core ++ List.replicate s false) = splice l (i + p) core := by
  have hlen : (List.replicate p false ++ core ++ List.replicate s false).length = p + core.length + s := by
    simp; omega
  have hg : ∀ j, (splice l i (List.replicate p false ++ core ++ List.replicate s false))[j]? =
      if j < i then l[j]? else if j < i + (p + core.length + s) then
        (List.replicate p false ++ core ++ List.replicate s false)[j - i]? else l[j]? := by
    intro j; rw [splice_getElem? l i _ (by omega), hlen]
  have hX1 : ∀ j, j < p → (List.replicate p false ++ core ++ List.replicate s false)[j]? = some false := by
    intro j hj
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_replicate, hj]
  have hX2 : ∀ j, p ≤ j → j < p + core.length →
      (List.replicate p false ++ core ++ List.replicate s false)[j]? = core[j - p]? := by
    intro j h1 h2
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp
  have hX3 : ∀ j, p + core.length ≤ j → j < p + core.length + s →
      (List.replicate p false ++ core ++ List.replicate s false)[j]? = some false := by
    intro j h1 h2
    rw [List.getElem?_append_right (by simp; omega)]
    simp [List.getElem?_replicate]
    omega
  refine (splice_ext l (splice l i (List.replicate p false ++ core ++ List.replicate s false)) (i + p) core (by omega)).mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [splice_length _ _ _ (by omega)]
  · intro j hj
    rw [hg]
    by_cases a : j < i
    · rw [if_pos a]
    · rw [if_neg a, if_pos (by omega), hX1 _ (by omega)]
      have := hf1 (j - i) (by omega)
      rw [show i + (j - i) = j by omega] at this
      exact this.symm
  · intro j h1 h2
    rw [hg, if_neg (by omega), if_pos (by omega), hX2 _ (by omega) (by omega)]
    congr 1; omega
  · intro j hj
    rw [hg]
    by_cases a : j < i + (p + core.length + s)
    · rw [if_neg (by omega), if_pos a, hX3 _ (by omega) (by omega)]
      have := hf2 (j - (i + p + core.length)) (by omega)
      rw [show i + p + core.length + (j - (i + p + core.length)) = j by omega] at this
      exact this.symm
    · rw [if_neg (by omega), if_neg a]

end Myers
