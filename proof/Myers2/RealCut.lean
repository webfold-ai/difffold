import RealSplit
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- `q` is the start of the line containing byte `p` (the cut position), with `p` at most the length. -/
def LineStart (l : List Nat) (p q : Nat) : Prop :=
  q ≤ p ∧ (q = 0 ∨ l[q - 1]? = some 10) ∧ ∀ j, q ≤ j → j < p → l[j]? ≠ some 10

theorem line_start_spec (t : Slice U8) (p : Usize) (hp : p.val ≤ t.val.length) :
    lines.line_start t p ⦃ q => LineStart (bytes t.val) p.val q.val ⦄ := by
  unfold lines.line_start
  step as ⟨s, hs, hs1⟩
  have hsv : s.val = t.val.take p.val := by rw [hs]; simp [List.slice]
  step with (last_nl_spec _ s rfl) as ⟨o, ho⟩
  cases o with
  | none =>
    simp only [LastFound] at ho
    rw [hsv, bytes_take] at ho
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨by simp, Or.inl (by simp), ?_⟩
    intro j _ hj hc
    apply ho
    exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_take]; simpa [hj] using hc⟩
  | some i =>
    simp only [LastFound] at ho
    rw [hsv, bytes_take] at ho
    obtain ⟨h1, h2⟩ := ho
    have hi : i.val < p.val := by
      have := (List.getElem?_eq_some_iff.mp h1).1; simp [bytes_length] at this; omega
    step as ⟨r, hr⟩
    refine ⟨by omega, Or.inr ?_, ?_⟩
    · rw [show r.val - 1 = i.val by omega]
      rw [List.getElem?_take] at h1; simpa [hi] using h1
    · intro j hj hjp hc
      have := h2 j (by omega)
      apply this
      rw [List.getElem?_take]; simpa [hjp] using hc

theorem shrink_suffix_spec (ro : Slice U8) (q : Usize) (B : Nat) (hB : B + 8 ≤ Usize.max)
    (hq : q.val ≤ ro.val.length) (hro : ro.val.length ≤ B) :
    lines.shrink_suffix ro q ⦃ r => (r.val = 0 ∧ 10 ∉ (bytes ro.val).drop (ro.val.length - q.val)) ∨
      (∃ k, IsFirst10 ((bytes ro.val).drop (ro.val.length - q.val)) k ∧ r.val = q.val - k - 1) ⦄ := by
  unfold lines.shrink_suffix
  have hl : (Slice.len ro).val = ro.val.length := by simp [Slice.len]
  step as ⟨i1, hi1⟩
  step as ⟨s, hs, hs1⟩
  have hsv : s.val = ro.val.drop (ro.val.length - q.val) := by rw [hs]; simp [hi1, hl]
  have hsl : s.val.length = q.val := by rw [hsv]; simp; omega
  step with (first_nl_spec B hB _ s hsl (by omega)) as ⟨o, ho⟩
  rw [hsv, bytes_drop] at ho
  cases o with
  | none =>
    simp only [Found, List.drop_zero] at ho
    simp only [Aeneas.Std.WP.spec_ok]
    exact Or.inl ⟨rfl, ho⟩
  | some k =>
    simp only [Found, List.drop_zero, Nat.sub_zero] at ho
    have hk : k.val < q.val := by
      have := (List.getElem?_eq_some_iff.mp ho.2.1).1; simp [bytes_length] at this; omega
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    exact Or.inr ⟨k.val, ho.2, by omega⟩


/-- The cut suffix of length `q'` is common to both texts and starts a line in both. -/
def SufPost (A Bl : List Nat) (q q' : Nat) : Prop :=
  q' ≤ q ∧ A.drop (A.length - q') = Bl.drop (Bl.length - q') ∧
    (q' = 0 ∨ ((q' = A.length ∨ A[A.length - q' - 1]? = some 10) ∧
      (q' = Bl.length ∨ Bl[Bl.length - q' - 1]? = some 10)))

theorem suf_mono (A Bl : List Nat) (q q' : Nat) (hA : q ≤ A.length) (hB : q ≤ Bl.length) (hq : q' ≤ q)
    (h : A.drop (A.length - q) = Bl.drop (Bl.length - q)) :
    A.drop (A.length - q') = Bl.drop (Bl.length - q') := by
  have e1 : A.drop (A.length - q') = (A.drop (A.length - q)).drop (q - q') := by
    rw [List.drop_drop]; congr 1; omega
  have e2 : Bl.drop (Bl.length - q') = (Bl.drop (Bl.length - q)).drop (q - q') := by
    rw [List.drop_drop]; congr 1; omega
  rw [e1, e2, h]

theorem shrink_ok (A Bl : List Nat) (q r : Nat) (hA : q ≤ A.length) (hB : q ≤ Bl.length)
    (h : A.drop (A.length - q) = Bl.drop (Bl.length - q))
    (hr : (r = 0 ∧ 10 ∉ A.drop (A.length - q)) ∨
      (∃ k, IsFirst10 (A.drop (A.length - q)) k ∧ r = q - k - 1)) : SufPost A Bl q r := by
  rcases hr with ⟨rfl, _⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩
  · exact ⟨by omega, by simp, Or.inl rfl⟩
  · have hkq : k < q := by
      have := (List.getElem?_eq_some_iff.mp hk1).1; simp at this; omega
    refine ⟨by omega, suf_mono A Bl q _ hA hB (by omega) h, ?_⟩
    by_cases h0 : q - k - 1 = 0
    · exact Or.inl h0
    · right
      refine ⟨Or.inr ?_, Or.inr ?_⟩
      · rw [show A.length - (q - k - 1) - 1 = (A.length - q) + k by omega]
        rw [List.getElem?_drop] at hk1; exact hk1
      · rw [show Bl.length - (q - k - 1) - 1 = (Bl.length - q) + k by omega]
        rw [h] at hk1
        rw [List.getElem?_drop] at hk1; exact hk1

theorem suffix_on_line_start_spec (B : Nat) (hB : B + 8 ≤ Usize.max) (ro rn : Slice U8) (q : Usize)
    (hqo : q.val ≤ ro.val.length) (hqn : q.val ≤ rn.val.length) (hro : ro.val.length ≤ B)
    (h : (bytes ro.val).drop (ro.val.length - q.val) = (bytes rn.val).drop (rn.val.length - q.val)) :
    lines.suffix_on_line_start ro rn q ⦃ r => SufPost (bytes ro.val) (bytes rn.val) q.val r.val ⦄ := by
  have hA : q.val ≤ (bytes ro.val).length := by simpa [bytes_length] using hqo
  have hBl : q.val ≤ (bytes rn.val).length := by simpa [bytes_length] using hqn
  have h' : (bytes ro.val).drop ((bytes ro.val).length - q.val) =
      (bytes rn.val).drop ((bytes rn.val).length - q.val) := by simpa [bytes_length] using h
  have hl1 : (Slice.len ro).val = ro.val.length := by simp [Slice.len]
  have hl2 : (Slice.len rn).val = rn.val.length := by simp [Slice.len]
  have hshrink : lines.shrink_suffix ro q ⦃ r => SufPost (bytes ro.val) (bytes rn.val) q.val r.val ⦄ := by
    have := shrink_suffix_spec ro q B hB hqo hro
    refine Aeneas.Std.WP.spec_mono this (fun r hr => ?_)
    refine shrink_ok _ _ _ _ hA hBl h' ?_
    simpa [bytes_length] using hr
  have hkeep : (q.val = 0 ∨ ((q.val = (bytes ro.val).length ∨ (bytes ro.val)[(bytes ro.val).length - q.val - 1]? = some 10) ∧
      (q.val = (bytes rn.val).length ∨ (bytes rn.val)[(bytes rn.val).length - q.val - 1]? = some 10))) →
      SufPost (bytes ro.val) (bytes rn.val) q.val q.val := by
    intro hk
    exact ⟨le_refl _, suf_mono _ _ _ _ hA hBl (le_refl _) h', hk⟩
  have byte_at : ∀ (x : Slice U8) (i : Usize) (b : U8) (hi : i.val < x.val.length), b = x.val[i.val]'hi →
      ((bytes x.val)[i.val]? = some 10 ↔ (b != 10#u8) = false) := by
    intro x i b hi hb
    have hget : (bytes x.val)[i.val]? = some (x.val[i.val]'hi).val := by
      simp [bytes, List.getElem?_eq_getElem hi]
    have hb' : b = x.val[i.val]'hi := hb
    rw [hget, hb']
    constructor
    · intro h
      have : (x.val[i.val]'hi).val = 10 := Option.some.inj h
      have e : x.val[i.val]'hi = 10#u8 := UScalar.eq_of_val_eq (by simpa using this)
      simp [e]
    · intro h
      have : x.val[i.val]'hi = 10#u8 := by simpa using h
      rw [this]; rfl
  unfold lines.suffix_on_line_start
  split
  · rename_i hq0
    rw [Aeneas.Std.WP.spec_ok]
    apply hkeep
    left; scalar_tac
  · rename_i hq0
    have hqpos : 0 < q.val := by
      have : q.val ≠ 0 := fun e => hq0 (UScalar.eq_of_val_eq (by simpa using e))
      omega
    dsimp only
    split
    · rename_i hlt
      have hlt' : q.val < ro.val.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi3v : i3.val = ro.val.length - q.val - 1 := by scalar_tac
      have hbo := byte_at ro i3 i4 (by omega) hi4
      by_cases hb : (i4 != 10#u8) = true
      · rw [if_pos hb]; exact hshrink
      · have hb' : (i4 != 10#u8) = false := Bool.eq_false_iff.mpr hb
        rw [if_neg hb]
        have hro10 : (bytes ro.val)[ro.val.length - q.val - 1]? = some 10 := by
          rw [← hi3v]; exact hbo.mpr hb'
        split
        · rename_i hlt2
          have hlt2' : q.val < rn.val.length := by scalar_tac
          step as ⟨i7, hi7⟩
          step as ⟨i8, hi8⟩
          step as ⟨i9, hi9⟩
          have hi8v : i8.val = rn.val.length - q.val - 1 := by scalar_tac
          have hbn := byte_at rn i8 i9 (by omega) hi9
          by_cases hb2 : (i9 != 10#u8) = true
          · rw [if_pos hb2]; exact hshrink
          · have hb2' : (i9 != 10#u8) = false := Bool.eq_false_iff.mpr hb2
            rw [if_neg hb2, Aeneas.Std.WP.spec_ok]
            apply hkeep
            right
            refine ⟨Or.inr (by simpa [bytes_length] using hro10), Or.inr ?_⟩
            have := hbn.mpr hb2'
            rw [hi8v] at this
            simpa [bytes_length] using this
        · rename_i hge2
          rw [Aeneas.Std.WP.spec_ok]
          apply hkeep
          right
          refine ⟨Or.inr (by simpa [bytes_length] using hro10), Or.inl ?_⟩
          simp [bytes_length]; scalar_tac
    · rename_i hge
      split
      · rename_i hlt2
        have hlt2' : q.val < rn.val.length := by scalar_tac
        step as ⟨i3, hi3⟩
        step as ⟨i4, hi4⟩
        step as ⟨i5, hi5⟩
        have hi4v : i4.val = rn.val.length - q.val - 1 := by scalar_tac
        have hbn := byte_at rn i4 i5 (by omega) hi5
        by_cases hb2 : (i5 != 10#u8) = true
        · rw [if_pos hb2]; exact hshrink
        · have hb2' : (i5 != 10#u8) = false := Bool.eq_false_iff.mpr hb2
          rw [if_neg hb2, Aeneas.Std.WP.spec_ok]
          apply hkeep
          right
          refine ⟨Or.inl ?_, Or.inr ?_⟩
          · simp [bytes_length]; scalar_tac
          · have := hbn.mpr hb2'
            rw [hi4v] at this
            simpa [bytes_length] using this
      · rename_i hge2
        rw [Aeneas.Std.WP.spec_ok]
        apply hkeep
        right
        refine ⟨Or.inl ?_, Or.inl ?_⟩ <;> (simp [bytes_length]; scalar_tac)

end difffold_myers_extract
