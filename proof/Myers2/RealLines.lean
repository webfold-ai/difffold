import RealNL
import Text
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem IsFirst10_skipn (s : List Nat) (k : Nat) (hno : 10 ∉ s.take k) (i : Nat)
    (h : IsFirst10 (s.drop k) i) : IsFirst10 s (i + k) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [List.getElem?_drop] at h1; simpa [Nat.add_comm] using h1, ?_⟩
  intro j hj
  by_cases hjk : j < k
  · intro hc
    apply hno
    have : (s.take k)[j]? = some 10 := by rw [List.getElem?_take]; simpa [hjk] using hc
    exact List.mem_of_getElem? this
  · have := h2 (j - k) (by omega)
    rw [List.getElem?_drop] at this
    rwa [show k + (j - k) = j by omega] at this

theorem IsFirst10_take (s : List Nat) (k i : Nat) (h : IsFirst10 (s.take k) i) : IsFirst10 s i := by
  obtain ⟨h1, h2⟩ := h
  have hi : i < k := by
    have := (List.getElem?_eq_some_iff.mp h1).1; simp at this; omega
  refine ⟨by rw [List.getElem?_take] at h1; simpa [hi] using h1, ?_⟩
  intro j hj hc
  apply h2 j hj
  rw [List.getElem?_take]; simpa [show j < k by omega] using hc

theorem bytes_drop (l : List U8) (k : Nat) : bytes (l.drop k) = (bytes l).drop k := by simp [bytes, List.map_drop]
theorem bytes_take (l : List U8) (k : Nat) : bytes (l.take k) = (bytes l).take k := by simp [bytes, List.map_take]

theorem first_nl_spec (B : Nat) (hB : B + 8 ≤ Usize.max) :
    ∀ (N : Nat) (t : Slice U8), t.val.length = N → N ≤ B →
    lines.first_nl t ⦃ r => Found 0 (bytes t.val) r ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t hN hNB
  rw [lines.first_nl.eq_1]
  have hl : (Slice.len t).val = t.val.length := by simp [Slice.len]
  split
  · rename_i hle
    have := first_in_block_spec t (by omega) _ 0#usize rfl
    exact Aeneas.Std.WP.spec_mono this (fun r hr => hr)
  · rename_i hgt
    step as ⟨i2, hi2⟩
    step as ⟨s, hs, hs1⟩
    have hsv : s.val = t.val.take i2.val := by rw [hs]; simp [List.slice]
    have hslen : s.val.length = i2.val := by rw [hsv]; simp; scalar_tac
    have hlt : i2.val < N := by scalar_tac
    step with (ih _ hlt s hslen (by omega)) as ⟨o, ho⟩
    cases o with
    | some j =>
      simp only [Aeneas.Std.WP.spec_ok]
      simp only [Found, List.drop_zero, Nat.sub_zero] at ho ⊢
      refine ⟨by omega, ?_⟩
      rw [hsv, bytes_take] at ho
      exact IsFirst10_take _ _ _ ho.2
    | none =>
      simp only [Found, List.drop_zero] at ho
      rw [hsv, bytes_take] at ho
      step as ⟨i4, hi4⟩
      step as ⟨s1, hs', hs1'⟩
      have hsv1 : s1.val = t.val.drop i4.val := hs'
      have hslen1 : s1.val.length = N - i4.val := by rw [hsv1]; simp; omega
      have hlt1 : N - i4.val < N := by
        have : 0 < i4.val := by scalar_tac
        omega
      step with (ih _ hlt1 s1 hslen1 (by omega)) as ⟨o1, ho1⟩
      have hi4v : i4.val = i2.val := by scalar_tac
      cases o1 with
      | none =>
        simp only [Aeneas.Std.WP.spec_ok, Found, List.drop_zero]
        simp only [Found, List.drop_zero] at ho1
        rw [hsv1, bytes_drop, hi4v] at ho1
        have hd : bytes t.val = (bytes t.val).take i2.val ++ (bytes t.val).drop i2.val := (List.take_append_drop _ _).symm
        rw [hd]; simp only [List.mem_append, not_or]; exact ⟨ho, ho1⟩
      | some j =>
        simp only [Found, List.drop_zero, Nat.sub_zero] at ho1
        rw [hsv1, bytes_drop, hi4v] at ho1
        have hjl := (List.getElem?_eq_some_iff.mp ho1.2.1).1
        simp [bytes_length] at hjl
        step as ⟨i7, hi7⟩
        have hb : j.val + i7.val ≤ Usize.max := by scalar_tac
        step as ⟨i8, hi8⟩
        simp only [Found, List.drop_zero, Nat.sub_zero]
        refine ⟨by omega, ?_⟩
        have := IsFirst10_skipn (bytes t.val) i2.val ho j.val ho1.2
        have e : i8.val = j.val + i2.val := by scalar_tac
        rw [e]; exact this


/-! ### last newline -/

def LastFound (l : List Nat) : Option Usize → Prop
  | none => 10 ∉ l
  | some i => IsLast10 l i.val

theorem IsLast10_drop (l : List Nat) (h i : Nat) (hi : IsLast10 (l.drop h) i) : IsLast10 l (i + h) := by
  obtain ⟨h1, h2⟩ := hi
  refine ⟨by rw [List.getElem?_drop] at h1; simpa [Nat.add_comm] using h1, ?_⟩
  intro j hj
  have := h2 (j - h) (by omega)
  rw [List.getElem?_drop] at this
  rwa [show h + (j - h) = j by omega] at this

theorem IsLast10_take (l : List Nat) (h i : Nat) (hno : 10 ∉ l.drop h) (hi : IsLast10 (l.take h) i) :
    IsLast10 l i := by
  obtain ⟨h1, h2⟩ := hi
  have hih : i < h := by
    have := (List.getElem?_eq_some_iff.mp h1).1; simp at this; omega
  refine ⟨by rw [List.getElem?_take] at h1; simpa [hih] using h1, ?_⟩
  intro j hj hc
  by_cases hjh : j < h
  · apply h2 j hj; rw [List.getElem?_take]; simpa [hjh] using hc
  · apply hno
    have : (l.drop h)[j - h]? = some 10 := by rw [List.getElem?_drop]; simpa [show h + (j - h) = j by omega] using hc
    exact List.mem_of_getElem? this

theorem no10_snoc (l : List Nat) (N : Nat) (hlen : l.length = N + 1) (h1 : 10 ∉ l.take N)
    (h2 : l[N]? ≠ some 10) : 10 ∉ l := by
  intro h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  by_cases hkN : k < N
  · apply h1; exact List.mem_iff_getElem?.mpr ⟨k, by rw [List.getElem?_take]; simpa [hkN] using hk⟩
  · by_cases hk' : k = N
    · subst hk'; exact h2 hk
    · rw [List.getElem?_eq_none (by omega)] at hk; simp at hk

theorem IsLast10_snoc (l : List Nat) (N i : Nat) (hlen : l.length = N + 1) (h2 : l[N]? ≠ some 10)
    (hi : IsLast10 (l.take N) i) : IsLast10 l i := by
  obtain ⟨h1, h3⟩ := hi
  have hiN : i < N := by
    have := (List.getElem?_eq_some_iff.mp h1).1; simp at this; omega
  refine ⟨by rw [List.getElem?_take] at h1; simpa [hiN] using h1, ?_⟩
  intro j hj hc
  by_cases hjN : j < N
  · apply h3 j hj; rw [List.getElem?_take]; simpa [hjN] using hc
  · by_cases hk' : j = N
    · subst hk'; exact h2 hc
    · rw [List.getElem?_eq_none (by omega)] at hc; simp at hc

theorem last_in_block_spec : ∀ (N : Nat) (t : Slice U8), t.val.length = N →
    lines.last_in_block t ⦃ r => LastFound (bytes t.val) r ⦄ := by
  intro N
  induction N with
  | zero =>
    intro t hN
    rw [lines.last_in_block.eq_1]
    have : t.val = [] := List.length_eq_zero_iff.mp hN
    split
    · simp [Aeneas.Std.WP.spec_ok, LastFound, this, bytes]
    · rename_i hn; simp [Slice.len, this] at hn
  | succ N ih =>
    intro t hN
    rw [lines.last_in_block.eq_1]
    have hl : (Slice.len t).val = N + 1 := by simp [Slice.len, hN]
    split
    · rename_i h0; omega
    · step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      split
      · rename_i h10
        simp only [Aeneas.Std.WP.spec_ok, LastFound]
        have hi' : i.val = N := by omega
        have hx : (bytes t.val)[N]? = some 10 := by
          have : i1.val = 10 := by rw [h10]; rfl
          have hlt : N < t.val.length := by omega
          have e : i1 = t.val[N]'hlt := by rw [hi1]; simp [hi']
          simp [bytes, List.getElem?_eq_getElem hlt, ← e, this]
        refine ⟨by rwa [hi'], ?_⟩
        intro j hj
        rw [hi'] at hj
        rw [List.getElem?_eq_none]; simp; simp [bytes_length]; omega
      · rename_i h10
        step as ⟨s, hs, hs1⟩
        have hsv : s.val = t.val.take i.val := by rw [hs]; simp [List.slice]
        have hi' : i.val = N := by omega
        have hslen : s.val.length = N := by rw [hsv]; simp; omega
        step with (ih s hslen) as ⟨o, ho⟩
        cases o with
        | none =>
          simp only [Aeneas.Std.WP.spec_ok, LastFound] at ho ⊢
          rw [hsv, bytes_take, hi'] at ho
          have hlt : N < t.val.length := by omega
          have hx : (bytes t.val)[N]? ≠ some 10 := by
            have e : i1 = t.val[N]'hlt := by rw [hi1]; simp [hi']
            have hne : i1.val ≠ 10 := fun h => h10 (UScalar.eq_of_val_eq (by simpa using h))
            simp [bytes, List.getElem?_eq_getElem hlt, ← e, hne]
          exact no10_snoc _ N (by simp [bytes_length]; omega) ho hx
        | some j =>
          simp only [Aeneas.Std.WP.spec_ok, LastFound] at ho ⊢
          rw [hsv, bytes_take, hi'] at ho
          have hlt : N < t.val.length := by omega
          have hx : (bytes t.val)[N]? ≠ some 10 := by
            have e : i1 = t.val[N]'hlt := by rw [hi1]; simp [hi']
            have hne : i1.val ≠ 10 := fun h => h10 (UScalar.eq_of_val_eq (by simpa using h))
            simp [bytes, List.getElem?_eq_getElem hlt, ← e, hne]
          exact IsLast10_snoc _ N _ (by simp [bytes_length]; omega) hx ho


theorem last_nl_spec : ∀ (N : Nat) (t : Slice U8), t.val.length = N →
    lines.last_nl t ⦃ r => LastFound (bytes t.val) r ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t hN
  rw [lines.last_nl.eq_1]
  have hl : (Slice.len t).val = t.val.length := by simp [Slice.len]
  split
  · exact last_in_block_spec _ t rfl
  · rename_i hgt
    step as ⟨i2, hi2⟩
    step as ⟨s, hs, hs1⟩
    have hsv : s.val = t.val.drop i2.val := hs
    have hslen : s.val.length = N - i2.val := by rw [hsv]; simp [hN]
    have hlt : N - i2.val < N := by scalar_tac
    step with (ih _ hlt s hslen) as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [LastFound] at ho
      rw [hsv, bytes_drop] at ho
      step as ⟨i4, hi4⟩
      step as ⟨s1, hs', hs1'⟩
      have hsv1 : s1.val = t.val.take i4.val := by rw [hs']; simp [List.slice]
      have hi4v : i4.val = i2.val := by scalar_tac
      have hslen1 : s1.val.length = i4.val := by rw [hsv1]; simp; scalar_tac
      have hlt1 : i4.val < N := by scalar_tac
      step with (ih _ hlt1 s1 hslen1) as ⟨o1, ho1⟩
      cases o1 with
      | none =>
        simp only [LastFound] at ho1 ⊢
        rw [hsv1, bytes_take, hi4v] at ho1
        have hd : bytes t.val = (bytes t.val).take i2.val ++ (bytes t.val).drop i2.val := (List.take_append_drop _ _).symm
        rw [hd]; simp only [List.mem_append, not_or]; exact ⟨ho1, ho⟩
      | some j =>
        simp only [LastFound] at ho1 ⊢
        rw [hsv1, bytes_take, hi4v] at ho1
        exact IsLast10_take _ _ _ ho ho1
    | some j =>
      simp only [LastFound] at ho
      rw [hsv, bytes_drop] at ho
      step as ⟨i4, hi4⟩
      have hjl := (List.getElem?_eq_some_iff.mp ho.1).1
      simp [bytes_length] at hjl
      have hb : j.val + i4.val ≤ Usize.max := by scalar_tac
      step as ⟨i6, hi6⟩
      simp only [Aeneas.Std.WP.spec_ok, LastFound]
      have := IsLast10_drop (bytes t.val) i2.val j.val ho
      have e : i6.val = j.val + i2.val := by scalar_tac
      rw [e]; exact this

/-! ### counting newlines -/

theorem count_pad8 (l : List Nat) : (pad8 l).count 10 = (l.take 8).count 10 := by
  simp [pad8, List.count_append, List.count_replicate]

theorem count_block_spec : ∀ (N : Nat) (t : Slice U8), t.val.length = N →
    lines.count_block t ⦃ r => r.val = (bytes t.val).count 10 ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t hN
  rw [lines.count_block.eq_1]
  step as ⟨b, hb⟩
  split
  · rename_i hb0
    have : t.val = [] := List.length_eq_zero_iff.mp (hb.mp hb0)
    simp [Aeneas.Std.WP.spec_ok, this, bytes]
  · rename_i hb0
    have hne : t.val.length ≠ 0 := fun h => hb0 (hb.mpr h)
    have hu8 : ∀ u : U8, u.val < 256 := fun u => by scalar_tac
    have hbl : ∀ x ∈ bytes t.val, x < 256 := by
      intro x hx; simp only [bytes, List.mem_map] at hx
      obtain ⟨u, _, rfl⟩ := hx; exact hu8 u
    step with (word_spec _ t rfl) as ⟨w, hw⟩
    step with (nl_mask_spec w (pad8 (bytes t.val)) (pad8_length _) (pad8_lt _ hbl) hw) as ⟨m, hm⟩
    step with (newline_count_spec m (pad8 (bytes t.val)) (pad8_length _) hm) as ⟨c, hc⟩
    step as ⟨i4, hi4⟩
    step as ⟨s, hs, hs1⟩
    have hsv : s.val = t.val.drop i4.val := hs
    have hi4v : i4.val = min t.val.length 8 := by
      rw [hi4]; unfold core.cmp.impls.OrdUsize.min
      have h1 : t.len.val = t.val.length := by simp [Slice.len]
      have h8 : (8#usize).val = 8 := by simp
      split
      · rename_i h; have : (8#usize).val < t.len.val := by scalar_tac
        omega
      · rename_i h; have : ¬ (8#usize).val < t.len.val := by scalar_tac
        omega
    have hslen : s.val.length = N - i4.val := by rw [hsv]; simp; omega
    have hlt : N - i4.val < N := by omega
    step with (ih _ hlt s hslen) as ⟨c5, hc5⟩
    have hdr : (bytes t.val).drop i4.val = (bytes t.val).drop 8 := by
      have hd : i4.val = min (bytes t.val).length 8 := by rw [bytes_length]; exact hi4v
      rcases Nat.le_total (bytes t.val).length 8 with h | h
      · rw [hd, Nat.min_eq_left h, List.drop_of_length_le h, List.drop_of_length_le (Nat.le_refl _)]
      · rw [hd, Nat.min_eq_right h]
    have hcnt : (bytes t.val).count 10 = (pad8 (bytes t.val)).count 10 + (bytes s.val).count 10 := by
      rw [count_pad8, hsv, bytes_drop, hdr, ← List.count_append, List.take_append_drop]
    have hbd : (bytes t.val).count 10 ≤ t.val.length := by
      have := List.count_le_length (a := 10) (l := bytes t.val); simpa [bytes_length] using this
    have hmaxl := Slice.length_ineq t
    step as ⟨r, hr⟩
    scalar_tac

theorem count_byte_spec : ∀ (N : Nat) (t : Slice U8) (b : U8), t.val.length = N →
    lines.count_byte t b ⦃ r => r.val = (bytes t.val).count 10 ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t b hN
  rw [lines.count_byte.eq_1]
  split
  · exact count_block_spec _ t rfl
  · rename_i hgt
    have hl : (Slice.len t).val = N := by simp [Slice.len, hN]
    step as ⟨i2, hi2⟩
    step as ⟨s, hs, hs1⟩
    have hsv : s.val = t.val.take i2.val := by rw [hs]; simp [List.slice]
    have hslen : s.val.length = i2.val := by rw [hsv]; simp; scalar_tac
    have hlt : i2.val < N := by scalar_tac
    step with (ih _ hlt s 10#u8 hslen) as ⟨c1, hc1⟩
    step as ⟨i5, hi5⟩
    step as ⟨s1, hs', hs1'⟩
    have hsv1 : s1.val = t.val.drop i5.val := hs'
    have hi5v : i5.val = i2.val := by scalar_tac
    have hslen1 : s1.val.length = N - i5.val := by rw [hsv1]; simp; omega
    have hlt1 : N - i5.val < N := by scalar_tac
    step with (ih _ hlt1 s1 10#u8 hslen1) as ⟨c2, hc2⟩
    have hcnt : (bytes t.val).count 10 = (bytes s.val).count 10 + (bytes s1.val).count 10 := by
      rw [hsv, hsv1, bytes_take, bytes_drop, hi5v, ← List.count_append, List.take_append_drop]
    have hbd : (bytes t.val).count 10 ≤ t.val.length := by
      have := List.count_le_length (a := 10) (l := bytes t.val); simpa [bytes_length] using this
    have hmaxl := Slice.length_ineq t
    step as ⟨r, hr⟩
    scalar_tac

theorem count_lines_spec (t : Slice U8) :
    lines.count_lines t ⦃ r => r.val = (Myers.lines (bytes t.val)).length ⦄ := by
  rw [Myers.lines_length]
  unfold lines.count_lines
  step with (count_byte_spec _ t 10#u8 rfl) as ⟨c, hc⟩
  step as ⟨b, hb⟩
  have hcb : c.val ≤ t.val.length := by
    rw [hc]; have := List.count_le_length (a := 10) (l := bytes t.val); simpa [bytes_length] using this
  have hmaxl := Slice.length_ineq t
  by_cases hnil : t.val = []
  · have hbt : b = true := by rw [hb]; simp [hnil]
    subst hbt
    simp only [if_true, bind_tc_ok, lift]
    simp [hnil, bytes, core.convert.num.FromUsizeBool.from, hc]
  · have hbf : b = false := by
      cases b
      · rfl
      · exfalso; apply hnil; have := hb.mp rfl; exact List.length_eq_zero_iff.mp this
    subst hbf
    simp only [Bool.false_eq_true, if_false]
    trace_state
    sorry

end difffold_myers_extract
