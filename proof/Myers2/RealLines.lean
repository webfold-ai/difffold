import RealNL
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
        step as ⟨i7, hi7⟩
        step as ⟨i8, hi8⟩
        try simp only [Aeneas.Std.WP.spec_ok]
        simp only [Found, List.drop_zero, Nat.sub_zero] at ho1 ⊢
        refine ⟨by omega, ?_⟩
        rw [hsv1, bytes_drop, hi4v] at ho1
        have := IsFirst10_skipn (bytes t.val) i2.val ho (j.val - 0) (by simpa using ho1.2)
        have e : i8.val = j.val + i2.val := by scalar_tac
        rw [e]; simpa using this

end difffold_myers_extract
