import RealLines
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- Byte content of each slice of a list of slices. -/
def sb (v : List (Slice U8)) : List (List Nat) := v.map (fun s => bytes s.val)

theorem sb_append (a b : List (Slice U8)) : sb (a ++ b) = sb a ++ sb b := by simp [sb]

/-- The first line is cut at the first newline. -/
theorem lines_of_first10 (l : List Nat) (i : Nat) (h : IsFirst10 l i) :
    Myers.lines l = l.take (i + 1) :: Myers.lines (l.drop (i + 1)) := by
  obtain ⟨h1, h2⟩ := h
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h1).1
  have hne : l.take (i + 1) ≠ [] := by
    apply List.ne_nil_of_length_pos; simp; omega
  have hlast : (l.take (i + 1)).getLast? = some 10 := by
    have hlen : (l.take (i + 1)).length = i + 1 := by simp; omega
    rw [List.getLast?_eq_getElem?, hlen]
    simpa [List.getElem?_take] using h1
  have hdl : (l.take (i + 1)).dropLast = l.take i := by
    rw [List.dropLast_eq_take]; simp [List.take_take]; omega
  have hn : 10 ∉ (l.take (i + 1)).dropLast := by
    rw [hdl]; intro hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_take] at hk
    by_cases hki : k < i
    · exact h2 k hki (by simpa [hki] using hk)
    · simp [hki] at hk
  conv_lhs => rw [← List.take_append_drop (i + 1) l]
  exact Myers.lines_first _ _ hne hlast hn

/-- Cutting after a newline cuts the lines. -/
theorem lines_cut (l : List Nat) (c : Nat) (hc : 1 ≤ c) (h : l[c - 1]? = some 10) :
    Myers.lines l = Myers.lines (l.take c) ++ Myers.lines (l.drop c) := by
  conv_lhs => rw [← List.take_append_drop c l]
  apply Myers.lines_append
  right
  have hlt : c - 1 < l.length := (List.getElem?_eq_some_iff.mp h).1
  have hlen : (l.take c).length = c := by simp; omega
  rw [List.getLast?_eq_getElem?, hlen]
  simpa [List.getElem?_take, show c - 1 < c by omega] using h

/-- A text with no newline except possibly the last byte is a single line. -/
theorem lines_single (l : List Nat) (hl : l ≠ []) (h : ∀ j, j + 1 < l.length → l[j]? ≠ some 10) :
    Myers.lines l = [l] := by
  by_cases hlast : l.getLast? = some 10
  · apply Myers.lines_one l hl hlast
    intro hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    have hk' : k < l.dropLast.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [List.length_dropLast] at hk'
    rw [List.getElem?_dropLast] at hk
    exact h k (by omega) (by simpa [show k < l.length - 1 by omega] using hk)
  · apply Myers.lines_no_nl l _ hl
    intro hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    have hkl : k < l.length := (List.getElem?_eq_some_iff.mp hk).1
    by_cases hk1 : k + 1 < l.length
    · exact h k hk1 hk
    · apply hlast
      have : k = l.length - 1 := by omega
      subst this
      rw [List.getLast?_eq_getElem?]; exact hk


theorem split_seq_spec (B : Nat) (hB : B + 8 ≤ Usize.max) :
    ∀ (N : Nat) (t : Slice U8) (out : alloc.vec.Vec (Slice U8)), t.val.length = N → N ≤ B →
    out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max →
    lines.split_seq t out ⦃ r => sb r.val = sb out.val ++ Myers.lines (bytes t.val) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t out hN hNB hcap
  rw [lines.split_seq.eq_1]
  step as ⟨b, hb⟩
  split
  · rename_i hb0
    have : t.val = [] := List.length_eq_zero_iff.mp (hb.mp hb0)
    simp [Aeneas.Std.WP.spec_ok, this, bytes, Myers.lines]
  · rename_i hb0
    have hne : t.val ≠ [] := fun h => hb0 (hb.mpr (by simp [h]))
    step with (first_nl_spec B hB N t hN hNB) as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Found, List.drop_zero] at ho
      have hbne : bytes t.val ≠ [] := by intro h; apply hne; simpa [bytes] using h
      have hl := Myers.lines_no_nl _ ho hbne
      rw [hl] at hcap
      step as ⟨r, hr⟩
      rw [hr, hl]; simp [sb]
    | some i =>
      simp only [Found, List.drop_zero, Nat.sub_zero] at ho
      obtain ⟨_, ho⟩ := ho
      have hil : i.val < t.val.length := by
        have := (List.getElem?_eq_some_iff.mp ho.1).1; simpa [bytes_length] using this
      have hlines := lines_of_first10 _ _ ho
      rw [hlines] at hcap ⊢
      simp only [List.length_cons] at hcap
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = i.val + 1 := by omega
      step as ⟨s, hs, hs1⟩
      have hsv : s.val = t.val.take i1.val := by rw [hs]; simp [List.slice]
      step as ⟨out1, hout1⟩
      step as ⟨s1, hs', hs1'⟩
      have hsv1 : s1.val = t.val.drop i1.val := hs'
      have hslen1 : s1.val.length = N - i1.val := by rw [hsv1]; simp; omega
      have hlt1 : N - i1.val < N := by omega
      have hcap1 : out1.val.length + (Myers.lines (bytes s1.val)).length ≤ Usize.max := by
        rw [hout1, hsv1, bytes_drop, hi1v]; simp; omega
      step with (ih _ hlt1 s1 out1 hslen1 (by omega) hcap1) as ⟨r, hr⟩
      rw [hr, hout1, hsv1, bytes_drop, hi1v]
      simp [sb, hsv, bytes_take, hi1v]


/-- Postcondition of `split_into`. -/
def SplitPost (t : Slice U8) (out : alloc.vec.Vec (Slice U8)) (r : alloc.vec.Vec (Slice U8)) : Prop :=
  sb r.val = sb out.val ++ Myers.lines (bytes t.val)

theorem cut_step (B : Nat) (N : Nat)
    (ih : ∀ m < N, ∀ (t : Slice U8) (out : alloc.vec.Vec (Slice U8)), t.val.length = m → m ≤ B →
      out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max →
      lines.split_into t out ⦃ r => SplitPost t out r ⦄)
    (t : Slice U8) (out : alloc.vec.Vec (Slice U8)) (hN : t.val.length = N) (hNB : N ≤ B)
    (hcap : out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max)
    (c : Usize) (hc1 : 1 ≤ c.val) (hcl : c.val < N) (hend : (bytes t.val)[c.val - 1]? = some 10) :
    (do
      let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) t { «end» := c }
      let out1 ← lines.split_into s2 out
      let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) t { start := c }
      lines.split_into s3 out1) ⦃ r => SplitPost t out r ⦄ := by
  have hcut := lines_cut (bytes t.val) c.val hc1 hend
  rw [hcut] at hcap
  simp only [List.length_append] at hcap
  step as ⟨s2, hs2, hs2l⟩
  have hs2v : s2.val = t.val.take c.val := by rw [hs2]; simp [List.slice]
  have hl2 : s2.val.length = c.val := by rw [hs2v]; simp; omega
  have hcap2 : out.val.length + (Myers.lines (bytes s2.val)).length ≤ Usize.max := by
    rw [hs2v, bytes_take]; omega
  step with (ih c.val hcl s2 out hl2 (by omega) hcap2) as ⟨out1, hout1⟩
  step as ⟨s3, hs3, hs3l⟩
  have hs3v : s3.val = t.val.drop c.val := hs3
  have hl3 : s3.val.length = N - c.val := by rw [hs3v]; simp; omega
  have hlt3 : N - c.val < N := by omega
  have hlen1 : out1.val.length = out.val.length + (Myers.lines (bytes s2.val)).length := by
    have := congrArg List.length hout1
    simp only [sb, List.length_map, List.length_append] at this
    omega
  have hcap3 : out1.val.length + (Myers.lines (bytes s3.val)).length ≤ Usize.max := by
    rw [hlen1, hs2v, bytes_take, hs3v, bytes_drop]; omega
  step with (ih _ hlt3 s3 out1 hl3 (by omega) hcap3) as ⟨r, hr⟩
  unfold SplitPost at hout1 hr ⊢
  rw [hr, hout1, hs3v, hs2v, bytes_drop, bytes_take, hcut]
  simp


theorem fallback_step (B : Nat) (N : Nat)
    (ih : ∀ m < N, ∀ (t : Slice U8) (out : alloc.vec.Vec (Slice U8)), t.val.length = m → m ≤ B →
      out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max →
      lines.split_into t out ⦃ r => SplitPost t out r ⦄)
    (t : Slice U8) (out : alloc.vec.Vec (Slice U8)) (hN : t.val.length = N) (hNB : N ≤ B)
    (hcap : out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max)
    (mid : Usize) (hmid1 : 1 ≤ mid.val) (hmid : mid.val < N)
    (hH : ∀ j, mid.val ≤ j → j + 1 < N → (bytes t.val)[j]? ≠ some 10) :
    (do
      let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) t { «end» := mid }
      let o1 ← lines.last_nl s1
      let cut ←
        match o1 with
        | none => ok none
        | some i6 => do
            let i7 ← i6 + 1#usize
            ok (some i7)
      match cut with
      | none => alloc.vec.Vec.push out t
      | some c => do
          let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) t { «end» := c }
          let out1 ← lines.split_into s2 out
          let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) t { start := c }
          lines.split_into s3 out1) ⦃ r => SplitPost t out r ⦄ := by
  step as ⟨s1, hs1, hs1l⟩
  have hs1v : s1.val = t.val.take mid.val := by rw [hs1]; simp [List.slice]
  have hl1 : s1.val.length = mid.val := by rw [hs1v]; simp; omega
  step with (last_nl_spec _ s1 rfl) as ⟨o1, ho1⟩
  cases o1 with
  | none =>
    simp only [LastFound] at ho1
    rw [hs1v, bytes_take] at ho1
    have hne : bytes t.val ≠ [] := by
      apply List.ne_nil_of_length_pos; simp [bytes_length]; omega
    have hsingle : Myers.lines (bytes t.val) = [bytes t.val] := by
      apply lines_single _ hne
      intro j hj hc
      by_cases hjm : j < mid.val
      · apply ho1; exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_take]; simpa [hjm] using hc⟩
      · exact hH j (by omega) (by simp [bytes_length] at hj; omega) hc
    rw [hsingle] at hcap
    simp only [Aeneas.Std.WP.spec_ok]
    step as ⟨r, hr⟩
    unfold SplitPost
    rw [hr, hsingle]; simp [sb]
  | some i =>
    simp only [LastFound] at ho1
    rw [hs1v, bytes_take] at ho1
    obtain ⟨ho1a, _⟩ := ho1
    have hil : i.val < mid.val := by
      have := (List.getElem?_eq_some_iff.mp ho1a).1; simp [bytes_length] at this; omega
    step as ⟨i7, hi7⟩
    apply cut_step B N ih t out hN hNB hcap i7 (by omega) (by omega)
    rw [show i7.val - 1 = i.val by omega, ← ho1a]
    rw [List.getElem?_take]; simp [hil]


theorem split_into_spec (B : Nat) (hB : B + 8 ≤ Usize.max) :
    ∀ (N : Nat) (t : Slice U8) (out : alloc.vec.Vec (Slice U8)), t.val.length = N → N ≤ B →
    out.val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max →
    lines.split_into t out ⦃ r => SplitPost t out r ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t out hN hNB hcap
  rw [lines.split_into.eq_1]
  have hl : (Slice.len t).val = t.val.length := by simp [Slice.len]
  have hchunk : lines.SEQ_CHUNK.val = 4096 := by unfold lines.SEQ_CHUNK; simp
  split
  · rename_i hle
    exact split_seq_spec B hB N t out hN hNB hcap
  · rename_i hgt
    have hN4 : 4096 < N := by scalar_tac
    step as ⟨mid, hmid⟩
    step as ⟨s, hs, hs1⟩
    have hsv : s.val = t.val.drop mid.val := hs
    have hsl : s.val.length = N - mid.val := by rw [hsv]; simp; omega
    step with (first_nl_spec B hB _ s hsl (by omega)) as ⟨o, ho⟩
    have hmv : mid.val = N / 2 := by scalar_tac
    have hmid1 : 1 ≤ mid.val := by omega
    have hmidN : mid.val < N := by omega
    cases o with
    | none =>
      simp only [Found, List.drop_zero] at ho
      rw [hsv, bytes_drop] at ho
      refine fallback_step B N ih t out hN hNB hcap mid hmid1 hmidN ?_
      intro j hj _ hc
      apply ho
      exact List.mem_iff_getElem?.mpr ⟨j - mid.val, by rw [List.getElem?_drop]; simpa [show mid.val + (j - mid.val) = j by omega] using hc⟩
    | some i2 =>
      simp only [Found, List.drop_zero, Nat.sub_zero] at ho
      obtain ⟨_, ho⟩ := ho
      rw [hsv, bytes_drop] at ho
      have hi2l : i2.val < N - mid.val := by
        have := (List.getElem?_eq_some_iff.mp ho.1).1; simp [bytes_length] at this; omega
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      split
      · rename_i hlt
        step as ⟨c, hc⟩
        apply cut_step B N ih t out hN hNB hcap c (by omega) (by scalar_tac)
        rw [show c.val - 1 = mid.val + i2.val by omega]
        have := ho.1
        rw [List.getElem?_drop] at this
        exact this
      · rename_i hge
        refine fallback_step B N ih t out hN hNB hcap mid hmid1 hmidN ?_
        intro j hj hj1 hc
        have := ho.2 (j - mid.val) (by scalar_tac)
        apply this
        rw [List.getElem?_drop, show mid.val + (j - mid.val) = j by omega]; exact hc


theorem length_le_flatten : ∀ ls : List (List Nat), (∀ l ∈ ls, l ≠ []) → ls.length ≤ ls.flatten.length
  | [], _ => by simp
  | l :: ls, h => by
    have ih := length_le_flatten ls (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have : l ≠ [] := h l (by simp)
    have : 0 < l.length := List.length_pos_iff.mpr this
    rw [List.flatten_cons, List.length_append, List.length_cons]; omega

theorem lines_length_le (l : List Nat) : (Myers.lines l).length ≤ l.length := by
  have := length_le_flatten (Myers.lines l) (Myers.lines_ne_nil l)
  rwa [Myers.lines_flatten] at this

/-- `split_lines` returns the lines of the text, each as a subslice (the bytes of the slices). -/
theorem split_lines_spec (B : Nat) (hB : B + 8 ≤ Usize.max) (t : Slice U8) (hNB : t.val.length ≤ B) :
    lines.split_lines t ⦃ r => sb r.val = Myers.lines (bytes t.val) ⦄ := by
  unfold lines.split_lines
  have hcap : (alloc.vec.Vec.new (Slice U8)).val.length + (Myers.lines (bytes t.val)).length ≤ Usize.max := by
    have := lines_length_le (bytes t.val)
    have h2 := Slice.length_ineq t
    simp [alloc.vec.Vec.new, bytes_length] at *
    omega
  have := split_into_spec B hB _ t (alloc.vec.Vec.new (Slice U8)) rfl hNB hcap
  exact Aeneas.Std.WP.spec_mono this (fun r hr => by simpa [SplitPost, sb, alloc.vec.Vec.new] using hr)

end difffold_myers_extract
