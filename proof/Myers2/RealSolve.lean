import RealMiddle
import SolveLen
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem vals_take (l : List U32) (n : Nat) : vals (l.take n) = (vals l).take n := by simp [vals, List.map_take]
theorem vals_drop (l : List U32) (n : Nat) : vals (l.drop n) = (vals l).drop n := by simp [vals, List.map_drop]
theorem vals_len (l : List U32) : (vals l).length = l.length := by simp [vals]

/-- The proved specs of the extracted `common_prefix` and `common_suffix` give the `Trim` of the model. -/
theorem trim_slices (a b : List U32) (s e : Nat)
    (hs1 : s ≤ min a.length b.length) (hs2 : a.take s = b.take s)
    (hs3 : s = min a.length b.length ∨ ∃ x y, a[s]? = some x ∧ b[s]? = some y ∧ x ≠ y)
    (he1 : e ≤ min (a.drop s).length (b.drop s).length)
    (he2 : (a.drop s).drop ((a.drop s).length - e) = (b.drop s).drop ((b.drop s).length - e))
    (he3 : e = min (a.drop s).length (b.drop s).length ∨ (e < min (a.drop s).length (b.drop s).length ∧
      ∃ x y, (a.drop s)[(a.drop s).length - 1 - e]? = some x ∧ (b.drop s)[(b.drop s).length - 1 - e]? = some y ∧ x ≠ y)) :
    Myers.Trim (vals a) (vals b) ((vals a).take s) (((vals a).drop s).take (a.length - s - e))
      (((vals b).drop s).take (b.length - s - e)) ((vals a).drop (a.length - e)) := by
  simp only [List.length_drop] at he1 he2 he3
  have n1 : s + (a.length - s - e) = a.length - e := by omega
  have n2 : s + (b.length - s - e) = b.length - e := by omega
  rw [List.drop_drop, List.drop_drop, n1, n2] at he2
  have := Myers.trim_of_specs (vals a) (vals b) s e (by simpa [vals_len] using hs1)
    (by have := congrArg vals hs2; simpa [vals_take] using this)
    (by simpa [vals_len] using he1)
    (by have := congrArg vals he2; simpa [vals_drop, vals_len] using this)
    (by
      rcases hs3 with h | ⟨x, y, hx, hy, hxy⟩
      · left; simpa [vals_len] using h
      · right
        refine ⟨x.val, y.val, ?_, ?_, fun h => hxy (UScalar.eq_of_val_eq h)⟩
        · simp [vals, List.getElem?_map, hx]
        · simp [vals, List.getElem?_map, hy])
    (by
      rcases he3 with h | ⟨h1, x, y, hx, hy, hxy⟩
      · left; simpa [vals_len] using h
      · right
        refine ⟨by simpa [vals_len] using h1, x.val, y.val, ?_, ?_, fun h => hxy (UScalar.eq_of_val_eq h)⟩
        · rw [List.getElem?_drop] at hx
          have : s + (a.length - s - 1 - e) = a.length - 1 - e := by omega
          rw [this] at hx
          simp [vals, List.getElem?_map, hx]
        · rw [List.getElem?_drop] at hy
          have : s + (b.length - s - 1 - e) = b.length - 1 - e := by omega
          rw [this] at hy
          simp [vals, List.getElem?_map, hy])
  simpa [vals_len, vals_take, vals_drop] using this

theorem setSlice_splice (l d : List Bool) (i : Nat) (h : i + d.length ≤ l.length) :
    l.setSlice! i d = Myers.splice l i d := by
  have : min d.length (l.length - i) = d.length := by omega
  unfold List.setSlice! Myers.splice
  simp only []
  rw [this, List.take_length]

theorem splice_trim_all (l core : List Bool) (i p s : Nat) (hb : i + (p + core.length + s) ≤ l.length)
    (hf : ∀ j, j < p + core.length + s → l[i + j]? = some false) :
    Myers.splice l i (List.replicate p false ++ core ++ List.replicate s false) = Myers.splice l (i + p) core :=
  Myers.splice_trim l core i p s (by omega) (fun j hj => hf j (by omega)) (fun j hj => by
    have := hf (p + core.length + j) (by omega)
    rwa [show i + (p + core.length + j) = i + p + core.length + j by omega] at this)

/-- What `solve` achieves: the model flags, written into the two flag arrays, scratch arrays keep their size. -/
def SolvePost (A B : List Nat) (ao bo : Usize) (ra rb : Slice Bool) (vf vb : Slice I32)
    (r : Slice Bool × Slice Bool × Slice I32 × Slice I32) : Prop :=
  ∃ da di, Myers.Solve Myers.mid A B da di ∧
    r.1.val = Myers.splice ra.val ao.val da ∧ r.2.1.val = Myers.splice rb.val bo.val di ∧
    r.2.2.1.val.length = vf.val.length ∧ r.2.2.2.val.length = vb.val.length

theorem solve_spec :
    ∀ (N : Nat) (a b : Slice U32) (A B : List Nat) (ao bo : Usize) (ra rb : Slice Bool) (vf vb : Slice I32),
    A.length + B.length = N → vals a.val = A → vals b.val = B → A.length + B.length ≤ NMAX →
    ao.val + A.length ≤ ra.val.length → bo.val + B.length ≤ rb.val.length →
    (∀ j, j < A.length → ra.val[ao.val + j]? = some false) →
    (∀ j, j < B.length → rb.val[bo.val + j]? = some false) →
    2 * (A.length + B.length) + 3 ≤ vf.val.length → 2 * (A.length + B.length) + 3 ≤ vb.val.length →
    lines.solve a b ao bo ra rb vf vb ⦃ r => SolvePost A B ao bo ra rb vf vb r ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro a b A B ao bo ra rb vf vb hN ha hb hNM hao hbo hfa hfb hvf hvb
  rw [lines.solve.eq_1]
  have hal : a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : b.val.length = B.length := by have := congrArg List.length hb; simpa [vals] using this
  step with (common_prefix_u32 a b) as ⟨s, hs1, hs2, hs3⟩
  step as ⟨s1, hs1a, hs1b⟩
  step as ⟨s2, hs2a, hs2b⟩
  step with (common_suffix_u32 s1 s2) as ⟨e, he1, he2, he3⟩
  rw [hs1a, hs2a] at he1 he2 he3
  have hTrim := trim_slices a.val b.val s.val e.val hs1 hs2 hs3 he1 he2 he3
  clear hs3 he3
  have hse : s.val + e.val ≤ a.val.length ∧ s.val + e.val ≤ b.val.length := by
    simp only [List.length_drop] at he1; omega
  have hlA : a.len.val = a.val.length := by simp [Slice.len]
  have hlB : b.len.val = b.val.length := by simp [Slice.len]
  have hrap := ra.property
  have hrbp := rb.property
  have hs1' : s.val ≤ a.val.length ∧ s.val ≤ b.val.length := by
    simp only [Nat.le_min] at hs1; exact hs1
  step as ⟨i1, hi1⟩
  step as ⟨a1, ha1v, ha1l⟩
  step as ⟨i3, hi3⟩
  step as ⟨b1, hb1v, hb1l⟩
  step as ⟨ao1, hao1⟩
  step as ⟨bo1, hbo1⟩
  step as ⟨b2, hb2⟩
  have hi1v : i1.val = a.val.length - e.val := by rw [hi1, hlA]
  have hi3v : i3.val = b.val.length - e.val := by rw [hi3, hlB]
  have ha1' : vals a1.val = ((vals a.val).drop s.val).take (a.val.length - s.val - e.val) := by
    rw [ha1v]; simp [List.slice, vals, List.map_take, List.map_drop]
    congr 1; omega
  have hb1' : vals b1.val = ((vals b.val).drop s.val).take (b.val.length - s.val - e.val) := by
    rw [hb1v]; simp [List.slice, vals, List.map_take, List.map_drop]
    congr 1; omega
  obtain ⟨p, A1, B1, sf, hT, hpl, hA1l, hB1l, hA1, hB1, hsfl⟩ : ∃ p A1 B1 sf, Myers.Trim A B p A1 B1 sf ∧
      p.length = s.val ∧ A1.length = a1.val.length ∧ B1.length = b1.val.length ∧
      vals a1.val = A1 ∧ vals b1.val = B1 ∧ sf.length = e.val := by
    refine ⟨(vals a.val).take s.val, _, _, (vals a.val).drop (a.val.length - e.val), ?_, ?_, ?_, ?_, ha1', hb1', ?_⟩
    · rw [← ha, ← hb]; exact hTrim
    · simp [vals_len]; omega
    · rw [← vals_len a1.val, ha1']
    · rw [← vals_len b1.val, hb1']
    · simp [vals_len]; omega
  have hAl : A.length = s.val + a1.val.length + e.val := by
    have := congrArg List.length hT.1; simp at this; omega
  have hBl : B.length = s.val + b1.val.length + e.val := by
    have := congrArg List.length hT.2.1; simp at this; omega
  have hao1v : ao1.val = ao.val + s.val := hao1
  have hbo1v : bo1.val = bo.val + s.val := hbo1
  clear hs1 hs2 he1 he2 hs1a hs2a hs1b hs2b hTrim ha1v hb1v ha1' hb1' hi1 hi3
  split
  · rename_i hb2t
    have hA1e : A1 = [] := by
      have h0 : a1.length = 0 := by rw [hb2] at hb2t; simpa using hb2t
      have : A1.length = 0 := by rw [hA1l]; simpa [Slice.length] using h0
      exact List.length_eq_zero_iff.mp this
    subst hA1e
    have hb1e : b1.val.length = B1.length := hB1l.symm
    step as ⟨i5, hi5⟩
    step as ⟨s3, bk, hs3v, hs3l, hbk⟩
    step as ⟨s4, hs4l, hs4v⟩
    try simp only [Aeneas.Std.WP.spec_ok]
    unfold SolvePost
    have hAl' : A.length = p.length + 0 + sf.length := by
      have := congrArg List.length hT.1; simpa using this
    have hBl' : B.length = p.length + B1.length + sf.length := by
      have := congrArg List.length hT.2.1; simp at this; omega
    refine ⟨_, _, Myers.Solve.emptyA hT, ?_, ?_, rfl, rfl⟩
    · rw [splice_trim_all ra.val [] ao.val p.length sf.length (by simp; omega) (by
        intro j hj; exact hfa j (by omega)), Myers.splice_nil]
    · have hi5v : i5.val = bo1.val + b1.val.length := by rw [hi5]; simp [Slice.len]
      have hs3len : s3.val.length = B1.length := by
        have : s3.length = i5.val - bo1.val := hs3l
        simp only [Slice.length] at this; omega
      rw [hbk, Slice.setSlice!_val, hs4v]
      simp only [Slice.length] at hs3len ⊢
      rw [hs3len]
      rw [setSlice_splice _ _ _ (by simp; omega)]
      rw [splice_trim_all rb.val (List.replicate B1.length true) bo.val p.length sf.length (by rw [List.length_replicate]; omega) (by
        intro j hj; exact hfb j (by rw [List.length_replicate] at hj; omega))]
      rw [hbo1v, hpl]
  · rename_i hb2f
    have hA1ne : A1 ≠ [] := by
      intro h
      have h0 : a1.length = 0 := by
        have : a1.val.length = 0 := by rw [← hA1l, h]; rfl
        simpa [Slice.length] using this
      apply hb2f; rw [hb2]; simpa using h0
    step as ⟨b3, hb3⟩
    split
    · rename_i hb3t
      have hB1e : B1 = [] := by
        have h0 : b1.length = 0 := by rw [hb3] at hb3t; simpa using hb3t
        have : B1.length = 0 := by rw [hB1l]; simpa [Slice.length] using h0
        exact List.length_eq_zero_iff.mp this
      subst hB1e
      step as ⟨i5, hi5⟩
      step as ⟨s3, bk, hs3v, hs3l, hbk⟩
      step as ⟨s4, hs4l, hs4v⟩
      try simp only [Aeneas.Std.WP.spec_ok]
      unfold SolvePost
      have hAl' : A.length = p.length + A1.length + sf.length := by
        have := congrArg List.length hT.1; simp at this; omega
      have hBl' : B.length = p.length + 0 + sf.length := by
        have := congrArg List.length hT.2.1; simpa using this
      refine ⟨_, _, Myers.Solve.emptyB hT, ?_, ?_, rfl, rfl⟩
      · have hi5v : i5.val = ao1.val + a1.val.length := by rw [hi5]; simp [Slice.len]
        have hs3len : s3.val.length = A1.length := by
          have : s3.length = i5.val - ao1.val := hs3l
          simp only [Slice.length] at this; omega
        rw [hbk, Slice.setSlice!_val, hs4v]
        simp only [Slice.length] at hs3len ⊢
        rw [hs3len]
        rw [setSlice_splice _ _ _ (by simp; omega)]
        rw [splice_trim_all ra.val (List.replicate A1.length true) ao.val p.length sf.length (by rw [List.length_replicate]; omega) (by
          intro j hj; exact hfa j (by rw [List.length_replicate] at hj; omega))]
        rw [hao1v, hpl]
      · rw [splice_trim_all rb.val [] bo.val p.length sf.length (by simp; omega) (by
          intro j hj; exact hfb j (by omega)), Myers.splice_nil]
    · rename_i hb3f
      have hB1ne : B1 ≠ [] := by
        intro h
        have h0 : b1.length = 0 := by
          have : b1.val.length = 0 := by rw [← hB1l, h]; rfl
          simpa [Slice.length] using this
        apply hb3f; rw [hb3]; simpa using h0
      have hAl' : A.length = p.length + A1.length + sf.length := by
        have := congrArg List.length hT.1; simp at this; omega
      have hBl' : B.length = p.length + B1.length + sf.length := by
        have := congrArg List.length hT.2.1; simp at this; omega
      have hN1 : A1.length + B1.length ≤ NMAX := by omega
      step with (middle_spec a1 b1 A1 B1 vf vb hA1 hB1 hN1 (by omega) (by omega))
        as ⟨xy, vf1, vb1, hm1, hm2, hm3, hm4⟩
      obtain ⟨x, y⟩ := xy
      simp only [] at hm1 hm2 hm3 hm4 ⊢
      obtain ⟨x0, y0, hmp, hx0, hy0, hsp, hnt0, hntn⟩ :=
        Myers.midPt_spec A1 B1 hA1ne hB1ne hT.2.2.1 hT.2.2.2
      have hxy := hm1 _ hmp (by omega) (by omega)
      have hxv : x.val = x0 := by simp at hxy; omega
      have hyv : y.val = y0 := by simp at hxy; omega
      have hmid : Myers.mid A1 B1 = (x.val, y.val) := by
        unfold Myers.mid; rw [hmp]; simp [hxv, hyv]
      have hxle : x.val ≤ A1.length := by omega
      have hyle : y.val ≤ B1.length := by omega
      have hxlt : x.val + y.val < A1.length + B1.length := by omega
      have hxpos : 0 < x.val + y.val := by omega
      have hmid' : Myers.mid A1 B1 = (x0, y0) := by rw [hmid, hxv, hyv]
      have hsp' := hsp
      have hnt : ¬((x0 = 0 ∧ y0 = 0) ∨ (x0 = A1.length ∧ y0 = B1.length)) := by omega
      have hrec : (do
          let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32) a1 { «end» := x }
          let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32) b1 { «end» := y }
          let (ra1, rb1, vf2, vb2) ← lines.solve s3 s4 ao1 bo1 ra rb vf1 vb1
          let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) a1 { start := x }
          let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) b1 { start := y }
          let i5 ← ao1 + x
          let i6 ← bo1 + y
          lines.solve s5 s6 i5 i6 ra1 rb1 vf2 vb2 : Result _) ⦃ r => SolvePost A B ao bo ra rb vf vb r ⦄ := by
        step as ⟨s3, hs3v, hs3l⟩
        step as ⟨s4, hs4v, hs4l⟩
        have hs3A : vals s3.val = A1.take x.val := by
          rw [hs3v, ← hA1]; simp [List.slice, vals, List.map_take]
        have hs4B : vals s4.val = B1.take y.val := by
          rw [hs4v, ← hB1]; simp [List.slice, vals, List.map_take]
        have hao1v' : ao1.val = ao.val + p.length := by rw [hao1v, hpl]
        have hbo1v' : bo1.val = bo.val + p.length := by rw [hbo1v, hpl]
        have hfaA : ∀ j, j < (A1.take x.val).length → ra.val[ao1.val + j]? = some false := by
          intro j hj
          have := hfa (p.length + j) (by simp at hj; omega)
          rw [show ao.val + (p.length + j) = ao1.val + j by omega] at this; exact this
        have hfbB : ∀ j, j < (B1.take y.val).length → rb.val[bo1.val + j]? = some false := by
          intro j hj
          have := hfb (p.length + j) (by simp at hj; omega)
          rw [show bo.val + (p.length + j) = bo1.val + j by omega] at this; exact this
        step with (ih (x.val + y.val) (by omega) s3 s4 (A1.take x.val) (B1.take y.val) ao1 bo1 ra rb vf1 vb1
          (by simp; omega) hs3A hs4B (by simp; omega) (by simp; omega) (by simp; omega) hfaA hfbB
          (by simp; omega) (by simp; omega)) as ⟨ra1, rb1, vf2, vb2, hr1⟩
        obtain ⟨d1, e1, hS1, hra1, hrb1, hl1, hl2⟩ := hr1
        dsimp only at hra1 hrb1 hl1 hl2
        have hd1 := (Myers.Solve.lens hS1)
        have he1' := hd1.2
        have hd1' := hd1.1
        simp only [List.length_take, Nat.min_eq_left hxle, Nat.min_eq_left hyle] at hd1' he1'
        step as ⟨s5, hs5v, hs5l⟩
        step as ⟨s6, hs6v, hs6l⟩
        step as ⟨i5, hi5⟩
        step as ⟨i6, hi6⟩
        have hs5A : vals s5.val = A1.drop x.val := by
          rw [hs5v, ← hA1]; simp [vals, List.map_drop]
        have hs6B : vals s6.val = B1.drop y.val := by
          rw [hs6v, ← hB1]; simp [vals, List.map_drop]
        have hrl : ra1.val.length = ra.val.length := by
          rw [hra1]; exact Myers.splice_length _ _ _ (by omega)
        have hrbl : rb1.val.length = rb.val.length := by
          rw [hrb1]; exact Myers.splice_length _ _ _ (by omega)
        have hfa2 : ∀ j, j < (A1.drop x.val).length → ra1.val[i5.val + j]? = some false := by
          intro j hj
          rw [hra1, Myers.splice_getElem? _ _ _ (by omega), if_neg (by simp at hj; omega), if_neg (by omega)]
          have := hfa (p.length + x.val + j) (by simp at hj; omega)
          rw [show ao.val + (p.length + x.val + j) = i5.val + j by omega] at this; exact this
        have hfb2 : ∀ j, j < (B1.drop y.val).length → rb1.val[i6.val + j]? = some false := by
          intro j hj
          rw [hrb1, Myers.splice_getElem? _ _ _ (by omega), if_neg (by simp at hj; omega), if_neg (by omega)]
          have := hfb (p.length + y.val + j) (by simp at hj; omega)
          rw [show bo.val + (p.length + y.val + j) = i6.val + j by omega] at this; exact this
        have hvf2 : 2 * ((A1.drop x.val).length + (B1.drop y.val).length) + 3 ≤ vf2.val.length := by
          simp; omega
        refine Aeneas.Std.WP.spec_mono (ih (A1.length - x.val + (B1.length - y.val)) (by omega) s5 s6
          (A1.drop x.val) (B1.drop y.val)
          i5 i6 ra1 rb1 vf2 vb2 (by simp) hs5A hs6B (by simp; omega) (by simp; omega) (by simp; omega) hfa2 hfb2
          (by simp; omega) (by simp; omega)) ?_
        rintro ⟨ra2, rb2, vf3, vb3⟩ hr2
        obtain ⟨d2, e2, hS2, hra2, hrb2, hl3, hl4⟩ := hr2
        dsimp only at hra2 hrb2 hl3 hl4
        have hd2 := (Myers.Solve.lens hS2)
        simp only [List.length_drop] at hd2
        unfold SolvePost
        have hS1' := hS1
        have hS2' := hS2
        rw [hxv, hyv] at hS1' hS2'
        refine ⟨_, _, Myers.Solve.split hT hA1ne hB1ne hmid' hnt hS1' hS2', ?_, ?_, ?_, ?_⟩
        · show ra2.val = _
          have hlen12 : (d1 ++ d2).length = A1.length := by
            have := hd2.1; simp at this ⊢; omega
          rw [hra2, hra1, show i5.val = ao1.val + d1.length by omega,
            Myers.splice_splice ra.val d1 d2 ao1.val (by omega), hao1v',
            splice_trim_all ra.val (d1 ++ d2) ao.val p.length sf.length (by omega) (by
              intro j hj; exact hfa j (by omega))]
        · show rb2.val = _
          have hlen12 : (e1 ++ e2).length = B1.length := by
            have := hd2.2; simp at this ⊢; omega
          rw [hrb2, hrb1, show i6.val = bo1.val + e1.length by omega,
            Myers.splice_splice rb.val e1 e2 bo1.val (by omega), hbo1v',
            splice_trim_all rb.val (e1 ++ e2) bo.val p.length sf.length (by omega) (by
              intro j hj; exact hfb j (by omega))]
        · show vf3.val.length = _
          omega
        · show vb3.val.length = _
          omega
      have lenA1 : (Slice.len a1).val = A1.length := by simp [Slice.len]; omega
      have lenB1 : (Slice.len b1).val = B1.length := by simp [Slice.len]; omega
      have hnt0' : ¬(x.val = 0 ∧ y.val = 0) := by omega
      have hntn' : ¬(x.val = A1.length ∧ y.val = B1.length) := by omega
      show Aeneas.Std.WP.spec (if x = 0#usize then _ else _) _
      split
      · rename_i h1
        have e1 := congrArg UScalar.val h1
        split
        · rename_i h2
          have e2 := congrArg UScalar.val h2
          exfalso; simp at e1 e2; omega
        · split
          · rename_i h3
            have e3 := congrArg UScalar.val h3
            split
            · rename_i h4
              have e4 := congrArg UScalar.val h4
              exfalso; omega
            · exact hrec
          · exact hrec
      · split
        · rename_i h3
          have e3 := congrArg UScalar.val h3
          split
          · rename_i h4
            have e4 := congrArg UScalar.val h4
            exfalso; omega
          · exact hrec
        · exact hrec

end difffold_myers_extract
