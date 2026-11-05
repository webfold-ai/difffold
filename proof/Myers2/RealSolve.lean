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

theorem solve_spec :
    ∀ (N : Nat) (a b : Slice U32) (A B : List Nat) (ao bo : Usize) (ra rb : Slice Bool) (vf vb : Slice I32),
    A.length + B.length = N → vals a.val = A → vals b.val = B → A.length + B.length ≤ NMAX →
    ao.val + A.length ≤ ra.val.length → bo.val + B.length ≤ rb.val.length →
    (∀ j, j < A.length → ra.val[ao.val + j]? = some false) →
    (∀ j, j < B.length → rb.val[bo.val + j]? = some false) →
    2 * (A.length + B.length) + 3 ≤ vf.val.length → 2 * (A.length + B.length) + 3 ≤ vb.val.length →
    lines.solve a b ao bo ra rb vf vb ⦃ r => ∃ da di, Myers.Solve Myers.mid A B da di ∧
      r.1.val = Myers.splice ra.val ao.val da ∧ r.2.1.val = Myers.splice rb.val bo.val di ∧
      r.2.2.1.val.length = vf.val.length ∧ r.2.2.2.val.length = vb.val.length ⦄ := by
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
  trace_state
  sorry

end difffold_myers_extract
