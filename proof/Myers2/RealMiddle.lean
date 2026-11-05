import RealSweep
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- `middle` returns the model's middle snake and gives the scratch arrays back with their sizes. -/
theorem middle_spec (a b : Slice U32) (A B : List Nat) (vf vb : Slice I32)
    (ha : vals a.val = A) (hb : vals b.val = B) (hN : A.length + B.length ≤ NMAX)
    (hlf : vf.val.length = 2 * (A.length + B.length) + 3) (hlb : vb.val.length = 2 * (A.length + B.length) + 3) :
    lines.middle a b vf vb ⦃ r =>
      (∀ pt, Myers.midPt A B = some pt → 0 ≤ pt.1 → 0 ≤ pt.2 →
        (r.1.1.val : Int) = pt.1 ∧ (r.1.2.val : Int) = pt.2) ∧
      (Myers.midPt A B = none → r.1.1.val = 0 ∧ r.1.2.val = 0) ∧
      r.2.1.val.length = vf.val.length ∧ r.2.2.val.length = vb.val.length ⦄ := by
  unfold lines.middle
  have hNM : A.length + B.length ≤ 268435456 := by simpa [NMAX] using hN
  have hal : a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : b.val.length = B.length := by have := congrArg List.length hb; simpa [vals] using this
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
  have hn := hlen a (by omega)
  have hm := hlen b (by omega)
  step*
  · have hnv : n.val = A.length := by rw [n_post, hn, hal]
    have hmv : m.val = B.length := by rw [m_post, hm, hbl]
    simp only [Slice.length] at *; omega
  · have hnv : n.val = A.length := by rw [n_post, hn, hal]
    have hmv : m.val = B.length := by rw [m_post, hm, hbl]
    simp only [Slice.length] at *; omega
  · have hnv : n.val = A.length := by rw [n_post, hn, hal]
    have hmv : m.val = B.length := by rw [m_post, hm, hbl]
    have hand : i3.val = i2.val % 2 := by rw [i3_post]; exact and_one i2
    have hi7v : i7.val = ((A.length : Int) + B.length + 1) / 2 := by
      rw [i7_post, i6_post, i4_post]
      rw [Int.tdiv_eq_ediv] <;> omega
    have hoddI : (i3 != 0#i32) = true ↔ ((A.length : Int) - B.length) % 2 = 1 := by
      constructor
      · intro h
        have : ¬ (i3 = 0#i32) := by simpa using h
        have h0 : i3.val ≠ 0 := fun e => this (IScalar.eq_of_val_eq (by simpa using e))
        omega
      · intro h
        have : i3 ≠ 0#i32 := fun e => by
          have := congrArg IScalar.val e; simp at this; omega
        simpa using this
    have hvf1 : vf1.val.length = 2 * (A.length + B.length) + 3 := by
      rw [vf1_post, Slice.set_val_eq]; simp [hlf]
    have hvb1 : vb1.val.length = 2 * (A.length + B.length) + 3 := by
      rw [vb1_post, Slice.set_val_eq]; simp [hlb]
    have hinv : SInv ({ a := a, b := b, n := n, m := m, delta := i2, odd := (i3 != 0#i32), off := i5, vf := vf1, vb := vb1 } : lines.Search) A B :=
      ⟨ha, hb, by simpa using hnv, by simpa using hmv, by simp; omega, hoddI,
        by simp; omega, hvf1, hvb1, hN⟩
    have hoo : o.val = (i5.val + 1).toNat := o_post
    have hlt : o.val < vf.val.length := by omega
    have hlt2 : o.val < vb.val.length := by omega
    have hf0 : RdyArr vf1 i5.val (fun d k => Myers.F A B d k) 0 := by
      refine ⟨0#i32, ?_, rfl⟩
      rw [vf1_post, Slice.set_val_eq, ← hoo, List.getElem?_set_self hlt]
    have hb0 : RdyArr vb1 i5.val (fun d k => Myers.Bk A B d k) 0 := by
      refine ⟨0#i32, ?_, rfl⟩
      rw [vb1_post, Slice.set_val_eq, ← hoo, List.getElem?_set_self hlt2]
    have h0v : (0#i32).val = 0 := rfl
    step with (sweep_spec A B hNM ((A.length + B.length + 1) / 2 + 1)
      ({ a := a, b := b, n := n, m := m, delta := i2, odd := (i3 != 0#i32), off := i5, vf := vf1, vb := vb1 } : lines.Search)
      0#i32 i7 0 rfl (by scalar_tac) (by rw [h0v]; omega) (by omega) hinv hf0 hb0) as ⟨p, s3, bk3, hz⟩
    obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩ := hz
    have hfuel : (i7.val + 1 - 0).toNat = (A.length + B.length + 1) / 2 + 1 := by omega
    rw [hfuel] at hz1 hz2
    try simp only [Aeneas.Std.WP.spec_ok]
    have hmp : Myers.midPt A B = Myers.sweep A B ((A.length + B.length + 1) / 2 + 1) 0 := rfl
    rw [hmp]
    refine ⟨hz1, hz2, ?_, ?_⟩
    · rw [(hz0 s3).1]; exact hz4.trans (hvf1.trans hlf.symm)
    · rw [(hz0 s3).2]; exact hz5.trans (hvb1.trans hlb.symm)

end difffold_myers_extract
