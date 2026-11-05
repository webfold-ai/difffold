import RealX0
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- `forward_one`: sets `vf[off + k]` to the furthest-reaching value and reports the overlap. -/
def FwdPost (s : lines.Search) (A B : List Nat) (dn : Nat) (k : Int) (r : Option (Usize × Usize) × lines.Search × (lines.Search → lines.Search)) : Prop :=
  (∃ ik x, ik.val = (s.off.val + k).toNat ∧ x.val = (Myers.F A B dn k : Int) ∧ r.2.1 = { s with vf := s.vf.set ik x }) ∧
  ((r.1 = none ∧ ¬ Myers.fhit A B dn k) ∨
   (∃ p q : Usize, r.1 = some (p, q) ∧ Myers.fhit A B dn k ∧ (p.val : Int) = (Myers.F A B dn k : Int) ∧
      (q.val : Int) = (Myers.F A B dn k : Int) - k))

theorem forward_one_spec (s : lines.Search) (A B : List Nat) (dn : Nat) (k : Int) (d kk : I32)
    (hd : d.val = dn) (hk : kk.val = k) (hdom : Myers.Dom dn k) (hdle : dn ≤ A.length + B.length)
    (hinv : SInv s A B)
    (hf : RdyArr s.vf s.off.val (fun d k => Myers.F A B d k) dn)
    (hb : RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn) :
    lines.forward_one s d kk ⦃ r => FwdPost s A B dn k r ⦄ := by
  unfold lines.forward_one
  obtain ⟨ha, hb', hn, hm, hdl, hodd, hoff, hlf, hlb, hN⟩ := hinv
  have hNM' : A.length + B.length ≤ 268435456 := by simpa [NMAX] using hN
  have hdom0 := hdom
  obtain ⟨hd1, hd2, hd3⟩ := hdom
  have hdv : d.val ≤ 268435456 := by omega
  have hlfb : s.vf.length = 2 * (A.length + B.length) + 3 := by simpa [Slice.length] using hlf
  have hlbb : s.vb.length = 2 * (A.length + B.length) + 3 := by simpa [Slice.length] using hlb
  have hal : s.a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : s.b.val.length = B.length := by have := congrArg List.length hb'; simpa [vals] using this
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
  step as ⟨i, i_post⟩
  step as ⟨ikm, ikm_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨ikp, ikp_post⟩
  step as ⟨i2, i2_post⟩
  step with (x0_block s.vf A B dn k kk d i2 ikm ikp s.off.val hk hd (by omega) hdom0 hdle hoff hlfb
    (by rw [ikm_post]; congr 1; omega) (by rw [ikp_post]; congr 1; omega) hf
    (Myers.F_le A B) hNM') as ⟨x0, hx0v⟩
  have hxb : X0v A B dn k ≤ A.length + dn := by
    have := Myers.F_le A B dn k; rw [F_eq_X0v] at this; omega
  have hx0b : x0.val ≤ (A.length : Int) + dn := by rw [hx0v]; exact_mod_cast hxb
  have hx0n : 0 ≤ x0.val := by rw [hx0v]; omega
  have hx0k : kk.val ≤ x0.val := by rw [hx0v, hk]; exact X0v_ge A B dn k hdom0
  step as ⟨y0, hy0⟩
  step with (snake_step s.a s.b x0 y0 (by omega) (by omega) (by omega) (by omega)) as ⟨run, hr0, hr1, hr2, hr3⟩
  have hxr : x0.val + run.val ≤ (A.length : Int) + dn := by rw [hal] at hr1; omega
  have hyr : y0.val + run.val ≤ (A.length : Int) + 2 * dn + B.length := by
    rw [hbl] at hr2; omega
  step as ⟨x, hx⟩
  step as ⟨y, hy⟩
  step as ⟨ik, hik⟩
  have hikb : ik.val < s.vf.length := by omega
  step as ⟨xo, bk, hxo, hbk⟩
  step as ⟨kb, hkb⟩
  have hFx : x.val = (Myers.F A B dn k : Int) := by
    rw [F_eq_X0v A B dn k]
    have e1 : Myers.snake A B (X0v A B dn k) ((X0v A B dn k : Nat) - k) = run.val.toNat := by
      rw [hr3, ha, hb']
      have e3 : x0.val.toNat = X0v A B dn k := by omega
      have e4 : y0.val = ((X0v A B dn k : Nat) : Int) - k := by omega
      rw [e3, e4]; simp
    omega
  have hFy : y.val = (Myers.F A B dn k : Int) - k := by omega
  have hbkv : bk = Slice.set s.vf ik := hbk
  have hframe : ∃ ik' x', ik'.val = (s.off.val + k).toNat ∧ x'.val = (Myers.F A B dn k : Int) ∧
      ({ s with vf := bk x } : lines.Search) = { s with vf := s.vf.set ik' x' } :=
    ⟨ik, x, by rw [hik]; congr 1; omega, hFx, by rw [hbkv]⟩
  have hodd' : (s.odd = true) ↔ ((A.length : Int) - B.length) % 2 = 1 := hodd
  split
  · rename_i hso
    have hpar : ((A.length : Int) - B.length) % 2 = 1 := hodd'.mp hso
    split
    · rename_i hc1
      split
      · rename_i hc2
        rw [gt_iff_lt, IScalar.lt_equiv] at hc1
        rw [IScalar.lt_equiv] at hc2
        obtain ⟨d', hdn⟩ : ∃ d', dn = d' + 1 := ⟨dn - 1, by omega⟩
        subst hdn
        have hkbv : kb.val = (A.length : Int) - B.length - k := by omega
        have hDomb : Myers.Dom d' kb.val := by
          unfold Myers.Dom; push_cast at *; omega
        have hrb : ∀ k', Myers.Dom d' k' → ∃ e, s.vb.val[(s.off.val + k').toNat]? = some e ∧
            e.val = (Myers.Bk A B d' k' : Int) := hb
        have hi3pre : 0 ≤ ({ s with vf := bk x } : lines.Search).off.val + kb.val := by
          show 0 ≤ s.off.val + kb.val; push_cast at *; omega
        have hi3pre2 : ({ s with vf := bk x } : lines.Search).off.val + kb.val ≤ I32.max := by
          show s.off.val + kb.val ≤ I32.max; push_cast at *; omega
        step with (Search_ix_spec { s with vf := bk x } kb hi3pre hi3pre2) as ⟨i3, hi3⟩
        have hi3' : i3.val = (s.off.val + kb.val).toNat := hi3
        have hi3b : i3.val < s.vb.length := by push_cast at *; omega
        step with (rd_read s.vb s.off.val (fun d k => Myers.Bk A B d k) d' hrb i3 kb.val hi3' hDomb hi3b) as ⟨i4, hi4⟩
        have hBle : (Myers.Bk A B d' kb.val : Int) ≤ A.length + d' := by
          have := Myers.F_le A.reverse B.reverse d' kb.val
          unfold Myers.Bk; simp at this; exact_mod_cast this
        have hi4n : 0 ≤ i4.val := by rw [hi4]; omega
        step as ⟨i5, hi5⟩
        split
        · rename_i hc3
          rw [ge_iff_le, IScalar.le_equiv] at hc3
          step as ⟨i6, hi6⟩
          step as ⟨i7, hi7⟩
          have hxn : 0 ≤ x.val := by omega
          have hyn : 0 ≤ y.val := by omega
          have e6 := hus x hxn
          have e7 := hus y hyn
          try simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨hframe, Or.inr ⟨i6, i7, rfl, ⟨hpar, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
          · push_cast at *; omega
          · push_cast at *; omega
          · have : (Myers.Bk A B (d' + 1 - 1) ((A.length : Int) - B.length - k) : Int) = i4.val := by
              rw [hi4, Nat.add_sub_cancel, ← hkbv]
            push_cast at *; omega
          · rw [hi6, e6]; omega
          · rw [hi7, e7]; omega
        · rename_i hc3
          rw [ge_iff_le, IScalar.le_equiv] at hc3
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨hframe, Or.inl ⟨rfl, ?_⟩⟩
          rintro ⟨_, _, _, h4⟩
          have : (Myers.Bk A B (d' + 1 - 1) ((A.length : Int) - B.length - k) : Int) = i4.val := by
            rw [hi4, Nat.add_sub_cancel, ← hkbv]
          push_cast at *; omega
      · rename_i hc2
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hframe, Or.inl ⟨rfl, ?_⟩⟩
        rintro ⟨_, _, h3, _⟩
        rw [IScalar.lt_equiv] at hc2
        omega
    · rename_i hc1
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨hframe, Or.inl ⟨rfl, ?_⟩⟩
      rintro ⟨_, h2, _, _⟩
      rw [gt_iff_lt, IScalar.lt_equiv] at hc1
      omega
  · rename_i hso
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨hframe, Or.inl ⟨rfl, ?_⟩⟩
    rintro ⟨h1, _, _, _⟩
    exact hso (hodd'.mpr h1)

end difffold_myers_extract
