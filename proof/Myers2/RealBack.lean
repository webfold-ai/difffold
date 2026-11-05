import RealFwd
import RealSnakeBack
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

attribute [step] difffold_myers_extract.snake_back_spec

/-- `backward_one`: sets `vb[off + k]` and reports the overlap with the forward values of the same round. -/
def BwdPost (s : lines.Search) (A B : List Nat) (dn : Nat) (k : Int) (r : Option (Usize × Usize) × lines.Search × (lines.Search → lines.Search)) : Prop :=
  BackId r.2.2 ∧
  (∃ ik x, ik.val = (s.off.val + k).toNat ∧ x.val = (Myers.Bk A B dn k : Int) ∧ r.2.1 = { s with vb := s.vb.set ik x }) ∧
  ((r.1 = none ∧ ¬ Myers.bhit A B dn k) ∨
   (∃ p q : Usize, r.1 = some (p, q) ∧ Myers.bhit A B dn k ∧
      (0 ≤ (A.length : Int) - (Myers.Bk A B dn k : Int) → (p.val : Int) = (A.length : Int) - (Myers.Bk A B dn k : Int)) ∧
      (0 ≤ (B.length : Int) - ((Myers.Bk A B dn k : Int) - k) →
        (q.val : Int) = (B.length : Int) - ((Myers.Bk A B dn k : Int) - k))))

theorem backward_one_spec (s : lines.Search) (A B : List Nat) (dn : Nat) (k : Int) (d kk : I32)
    (hd : d.val = dn) (hk : kk.val = k) (hdom : Myers.Dom dn k) (hdle : dn ≤ A.length + B.length)
    (hinv : SInv s A B)
    (hf : ∀ k', Myers.Dom dn k' → ∃ e, s.vf.val[(s.off.val + k').toNat]? = some e ∧ e.val = (Myers.F A B dn k' : Int))
    (hb : RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn) :
    lines.backward_one s d kk ⦃ r => BwdPost s A B dn k r ⦄ := by
  unfold lines.backward_one
  obtain ⟨ha, hb', hn, hm, hdl, hodd, hoff, hlf, hlb, hN⟩ := hinv
  have hNM' : A.length + B.length ≤ 268435456 := by simpa [NMAX] using hN
  have hdom0 := hdom
  obtain ⟨hd1, hd2, hd3⟩ := hdom
  have hdv : d.val ≤ 268435456 := by omega
  have hlfb : 2 * (A.length + B.length) + 3 ≤ s.vf.length := by simpa [Slice.length] using hlf
  have hlbb : 2 * (A.length + B.length) + 3 ≤ s.vb.length := by simpa [Slice.length] using hlb
  have hal : s.a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : s.b.val.length = B.length := by have := congrArg List.length hb'; simpa [vals] using this
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
  step as ⟨i, i_post⟩
  step as ⟨ikm, ikm_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨ikp, ikp_post⟩
  step as ⟨i2, i2_post⟩
  step with (x0_block s.vb A.reverse B.reverse dn k kk d i2 ikm ikp s.off.val hk hd (by omega) hdom0
    (by simpa using hdle) (by simp; omega) (by simpa using hlbb)
    (by rw [ikm_post]; congr 1; omega) (by rw [ikp_post]; congr 1; omega) hb
    (Myers.F_le A.reverse B.reverse) (by simpa using hNM')) as ⟨x0, hx0v⟩
  have hxb : X0v A.reverse B.reverse dn k ≤ A.length + dn := by
    have := Myers.F_le A.reverse B.reverse dn k; rw [F_eq_X0v] at this; simp at this; omega
  have hx0b : x0.val ≤ (A.length : Int) + dn := by rw [hx0v]; exact_mod_cast hxb
  have hx0n : 0 ≤ x0.val := by rw [hx0v]; omega
  have hx0k : kk.val ≤ x0.val := by rw [hx0v, hk]; exact X0v_ge A.reverse B.reverse dn k hdom0
  step as ⟨y0, hy0⟩
  step with (snake_back_spec s.a s.b x0 y0 (by omega) (by omega) (by omega) (by omega)) as ⟨run, hr0, hr1, hr2, hr3⟩
  have hxr : x0.val + run.val ≤ (A.length : Int) + dn := by rw [hal] at hr1; omega
  have hyr : y0.val + run.val ≤ (A.length : Int) + 2 * dn + B.length := by
    rw [hbl] at hr2; omega
  step as ⟨x, hx⟩
  step as ⟨y, hy⟩
  step as ⟨ik, hik⟩
  have hikb : ik.val < s.vb.length := by omega
  step as ⟨xo, bk, hxo, hbk⟩
  step as ⟨kf, hkf⟩
  have hFx : x.val = (Myers.Bk A B dn k : Int) := by
    unfold Myers.Bk
    rw [F_eq_X0v A.reverse B.reverse dn k]
    have e1 : Myers.snake A.reverse B.reverse (X0v A.reverse B.reverse dn k)
        ((X0v A.reverse B.reverse dn k : Nat) - k) = run.val.toNat := by
      have e3 : x0.val.toNat = X0v A.reverse B.reverse dn k := by omega
      have e4 : y0.val = ((X0v A.reverse B.reverse dn k : Nat) : Int) - k := by omega
      rw [hr3, e3, e4, ha, hb']; simp
    omega
  have hFy : y.val = (Myers.Bk A B dn k : Int) - k := by omega
  have hbkv : bk = Slice.set s.vb ik := hbk
  have hframe : ∃ ik' x', ik'.val = (s.off.val + k).toNat ∧ x'.val = (Myers.Bk A B dn k : Int) ∧
      ({ s with vb := bk x } : lines.Search) = { s with vb := s.vb.set ik' x' } :=
    ⟨ik, x, by rw [hik]; congr 1; omega, hFx, by rw [hbkv]⟩
  have hodd' : (s.odd = true) ↔ ((A.length : Int) - B.length) % 2 = 1 := hodd
  split
  · rename_i hso
    have hpar : ((A.length : Int) - B.length) % 2 = 1 := hodd'.mp hso
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨fun t => ⟨rfl, rfl⟩, hframe, Or.inl ⟨rfl, ?_⟩⟩
    rintro ⟨h1, _, _, _⟩
    exact h1 hpar
  · rename_i hso
    have hpar : ¬ (((A.length : Int) - B.length) % 2 = 1) := fun h => hso (hodd'.mpr h)
    split
    · rename_i hc1
      split
      · rename_i hc2
        rw [ge_iff_le, IScalar.le_equiv] at hc1
        rw [IScalar.le_equiv] at hc2
        have hkfv : kf.val = (A.length : Int) - B.length - k := by omega
        have hDomf : Myers.Dom dn kf.val := by
          unfold Myers.Dom; push_cast at *; omega
        have hi3pre : 0 ≤ ({ s with vb := bk x } : lines.Search).off.val + kf.val := by
          show 0 ≤ s.off.val + kf.val; push_cast at *; omega
        have hi3pre2 : ({ s with vb := bk x } : lines.Search).off.val + kf.val ≤ I32.max := by
          show s.off.val + kf.val ≤ I32.max; push_cast at *; omega
        step with (Search_ix_spec { s with vb := bk x } kf hi3pre hi3pre2) as ⟨i3, hi3⟩
        have hi3' : i3.val = (s.off.val + kf.val).toNat := hi3
        have hi3b : i3.val < s.vf.length := by push_cast at *; omega
        have hdn : ∀ k', Myers.Dom dn k' → ∃ e, s.vf.val[(s.off.val + k').toNat]? = some e ∧
            e.val = (Myers.F A B dn k' : Int) := hf
        step with (rd_read s.vf s.off.val (fun d k => Myers.F A B d k) dn hdn i3 kf.val hi3' hDomf hi3b) as ⟨i4, hi4⟩
        have hFle : (Myers.F A B dn kf.val : Int) ≤ A.length + dn := by
          have := Myers.F_le A B dn kf.val; exact_mod_cast this
        have hi4n : 0 ≤ i4.val := by rw [hi4]; omega
        step as ⟨i5, hi5⟩
        split
        · rename_i hc3
          rw [ge_iff_le, IScalar.le_equiv] at hc3
          step as ⟨i6, hi6⟩
          step as ⟨i7, hi7⟩
          step as ⟨i8, hi8⟩
          step as ⟨i9, hi9⟩
          try simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨fun t => ⟨rfl, rfl⟩, hframe, Or.inr ⟨i7, i9, rfl, ⟨hpar, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
          · push_cast at *; omega
          · push_cast at *; omega
          · have : (Myers.F A B dn ((A.length : Int) - B.length - k) : Int) = i4.val := by
              rw [hi4, ← hkfv]
            push_cast at *; omega
          · intro hnn
            have e7 := hus i6 (by omega)
            rw [hi7, e7]; omega
          · intro hnn
            have e9 := hus i8 (by omega)
            rw [hi9, e9]; omega
        · rename_i hc3
          rw [ge_iff_le, IScalar.le_equiv] at hc3
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨fun t => ⟨rfl, rfl⟩, hframe, Or.inl ⟨rfl, ?_⟩⟩
          rintro ⟨_, _, _, h4⟩
          have : (Myers.F A B dn ((A.length : Int) - B.length - k) : Int) = i4.val := by
            rw [hi4, ← hkfv]
          push_cast at *; omega
      · rename_i hc2
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨fun t => ⟨rfl, rfl⟩, hframe, Or.inl ⟨rfl, ?_⟩⟩
        rintro ⟨_, _, h3, _⟩
        rw [IScalar.le_equiv] at hc2
        omega
    · rename_i hc1
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨fun t => ⟨rfl, rfl⟩, hframe, Or.inl ⟨rfl, ?_⟩⟩
      rintro ⟨_, h2, _, _⟩
      rw [ge_iff_le, IScalar.le_equiv] at hc1
      omega

end difffold_myers_extract
