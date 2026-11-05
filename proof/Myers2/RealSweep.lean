import RealHalve
import Glue
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem inr_dom {d : Nat} {k : Int} : InR (-(d : Int)) d k ↔ Myers.Dom d k := by
  unfold InR Myers.Dom; omega

/-- What `sweep` returns, in terms of the model sweep. -/
def SweepPost (s : lines.Search) (A B : List Nat) (f dn : Nat)
    (r : (Usize × Usize) × lines.Search × (lines.Search → lines.Search)) : Prop :=
  (∀ pt, Myers.sweep A B f dn = some pt → 0 ≤ pt.1 → 0 ≤ pt.2 →
      (r.1.1.val : Int) = pt.1 ∧ (r.1.2.val : Int) = pt.2) ∧
  (Myers.sweep A B f dn = none → r.1.1.val = 0 ∧ r.1.2.val = 0) ∧
  SameShape s r.2.1 ∧ r.2.1.vf.val.length = s.vf.val.length ∧ r.2.1.vb.val.length = s.vb.val.length

theorem sweep_spec (A B : List Nat) (hNM : A.length + B.length ≤ 268435456) :
    ∀ (N : Nat) (s : lines.Search) (d max_d : I32) (dn : Nat), d.val = dn → 0 ≤ d.val →
      max_d.val + 1 - d.val ≤ (N : Int) → max_d.val ≤ A.length + B.length →
      SInv s A B → RdyArr s.vf s.off.val (fun d k => Myers.F A B d k) dn →
      RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn →
      lines.sweep s d max_d ⦃ r => SweepPost s A B (max_d.val + 1 - d.val).toNat dn r ⦄ := by
  intro N
  induction N with
  | zero =>
    intro s d max_d dn hd hd0 hN hm hinv hf hb
    rw [lines.sweep.eq_1]
    have hc : d > max_d := by rw [gt_iff_lt, IScalar.lt_equiv]; omega
    rw [if_pos hc]
    simp only [Aeneas.Std.WP.spec_ok, SweepPost]
    have : (max_d.val + 1 - d.val).toNat = 0 := by omega
    rw [this]
    refine ⟨by simp [Myers.sweep], by intro _; exact ⟨rfl, rfl⟩, SameShape.refl _, by simp⟩
  | succ N ih =>
    intro s d max_d dn hd hd0 hN hm hinv hf hb
    rw [lines.sweep.eq_1]
    split
    · rename_i hc
      simp only [Aeneas.Std.WP.spec_ok, SweepPost]
      rw [gt_iff_lt, IScalar.lt_equiv] at hc
      have : (max_d.val + 1 - d.val).toNat = 0 := by omega
      rw [this]
      refine ⟨by simp [Myers.sweep], by intro _; exact ⟨rfl, rfl⟩, SameShape.refl _, by simp⟩
    · rename_i hc
      rw [gt_iff_lt, IScalar.lt_equiv] at hc
      have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
      have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
      have hdle : dn ≤ A.length + B.length := by omega
      have hdomR : ∀ k, InR (-(dn : Int)) d.val k ↔ Myers.Dom dn k := by
        intro k; unfold InR Myers.Dom; omega
      have hfuel : (max_d.val + 1 - d.val).toNat = (max_d.val + 1 - (d.val + 1)).toNat + 1 := by omega
      step as ⟨i, hi⟩
      have hiv : i.val = -(dn : Int) := by omega
      have hrr : i.val ≤ d.val → -(dn : Int) ≤ i.val ∧ (i.val + dn) % 2 = 0 ∧ d.val ≤ dn :=
        fun _ => ⟨by omega, by omega, by omega⟩
      step with (forward_spec A B dn hdle (2 * dn + 1) s d i d hd (by omega) hrr hinv hf hb)
        as ⟨o, s1, bk, hp⟩
      obtain ⟨hsh1, hvb1, hlen1, hp'⟩ := hp
      rw [hiv] at hp'
      rcases hp' with ⟨hno, hnf, hw, hfr⟩ | ⟨k, p, q, hk, hso, hfh, hpv, hqv, hmin⟩
      · subst hno
        simp only []
        have hfn : Myers.fwdFind A B dn = none :=
          Myers.fwdFind_none_of A B dn (fun k hk => hnf k ((hdomR k).mpr hk))
        have hinv1 : SInv s1 A B := SInv.of_shape hinv hsh1 hlen1 (by rw [hvb1])
        have hb1 : RdyArr s1.vb s1.off.val (fun d k => Myers.Bk A B d k) dn := by
          rw [hvb1, show s1.off = s.off from hsh1.2.2.2.2.2.2]; exact hb
        have hfd1 : ∀ k', Myers.Dom dn k' → ∃ e, s1.vf.val[(s1.off.val + k').toNat]? = some e ∧
            e.val = (Myers.F A B dn k' : Int) := by
          intro k' hk'
          rw [show s1.off = s.off from hsh1.2.2.2.2.2.2]
          exact hw k' ((hdomR k').mpr hk')
        step with (backward_spec A B dn hdle (2 * dn + 1) s1 d i d hd (by omega) hrr hinv1 hfd1 hb1)
          as ⟨o1, s2, bk2, hq⟩
        obtain ⟨hsh2, hvf2, hlen2, hq'⟩ := hq
        rw [hiv] at hq'
        rcases hq' with ⟨hno1, hnb, hw2, hfr2⟩ | ⟨k, p, q, hk, hso, hbh, hpv, hqv, hmin⟩
        · subst hno1
          simp only []
          have hbn : Myers.bwdFind A B dn = none :=
            Myers.bwdFind_none_of A B dn (fun k hk => hnb k ((hdomR k).mpr hk))
          step as ⟨i1, hi1⟩
          have hi1v : i1.val = d.val + 1 := hi1
          have hinv2 : SInv s2 A B := SInv.of_shape hinv1 hsh2 (by rw [hvf2]) hlen2
          have hoff2 : s2.off = s.off := (hsh2.2.2.2.2.2.2).trans hsh1.2.2.2.2.2.2
          have hf2 : RdyArr s2.vf s2.off.val (fun d k => Myers.F A B d k) (dn + 1) := by
            intro k' hk'
            rw [hvf2, hoff2]
            have := hfd1 k' hk'
            rw [show s1.off = s.off from hsh1.2.2.2.2.2.2] at this
            exact this
          have hb2 : RdyArr s2.vb s2.off.val (fun d k => Myers.Bk A B d k) (dn + 1) := by
            intro k' hk'
            rw [hoff2]
            have := hw2 k' ((hdomR k').mpr hk')
            rw [show s1.off = s.off from hsh1.2.2.2.2.2.2] at this
            exact this
          step with (ih s2 i1 max_d (dn + 1) (by omega) (by omega) (by omega) hm hinv2 hf2 hb2)
            as ⟨r1, s3, bk3, hz⟩
          obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
          have hf3 : (max_d.val + 1 - i1.val).toNat = (max_d.val + 1 - (d.val + 1)).toNat := by rw [hi1v]
          rw [hf3] at hz1 hz2
          have hmodel : Myers.sweep A B ((max_d.val + 1 - d.val).toNat) dn =
              Myers.sweep A B ((max_d.val + 1 - (d.val + 1)).toNat) (dn + 1) := by
            rw [hfuel]; simp only [Myers.sweep, hfn, hbn]
          refine ⟨?_, ?_, hsh1.trans (hsh2.trans hz3), ?_, ?_⟩
          · intro pt hpt; rw [hmodel] at hpt; exact hz1 pt hpt
          · intro hnone; rw [hmodel] at hnone; exact hz2 hnone
          · rw [hz4, hvf2, hlen1]
          · rw [hz5, hlen2, hvb1]
        · subst hso
          simp only [Aeneas.Std.WP.spec_ok, SweepPost]
          have hbf : Myers.bwdFind A B dn = some (Myers.bpt A B dn k) :=
            Myers.bwdFind_first A B dn k ((hdomR k).mp hk) hbh
              (fun k' hk' hlt => hmin k' ((hdomR k').mpr hk') hlt)
          have hmodel : Myers.sweep A B ((max_d.val + 1 - d.val).toNat) dn = some (Myers.bpt A B dn k) := by
            rw [hfuel]; simp only [Myers.sweep, hfn, hbf]
          refine ⟨?_, ?_, hsh1.trans hsh2, ?_, ?_⟩
          · intro pt hpt h1 h2
            rw [hmodel] at hpt
            have := Option.some.inj hpt
            subst this
            exact ⟨hpv h1, hqv h2⟩
          · intro hnone; rw [hmodel] at hnone; cases hnone
          · rw [hvf2, hlen1]
          · rw [hlen2, hvb1]
      · subst hso
        simp only [Aeneas.Std.WP.spec_ok, SweepPost]
        have hff : Myers.fwdFind A B dn = some (Myers.fpt A B dn k) :=
          Myers.fwdFind_first A B dn k ((hdomR k).mp hk) hfh
            (fun k' hk' hlt => hmin k' ((hdomR k').mpr hk') hlt)
        have hmodel : Myers.sweep A B ((max_d.val + 1 - d.val).toNat) dn = some (Myers.fpt A B dn k) := by
          rw [hfuel]; simp only [Myers.sweep, hff]
        refine ⟨?_, ?_, hsh1, hlen1, ?_⟩
        · intro pt hpt h1 h2
          rw [hmodel] at hpt
          have := Option.some.inj hpt
          subst this
          exact ⟨hpv, hqv⟩
        · intro hnone; rw [hmodel] at hnone; cases hnone
        · rw [hvb1]

end difffold_myers_extract
