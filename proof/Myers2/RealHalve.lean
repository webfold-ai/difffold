import RealScan
import RealBits
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem inr_left {lo mid hi k : Int} (h : InR lo mid k) (hm : mid ≤ hi) : InR lo hi k :=
  ⟨h.1, by have := h.2.1; omega, h.2.2⟩
theorem inr_right {lo mid hi k : Int} (h : InR (mid + 2) hi k) (hl : lo ≤ mid) (hp : (mid - lo) % 2 = 0) :
    InR lo hi k := ⟨by have := h.1; omega, h.2.1, by have := h.2.2; have := h.1; omega⟩
theorem inr_cases {lo mid hi k : Int} (h : InR lo hi k) (hp : (mid - lo) % 2 = 0) :
    InR lo mid k ∨ InR (mid + 2) hi k := by
  obtain ⟨a, b, c⟩ := h
  by_cases hk : k ≤ mid
  · left; exact ⟨a, hk, c⟩
  · right; exact ⟨by omega, b, by omega⟩

theorem DIAG_val : lines.DIAG_BLOCK.val = 64 := by unfold lines.DIAG_BLOCK; rfl

theorem forward_spec (A B : List Nat) (dn : Nat) (hdle : dn ≤ A.length + B.length) :
    ∀ (N : Nat) (s : lines.Search) (d lo hi : I32), d.val = dn → hi.val - lo.val < (N : Int) →
    (lo.val ≤ hi.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ hi.val ≤ dn) →
    SInv s A B → RdyArr s.vf s.off.val (fun d k => Myers.F A B d k) dn →
    RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn →
    lines.forward s d lo hi ⦃ r => FwdScanPost s A B dn lo.val hi.val r ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s d lo hi hd hN hr hinv hf hb
  rw [lines.forward.eq_1]
  split
  · rename_i hc
    simp only [Aeneas.Std.WP.spec_ok]
    rw [gt_iff_lt, IScalar.lt_equiv] at hc
    refine ⟨SameShape.refl _, rfl, rfl, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro j _; rfl
  · rename_i hc
    rw [gt_iff_lt, IScalar.lt_equiv] at hc
    have hNM : A.length + B.length ≤ 268435456 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hN⟩ := hinv; simpa [NMAX] using hN
    have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
    have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
    obtain ⟨hl1, hl2, hh⟩ := hr (by omega)
    step as ⟨i, hi_post⟩
    split
    · rename_i hsm
      rw [IScalar.le_equiv, DIAG_val] at hsm
      step with (forward_seq_spec A B dn hdle (hi.val - lo.val).toNat.succ s d lo hi hd (by omega) (by
          intro _; exact ⟨hl1, hl2, hh⟩) hinv hf hb) as ⟨o, s1, bk, hp⟩
      exact hp
    · rename_i hbig
      rw [IScalar.le_equiv, DIAG_val] at hbig
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      have hi2' : i2 = ~~~(1#i32) := hi2
      have htd : i.val.tdiv 2 = i.val / 2 := by rw [Int.tdiv_eq_ediv]; rw [if_pos (Or.inl (by omega))]; simp
      have hnn : 0 ≤ i1.val := by omega
      have hi3v : i3.val = i1.val - i1.val % 2 := by
        have := and_not1 i1 hnn
        rw [hi2'] at hi3; rw [hi3]; exact this
      step as ⟨mid, hmid⟩
      have hmv : mid.val = lo.val + (i1.val - i1.val % 2) := by omega
      have hi1v : i1.val = i.val / 2 := by omega
      have hmid1 : lo.val ≤ mid.val ∧ mid.val + 2 ≤ hi.val ∧ (mid.val - lo.val) % 2 = 0 ∧
          mid.val - lo.val < hi.val - lo.val := by omega
      obtain ⟨hm1, hm2, hm3, hm4⟩ := hmid1
      have hrl : lo.val ≤ mid.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ mid.val ≤ dn :=
        fun _ => ⟨hl1, hl2, by omega⟩
      step with (ih ((mid.val - lo.val).toNat + 1) (by omega) s d lo mid hd (by omega) hrl hinv hf hb)
        as ⟨o, s1, bk, hp1⟩
      obtain ⟨hsh1, hvb1, hlen1, hp1'⟩ := hp1
      rcases hp1' with ⟨hno, hnf, hw, hfr⟩ | ⟨k, p, q, hk, hso, hfh, hpv, hqv, hmin⟩
      · subst hno
        simp only []
        have hoffv : (dn : Int) + 1 ≤ s.off.val := by
          obtain ⟨_, _, _, _, _, _, hoff, _⟩ := hinv; omega
        have hinv1 : SInv s1 A B := SInv.of_shape hinv hsh1 hlen1 (by rw [hvb1])
        have hf1 : RdyArr s1.vf s.off.val (fun d k => Myers.F A B d k) dn :=
          rdy_frame s.vf s1.vf s.off.val _ dn lo.val mid.val
            (fun k hk => ⟨by have := hk.1; omega, by have := hk.2.1; omega, by have := hk.1; have := hk.2.2; omega⟩)
            hoffv hfr hf
        have hb1 : RdyArr s1.vb s.off.val (fun d k => Myers.Bk A B d k) dn := by rw [hvb1]; exact hb
        have hin1 : s1.off = s.off := hsh1.2.2.2.2.2.2
        rw [← hin1] at hb1 hf1
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = mid.val + 2 := hi4
        step with (ih ((hi.val - (mid.val + 2)).toNat + 1) (by omega) s1 d i4 hi hd (by omega)
          (by intro _; exact ⟨by omega, by omega, hh⟩) hinv1 hf1 hb1) as ⟨o2, s2, bk2, hp2⟩
        obtain ⟨hsh2, hvb2, hlen2, hp2'⟩ := hp2
        have hoff1 : s1.off.val = s.off.val := by rw [hin1]
        rw [hoff1, hi4v] at hp2'
        refine ⟨hsh1.trans hsh2, by rw [hvb2, hvb1], by rw [hlen2, hlen1], ?_⟩
        rcases hp2' with ⟨h0, h1, h2, h3⟩ | ⟨k, p, q, hk, h0, h1, h2, h3, h4⟩
        · left
          refine ⟨h0, ?_, ?_, ?_⟩
          · intro k hk
            rcases inr_cases (mid := mid.val) hk hm3 with hk' | hk'
            · exact hnf k hk'
            · exact h1 k hk'
          · intro k hk
            rcases inr_cases (mid := mid.val) hk hm3 with hk' | hk'
            · obtain ⟨e, he, hev⟩ := hw k hk'
              refine ⟨e, ?_, hev⟩
              rw [h3 _ (by
                intro k' hk' heq
                obtain ⟨a, b, c⟩ := hk'
                obtain ⟨a', b', c'⟩ := hk'
                omega), he]
            · exact h2 k hk'
          · intro j hj
            rw [h3 j (fun k' hk' => hj k' (inr_right hk' hm1 hm3))]
            exact hfr j (fun k' hk' => hj k' (inr_left hk' (by omega)))
        · right
          exact ⟨k, p, q, inr_right hk hm1 hm3, h0, h1, h2, h3, by
            intro k' hk' hlt
            rcases inr_cases (mid := mid.val) hk' hm3 with hk'' | hk''
            · exact hnf k' hk''
            · exact h4 k' hk'' hlt⟩
      · subst hso
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hsh1, hvb1, hlen1, Or.inr ⟨k, p, q, inr_left hk (by omega), rfl, hfh, hpv, hqv, ?_⟩⟩
        intro k' hk' hlt
        apply hmin k' _ hlt
        obtain ⟨a, b, c⟩ := hk'
        exact ⟨a, by have := hk.2.1; omega, c⟩


theorem backward_spec (A B : List Nat) (dn : Nat) (hdle : dn ≤ A.length + B.length) :
    ∀ (N : Nat) (s : lines.Search) (d lo hi : I32), d.val = dn → hi.val - lo.val < (N : Int) →
    (lo.val ≤ hi.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ hi.val ≤ dn) →
    SInv s A B →
    (∀ k', Myers.Dom dn k' → ∃ e, s.vf.val[(s.off.val + k').toNat]? = some e ∧ e.val = (Myers.F A B dn k' : Int)) →
    RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn →
    lines.backward s d lo hi ⦃ r => BwdScanPost s A B dn lo.val hi.val r ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s d lo hi hd hN hr hinv hfd hb
  rw [lines.backward.eq_1]
  split
  · rename_i hc
    simp only [Aeneas.Std.WP.spec_ok]
    rw [gt_iff_lt, IScalar.lt_equiv] at hc
    refine ⟨SameShape.refl _, rfl, rfl, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro j _; rfl
  · rename_i hc
    rw [gt_iff_lt, IScalar.lt_equiv] at hc
    have hNM : A.length + B.length ≤ 268435456 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hN⟩ := hinv; simpa [NMAX] using hN
    have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
    have hImin : (I32.min : Int) = -2147483648 := by scalar_tac
    obtain ⟨hl1, hl2, hh⟩ := hr (by omega)
    step as ⟨i, hi_post⟩
    split
    · rename_i hsm
      rw [IScalar.le_equiv, DIAG_val] at hsm
      step with (backward_seq_spec A B dn hdle (hi.val - lo.val).toNat.succ s d lo hi hd (by omega) (by
          intro _; exact ⟨hl1, hl2, hh⟩) hinv hfd hb) as ⟨o, s1, bk, hp⟩
      exact hp
    · rename_i hbig
      rw [IScalar.le_equiv, DIAG_val] at hbig
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      have hi2' : i2 = ~~~(1#i32) := hi2
      have htd : i.val.tdiv 2 = i.val / 2 := by rw [Int.tdiv_eq_ediv]; rw [if_pos (Or.inl (by omega))]; simp
      have hnn : 0 ≤ i1.val := by omega
      have hi3v : i3.val = i1.val - i1.val % 2 := by
        have := and_not1 i1 hnn
        rw [hi2'] at hi3; rw [hi3]; exact this
      step as ⟨mid, hmid⟩
      have hmv : mid.val = lo.val + (i1.val - i1.val % 2) := by omega
      have hi1v : i1.val = i.val / 2 := by omega
      have hmid1 : lo.val ≤ mid.val ∧ mid.val + 2 ≤ hi.val ∧ (mid.val - lo.val) % 2 = 0 ∧
          mid.val - lo.val < hi.val - lo.val := by omega
      obtain ⟨hm1, hm2, hm3, hm4⟩ := hmid1
      have hrl : lo.val ≤ mid.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ mid.val ≤ dn :=
        fun _ => ⟨hl1, hl2, by omega⟩
      step with (ih ((mid.val - lo.val).toNat + 1) (by omega) s d lo mid hd (by omega) hrl hinv hfd hb)
        as ⟨o, s1, bk, hp1⟩
      obtain ⟨hsh1, hvb1, hlen1, hp1'⟩ := hp1
      rcases hp1' with ⟨hno, hnf, hw, hfr⟩ | ⟨k, p, q, hk, hso, hfh, hpv, hqv, hmin⟩
      · subst hno
        simp only []
        have hoffv : (dn : Int) + 1 ≤ s.off.val := by
          obtain ⟨_, _, _, _, _, _, hoff, _⟩ := hinv; omega
        have hinv1 : SInv s1 A B := SInv.of_shape hinv hsh1 (by rw [hvb1]) hlen1
        have hb1 : RdyArr s1.vb s.off.val (fun d k => Myers.Bk A B d k) dn :=
          rdy_frame s.vb s1.vb s.off.val _ dn lo.val mid.val
            (fun k hk => ⟨by have := hk.1; omega, by have := hk.2.1; omega, by have := hk.1; have := hk.2.2; omega⟩)
            hoffv hfr hb
        have hf1 : ∀ k', Myers.Dom dn k' → ∃ e, s1.vf.val[(s.off.val + k').toNat]? = some e ∧
            e.val = (Myers.F A B dn k' : Int) := by rw [hvb1]; exact hfd
        have hin1 : s1.off = s.off := hsh1.2.2.2.2.2.2
        rw [← hin1] at hb1 hf1
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = mid.val + 2 := hi4
        step with (ih ((hi.val - (mid.val + 2)).toNat + 1) (by omega) s1 d i4 hi hd (by omega)
          (by intro _; exact ⟨by omega, by omega, hh⟩) hinv1 hf1 hb1) as ⟨o2, s2, bk2, hp2⟩
        obtain ⟨hsh2, hvb2, hlen2, hp2'⟩ := hp2
        have hoff1 : s1.off.val = s.off.val := by rw [hin1]
        rw [hoff1, hi4v] at hp2'
        refine ⟨hsh1.trans hsh2, by rw [hvb2, hvb1], by rw [hlen2, hlen1], ?_⟩
        rcases hp2' with ⟨h0, h1, h2, h3⟩ | ⟨k, p, q, hk, h0, h1, h2, h3, h4⟩
        · left
          refine ⟨h0, ?_, ?_, ?_⟩
          · intro k hk
            rcases inr_cases (mid := mid.val) hk hm3 with hk' | hk'
            · exact hnf k hk'
            · exact h1 k hk'
          · intro k hk
            rcases inr_cases (mid := mid.val) hk hm3 with hk' | hk'
            · obtain ⟨e, he, hev⟩ := hw k hk'
              refine ⟨e, ?_, hev⟩
              rw [h3 _ (by
                intro k' hk' heq
                obtain ⟨a, b, c⟩ := hk'
                obtain ⟨a', b', c'⟩ := hk'
                omega), he]
            · exact h2 k hk'
          · intro j hj
            rw [h3 j (fun k' hk' => hj k' (inr_right hk' hm1 hm3))]
            exact hfr j (fun k' hk' => hj k' (inr_left hk' (by omega)))
        · right
          exact ⟨k, p, q, inr_right hk hm1 hm3, h0, h1, h2, h3, by
            intro k' hk' hlt
            rcases inr_cases (mid := mid.val) hk' hm3 with hk'' | hk''
            · exact hnf k' hk''
            · exact h4 k' hk'' hlt⟩
      · subst hso
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hsh1, hvb1, hlen1, Or.inr ⟨k, p, q, inr_left hk (by omega), rfl, hfh, hpv, hqv, ?_⟩⟩
        intro k' hk' hlt
        apply hmin k' _ hlt
        obtain ⟨a, b, c⟩ := hk'
        exact ⟨a, by have := hk.2.1; omega, c⟩


end difffold_myers_extract
