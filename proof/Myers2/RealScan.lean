import RealBack
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- The diagonals `lo, lo + 2, ..., hi`. -/
def InR (lo hi k : Int) : Prop := lo ≤ k ∧ k ≤ hi ∧ (k - lo) % 2 = 0

/-- The immutable fields of the search state are unchanged. -/
def SameShape (s s' : lines.Search) : Prop :=
  s'.a = s.a ∧ s'.b = s.b ∧ s'.n = s.n ∧ s'.m = s.m ∧ s'.delta = s.delta ∧ s'.odd = s.odd ∧ s'.off = s.off

theorem SameShape.refl (s : lines.Search) : SameShape s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameShape.trans {s s1 s2 : lines.Search} (h1 : SameShape s s1) (h2 : SameShape s1 s2) : SameShape s s2 := by
  obtain ⟨a1, b1, n1, m1, d1, o1, f1⟩ := h1
  obtain ⟨a2, b2, n2, m2, d2, o2, f2⟩ := h2
  exact ⟨a2.trans a1, b2.trans b1, n2.trans n1, m2.trans m1, d2.trans d1, o2.trans o1, f2.trans f1⟩

theorem SInv.of_shape {s s' : lines.Search} {A B : List Nat} (h : SInv s A B) (hs : SameShape s s')
    (hf : s'.vf.val.length = s.vf.val.length) (hb : s'.vb.val.length = s.vb.val.length) : SInv s' A B := by
  obtain ⟨a1, b1, n1, m1, d1, o1, f1⟩ := hs
  obtain ⟨ha, hb', hn, hm, hdl, hodd, hoff, hlf, hlb, hN⟩ := h
  exact ⟨by rw [a1]; exact ha, by rw [b1]; exact hb', by rw [n1]; exact hn, by rw [m1]; exact hm,
    by rw [d1]; exact hdl, by rw [o1]; exact hodd, by rw [f1]; exact hoff, by rw [hf]; exact hlf,
    by rw [hb]; exact hlb, hN⟩

/-- Setting the entry of a diagonal of round `dn` does not disturb what round `dn` reads. -/
theorem rdy_set (v : Slice I32) (off : Int) (G : Nat → Int → Nat) (dn : Nat) (k : Int) (hk : Myers.Dom dn k)
    (hoff : (dn : Int) + 1 ≤ off) (i : Usize) (hi : i.val = (off + k).toNat) (x : I32) (h : RdyArr v off G dn) :
    RdyArr (v.set i x) off G dn := by
  cases dn with
  | zero =>
    obtain ⟨e, he, hev⟩ := h
    have hk0 : k = 0 := by obtain ⟨h1, h2, _⟩ := hk; simp at h1 h2; omega
    have hoff' : (1:Int) ≤ off := by simpa using hoff
    refine ⟨e, ?_, hev⟩
    rw [Slice.set_val_eq, List.getElem?_set_ne]
    · exact he
    · rw [hi, hk0]; omega
  | succ d' =>
    intro k' hk'
    obtain ⟨e, he, hev⟩ := h k' hk'
    refine ⟨e, ?_, hev⟩
    rw [Slice.set_val_eq, List.getElem?_set_ne]
    · exact he
    · rw [hi]
      obtain ⟨g1, g2, h3⟩ := hk
      obtain ⟨g3, g4, h3'⟩ := hk'
      intro heq
      have : (off + k').toNat = (off + k).toNat := heq.symm
      have : k' = k := by omega
      subst this; push_cast at *; omega


/-- Result of scanning the diagonals `lo, lo + 2, ..., hi` of the forward half-round. -/
def FwdScanPost (s : lines.Search) (A B : List Nat) (dn : Nat) (lo hi : Int)
    (r : Option (Usize × Usize) × lines.Search × (lines.Search → lines.Search)) : Prop :=
  SameShape s r.2.1 ∧ r.2.1.vb = s.vb ∧ r.2.1.vf.val.length = s.vf.val.length ∧
  ((r.1 = none ∧ (∀ k, InR lo hi k → ¬ Myers.fhit A B dn k) ∧
     (∀ k, InR lo hi k → ∃ e, r.2.1.vf.val[(s.off.val + k).toNat]? = some e ∧ e.val = (Myers.F A B dn k : Int)) ∧
     (∀ j, (∀ k, InR lo hi k → j ≠ (s.off.val + k).toNat) → r.2.1.vf.val[j]? = s.vf.val[j]?)) ∨
   (∃ k p q, InR lo hi k ∧ r.1 = some (p, q) ∧ Myers.fhit A B dn k ∧ (p.val : Int) = (Myers.F A B dn k : Int) ∧
      (q.val : Int) = (Myers.F A B dn k : Int) - k ∧ ∀ k', InR lo hi k' → k' < k → ¬ Myers.fhit A B dn k'))

theorem forward_seq_spec (A B : List Nat) (dn : Nat) (hdle : dn ≤ A.length + B.length) :
    ∀ (N : Nat) (s : lines.Search) (d lo hi : I32), d.val = dn → hi.val - lo.val < 2 * (N : Int) →
    (lo.val ≤ hi.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ hi.val ≤ dn) →
    SInv s A B → RdyArr s.vf s.off.val (fun d k => Myers.F A B d k) dn →
    RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn →
    lines.forward_seq s d lo hi ⦃ r => FwdScanPost s A B dn lo.val hi.val r ⦄ := by
  intro N
  induction N with
  | zero =>
    intro s d lo hi hd hN hr hinv hf hb
    rw [lines.forward_seq.eq_1]
    have : lo > hi := by rw [gt_iff_lt, IScalar.lt_equiv]; omega
    rw [if_pos this]
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨SameShape.refl _, rfl, rfl, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro j _; rfl
  | succ N ih =>
    intro s d lo hi hd hN hr hinv hf hb
    rw [lines.forward_seq.eq_1]
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
      obtain ⟨hl1, hl2, hh⟩ := hr (by omega)
      have hdom : Myers.Dom dn lo.val := ⟨hl1, by omega, hl2⟩
      step with (forward_one_spec s A B dn lo.val d lo hd rfl hdom hdle hinv hf hb) as ⟨o, s1, bk, hpost⟩
      obtain ⟨⟨ik, x, hik, hx, hs1⟩, hp2'⟩ := hpost
      have hs1' : s1 = { s with vf := s.vf.set ik x } := hs1
      have hoffv : (dn : Int) + 1 ≤ s.off.val := by
        obtain ⟨_, _, _, _, _, _, hoff, _⟩ := hinv; omega
      have hshape : SameShape s s1 := by rw [hs1']; exact SameShape.refl _
      have hlen1 : s1.vf.val.length = s.vf.val.length := by
        rw [hs1']; show (s.vf.set ik x).val.length = _; simp
      have hvb1 : s1.vb = s.vb := by rw [hs1']
      have hget : s1.vf.val[(s.off.val + lo.val).toNat]? = some x := by
        rw [hs1']; show (s.vf.set ik x).val[_]? = _
        rw [Slice.set_val_eq, ← hik]
        have hlt : ik.val < s.vf.val.length := by
          obtain ⟨_, _, _, _, _, _, hoff, hlf, _⟩ := hinv; rw [hik]; omega
        rw [List.getElem?_set_self hlt]
      have hother : ∀ j, j ≠ (s.off.val + lo.val).toNat → s1.vf.val[j]? = s.vf.val[j]? := by
        intro j hj
        rw [hs1']; show (s.vf.set ik x).val[j]? = _
        rw [Slice.set_val_eq, List.getElem?_set_ne]
        rw [hik]; exact fun h => hj h.symm
      rcases hp2' with ⟨hno, hnf⟩ | ⟨p, q, hso, hfh, hpv, hqv⟩
      · subst hno
        simp only []
        have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
        have hNM : A.length + B.length ≤ 268435456 := by
          obtain ⟨_, _, _, _, _, _, _, _, _, hN⟩ := hinv; simpa [NMAX] using hN
        step as ⟨i2, hi2⟩
        have hinv1 : SInv s1 A B := SInv.of_shape hinv hshape hlen1 (by rw [hvb1])
        have hf1 : RdyArr s1.vf s.off.val (fun d k => Myers.F A B d k) dn := by
          rw [hs1']
          exact rdy_set s.vf s.off.val _ dn lo.val hdom hoffv ik hik x hf
        have hb1 : RdyArr s1.vb s.off.val (fun d k => Myers.Bk A B d k) dn := by rw [hvb1]; exact hb
        have hin1 : s1.off = s.off := by rw [hs1']
        rw [← hin1] at hb1 hf1
        step with (ih s1 d i2 hi hd (by omega) (by intro hle; refine ⟨by omega, by omega, by omega⟩)
          hinv1 hf1 hb1) as ⟨o1, s2, bk2, hq⟩
        obtain ⟨hsh2, hvb2, hlen2, hq2⟩ := hq
        have hoff1 : s1.off.val = s.off.val := by rw [hin1]
        rw [hoff1] at hq2
        refine ⟨hshape.trans hsh2, by rw [hvb2, hvb1], by rw [hlen2, hlen1], ?_⟩
        rcases hq2 with ⟨h0, h1, h2, h3⟩ | ⟨k, p, q, hk, h0, h1, h2, h3, h4⟩
        · left
          refine ⟨h0, ?_, ?_, ?_⟩
          · intro k hk
            by_cases hkl : k = lo.val
            · subst hkl; exact hnf
            · exact h1 k ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩
          · intro k hk
            by_cases hkl : k = lo.val
            · subst hkl
              refine ⟨x, ?_, hx⟩
              rw [h3 _ (by
                intro k' hk'
                obtain ⟨a, b, c⟩ := hk'
                intro heq
                omega), hget]
            · exact h2 k ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩
          · intro j hj
            have hjl : j ≠ (s.off.val + lo.val).toNat := hj lo.val ⟨le_refl _, by omega, by omega⟩
            rw [h3 j (fun k' hk' => hj k' ⟨by obtain ⟨a, b, c⟩ := hk'; omega, hk'.2.1,
              by obtain ⟨a, b, c⟩ := hk'; omega⟩), hother j hjl]
        · right
          refine ⟨k, p, q, ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩,
            h0, h1, h2, h3, ?_⟩
          intro k' hk' hlt
          by_cases hkl : k' = lo.val
          · subst hkl; exact hnf
          · exact h4 k' ⟨by obtain ⟨a, b, c⟩ := hk'; omega, hk'.2.1, by obtain ⟨a, b, c⟩ := hk'; omega⟩ hlt
      · subst hso
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hshape, hvb1, hlen1, Or.inr ⟨lo.val, p, q, ⟨le_refl _, by omega, by omega⟩, rfl, hfh, hpv, hqv, ?_⟩⟩
        intro k' hk' hlt
        obtain ⟨a, b, c⟩ := hk'
        omega


/-- Result of scanning the diagonals `lo, lo + 2, ..., hi` of the backward half-round. -/
def BwdScanPost (s : lines.Search) (A B : List Nat) (dn : Nat) (lo hi : Int)
    (r : Option (Usize × Usize) × lines.Search × (lines.Search → lines.Search)) : Prop :=
  SameShape s r.2.1 ∧ r.2.1.vf = s.vf ∧ r.2.1.vb.val.length = s.vb.val.length ∧
  ((r.1 = none ∧ (∀ k, InR lo hi k → ¬ Myers.bhit A B dn k) ∧
     (∀ k, InR lo hi k → ∃ e, r.2.1.vb.val[(s.off.val + k).toNat]? = some e ∧ e.val = (Myers.Bk A B dn k : Int)) ∧
     (∀ j, (∀ k, InR lo hi k → j ≠ (s.off.val + k).toNat) → r.2.1.vb.val[j]? = s.vb.val[j]?)) ∨
   (∃ k p q, InR lo hi k ∧ r.1 = some (p, q) ∧ Myers.bhit A B dn k ∧ (0 ≤ (A.length : Int) - (Myers.Bk A B dn k : Int) → (p.val : Int) = (A.length : Int) - (Myers.Bk A B dn k : Int)) ∧
      (0 ≤ (B.length : Int) - ((Myers.Bk A B dn k : Int) - k) →
        (q.val : Int) = (B.length : Int) - ((Myers.Bk A B dn k : Int) - k)) ∧ ∀ k', InR lo hi k' → k' < k → ¬ Myers.bhit A B dn k'))

theorem backward_seq_spec (A B : List Nat) (dn : Nat) (hdle : dn ≤ A.length + B.length) :
    ∀ (N : Nat) (s : lines.Search) (d lo hi : I32), d.val = dn → hi.val - lo.val < 2 * (N : Int) →
    (lo.val ≤ hi.val → -(dn : Int) ≤ lo.val ∧ (lo.val + dn) % 2 = 0 ∧ hi.val ≤ dn) →
    SInv s A B →
    (∀ k', Myers.Dom dn k' → ∃ e, s.vf.val[(s.off.val + k').toNat]? = some e ∧ e.val = (Myers.F A B dn k' : Int)) →
    RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn →
    lines.backward_seq s d lo hi ⦃ r => BwdScanPost s A B dn lo.val hi.val r ⦄ := by
  intro N
  induction N with
  | zero =>
    intro s d lo hi hd hN hr hinv hfd hb
    rw [lines.backward_seq.eq_1]
    have : lo > hi := by rw [gt_iff_lt, IScalar.lt_equiv]; omega
    rw [if_pos this]
    simp only [Aeneas.Std.WP.spec_ok]
    refine ⟨SameShape.refl _, rfl, rfl, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro k hk; obtain ⟨h1, h2, _⟩ := hk; omega
    · intro j _; rfl
  | succ N ih =>
    intro s d lo hi hd hN hr hinv hfd hb
    rw [lines.backward_seq.eq_1]
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
      obtain ⟨hl1, hl2, hh⟩ := hr (by omega)
      have hdom : Myers.Dom dn lo.val := ⟨hl1, by omega, hl2⟩
      step with (backward_one_spec s A B dn lo.val d lo hd rfl hdom hdle hinv hfd hb) as ⟨o, s1, bk, hpost⟩
      obtain ⟨⟨ik, x, hik, hx, hs1⟩, hp2'⟩ := hpost
      have hs1' : s1 = { s with vb := s.vb.set ik x } := hs1
      have hoffv : (dn : Int) + 1 ≤ s.off.val := by
        obtain ⟨_, _, _, _, _, _, hoff, _⟩ := hinv; omega
      have hshape : SameShape s s1 := by rw [hs1']; exact SameShape.refl _
      have hlen1 : s1.vb.val.length = s.vb.val.length := by
        rw [hs1']; show (s.vb.set ik x).val.length = _; simp
      have hvb1 : s1.vf = s.vf := by rw [hs1']
      have hget : s1.vb.val[(s.off.val + lo.val).toNat]? = some x := by
        rw [hs1']; show (s.vb.set ik x).val[_]? = _
        rw [Slice.set_val_eq, ← hik]
        have hlt : ik.val < s.vb.val.length := by
          obtain ⟨_, _, _, _, _, _, hoff, hlf, _⟩ := hinv; rw [hik]; omega
        rw [List.getElem?_set_self hlt]
      have hother : ∀ j, j ≠ (s.off.val + lo.val).toNat → s1.vb.val[j]? = s.vb.val[j]? := by
        intro j hj
        rw [hs1']; show (s.vb.set ik x).val[j]? = _
        rw [Slice.set_val_eq, List.getElem?_set_ne]
        rw [hik]; exact fun h => hj h.symm
      rcases hp2' with ⟨hno, hnf⟩ | ⟨p, q, hso, hfh, hpv, hqv⟩
      · subst hno
        simp only []
        have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
        have hNM : A.length + B.length ≤ 268435456 := by
          obtain ⟨_, _, _, _, _, _, _, _, _, hN⟩ := hinv; simpa [NMAX] using hN
        step as ⟨i2, hi2⟩
        have hinv1 : SInv s1 A B := SInv.of_shape hinv hshape (by rw [hvb1]) hlen1
        have hb1 : RdyArr s1.vb s.off.val (fun d k => Myers.Bk A B d k) dn := by
          rw [hs1']
          exact rdy_set s.vb s.off.val _ dn lo.val hdom hoffv ik hik x hb
        have hf1 : ∀ k', Myers.Dom dn k' → ∃ e, s1.vf.val[(s.off.val + k').toNat]? = some e ∧
            e.val = (Myers.F A B dn k' : Int) := by rw [hvb1]; exact hfd
        have hin1 : s1.off = s.off := by rw [hs1']
        rw [← hin1] at hb1 hf1
        step with (ih s1 d i2 hi hd (by omega) (by intro hle; refine ⟨by omega, by omega, by omega⟩)
          hinv1 hf1 hb1) as ⟨o1, s2, bk2, hq⟩
        obtain ⟨hsh2, hvb2, hlen2, hq2⟩ := hq
        have hoff1 : s1.off.val = s.off.val := by rw [hin1]
        rw [hoff1] at hq2
        refine ⟨hshape.trans hsh2, by rw [hvb2, hvb1], by rw [hlen2, hlen1], ?_⟩
        rcases hq2 with ⟨h0, h1, h2, h3⟩ | ⟨k, p, q, hk, h0, h1, h2, h3, h4⟩
        · left
          refine ⟨h0, ?_, ?_, ?_⟩
          · intro k hk
            by_cases hkl : k = lo.val
            · subst hkl; exact hnf
            · exact h1 k ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩
          · intro k hk
            by_cases hkl : k = lo.val
            · subst hkl
              refine ⟨x, ?_, hx⟩
              rw [h3 _ (by
                intro k' hk'
                obtain ⟨a, b, c⟩ := hk'
                intro heq
                omega), hget]
            · exact h2 k ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩
          · intro j hj
            have hjl : j ≠ (s.off.val + lo.val).toNat := hj lo.val ⟨le_refl _, by omega, by omega⟩
            rw [h3 j (fun k' hk' => hj k' ⟨by obtain ⟨a, b, c⟩ := hk'; omega, hk'.2.1,
              by obtain ⟨a, b, c⟩ := hk'; omega⟩), hother j hjl]
        · right
          refine ⟨k, p, q, ⟨by obtain ⟨a, b, c⟩ := hk; omega, hk.2.1, by obtain ⟨a, b, c⟩ := hk; omega⟩,
            h0, h1, h2, h3, ?_⟩
          intro k' hk' hlt
          by_cases hkl : k' = lo.val
          · subst hkl; exact hnf
          · exact h4 k' ⟨by obtain ⟨a, b, c⟩ := hk'; omega, hk'.2.1, by obtain ⟨a, b, c⟩ := hk'; omega⟩ hlt
      · subst hso
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hshape, hvb1, hlen1, Or.inr ⟨lo.val, p, q, ⟨le_refl _, by omega, by omega⟩, rfl, hfh, hpv, hqv, ?_⟩⟩
        intro k' hk' hlt
        obtain ⟨a, b, c⟩ := hk'
        omega


end difffold_myers_extract
