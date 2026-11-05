import RealDefs
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- Reading one entry of an array that satisfies `RdyArr`. -/
theorem rd_read (v : Slice I32) (off : Int) (G : Nat → Int → Nat) (d' : Nat)
    (hrdy : ∀ k, Myers.Dom d' k → ∃ e, v.val[(off + k).toNat]? = some e ∧ e.val = (G d' k : Int))
    (i : Usize) (k : Int) (hi : i.val = (off + k).toNat) (hk : Myers.Dom d' k) (hb : i.val < v.length) :
    v.index_usize i ⦃ x => x.val = (G d' k : Int) ⦄ := by
  step with Slice.index_usize_spec as ⟨x, hx⟩
  rw [hx]; exact rdv hrdy i k hi hk hb

/-- The starting value of diagonal `k` in round `dn`: the first block of `forward_one`. -/
theorem x0_block (v : Slice I32) (A B : List Nat) (dn : Nat) (k : Int) (kk d i2 : I32) (ikm ikp : Usize)
    (off : Int) (hk : kk.val = k) (hd : d.val = dn) (hi2 : i2.val = -d.val)
    (hdom : Myers.Dom dn k) (hdle : dn ≤ A.length + B.length) (hoff : off = A.length + B.length + 1)
    (hlen : 2 * (A.length + B.length) + 3 ≤ v.length)
    (hikm : ikm.val = (off + (k - 1)).toNat) (hikp : ikp.val = (off + (k + 1)).toNat)
    (hrdy : RdyArr v off (fun d k => Myers.F A B d k) dn)
    (hFle : ∀ d' k', Myers.F A B d' k' ≤ A.length + d') (hN : A.length + B.length ≤ 268435456) :
    (do
        if kk = i2 then v.index_usize ikp
        else
          if (kk != d) = true then do
            let i3 ← v.index_usize ikm
            let i4 ← v.index_usize ikp
            if i3 < i4 then ok i4 else i3 + 1#i32
          else do
            let i3 ← v.index_usize ikm
            i3 + 1#i32 : Result I32) ⦃ x0 => x0.val = (X0v A B dn k : Int) ⦄ := by
  obtain ⟨hd1, hd2, hd3⟩ := hdom
  cases dn with
  | zero =>
    have hk0 : k = 0 := by omega
    have hc : kk = i2 := by apply IScalar.eq_of_val_eq; omega
    rw [if_pos hc]
    obtain ⟨e, he, hev⟩ := hrdy
    have hip : ikp.val = (off + 1).toNat := by rw [hikp, hk0]; simp
    have he' : v.val[ikp.val]? = some e := by rw [hip]; exact he
    have hb1 : ikp.val < v.length := by omega
    step with Slice.index_usize_spec as ⟨x, hx⟩
    have := rd_val he' hb1
    simp [X0v, hx, this, hev]
  | succ d' =>
    have hdom' : Myers.Dom (d' + 1) k := ⟨hd1, hd2, hd3⟩
    have hF1 := hFle d'
    by_cases hc : kk = i2
    · rw [if_pos hc]
      have hkv : k = -((d' : Int) + 1) := by
        have := congrArg IScalar.val hc; push_cast at *; omega
      have hD : Myers.Dom d' (k + 1) := by unfold Myers.Dom; push_cast at *; omega
      have hb1 : ikp.val < v.length := by omega
      step with (rd_read v off (fun d k => Myers.F A B d k) d' hrdy ikp (k + 1) (by omega) hD hb1) as ⟨x, hx⟩
      simp only [X0v, Myers.X0]; rw [if_pos (Or.inl hkv)]; exact hx
    · rw [if_neg hc]
      have hkne : k ≠ -((d' : Int) + 1) := by
        intro h; apply hc; apply IScalar.eq_of_val_eq; omega
      by_cases hd' : (kk != d) = true
      · rw [if_pos hd']
        have hkd : k ≠ (d' : Int) + 1 := by
          intro h; simp at hd'; omega
        have hD1 : Myers.Dom d' (k - 1) := by unfold Myers.Dom; push_cast at *; omega
        have hD2 : Myers.Dom d' (k + 1) := by unfold Myers.Dom; push_cast at *; omega
        have hb1 : ikm.val < v.length := by omega
        have hb2 : ikp.val < v.length := by omega
        step with (rd_read v off (fun d k => Myers.F A B d k) d' hrdy ikm (k - 1) (by omega) hD1 hb1) as ⟨i3, h3⟩
        step with (rd_read v off (fun d k => Myers.F A B d k) d' hrdy ikp (k + 1) (by omega) hD2 hb2) as ⟨i4, h4⟩
        have e1 := hF1 (k - 1)
        have e2 := hF1 (k + 1)
        split
        · rename_i hlt
          rw [IScalar.lt_equiv] at hlt
          simp only [X0v, Myers.X0]
          rw [if_pos (Or.inr ⟨hkd, by omega⟩)]
          simp only [Aeneas.Std.WP.spec_ok]; rw [h4]
        · rename_i hlt
          rw [IScalar.lt_equiv] at hlt
          step as ⟨r, hr⟩
          simp only [X0v, Myers.X0]
          rw [if_neg (by rintro (h | ⟨_, h⟩) <;> first | omega | (exact hkne h) | omega)]
          omega
      · rw [if_neg hd']
        have hkd : k = (d' : Int) + 1 := by
          simp at hd'; omega
        have hD1 : Myers.Dom d' (k - 1) := by unfold Myers.Dom; push_cast at *; omega
        have hb1 : ikm.val < v.length := by omega
        step with (rd_read v off (fun d k => Myers.F A B d k) d' hrdy ikm (k - 1) (by omega) hD1 hb1) as ⟨i3, h3⟩
        have e1 := hF1 (k - 1)
        step as ⟨r, hr⟩
        simp only [X0v, Myers.X0]
        rw [if_neg (by rintro (h | ⟨h, _⟩) <;> omega)]
        omega

end difffold_myers_extract
