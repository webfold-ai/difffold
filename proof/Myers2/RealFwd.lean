import RealDefs
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem forward_one_spec (s : lines.Search) (A B : List Nat) (dn : Nat) (k : Int) (d kk : I32)
    (hd : d.val = dn) (hk : kk.val = k) (hdom : Myers.Dom dn k) (hdle : dn ≤ A.length + B.length)
    (hinv : SInv s A B)
    (hf : RdyArr s.vf s.off.val (fun d k => Myers.F A B d k) dn)
    (hb : RdyArr s.vb s.off.val (fun d k => Myers.Bk A B d k) dn) :
    lines.forward_one s d kk ⦃ r => True ⦄ := by
  unfold lines.forward_one
  obtain ⟨ha, hb', hn, hm, hdl, hodd, hoff, hlf, hlb, hN⟩ := hinv
  have hNM : (2:Int)^28 = 268435456 := by norm_num
  have hNM' : A.length + B.length ≤ 268435456 := by simpa [NMAX] using hN
  obtain ⟨hd1, hd2, hd3⟩ := hdom
  have hdv : d.val ≤ 268435456 := by omega
  step*
  -- the starting value of the diagonal
  have hlfb : s.vf.length = 2 * (A.length + B.length) + 3 := by simpa [Slice.length] using hlf
  have key : (do
        if kk = i2 then s.vf.index_usize ikp
        else
          if (kk != d) = true then do
            let i3 ← s.vf.index_usize ikm
            let i4 ← s.vf.index_usize ikp
            if i3 < i4 then ok i4 else i3 + 1#i32
          else do
            let i3 ← s.vf.index_usize ikm
            i3 + 1#i32 : Result I32) ⦃ x0 => x0.val = (X0v A B dn k : Int) ⦄ := by
    cases dn with
    | zero =>
      have hk0 : k = 0 := by omega
      have hc : kk = i2 := by apply IScalar.eq_of_val_eq; omega
      rw [if_pos hc]
      obtain ⟨e, he, hev⟩ := hf
      have hb1 : ikp.val < s.vf.length := by omega
      have hip : ikp.val = ((s.off.val + 1).toNat) := by rw [ikp_post]; congr 1; omega
      have he' : s.vf.val[ikp.val]? = some e := by rw [hip]; exact he
      step with Slice.index_usize_spec as ⟨x, hx⟩
      have := rd_val he' hb1
      simp [X0v, hx, this, hev]
    | succ d' =>
      sorry
  step with key as ⟨x0, hx0v⟩
  have hxb : X0v A B dn k ≤ A.length + dn := by
    have := Myers.F_le A B dn k; rw [F_eq_X0v] at this; omega
  have hx0b : x0.val ≤ (A.length : Int) + dn := by rw [hx0v]; exact_mod_cast hxb
  have hx0n : 0 ≤ x0.val := by rw [hx0v]; omega
  have hx0k : kk.val ≤ x0.val := by rw [hx0v, hk]; exact X0v_ge A B dn k ⟨hd1, hd2, hd3⟩
  have hal : s.a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : s.b.val.length = B.length := by have := congrArg List.length hb'; simpa [vals] using this
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  step*
  all_goals (first | omega | skip)
  all_goals (trace_state; sorry)
