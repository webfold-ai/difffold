import DifffoldTed
import Overlap
import Basic
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Theorems over the Aeneas extraction of the real `label_lower_bound` of `src/ted.rs` (counting version).
It returns `max(n, m)` minus the size of the label multiset overlap (`Ted.overlap`, `Overlap.lean`). -/

/-- The values of a list of `u32`. -/
def vals (l : List Std.U32) : List Nat := l.map (fun x => x.val)

theorem vals_length (l : List Std.U32) : (vals l).length = l.length := by simp [vals]

theorem vals_getElem (l : List Std.U32) (i : Nat) (h : i < l.length) :
    (vals l)[i]'(by simpa [vals_length] using h) = (l[i]'h).val := by
  simp [vals]

theorem count_take_succ (l : List Std.U32) (i : Nat) (h : i < l.length) (x : Nat) :
    (vals (l.take (i + 1))).count x = (vals (l.take i)).count x + if (l[i]'h).val = x then 1 else 0 := by
  have e : vals (l.take (i + 1)) = vals (l.take i) ++ [(l[i]'h).val] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    simp only [vals, List.map_append]
    simp
  rw [e, List.count_append]
  by_cases hh : (l[i]'h).val = x <;> simp [hh]


/-- Loop 0 finds a bound on the labels of `a`. -/
@[step] theorem llb_top_loop_spec (a : ted.PostTree) (top i : Std.Usize)
    (hA : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (hi : i.val ≤ a.label.length) (htop : top.val ≤ 2 ^ 31)
    (hlt : ∀ j < i.val, (a.label.val[j]!).val < top.val) :
    ted.label_lower_bound_loop0 a top i ⦃ r =>
      r = (a.label, a.lml, a.keyroots, a.kids, a.kind, r.2.2.2.2.2) ∧
      r.2.2.2.2.2.val ≤ 2 ^ 31 ∧ ∀ j < a.label.length, (a.label.val[j]!).val < r.2.2.2.2.2.val ⦄ := by
  unfold ted.label_lower_bound_loop0
  apply loop.spec_decr_nat
    (measure := fun p => a.label.length - p.2.val)
    (inv := fun p => p.2.val ≤ a.label.length ∧ p.1.val ≤ 2 ^ 31 ∧
      ∀ j < p.2.val, (a.label.val[j]!).val < p.1.val)
  · intro p hp
    obtain ⟨tp, c⟩ := p
    obtain ⟨hc, ht, hl⟩ := hp
    unfold ted.label_lower_bound_loop0.body
    dsimp only at hc ht hl ⊢
    have hlen := alloc.vec.Vec.len_val a.label
    split
    · rename_i hci
      have hci' : c.val < a.label.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨l, hl'⟩
      have hlv : l.val = (a.label.val[c.val]!).val := by
        rw [hl', U32.cast_Usize_val_eq, hi2, getU_eq _ _ hci']
      have hAc := hA c.val hci'
      split
      · rename_i hlt'
        have hge : tp.val ≤ l.val := by scalar_tac
        step as ⟨top1, htop1⟩
        step as ⟨i3, hi3⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        intro j hj
        by_cases hjc : j = c.val
        · subst hjc; omega
        · have := hl j (by omega); omega
      · rename_i hlt'
        have hge : l.val < tp.val := by scalar_tac
        step as ⟨i3, hi3⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        intro j hj
        by_cases hjc : j = c.val
        · subst hjc; omega
        · have := hl j (by omega); omega
    · rename_i hci
      have hc2 : a.label.length ≤ c.val := by scalar_tac
      refine ⟨rfl, ht, ?_⟩
      intro j hj; exact hl j (by omega)
  · exact ⟨hi, htop, hlt⟩


/-- Loop 1 counts the labels of `a` into `cnt`. -/
@[step] theorem llb_count_loop_spec (v cnt : alloc.vec.Vec Std.U32) (i : Std.Usize) (top : Nat)
    (hv : ∀ j < v.length, (v.val[j]!).val < top) (hlen : v.length < 2 ^ 31)
    (hcnt : cnt.length = top) (hi : i.val ≤ v.length)
    (hinv : ∀ x < top, (cnt.val[x]!).val = (vals (v.val.take i.val)).count x) :
    ted.label_lower_bound_loop1 v i cnt ⦃ r =>
      r.length = top ∧ ∀ x < top, (r.val[x]!).val = (vals v.val).count x ⦄ := by
  unfold ted.label_lower_bound_loop1
  apply loop.spec_decr_nat
    (measure := fun p => v.length - p.1.val)
    (inv := fun p => p.1.val ≤ v.length ∧ p.2.length = top ∧
      ∀ x < top, (p.2.val[x]!).val = (vals (v.val.take p.1.val)).count x)
  · intro p hp
    obtain ⟨c, o⟩ := p
    obtain ⟨hc, hl, hI⟩ := hp
    unfold ted.label_lower_bound_loop1.body
    dsimp only at hc hl hI ⊢
    have hlenv := alloc.vec.Vec.len_val v
    split
    · rename_i hci
      have hci' : c.val < v.length := by scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨l, hl'⟩
      have hlv : l.val = (v.val[c.val]!).val := by
        rw [hl', U32.cast_Usize_val_eq, hi2, getU_eq _ _ hci']
      have hlt := hv c.val hci'
      have hlc : l.val < cnt.length := by
        have : o.length = top := hl
        have : l.val < top := by omega
        omega
      step as ⟨i3, imb, hi3, himb⟩
      have hb : l.val < o.val.length := hlc
      have e : (o.val[l.val]'hb) = o.val[l.val]! := (getU_eq _ _ hb).symm
      have hi3v : i3.val = (vals (v.val.take c.val)).count l.val := by
        rw [hi3, e]; exact hI l.val (by omega)
      have hcle : (vals (v.val.take c.val)).count l.val ≤ c.val := by
        have := List.count_le_length (a := l.val) (l := vals (v.val.take c.val))
        rw [vals_length, List.length_take] at this
        omega
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      have hset : (imb i4).val = o.val.set l.val i4 := by
        rw [himb, alloc.vec.Vec.set_val_eq]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
      · intro x hx
        rw [hset]
        have hsucc := count_take_succ v.val c.val hci' x
        rw [← hi5] at hsucc
        have hi5' : i5.val = c.val + 1 := by omega
        rw [hi5']
        rw [hsucc]
        by_cases hxl : x = l.val
        · subst hxl
          rw [getU_set_eq _ _ _ hb]
          simp [hi4, hi3v, hlv]
        · rw [getU_set_ne _ _ _ _ hxl, hI x hx]
          have : ¬ (v.val[c.val]'hci').val = x := by
            intro h; apply hxl; rw [hlv, ← h, getU_eq _ _ hci']
          simp [this]
    · rename_i hci
      have hc2 : v.length ≤ c.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hl, ?_⟩
      intro x hx
      rw [hI x hx]
      have : c.val = v.length := by omega
      rw [this]
      simp [vals]
  · exact ⟨hi, hcnt, hinv⟩

end difffold_lines_extract
