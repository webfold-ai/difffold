import DifffoldTed
import Overlap
import Basic
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Theorems over the Aeneas-extracted `ted_core::label_lower_bound`, the copy of `label_lower_bound` of the
real `src/ted.rs` (tied to it by `tests/ted_core.rs`). It returns `max(n, m)` minus the size of the label
multiset overlap (`Ted.overlap`, defined in `Overlap.lean`). -/

/-- The values of a list of `u32`. -/
def vals (l : List Std.U32) : List Nat := l.map (fun x => x.val)

theorem vals_length (l : List Std.U32) : (vals l).length = l.length := by simp [vals]

theorem vals_getElem (l : List Std.U32) (i : Nat) (h : i < l.length) :
    (vals l)[i]'(by simpa [vals_length] using h) = (l[i]'h).val := by
  simp [vals]

theorem vals_drop (l : List Std.U32) (i : Nat) : vals (l.drop i) = (vals l).drop i := by
  simp [vals, List.map_drop]

theorem drop_cons_vals (l : List Std.U32) (i : Nat) (h : i < l.length) :
    (vals l).drop i = (l[i]'h).val :: (vals l).drop (i + 1) := by
  have h' : i < (vals l).length := by simpa [vals_length] using h
  rw [List.drop_eq_getElem_cons h', vals_getElem l i h]

theorem sorted_tail (l : List Std.U32) (i : Nat) (h : i < l.length) (hs : (vals l).Pairwise (· ≤ ·)) :
    ∀ a ∈ (vals l).drop (i + 1), (l[i]'h).val ≤ a := by
  have h1 := hs.sublist (List.drop_sublist i (vals l))
  rw [drop_cons_vals l i h] at h1
  exact (List.pairwise_cons.mp h1).1

/-- Loop 0 of `label_lower_bound`: the merge of two sorted lists, counting equal heads. -/
@[step] theorem llb_loop_spec (la lb : alloc.vec.Vec Std.U32) (i j : Std.Usize) (common : Std.U32)
    (hsa : (vals la.val).Pairwise (· ≤ ·)) (hsb : (vals lb.val).Pairwise (· ≤ ·))
    (hla : la.length < 2 ^ 31)
    (hi : i.val ≤ la.length) (hj : j.val ≤ lb.length) (hc : common.val ≤ i.val) :
    ted_core.label_lower_bound_loop la lb i j common ⦃ r =>
      r.val = common.val + overlap ((vals la.val).drop i.val) ((vals lb.val).drop j.val) ⦄ := by
  unfold ted_core.label_lower_bound_loop
  apply loop.spec_decr_nat
    (measure := fun p => (la.length - p.1.val) + (lb.length - p.2.1.val))
    (inv := fun p => p.1.val ≤ la.length ∧ p.2.1.val ≤ lb.length ∧ p.2.2.val ≤ p.1.val ∧
      p.2.2.val + overlap ((vals la.val).drop p.1.val) ((vals lb.val).drop p.2.1.val) =
        common.val + overlap ((vals la.val).drop i.val) ((vals lb.val).drop j.val))
  · intro p hp
    obtain ⟨c, d, m⟩ := p
    obtain ⟨hc1, hd1, hm1, hfin⟩ := hp
    unfold ted_core.label_lower_bound_loop.body
    dsimp only at hc1 hd1 hm1 hfin ⊢
    have hlal : (alloc.vec.Vec.len la).val = la.length := alloc.vec.Vec.len_val la
    have hlbl : (alloc.vec.Vec.len lb).val = lb.length := alloc.vec.Vec.len_val lb
    split
    · rename_i hci
      have hci' : c.val < la.length := by scalar_tac
      split
      · rename_i hdj
        have hdj' : d.val < lb.length := by scalar_tac
        step as ⟨x, x_post⟩
        step as ⟨y, y_post⟩
        have hx : x = la.val[c.val]'hci' := x_post
        have hy : y = lb.val[d.val]'hdj' := y_post
        have hdA := drop_cons_vals la.val c.val hci'
        have hdB := drop_cons_vals lb.val d.val hdj'
        have hxs := sorted_tail la.val c.val hci' hsa
        have hys := sorted_tail lb.val d.val hdj' hsb
        rw [← hx] at hdA hxs
        rw [← hy] at hdB hys
        split
        · rename_i hxy
          have hxy' : x.val < y.val := by scalar_tac
          step as ⟨i5, i5_post⟩
          refine ⟨by omega, by omega, by omega, ?_, by omega⟩
          rw [i5_post, ← hfin, hdA, overlap_cons_lt _ _ _ ?_]
          intro z hz
          rw [hdB] at hz
          rcases List.mem_cons.mp hz with hz | hz
          · omega
          · have := hys z hz; omega
        · rename_i hxy
          split
          · rename_i hyx
            have hyx' : y.val < x.val := by scalar_tac
            step as ⟨j1, j1_post⟩
            refine ⟨by omega, by omega, by omega, ?_, by omega⟩
            rw [j1_post, ← hfin, hdB, overlap_cons_gt _ _ _ ?_]
            intro z hz
            rw [hdA] at hz
            rcases List.mem_cons.mp hz with hz | hz
            · omega
            · have := hxs z hz; omega
          · rename_i hyx
            have hxe : x.val = y.val := by scalar_tac
            step as ⟨common1, common1_post⟩
            step as ⟨i5, i5_post⟩
            step as ⟨j1, j1_post⟩
            refine ⟨by omega, by omega, by omega, ?_, by omega⟩
            rw [i5_post, j1_post, ← hfin, hdA, hdB, hxe, overlap_cons_eq]
            omega
      · rename_i hdj
        have hd2 : lb.length ≤ d.val := by scalar_tac
        have hB : (vals lb.val).drop d.val = [] :=
          List.drop_of_length_le (by rw [vals_length]; exact hd2)
        rw [hB, overlap_nil_right] at hfin
        simp only [WP.spec_ok]
        omega
    · rename_i hci
      have hc2 : la.length ≤ c.val := by scalar_tac
      have hA : (vals la.val).drop c.val = [] :=
        List.drop_of_length_le (by rw [vals_length]; exact hc2)
      rw [hA, overlap_nil_left] at hfin
      simp only [WP.spec_ok]
      omega
  · exact ⟨hi, hj, hc, rfl⟩


/-- What the proof assumes about `<[u32]>::sort_unstable`, which stock Aeneas leaves as an opaque axiom:
it returns a sorted permutation of its argument. This is the documented behaviour of the Rust function. -/
def SortSpec : Prop := ∀ s : Slice Std.U32,
  core.slice.Slice.sort_unstable core.cmp.OrdU32 s ⦃ r => r.val.Perm s.val ∧ (vals r.val).Pairwise (· ≤ ·) ⦄

theorem clone_u32 (v : alloc.vec.Vec Std.U32) :
    alloc.vec.CloneVec.clone core.clone.CloneU32 v ⦃ r => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  have h := Slice.clone_spec (clone := core.clone.CloneU32.clone) (s := v.slice) (by intro x _; rfl)
  obtain ⟨s', hs', hh⟩ := WP.spec_imp_exists h
  rw [hs']
  simp only [bind_tc_ok, WP.spec_ok]
  rw [← hh]

theorem label_lower_bound_spec (hsort : SortSpec) (a b : ted_core.PostTree)
    (ha : a.label.length < 2 ^ 31) (hb : b.label.length < 2 ^ 31) :
    ted_core.label_lower_bound a b ⦃ r =>
      r.val = max a.label.length b.label.length - overlap (vals a.label.val) (vals b.label.val) ⦄ := by
  unfold ted_core.label_lower_bound
  step with clone_u32 a.label as ⟨la, la_post⟩
  step with clone_u32 b.label as ⟨lb, lb_post⟩
  subst la_post lb_post
  simp only [lift, bind_tc_ok, alloc.vec.Vec.deref_mut]
  step with hsort a.label.slice as ⟨s1, hs1, hs1s⟩
  step with hsort b.label.slice as ⟨s3, hs3, hs3s⟩
  have hl1 : s1.val.length = a.label.length := hs1.length_eq
  have hl3 : s3.val.length = b.label.length := hs3.length_eq
  have hov : overlap (vals s1.val) (vals s3.val) = overlap (vals a.label.val) (vals b.label.val) :=
    overlap_perm (hs1.map _) (hs3.map _)
  step with llb_loop_spec ({ slice := s1 } : alloc.vec.Vec Std.U32) ({ slice := s3 } : alloc.vec.Vec Std.U32)
    0#usize 0#usize 0#u32 hs1s hs3s (by show s1.val.length < 2 ^ 31; omega) (by simp) (by simp) (by simp)
    as ⟨common, hcommon⟩
  step as ⟨i2, hi2⟩
  have hla := alloc.vec.Vec.len_val a.label
  have hlb := alloc.vec.Vec.len_val b.label
  have hc3 : (UScalar.cast .U32 i2).val = max a.label.length b.label.length := by
    rw [UScalar.cast_val_eq]
    simp only [UScalarTy.numBits]
    rw [hi2, Nat.mod_eq_of_lt (by omega)]
    omega
  have hcommon' : common.val = 0 + overlap (List.drop 0 (vals s1.val)) (List.drop 0 (vals s3.val)) := hcommon
  have hcv : common.val = overlap (vals a.label.val) (vals b.label.val) := by
    rw [hcommon', ← hov]; simp
  have hle : overlap (vals a.label.val) (vals b.label.val) ≤ max a.label.length b.label.length := by
    have := overlap_le_left (vals a.label.val) (vals b.label.val)
    rw [vals_length] at this
    exact Nat.le_trans this (Nat.le_max_left _ _)
  step as ⟨r, hr⟩
  rw [hr, hc3, hcv]

end difffold_lines_extract
