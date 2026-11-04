import FillLoop
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

/-- `fill` returns a result exactly when the model cell `(n, m)` survives pruning, and then the last stored
row holds the model's value there. When it returns `none`, the model cell is pruned. -/
theorem fill_spec (C : Ctx O inst) (o : O) (c : kernel.Counters)
    (hmsmall : C.g.m < 2 ^ 27) (hnsmall : C.g.n < 2 ^ 27) (hsum : sumU C.sb.val < 2 ^ 27)
    (htau0 : hK C.ra C.rb C.on 0 0 ≤ C.tau.val) (hInv : C.Inv o) :
    kernel.fill inst o C.sa C.sb C.ra C.rb C.tau C.on c ⦃ r =>
      C.Inv r.2.1 ∧
      (∀ rows, r.1 = some rows → rows.length = C.g.n + 1 ∧ (∀ k ≤ C.g.n, RowOK C rows.val[k]! k) ∧
         ∃ x, C.g.P C.h C.tau.val C.g.n C.g.m = some x ∧ rowSem rows.val[C.g.n]! C.g.m = x) ∧
      (r.1 = none → C.g.P C.h C.tau.val C.g.n C.g.m = none) ⦄ := by
  unfold kernel.fill
  have hnv : (Slice.len C.sa).val = C.g.n := by rw [C.hn]; simp [Slice.len]
  have hmv : (Slice.len C.sb).val = C.g.m := by rw [C.hm]; simp [Slice.len]
  have htau : C.tau.val < INFn := by have := C.htau; omega
  step with first_row_spec C.g C.sb C.ra C.rb C.on C.tau C.hgsb hsum C.hra C.hrb (by have := C.hralen; omega) C.hrblen htau htau0 as ⟨r0, hlo, hl0, hle0, hv0, hsem0, htail0⟩
  step as ⟨rows, hrows⟩
  have hrow0 : RowOK C r0 0 := by
    refine ⟨hl0, by have := C.hm; omega, ?_, by intro j hj; omega⟩
    intro j hj; exact hsem0 j (by rw [C.hm] at hj; omega)
  have hrowsv : rows.val = [r0] := by rw [hrows]; simp [alloc.vec.Vec.new]
  step with fill_loop_spec C (Slice.len C.sa) hnv hmsmall hnsmall o c rows 1#usize true (by simp) (by simp) hInv
    (by intro _; refine ⟨by simp [alloc.vec.Vec.length, hrowsv], ?_⟩; intro k hk; simp at hk; subst hk; simpa [hrowsv] using hrow0)
    (by intro h; simp at h) as ⟨o1, c1, rows1, ok1, hI1, hT, hF⟩
  cases ok1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hI1, by simp, fun _ => ?_⟩
    obtain ⟨k, hk, hkn⟩ := hF rfl
    have := allnone_forward C k hkn (C.g.n - k)
    rw [show k + (C.g.n - k) = C.g.n by omega] at this
    exact this C.g.m le_rfl
  | true =>
    obtain ⟨hlen, hall⟩ := hT rfl
    simp only [↓reduceIte]
    have hidx : (Slice.len C.sa).val < rows1.length := by rw [hnv]; omega
    step as ⟨r1, hr1⟩
    step as ⟨i, hi⟩
    have hrn : r1 = rows1.val[C.g.n]! := by
      have h1 : rows1.val[(Slice.len C.sa).val]! = rows1.val[C.g.n]! := by rw [hnv]
      rw [hr1, ← h1]; exact (getElem!_pos rows1.val _ hidx).symm
    have hrok := hall C.g.n le_rfl
    rw [← hrn] at hrok
    obtain ⟨_, _, hsemn, _⟩ := hrok
    have hival : i.val = enc (C.g.P C.h C.tau.val C.g.n C.g.m) := by rw [hi, hmv]; exact hsemn C.g.m le_rfl
    split
    · rename_i hlt
      have hlt' : i.val < INFn := by have h : i.val < kernel.INF.val := hlt; rw [kernel_INF_val] at h; exact h
      refine ⟨hI1, ?_, by simp⟩
      intro rows' hr'
      have hrr : rows' = rows1 := by simpa using hr'.symm
      subst hrr
      refine ⟨hlen, hall, ?_⟩
      cases hp : C.g.P C.h C.tau.val C.g.n C.g.m with
      | none => rw [hp] at hival; simp [enc] at hival; omega
      | some x =>
        have h2 : i.val = x := by rw [hival, hp]; simp [enc]
        have : rowSem r1 C.g.m = i.val := by rw [hi, hmv]
        rw [← hrn, this, h2]
    · rename_i hge
      have hge' : INFn ≤ i.val := by have h : ¬ i.val < kernel.INF.val := hge; rw [kernel_INF_val] at h; omega
      refine ⟨hI1, by simp, fun _ => ?_⟩
      exact enc_inf_none _ _ _ _ _ htau (by have := enc_le_inf C.g C.h C.tau.val C.g.n C.g.m htau; omega)

end difffold_kernel_extract
