import RowCellsWrap
import Trim
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

instance : Inhabited kernel.Row := ⟨⟨0#usize, alloc.vec.Vec.new Std.U32⟩⟩

/-- A stored row is the model row `k`: it covers the model row exactly, with no kept cell below its first column. -/
def RowOK (C : Ctx O inst) (r : kernel.Row) (k : Nat) : Prop :=
  0 < r.v.length ∧ r.lo.val + r.v.length ≤ C.g.m + 1 ∧
  (∀ j ≤ C.g.m, rowSem r j = enc (C.g.P C.h C.tau.val k j)) ∧
  (∀ j < r.lo.val, C.g.P C.h C.tau.val k j = none)

/-- Every cell of model row `k` is pruned. -/
def AllNone (C : Ctx O inst) (k : Nat) : Prop := ∀ j ≤ C.g.m, C.g.P C.h C.tau.val k j = none

theorem enc_le_inf (g : Grid) (h : Nat → Nat → Nat) (tau i j : Nat) (htau : tau < INFn) :
    enc (g.P h tau i j) ≤ INFn := by
  cases hp : g.P h tau i j with
  | none => simp [enc]
  | some x => have := P_le_tau g h tau i j x hp; simp only [enc]; omega

/-- `trim_row` of a raw row that satisfies the `row_cells` conclusion is either a faithful stored row or
proves that every cell of the row is pruned. -/
theorem after_row (C : Ctx O inst) (v : alloc.vec.Vec Std.U32) (plo : Std.Usize) (i : Nat)
    (hmsmall : C.g.m < 2 ^ 27)
    (hbelow : ∀ j < plo.val, C.g.P C.h C.tau.val i j = none)
    (hv0 : 0 < v.length) (hvs : plo.val + v.length ≤ C.g.m + 1)
    (hvv : ∀ t < v.length, v.val[t]!.val = enc (C.g.P C.h C.tau.val i (plo.val + t)))
    (htail : ∀ j', plo.val + v.length ≤ j' → j' ≤ C.g.m → C.g.P C.h C.tau.val i j' = none) :
    kernel.trim_row v plo ⦃ r =>
      match r with
      | none => AllNone C i
      | some row => RowOK C row i ⦄ := by
  have htau : C.tau.val < INFn := by have := C.htau; omega
  have hplo : plo.val < 2 ^ 31 := by omega
  have hlen : v.length < 2 ^ 31 := by omega
  have hv : ∀ t < v.length, v.val[t]!.val ≤ INFn := by
    intro t ht; rw [hvv t ht]; exact enc_le_inf _ _ _ _ _ htau
  have hraw : ∀ j ≤ C.g.m, rawSem v plo.val j = enc (C.g.P C.h C.tau.val i j) := by
    intro j hj
    unfold rawSem
    split_ifs with h1 h2
    · rw [hbelow j h1]; simp [enc]
    · have := hvv (j - plo.val) h2
      rw [this]; congr 3; omega
    · rw [htail j (by omega) hj]; simp [enc]
  refine WP.spec_mono (trim_row_spec v plo hlen hplo hv) ?_
  intro r hr
  cases r with
  | none =>
    intro j hj
    by_cases h1 : j < plo.val
    · exact hbelow j h1
    · by_cases h2 : j - plo.val < v.length
      · have h4 := hr (j - plo.val) h2
        have h3 := hvv (j - plo.val) h2
        have e : plo.val + (j - plo.val) = j := by omega
        rw [e, h4] at h3
        have : enc (C.g.P C.h C.tau.val i j) = INFn := h3.symm
        exact enc_inf_none _ _ _ _ _ htau this
      · exact htail j (by omega) hj
  | some row =>
    obtain ⟨hrl, hrlo, hrhi, hrs⟩ := hr
    refine ⟨hrl, by omega, ?_, ?_⟩
    · intro j hj; rw [hrs j]; exact hraw j hj
    · intro j hj
      have h1 := hrs j
      have h2 : rowSem row j = INFn := by unfold rowSem; simp [hj]
      have hjm : j ≤ C.g.m := by omega
      have := hraw j hjm
      rw [← h1, h2] at this
      exact enc_inf_none _ _ _ _ _ htau this.symm

/-- A fully pruned row stays fully pruned in every later row. -/
theorem allnone_forward (C : Ctx O inst) (k : Nat) (hk : AllNone C k) :
    ∀ d, AllNone C (k + d) := by
  have htau : True := trivial
  intro d
  induction d with
  | zero => simpa using hk
  | succ d ih =>
    show AllNone C (k + d + 1)
    intro j
    induction j with
    | zero =>
      intro _
      exact P_cell_none C.g C.h C.tau.val (k + d + 1) 0 (by omega) (by simpa using ih 0 (Nat.zero_le _)) (Or.inl rfl) (Or.inl rfl)
    | succ j ihj =>
      intro hj
      have hl := ihj (by omega)
      exact P_cell_none C.g C.h C.tau.val (k + d + 1) (j + 1) (by omega)
        (by simpa using ih (j + 1) hj) (Or.inr (by simpa using hl)) (Or.inr (by simpa using ih j (by omega)))


theorem getbang_append_left {α : Type} [Inhabited α] (l : List α) (x : α) (k : Nat) (hk : k < l.length) :
    (l ++ [x])[k]! = l[k]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getbang_append_last {α : Type} [Inhabited α] (l : List α) (x : α) : (l ++ [x])[l.length]! = x := by
  simp [List.getElem!_eq_getElem?_getD]

/-- The `fill` loop builds the model rows one after another, or stops at a fully pruned row. -/
theorem fill_loop_spec (C : Ctx O inst) (n : Std.Usize) (hn : n.val = C.g.n) (hmsmall : C.g.m < 2 ^ 27) (hnsmall : C.g.n < 2 ^ 27)
    (o : O) (c : kernel.Counters) (rows : alloc.vec.Vec kernel.Row) (i : Std.Usize) (ok1 : Bool)
    (hi : 1 ≤ i.val) (hin : i.val ≤ C.g.n + 1) (hInv : C.Inv o)
    (hrows : ok1 = true → rows.length = i.val ∧ ∀ k < i.val, RowOK C rows.val[k]! k)
    (hdead : ok1 = false → ∃ k, k < i.val ∧ AllNone C k) :
    kernel.fill_loop inst o C.sa C.sb C.ra C.rb C.tau C.on c n rows i ok1 ⦃ r =>
      C.Inv r.1 ∧
      (r.2.2.2 = true → r.2.2.1.length = C.g.n + 1 ∧ ∀ k ≤ C.g.n, RowOK C r.2.2.1.val[k]! k) ∧
      (r.2.2.2 = false → ∃ k, k ≤ C.g.n ∧ AllNone C k) ⦄ := by
  unfold kernel.fill_loop
  apply loop.spec_decr_nat
    (measure := fun p => n.val + 1 - p.2.2.2.1.val)
    (inv := fun p => C.Inv p.1 ∧ 1 ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ C.g.n + 1 ∧
      (p.2.2.2.2 = true → p.2.2.1.length = p.2.2.2.1.val ∧ ∀ k < p.2.2.2.1.val, RowOK C p.2.2.1.val[k]! k) ∧
      (p.2.2.2.2 = false → ∃ k, k < p.2.2.2.1.val ∧ AllNone C k))
  · intro p hp
    obtain ⟨o1, c1, rows1, i1, ok1'⟩ := p
    obtain ⟨hI, hi1, hi2, hR, hD⟩ := hp
    dsimp only at hI hi1 hi2 hR hD ⊢
    unfold kernel.fill_loop.body
    split
    · rename_i hle
      have hiN : i1.val ≤ n.val := by scalar_tac
      split
      · rename_i hok
        have hokb : ok1' = true := by simpa using hok
        obtain ⟨hlen, hall⟩ := hR hokb
        step as ⟨i1m, hi1m⟩
        have hidx : i1m.val < rows1.length := by omega
        step as ⟨r, hr⟩
        step as ⟨r1, hr1⟩
        have hr1r : r1 = r := by rw [hr1, hr]
        subst hr1r
        have hrr : r1 = rows1.val[i1m.val]! := by rw [hr]; exact (getElem!_pos rows1.val i1m.val (by omega)).symm
        have hrok : RowOK C r1 (i1.val - 1) := by
          have := hall i1m.val (by omega)
          rw [← hrr] at this
          rwa [show i1m.val = i1.val - 1 from hi1m] at this
        obtain ⟨hv0, hvs, hrs, hrb⟩ := hrok
        have hbelowI : ∀ j' < r1.lo.val, C.g.P C.h C.tau.val i1.val j' = none :=
          P_below_none C.g C.h C.tau.val i1.val r1.lo.val hi1 hrb
        have hmlt : C.sb.val.length < Std.Usize.max := by have := C.hm; scalar_tac
        have hi1n : i1.val ≤ C.g.n := by omega
        step with row_cells_spec C r1 o1 i1 c1 hi1 hi1n hmlt hv0 hvs hrs hI hbelowI as ⟨v, o2, c2, hI2, hl, hs, hvv, htail⟩
        step with after_row C v r1.lo i1.val hmsmall hbelowI hl hs hvv htail as ⟨o3, ho3⟩
        cases o3 with
        | none =>
          dsimp only
          step as ⟨i2, hi2v⟩
          refine ⟨hI2, by omega, by omega, by simp, fun _ => ⟨i1.val, by omega, ho3⟩, by omega⟩
        | some r2 =>
          dsimp only
          have hpush : rows1.val.length < Std.Usize.max := by
            have : rows1.val.length = i1.val := hlen
            scalar_tac
          step as ⟨rows2, hrows2⟩
          step as ⟨i2, hi2v⟩
          have hl2 : rows2.length = i2.val := by
            have : rows2.val.length = rows1.val.length + 1 := by rw [hrows2]; simp
            have : rows1.val.length = i1.val := hlen
            simp only [alloc.vec.Vec.length]; omega
          refine ⟨hI2, by omega, by omega, fun _ => ⟨hl2, ?_⟩, by simp, by omega⟩
          intro k hk
          rw [hrows2]
          have hl1 : rows1.val.length = i1.val := hlen
          by_cases hkk : k < rows1.val.length
          · rw [getbang_append_left _ _ _ hkk]; exact hall k (by omega)
          · have hke : k = rows1.val.length := by have : rows1.val.length = i1.val := hlen; omega
            rw [hke, getbang_append_last]
            have : rows1.val.length = i1.val := hlen
            rw [this] at *
            exact ho3
      · rename_i hok
        have hokb : ok1' = false := by simpa using hok
        obtain ⟨k, hk, hkn⟩ := hD hokb
        rw [WP.spec_ok]
        dsimp only
        exact ⟨hI, by simp, fun _ => ⟨k, by omega, hkn⟩⟩
    · rename_i hgt
      have hiN : n.val < i1.val := by scalar_tac
      rw [WP.spec_ok]
      dsimp only
      refine ⟨hI, fun hok => ?_, fun hok => ?_⟩
      · obtain ⟨hlen, hall⟩ := hR hok
        exact ⟨by omega, fun k hk => hall k (by omega)⟩
      · obtain ⟨k, hk, hkn⟩ := hD hok
        exact ⟨k, by omega, hkn⟩
  · exact ⟨hInv, hi, hin, hrows, hdead⟩

end difffold_kernel_extract
