import Difffold.Basic
import Difffold.Decision
/-!
# Linking the grid DP to alignments of child lists

`ofLists d a b` is the grid of `Differ::align_mid`: `sa i = size a[i]`, `sb j = size b[j]`,
`dd i j = d a[i] b[j]` (the recursive distance), and `h i j = |R_a(i) - R_b(j)|` with
`R_a(i) = sum of sizes of a[i..]` (the reversed accumulation, `suffix_sums`).
-/
namespace Difffold
open Grid

def sizeAt (a : List Tree) (i : Nat) : Nat := (a[i]?).elim 0 Tree.size

def ofLists (d : Tree → Tree → Nat) (a b : List Tree) : Grid where
  n := a.length
  m := b.length
  sa := sizeAt a
  sb := sizeAt b
  dd := fun i j => match a[i]?, b[j]? with
    | some x, some y => d x y
    | _, _ => 0

/-- The heuristic of the code: absolute difference of reversed size accumulations. -/
def hLists (a b : List Tree) (i j : Nat) : Nat := adiff (Tree.sizeF (a.drop i)) (Tree.sizeF (b.drop j))

theorem drop_cons_inv {a : List Tree} {i : Nat} {x : Tree} {xs : List Tree}
    (h : a.drop i = x :: xs) : ∃ hi : i < a.length, a[i] = x ∧ a.drop (i + 1) = xs := by
  by_cases hi : i < a.length
  · rw [List.drop_eq_getElem_cons hi] at h
    cases h
    exact ⟨hi, rfl, rfl⟩
  · rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h

theorem drop_cons {a : List Tree} {i : Nat} (hi : i < a.length) :
    a.drop i = a[i] :: a.drop (i + 1) := List.drop_eq_getElem_cons hi

theorem sizeAt_lt {a : List Tree} {i : Nat} (hi : i < a.length) : sizeAt a i = a[i].size := by
  simp [sizeAt, hi]

namespace Grid
variable (g : Grid)
theorem B_cases {i j : Nat} (hi : i < g.n) (hj : j < g.m) :
    g.B i j = g.sa i + g.B (i + 1) j ∨ g.B i j = g.sb j + g.B i (j + 1) ∨
      g.B i j = g.dd i j + g.B (i + 1) (j + 1) := by
  rw [B]; simp only [hi, hj, dite_true]; omega
theorem B_eq_del {i j : Nat} (hi : i < g.n) (hj : ¬ j < g.m) : g.B i j = g.sa i + g.B (i + 1) j := by
  rw [B]; simp only [hi, hj, dite_true, dite_false]
theorem B_eq_ins {i j : Nat} (hi : ¬ i < g.n) (hj : j < g.m) : g.B i j = g.sb j + g.B i (j + 1) := by
  rw [B]; simp only [hi, hj, dite_true, dite_false]
theorem B_eq_zero {i j : Nat} (hi : ¬ i < g.n) (hj : ¬ j < g.m) : g.B i j = 0 := by
  rw [B]; simp only [hi, hj, dite_false]
end Grid

section
variable (d : Tree → Tree → Nat) (a b : List Tree)

/-- `R*` is realised by an actual alignment of the suffixes. -/
theorem B_realized : ∀ k i j, ((ofLists d a b).n - i) + ((ofLists d a b).m - j) = k →
    i ≤ a.length → j ≤ b.length → Align d (a.drop i) (b.drop j) ((ofLists d a b).B i j) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i j hk hi hj
    have hn : (ofLists d a b).n = a.length := rfl
    have hm : (ofLists d a b).m = b.length := rfl
    by_cases h1 : i < a.length
    · have sa' : (ofLists d a b).sa i = a[i].size := sizeAt_lt h1
      have hd : a.drop i = a[i] :: a.drop (i + 1) := drop_cons h1
      by_cases h2 : j < b.length
      · have sb' : (ofLists d a b).sb j = b[j].size := sizeAt_lt h2
        have hd2 : b.drop j = b[j] :: b.drop (j + 1) := drop_cons h2
        have dd' : (ofLists d a b).dd i j = d a[i] b[j] := by simp [ofLists, h1, h2]
        have p1 := ih (((ofLists d a b).n - (i+1)) + ((ofLists d a b).m - j)) (by omega) (i+1) j rfl (by omega) (by omega)
        have p2 := ih (((ofLists d a b).n - i) + ((ofLists d a b).m - (j+1))) (by omega) i (j+1) rfl (by omega) (by omega)
        have p3 := ih (((ofLists d a b).n - (i+1)) + ((ofLists d a b).m - (j+1))) (by omega) (i+1) (j+1) rfl (by omega) (by omega)
        have cA : Align d (a.drop i) (b.drop j) (a[i].size + (ofLists d a b).B (i+1) j) := by
          rw [hd]; exact AlignR.del p1
        have cB : Align d (a.drop i) (b.drop j) (b[j].size + (ofLists d a b).B i (j+1)) := by
          rw [hd2]; exact AlignR.ins p2
        have cC : Align d (a.drop i) (b.drop j) (d a[i] b[j] + (ofLists d a b).B (i+1) (j+1)) := by
          rw [hd, hd2]; exact AlignR.pair rfl p3
        rcases (ofLists d a b).B_cases (i := i) (j := j) (by omega) (by omega) with e | e | e
        · rw [e, sa']; exact cA
        · rw [e, sb']; exact cB
        · rw [e, dd']; exact cC
      · have p1 := ih (((ofLists d a b).n - (i+1)) + ((ofLists d a b).m - j)) (by omega) (i+1) j rfl (by omega) (by omega)
        rw [(ofLists d a b).B_eq_del (by omega) (by omega), sa', hd]
        exact AlignR.del p1
    · by_cases h2 : j < b.length
      · have sb' : (ofLists d a b).sb j = b[j].size := sizeAt_lt h2
        have hd2 : b.drop j = b[j] :: b.drop (j + 1) := drop_cons h2
        have p2 := ih (((ofLists d a b).n - i) + ((ofLists d a b).m - (j+1))) (by omega) i (j+1) rfl (by omega) (by omega)
        rw [(ofLists d a b).B_eq_ins (by omega) (by omega), sb', hd2]
        exact AlignR.ins p2
      · rw [(ofLists d a b).B_eq_zero (by omega) (by omega),
          List.drop_eq_nil_of_le (by omega : a.length ≤ i), List.drop_eq_nil_of_le (by omega : b.length ≤ j)]
        exact AlignR.nil

/-- `R*` is a lower bound for every alignment of the suffixes. -/
theorem B_min : ∀ {xs ys c}, Align d xs ys c → ∀ i j, xs = a.drop i → ys = b.drop j →
    i ≤ a.length → j ≤ b.length → (ofLists d a b).B i j ≤ c := by
  intro xs ys c hA
  induction hA with
  | nil =>
    intro i j hx hy hi hj
    have h1 := List.drop_eq_nil_iff.mp hx.symm
    have h2 := List.drop_eq_nil_iff.mp hy.symm
    have := (ofLists d a b).B_eq_zero (i := i) (j := j) (by show ¬ i < a.length; omega) (by show ¬ j < b.length; omega)
    omega
  | @del x xs ys c h ih =>
    intro i j hx hy hi hj
    obtain ⟨hi', hax, hxs⟩ := drop_cons_inv hx.symm
    have := ih (i + 1) j hxs.symm hy (by omega) hj
    have hb := (ofLists d a b).B_del (i := i) (j := j) hi' hj
    have : (ofLists d a b).sa i = x.size := by rw [← hax]; exact sizeAt_lt hi'
    omega
  | @ins y xs ys c h ih =>
    intro i j hx hy hi hj
    obtain ⟨hj', hby, hys⟩ := drop_cons_inv hy.symm
    have := ih i (j + 1) hx hys.symm hi (by omega)
    have hb := (ofLists d a b).B_ins (i := i) (j := j) hi hj'
    have : (ofLists d a b).sb j = y.size := by rw [← hby]; exact sizeAt_lt hj'
    omega
  | @pair x y xs ys c c' hp h ih =>
    intro i j hx hy hi hj
    obtain ⟨hi', hax, hxs⟩ := drop_cons_inv hx.symm
    obtain ⟨hj', hby, hys⟩ := drop_cons_inv hy.symm
    have := ih (i + 1) (j + 1) hxs.symm hys.symm (by omega) (by omega)
    have hb := (ofLists d a b).B_pair (i := i) (j := j) hi' hj'
    have : (ofLists d a b).dd i j = d x y := by
      subst hax; subst hby; simp [ofLists, hi', hj']
    have hp' : c' = d x y := hp
    omega
end


namespace Grid
variable (g : Grid)

theorem B0_le_F : ∀ i j, i ≤ g.n → j ≤ g.m → g.B 0 0 ≤ g.F i j + g.B i j := by
  intro i
  induction i with
  | zero =>
    intro j
    induction j with
    | zero => intro _ _; simp [F]
    | succ j ih =>
      intro hi hj
      have := ih hi (by omega)
      have hb := g.B_ins (i := 0) hi (by omega : j < g.m)
      have e : g.F 0 (j + 1) = g.F 0 j + g.sb j := by rw [F]
      omega
  | succ i ihi =>
    intro j
    induction j with
    | zero =>
      intro hi hj
      have := ihi 0 (by omega) hj
      have hb := g.B_del (i := i) (j := 0) (by omega) hj
      have e : g.F (i + 1) 0 = g.F i 0 + g.sa i := by rw [F]
      omega
    | succ j ihj =>
      intro hi hj
      have h1 := ihi (j + 1) (by omega) hj
      have h2 := ihj hi (by omega)
      have h3 := ihi j (by omega) (by omega)
      have hA := g.B_del (i := i) (j := j + 1) (by omega) hj
      have hB := g.B_ins (i := i + 1) (j := j) hi (by omega)
      have hC := g.B_pair (i := i) (j := j) (by omega) (by omega)
      have e : g.F (i + 1) (j + 1) = min (min (g.F i (j + 1) + g.sa i) (g.F (i + 1) j + g.sb j)) (g.F i j + g.dd i j) := by
        rw [F]
      omega

theorem F_le : ∀ k i j, (g.n - i) + (g.m - j) = k → i ≤ g.n → j ≤ g.m →
    g.F g.n g.m ≤ g.F i j + g.B i j := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i j hk hi hj
    by_cases h1 : i < g.n
    · by_cases h2 : j < g.m
      · have q1 := ih ((g.n - (i+1)) + (g.m - j)) (by omega) (i+1) j rfl (by omega) (by omega)
        have q2 := ih ((g.n - i) + (g.m - (j+1))) (by omega) i (j+1) rfl (by omega) (by omega)
        have q3 := ih ((g.n - (i+1)) + (g.m - (j+1))) (by omega) (i+1) (j+1) rfl (by omega) (by omega)
        have := g.F_del i j; have := g.F_ins i j; have := g.F_pair i j
        rcases g.B_cases h1 h2 with e | e | e <;> omega
      · have q1 := ih ((g.n - (i+1)) + (g.m - j)) (by omega) (i+1) j rfl (by omega) (by omega)
        have := g.F_del i j
        have e := g.B_eq_del h1 h2
        omega
    · by_cases h2 : j < g.m
      · have q2 := ih ((g.n - i) + (g.m - (j+1))) (by omega) i (j+1) rfl (by omega) (by omega)
        have := g.F_ins i j
        have e := g.B_eq_ins h1 h2
        omega
      · have e := g.B_eq_zero h1 h2
        have : i = g.n := by omega
        have : j = g.m := by omega
        subst_vars; omega

/-- Duality: the forward DP and the backward DP agree on the optimum. -/
theorem F_eq_B0 : g.F g.n g.m = g.B 0 0 := by
  have h1 := g.B0_le_F g.n g.m (Nat.le_refl _) (Nat.le_refl _)
  have h2 := g.F_le _ 0 0 rfl (by omega) (by omega)
  have h3 := g.B_end
  have : g.F 0 0 = 0 := by simp [F]
  omega
end Grid

section
variable (d : Tree → Tree → Nat) (a b : List Tree)

/-- **min-cost result correctness (model).** The grid optimum `F*(n,m)` is achieved by an
alignment of the two child lists and no alignment is cheaper. -/
theorem fstar_is_opt :
    Align d a b ((ofLists d a b).F (ofLists d a b).n (ofLists d a b).m) ∧
      ∀ c, Align d a b c → (ofLists d a b).F (ofLists d a b).n (ofLists d a b).m ≤ c := by
  rw [Grid.F_eq_B0]
  refine ⟨?_, ?_⟩
  · have := B_realized d a b _ 0 0 rfl (Nat.zero_le _) (Nat.zero_le _)
    simpa using this
  · intro c hc
    exact B_min d a b hc 0 0 (by simp) (by simp) (Nat.zero_le _) (Nat.zero_le _)

/-- The heuristic `h(i,j) = |R_a(i) - R_b(j)|` is admissible: `h <= R*`, because `R*` is the cost
of an actual alignment (`B_realized`) and `h_admissible` bounds every alignment's cost. -/
theorem hLists_admissible (hd : ∀ x y, SizeBound x y (d x y)) :
    ∀ i j, i ≤ (ofLists d a b).n → j ≤ (ofLists d a b).m → hLists a b i j ≤ (ofLists d a b).B i j := by
  intro i j hi hj
  have := h_admissible hd (B_realized d a b _ i j rfl hi hj)
  unfold hLists adiff
  omega

/-- **Pruning, end to end on child lists.** For any pair-cost function with the size bound (true of
the Selkow distance), for every threshold `tau`: the kept-cell DP returns a result iff the optimal
alignment cost is `<= tau`, and the result is that optimal cost. -/
theorem prune_correct_lists (hd : ∀ x y, SizeBound x y (d x y)) (tau : Nat) :
    ((ofLists d a b).P (hLists a b) tau (ofLists d a b).n (ofLists d a b).m).isSome ↔
      (ofLists d a b).F (ofLists d a b).n (ofLists d a b).m ≤ tau :=
  Grid.decision (hLists_admissible d a b hd)

theorem widen_correct_lists (hd : ∀ x y, SizeBound x y (d x y)) :
    ∀ k tau v, Grid.search (ofLists d a b) (hLists a b) k tau = some v →
      Align d a b v ∧ ∀ c, Align d a b c → v ≤ c := by
  intro k tau v hv
  rw [Grid.search_min (hLists_admissible d a b hd) k tau v hv]
  exact fstar_is_opt d a b

end

end Difffold
