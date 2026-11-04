import FillOptimal
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

/-- The absolute difference of two naturals. -/
def ad (x y : Nat) : Nat := max x y - min x y

/-- The reversed accumulation of a size function: the total of `f i, f (i+1), ..., f (n-1)`. -/
def RS (f : Nat → Nat) (n i : Nat) : Nat := if i < n then f i + RS f n (i + 1) else 0
termination_by n - i

theorem RS_step (f : Nat → Nat) (n i : Nat) (h : i < n) : RS f n i = f i + RS f n (i + 1) := by
  rw [RS]; simp [h]

theorem RS_end (f : Nat → Nat) (n i : Nat) (h : n ≤ i) : RS f n i = 0 := by
  rw [RS]; simp; omega

/-- **The bound is admissible, for any grid whose pair costs respect the size bound.** The remaining cost
`B(i, j)` is at least `|R_a(i) - R_b(j)|`. -/
theorem ad_le_B (g : Grid)
    (hsz : ∀ i j, i < g.n → j < g.m → g.sa i ≤ g.sb j + g.dd i j ∧ g.sb j ≤ g.sa i + g.dd i j) :
    ∀ k i j, (g.n - i) + (g.m - j) = k → i ≤ g.n → j ≤ g.m →
      ad (RS g.sa g.n i) (RS g.sb g.m j) ≤ g.B i j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i j hk hi hj
    rw [Grid.B]
    by_cases hin : i < g.n <;> by_cases hjm : j < g.m
    · simp only [hin, hjm, ↓reduceDIte]
      have h1 := ih ((g.n - (i + 1)) + (g.m - j)) (by omega) (i + 1) j rfl (by omega) hj
      have h2 := ih ((g.n - i) + (g.m - (j + 1))) (by omega) i (j + 1) rfl hi (by omega)
      have h3 := ih ((g.n - (i + 1)) + (g.m - (j + 1))) (by omega) (i + 1) (j + 1) rfl (by omega) (by omega)
      have hs := hsz i j hin hjm
      have e1 := RS_step g.sa g.n i hin
      have e2 := RS_step g.sb g.m j hjm
      unfold ad at *
      omega
    · have hjm' : j = g.m := by omega
      simp only [hin, hjm, ↓reduceDIte]
      have h1 := ih ((g.n - (i + 1)) + (g.m - j)) (by omega) (i + 1) j rfl (by omega) hj
      have e1 := RS_step g.sa g.n i hin
      have e2 := RS_end g.sb g.m j (by omega)
      unfold ad at *
      omega
    · have hin' : i = g.n := by omega
      simp only [hin, hjm, ↓reduceDIte]
      have h2 := ih ((g.n - i) + (g.m - (j + 1))) (by omega) i (j + 1) rfl hi (by omega)
      have e1 := RS_step g.sb g.m j hjm
      have e2 := RS_end g.sa g.n i (by omega)
      unfold ad at *
      omega
    · have hin' : i = g.n := by omega
      have hjm' : j = g.m := by omega
      simp only [hin, hjm, ↓reduceDIte]
      rw [RS_end g.sa g.n i (by omega), RS_end g.sb g.m j (by omega)]
      simp [ad]


/-- The reversed accumulation of the sizes in a list is the sum of the suffix. -/
theorem RS_eq_sumU (l : List Std.U32) :
    ∀ k i, l.length - i = k → i ≤ l.length → RS (fun t => l[t]!.val) l.length i = sumU (l.drop i) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    rw [RS_end _ _ _ (by omega)]
    rw [List.drop_of_length_le (by omega)]; simp [sumU]
  | succ k ih =>
    intro i hk hi
    have hlt : i < l.length := by omega
    rw [RS_step _ _ _ hlt, sumU_drop_succ l i hlt, ih (i + 1) (by omega) (by omega)]
    rw [getElem!_pos l i hlt]

/-- **The kernel's bound is admissible.** If `ra`, `rb` hold the suffix sums of `sa`, `sb` (what the extracted
`suffix_sums` returns, by `suffix_sums_spec`) and the pair costs respect the size bound, then
`hK ra rb on i j <= B(i, j)`. -/
theorem hK_admissible {O : Type} {inst : kernel.Oracle O} (C : Ctx O inst)
    (hra : ∀ i, i ≤ C.sa.val.length → C.ra.val[i]!.val = sumU (C.sa.val.drop i))
    (hrb : ∀ j, j ≤ C.sb.val.length → C.rb.val[j]!.val = sumU (C.sb.val.drop j)) :
    ∀ i j, i ≤ C.g.n → j ≤ C.g.m → C.h i j ≤ C.g.B i j := by
  intro i j hi hj
  unfold Ctx.h hK
  split
  · rename_i hon
    have hsz : ∀ i j, i < C.g.n → j < C.g.m → C.g.sa i ≤ C.g.sb j + C.g.dd i j ∧ C.g.sb j ≤ C.g.sa i + C.g.dd i j :=
      fun i j hi hj => C.hsize hon i j hi hj
    have h := ad_le_B C.g hsz _ i j rfl hi hj
    have hsa : (fun t => C.g.sa t) = (fun t => C.sa.val[t]!.val) := funext C.hgsa
    have hsb : (fun t => C.g.sb t) = (fun t => C.sb.val[t]!.val) := funext C.hgsb
    have e1 : RS C.g.sa C.g.n i = C.ra.val[i]!.val := by
      rw [hra i (by rw [← C.hn]; exact hi), show C.g.sa = (fun t => C.sa.val[t]!.val) from hsa, C.hn]
      exact RS_eq_sumU C.sa.val _ i rfl (by rw [← C.hn]; exact hi)
    have e2 : RS C.g.sb C.g.m j = C.rb.val[j]!.val := by
      rw [hrb j (by rw [← C.hm]; exact hj), show C.g.sb = (fun t => C.sb.val[t]!.val) from hsb, C.hm]
      exact RS_eq_sumU C.sb.val _ j rfl (by rw [← C.hm]; exact hj)
    rw [e1, e2] at h
    unfold ad at h
    split_ifs <;> omega
  · exact Nat.zero_le _


/-- **`fill` is optimal over the extracted code, with the heuristic discharged.** The only remaining
hypotheses are that `ra`, `rb` are the suffix sums of `sa`, `sb` (`suffix_sums_spec` proves exactly this
for the extracted `suffix_sums`), the size-bound hypotheses carried by `Ctx` (`hsize`: the oracle's pair
cost respects the size bound), the usual size limits, and `tau` at least the bound at the origin.
The result is stated against the grid optimum `F*`; that this grid is the child-list alignment of the two
nodes, and that the oracle's `pair_cost` is the recursive distance, are properties of `diff.rs`, not
proved here. -/
theorem fill_correct {O : Type} {inst : kernel.Oracle O} (C : Ctx O inst) (o : O) (c : kernel.Counters)
    (hmsmall : C.g.m < 2 ^ 27) (hnsmall : C.g.n < 2 ^ 27) (hsum : sumU C.sb.val < 2 ^ 27)
    (htau0 : hK C.ra C.rb C.on 0 0 ≤ C.tau.val) (hInv : C.Inv o)
    (hra : ∀ i, i ≤ C.sa.val.length → C.ra.val[i]!.val = sumU (C.sa.val.drop i))
    (hrb : ∀ j, j ≤ C.sb.val.length → C.rb.val[j]!.val = sumU (C.sb.val.drop j)) :
    kernel.fill inst o C.sa C.sb C.ra C.rb C.tau C.on c ⦃ r =>
      C.Inv r.2.1 ∧
      (∀ rows, r.1 = some rows →
        rowSem rows.val[C.g.n]! C.g.m = C.g.F C.g.n C.g.m ∧ C.g.F C.g.n C.g.m ≤ C.tau.val) ∧
      (r.1 = none → C.tau.val < C.g.F C.g.n C.g.m) ⦄ :=
  fill_optimal C o c hmsmall hnsmall hsum htau0 hInv (hK_admissible C hra hrb)

end difffold_kernel_extract
