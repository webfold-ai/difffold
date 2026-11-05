/-! The Zhang-Shasha forest distance on postorder indices, in plain Lean.

Two trees are given by their leftmost-leaf maps `la lb : Nat → Nat` (1-based postorder) and a relabel cost
`ren x y` for node `x` of the first and `y` of the second. `D la lb ren l x l' y` is the edit distance between
the forests made of the nodes `l .. x` of the first tree and `l' .. y` of the second, with unit insertion and
deletion cost and relabel cost `ren`. It is the textbook right-to-left recursion: the last node of either
forest is deleted or inserted, or the two last trees are matched. When the last trees start at the left
ends of both forests (`lml x = l` and `lml y = l'`) the match is one whole tree against one whole tree and
costs `D (x-1) (y-1) + ren x y`; otherwise it splits the forests before the last trees and adds the distance
of the two last trees. (`lml x` is clamped into `l .. x`, which changes nothing on well formed trees.) -/
namespace Ted

def clampL (l x lx : Nat) : Nat := max l (min lx x)

def D (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (l x l' y : Nat) : Nat :=
  if h1 : x < l ∨ x = 0 then y + 1 - l'
  else if h2 : y < l' ∨ y = 0 then x + 1 - l
  else
    if clampL l x (la x) = l ∧ clampL l' y (lb y) = l' then
      min (min (D la lb ren l (x - 1) l' y + 1) (D la lb ren l x l' (y - 1) + 1))
        (D la lb ren l (x - 1) l' (y - 1) + ren x y)
    else
      min (min (D la lb ren l (x - 1) l' y + 1) (D la lb ren l x l' (y - 1) + 1))
        (D la lb ren l (clampL l x (la x) - 1) l' (clampL l' y (lb y) - 1) +
          D la lb ren (clampL l x (la x)) x (clampL l' y (lb y)) y)
termination_by (x + 1 - l) + (y + 1 - l')
decreasing_by
  all_goals simp_wf
  all_goals (try unfold clampL at *)
  all_goals omega

section
variable (la lb : Nat → Nat) (ren : Nat → Nat → Nat)

theorem D_base1 (l x l' y : Nat) (h : x < l ∨ x = 0) : D la lb ren l x l' y = y + 1 - l' := by
  rw [D]; simp [h]

theorem D_base2 (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : y < l' ∨ y = 0) :
    D la lb ren l x l' y = x + 1 - l := by
  rw [D]; simp [h1, h2]

theorem D_leaf (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l') :
    D la lb ren l x l' y =
      min (min (D la lb ren l (x - 1) l' y + 1) (D la lb ren l x l' (y - 1) + 1))
        (D la lb ren l (x - 1) l' (y - 1) + ren x y) := by
  rw [D]; simp [h1, h2, hc]

theorem D_nonleaf (l x l' y : Nat) (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hc : ¬ (clampL l x (la x) = l ∧ clampL l' y (lb y) = l')) :
    D la lb ren l x l' y =
      min (min (D la lb ren l (x - 1) l' y + 1) (D la lb ren l x l' (y - 1) + 1))
        (D la lb ren l (clampL l x (la x) - 1) l' (clampL l' y (lb y) - 1) +
          D la lb ren (clampL l x (la x)) x (clampL l' y (lb y)) y) := by
  rw [D]; simp [h1, h2, hc]

/-- The distance is at least the difference of the sizes, and at most their sum. -/
theorem D_size : ∀ (n l x l' y : Nat), 1 ≤ l → 1 ≤ l' → (x + 1 - l) + (y + 1 - l') = n →
    (x + 1 - l ≤ (y + 1 - l') + D la lb ren l x l' y ∧ y + 1 - l' ≤ (x + 1 - l) + D la lb ren l x l' y ∧
      D la lb ren l x l' y ≤ (x + 1 - l) + (y + 1 - l')) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro l x l' y hl hl' hn
  by_cases h1 : x < l ∨ x = 0
  · rw [D_base1 la lb ren l x l' y h1]; omega
  by_cases h2 : y < l' ∨ y = 0
  · rw [D_base2 la lb ren l x l' y h1 h2]; omega
  have hxl : l ≤ x := by omega
  have hyl : l' ≤ y := by omega
  have i1 := ih ((x - 1 + 1 - l) + (y + 1 - l')) (by omega) l (x - 1) l' y hl hl' rfl
  have i2 := ih ((x + 1 - l) + (y - 1 + 1 - l')) (by omega) l x l' (y - 1) hl hl' rfl
  by_cases hc : clampL l x (la x) = l ∧ clampL l' y (lb y) = l'
  · rw [D_leaf la lb ren l x l' y h1 h2 hc]
    have i3 := ih ((x - 1 + 1 - l) + (y - 1 + 1 - l')) (by omega) l (x - 1) l' (y - 1) hl hl' rfl
    omega
  · rw [D_nonleaf la lb ren l x l' y h1 h2 hc]
    unfold clampL at hc ⊢
    have hlx1 : l ≤ max l (min (la x) x) := Nat.le_max_left _ _
    have hlx2 : max l (min (la x) x) ≤ x := by omega
    have hly1 : l' ≤ max l' (min (lb y) y) := Nat.le_max_left _ _
    have hly2 : max l' (min (lb y) y) ≤ y := by omega
    have i3 := ih ((max l (min (la x) x) - 1 + 1 - l) + (max l' (min (lb y) y) - 1 + 1 - l')) (by omega)
      l (max l (min (la x) x) - 1) l' (max l' (min (lb y) y) - 1) hl hl' rfl
    have i4 := ih ((x + 1 - max l (min (la x) x)) + (y + 1 - max l' (min (lb y) y))) (by omega)
      (max l (min (la x) x)) x (max l' (min (lb y) y)) y (by omega) (by omega) rfl
    clear ih hc h1 h2
    generalize max l (min (la x) x) = lx at *
    generalize max l' (min (lb y) y) = ly at *
    omega

end

end Ted
