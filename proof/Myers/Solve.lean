import Script
/-! A Lean model of `solve` in `src/lines.rs`: cut the common prefix and suffix, mark everything when one
side is empty, otherwise ask a middle-snake oracle `mid` for a split point and recurse on both halves.
`MidSpec` is the contract the oracle must meet; `Myers.lean` proves that the Myers sweep meets it.
The theorems here are about this model, not about the Rust code. -/
open scoped List
namespace Myers

def HeadsDiff (a b : List Nat) : Prop := ∀ x u y v, a = x :: u → b = y :: v → x ≠ y
/-- The last elements differ (when both lists are nonempty). -/
def LastsDiff (a b : List Nat) : Prop := HeadsDiff a.reverse b.reverse

/-- `a = p ++ a1 ++ s`, `b = p ++ b1 ++ s`, with the prefix and suffix maximal, as `common_prefix` and
`common_suffix` compute them. -/
def Trim (a b p a1 b1 s : List Nat) : Prop :=
  a = p ++ a1 ++ s ∧ b = p ++ b1 ++ s ∧ HeadsDiff a1 b1 ∧ LastsDiff a1 b1

/-- What the middle-snake oracle must deliver on a trimmed nonempty pair: a point inside the rectangle on
an optimal path (`Split`), and not the corner `(0,0)` or `(n,m)`, so that both halves are smaller. -/
def MidSpec (mid : List Nat → List Nat → Nat × Nat) : Prop :=
  ∀ a b, a ≠ [] → b ≠ [] → HeadsDiff a b → LastsDiff a b →
    (mid a b).1 ≤ a.length ∧ (mid a b).2 ≤ b.length ∧ Split a b (mid a b).1 (mid a b).2 ∧
    ¬((mid a b).1 = 0 ∧ (mid a b).2 = 0) ∧ ¬((mid a b).1 = a.length ∧ (mid a b).2 = b.length)

/-- `Solve mid a b da di`: the flags `solve` produces. The branches are those of the Rust function:
`emptyA`/`emptyB` fill, `split` recurses, `fallback` is the "no progress is possible" branch. -/
inductive Solve (mid : List Nat → List Nat → Nat × Nat) :
    List Nat → List Nat → List Bool → List Bool → Prop
  | emptyA {a b p b1 s : List Nat} : Trim a b p [] b1 s →
      Solve mid a b (List.replicate p.length false ++ [] ++ List.replicate s.length false)
        (List.replicate p.length false ++ List.replicate b1.length true ++ List.replicate s.length false)
  | emptyB {a b p a1 s : List Nat} : Trim a b p a1 [] s →
      Solve mid a b
        (List.replicate p.length false ++ List.replicate a1.length true ++ List.replicate s.length false)
        (List.replicate p.length false ++ [] ++ List.replicate s.length false)
  | split {a b p a1 b1 s : List Nat} {x y : Nat} {d1 e1 d2 e2 : List Bool} :
      Trim a b p a1 b1 s → a1 ≠ [] → b1 ≠ [] → mid a1 b1 = (x, y) →
      ¬((x = 0 ∧ y = 0) ∨ (x = a1.length ∧ y = b1.length)) →
      Solve mid (a1.take x) (b1.take y) d1 e1 → Solve mid (a1.drop x) (b1.drop y) d2 e2 →
      Solve mid a b (List.replicate p.length false ++ (d1 ++ d2) ++ List.replicate s.length false)
        (List.replicate p.length false ++ (e1 ++ e2) ++ List.replicate s.length false)
  | fallback {a b p a1 b1 s : List Nat} {x y : Nat} :
      Trim a b p a1 b1 s → a1 ≠ [] → b1 ≠ [] → mid a1 b1 = (x, y) →
      ((x = 0 ∧ y = 0) ∨ (x = a1.length ∧ y = b1.length)) →
      Solve mid a b
        (List.replicate p.length false ++ List.replicate a1.length true ++ List.replicate s.length false)
        (List.replicate p.length false ++ List.replicate b1.length true ++ List.replicate s.length false)

/-- Soundness and optimality of `solve`: whatever the oracle meets `MidSpec`, the flags are optimal. -/
theorem solve_optimal {mid : List Nat → List Nat → Nat × Nat} (hm : MidSpec mid)
    {a b : List Nat} {da di : List Bool} (h : Solve mid a b da di) : Optimal a b da di := by
  induction h with
  | emptyA ht =>
    obtain ⟨ha, hb, -, -⟩ := ht
    subst ha; subst hb
    have := @opt_trim _ [] _ _ [] [] (b1 := _) ?_ 
    all_goals sorry
  | emptyB ht => sorry
  | split ht h1 h2 hmid hnt s1 s2 ih1 ih2 => sorry
  | fallback ht h1 h2 hmid htriv => sorry

end Myers
