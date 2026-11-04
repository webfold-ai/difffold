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

theorem opt_empty_left (b : List Nat) : Optimal [] b [] (List.replicate b.length true) := by
  refine ⟨⟨rfl, by simp, ?_⟩, by simp [kept, lcs_nil_left]⟩
  rw [kept_rep_true]; simp [kept]

theorem opt_empty_right (a : List Nat) : Optimal a [] (List.replicate a.length true) [] := by
  refine ⟨⟨by simp, rfl, ?_⟩, by simp [lcs_nil_right, kept_rep_true]⟩
  rw [kept_rep_true]; simp [kept_nil_right]

/-- Soundness and optimality of `solve`: whenever the oracle meets `MidSpec`, the flags are optimal. -/
theorem solve_optimal {mid : List Nat → List Nat → Nat × Nat} (hm : MidSpec mid)
    {a b : List Nat} {da di : List Bool} (h : Solve mid a b da di) : Optimal a b da di := by
  induction h with
  | emptyA ht =>
    obtain ⟨ha, hb, -, -⟩ := ht
    subst ha; subst hb
    exact opt_trim (opt_empty_left _)
  | emptyB ht =>
    obtain ⟨ha, hb, -, -⟩ := ht
    subst ha; subst hb
    exact opt_trim (opt_empty_right _)
  | split ht h1 h2 hmid hnt s1 s2 ih1 ih2 =>
    obtain ⟨ha, hb, hh, hl⟩ := ht
    subst ha; subst hb
    have := hm _ _ h1 h2 hh hl
    rw [hmid] at this
    exact opt_trim (optimal_append this.2.2.1 ih1 ih2)
  | fallback ht h1 h2 hmid htriv =>
    obtain ⟨ha, hb, hh, hl⟩ := ht
    subst ha; subst hb
    have := hm _ _ h1 h2 hh hl
    rw [hmid] at this
    exact absurd htriv (by
      intro ht'; rcases ht' with ht' | ht'
      · exact this.2.2.2.1 ht'
      · exact this.2.2.2.2 ht')

/-! ### The model never gets stuck -/

theorem pre_exists : ∀ (a b : List Nat), ∃ p a' b', a = p ++ a' ∧ b = p ++ b' ∧ HeadsDiff a' b' := by
  intro a
  induction a with
  | nil => intro b; exact ⟨[], [], b, rfl, rfl, fun x u y v h => by simp at h⟩
  | cons x a ih =>
    intro b
    cases b with
    | nil => exact ⟨[], x :: a, [], rfl, rfl, fun x u y v _ h => by simp at h⟩
    | cons y b =>
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨p, a', b', h1, h2, h3⟩ := ih b
        exact ⟨x :: p, a', b', by simp [h1], by simp [h2], h3⟩
      · exact ⟨[], x :: a, y :: b, rfl, rfl, fun x' u y' v h1 h2 => by
          simp at h1 h2; rw [← h1.1, ← h2.1]; exact hxy⟩

theorem trim_exists (a b : List Nat) : ∃ p a1 b1 s, Trim a b p a1 b1 s := by
  obtain ⟨p, a', b', h1, h2, h3⟩ := pre_exists a b
  obtain ⟨q, c, e, g1, g2, g3⟩ := pre_exists a'.reverse b'.reverse
  have ea : a' = c.reverse ++ q.reverse := by
    have := congrArg List.reverse g1; simpa using this
  have eb : b' = e.reverse ++ q.reverse := by
    have := congrArg List.reverse g2; simpa using this
  refine ⟨p, c.reverse, e.reverse, q.reverse, ?_, ?_, ?_, ?_⟩
  · rw [h1, ea]; simp
  · rw [h2, eb]; simp
  · intro x u y v hx hy
    apply h3 x (u ++ q.reverse) y (v ++ q.reverse)
    · rw [ea, hx]; simp
    · rw [eb, hy]; simp
  · simpa [LastsDiff] using g3

theorem solve_total {mid : List Nat → List Nat → Nat × Nat} (hm : MidSpec mid) :
    ∀ (n : Nat) (a b : List Nat), a.length + b.length ≤ n → ∃ da di, Solve mid a b da di := by
  intro n
  induction n with
  | zero =>
    intro a b hn
    obtain ⟨p, a1, b1, s, ht⟩ := trim_exists a b
    have ha : a1 = [] := List.length_eq_zero_iff.mp (by
      have := congrArg List.length ht.1; simp at this; omega)
    subst ha
    exact ⟨_, _, Solve.emptyA ht⟩
  | succ n ih =>
    intro a b hn
    obtain ⟨p, a1, b1, s, ht⟩ := trim_exists a b
    by_cases h1 : a1 = []
    · subst h1; exact ⟨_, _, Solve.emptyA ht⟩
    by_cases h2 : b1 = []
    · subst h2; exact ⟨_, _, Solve.emptyB ht⟩
    have hs := hm a1 b1 h1 h2 ht.2.2.1 ht.2.2.2
    obtain ⟨hx, hy, -, hn0, hnn⟩ := hs
    have la := congrArg List.length ht.1
    have lb := congrArg List.length ht.2.1
    simp at la lb
    obtain ⟨x, y, hhh⟩ : ∃ x y, mid a1 b1 = (x, y) := ⟨_, _, rfl⟩
    rw [hhh] at hx hy hn0 hnn
    simp only at hx hy hn0 hnn
    have hnt : ¬((x = 0 ∧ y = 0) ∨ (x = a1.length ∧ y = b1.length)) := by
      intro h; rcases h with h | h
      · exact hn0 h
      · exact hnn h
    have lt1 : (a1.take x).length + (b1.take y).length ≤ n := by
      simp; omega
    have lt2 : (a1.drop x).length + (b1.drop y).length ≤ n := by
      simp; omega
    obtain ⟨d1, e1, s1⟩ := ih _ _ lt1
    obtain ⟨d2, e2, s2⟩ := ih _ _ lt2
    exact ⟨_, _, Solve.split ht h1 h2 hhh hnt s1 s2⟩

end Myers
