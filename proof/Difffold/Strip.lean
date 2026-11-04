import Difffold.Basic
/-!
# strip_safe: pairing equal first/last children at cost 0 loses no optimality

Side conditions on the pair cost `d` (all PROVED from the Selkow cost model, `dok_of_dist`):
* `d x x = 0`
* the size bound `|size x - size y| <= d x y`.
No triangle inequality is needed in this model: the exchange argument only uses that deleting
`x` (cost `size x`) is never worse than pairing it (cost `d x y`) and then deleting `y`
(cost `size y`), which is the size bound.
-/
namespace Difffold

mutual
theorem tedit_refl : ∀ t : Tree, TEdit t t 0
  | .node l ks => by
      have := TEdit.mk (l := l) (l' := l) (align_refl ks)
      simpa using this
theorem align_refl : ∀ ts : List Tree, AlignR TEdit ts ts 0
  | [] => .nil
  | t :: ts => by
      have := AlignR.pair (tedit_refl t) (align_refl ts)
      simpa using this
end

structure DOK (d : Tree → Tree → Nat) : Prop where
  refl : ∀ x, d x x = 0
  bound : ∀ x y, SizeBound x y (d x y)

/-- Both side conditions hold for the Selkow distance. -/
theorem dok_of_dist {d : Tree → Tree → Nat} (hd : ∀ x y, IsDist x y (d x y)) : DOK d where
  refl x := by
    have := (hd x x).2 0 (tedit_refl x)
    omega
  bound x y := tedit_bound (hd x y).1

def IsOpt (d : Tree → Tree → Nat) (xs ys : List Tree) (k : Nat) : Prop :=
  Align d xs ys k ∧ ∀ c, Align d xs ys c → k ≤ c

theorem isOpt_unique {d xs ys k k'} (h : IsOpt d xs ys k) (h' : IsOpt d xs ys k') : k = k' := by
  have := h.2 _ h'.1; have := h'.2 _ h.1; omega

section
variable {d : Tree → Tree → Nat}

theorem align_cast {xs ys c c'} (h : Align d xs ys c) (e : c = c') : Align d xs ys c' := e ▸ h

/-- Dropping an unmatched head of `ys` costs at most its size. -/
theorem ins_shift (hd : DOK d) : ∀ {xs zs c}, Align d xs zs c → ∀ y ys, zs = y :: ys →
    ∃ c', Align d xs ys c' ∧ c' ≤ y.size + c := by
  intro xs zs c h
  induction h with
  | nil => intro y ys e; cases e
  | @del x xs ys c h ih =>
    intro y ys' e
    obtain ⟨c', h1, h2⟩ := ih y ys' e
    exact ⟨x.size + c', AlignR.del h1, by omega⟩
  | @ins y0 xs ys c h ih =>
    intro y ys' e
    cases e
    exact ⟨c, h, by omega⟩
  | @pair x y0 xs ys c c' hp h ih =>
    intro y ys' e
    cases e
    have hp' : c' = d x y0 := hp
    have := (hd.bound x y0).1
    exact ⟨x.size + c, AlignR.del h, by omega⟩

/-- Dropping an unmatched head of `xs` costs at most its size. -/
theorem del_shift (hd : DOK d) : ∀ {zs ys c}, Align d zs ys c → ∀ x xs, zs = x :: xs →
    ∃ c', Align d xs ys c' ∧ c' ≤ x.size + c := by
  intro zs ys c h
  induction h with
  | nil => intro y ys e; cases e
  | @del x0 xs ys c h ih =>
    intro x xs' e
    cases e
    exact ⟨c, h, by omega⟩
  | @ins y xs ys c h ih =>
    intro x xs' e
    obtain ⟨c', h1, h2⟩ := ih x xs' e
    exact ⟨y.size + c', AlignR.ins h1, by omega⟩
  | @pair x0 y xs ys c c' hp h ih =>
    intro x xs' e
    cases e
    have hp' : c' = d x0 y := hp
    have := (hd.bound x0 y).2
    exact ⟨y.size + c, AlignR.ins h, by omega⟩

/-- `strip_safe`, first child. -/
theorem strip_first (hd : DOK d) {xs ys k} (h : IsOpt d xs ys k) (x : Tree) :
    IsOpt d (x :: xs) (x :: ys) k := by
  refine ⟨?_, ?_⟩
  · have := AlignR.pair (P := fun x y c => c = d x y) (x := x) (y := x) (c' := 0) (by simp [hd.refl]) h.1
    simpa using this
  · intro c hc
    cases hc with
    | del h1 =>
      obtain ⟨c', a1, a2⟩ := ins_shift hd h1 x ys rfl
      have := h.2 _ a1; omega
    | ins h1 =>
      obtain ⟨c', a1, a2⟩ := del_shift hd h1 x xs rfl
      have := h.2 _ a1; omega
    | pair hp h1 =>
      have := h.2 _ h1; omega

theorem align_append {xs ys c xs' ys' c'} (h : Align d xs ys c) (h' : Align d xs' ys' c') :
    Align d (xs ++ xs') (ys ++ ys') (c + c') := by
  induction h with
  | nil => simpa using h'
  | @del x xs ys c h ih => exact align_cast (AlignR.del ih) (by omega)
  | @ins y xs ys c h ih => exact align_cast (AlignR.ins ih) (by omega)
  | @pair x y xs ys c c'' hp h ih => exact align_cast (AlignR.pair hp ih) (by omega)

theorem align_reverse {xs ys c} (h : Align d xs ys c) : Align d xs.reverse ys.reverse c := by
  induction h with
  | nil => exact AlignR.nil
  | @del x xs ys c h ih =>
    have := align_append ih (AlignR.del (P := fun x y c => c = d x y) (x := x) (xs := []) (ys := []) AlignR.nil)
    exact align_cast (by simpa using this) (by omega)
  | @ins y xs ys c h ih =>
    have := align_append ih (AlignR.ins (P := fun x y c => c = d x y) (y := y) (xs := []) (ys := []) AlignR.nil)
    exact align_cast (by simpa using this) (by omega)
  | @pair x y xs ys c c' hp h ih =>
    have := align_append ih (AlignR.pair (P := fun x y c => c = d x y) (x := x) (y := y) (xs := []) (ys := []) hp AlignR.nil)
    exact align_cast (by simpa using this) (by omega)

theorem isOpt_reverse {xs ys k} (h : IsOpt d xs ys k) : IsOpt d xs.reverse ys.reverse k := by
  refine ⟨align_reverse h.1, fun c hc => h.2 c ?_⟩
  simpa using align_reverse hc

/-- `strip_safe`, last child. -/
theorem strip_last (hd : DOK d) {xs ys k} (h : IsOpt d xs ys k) (x : Tree) :
    IsOpt d (xs ++ [x]) (ys ++ [x]) k := by
  have := isOpt_reverse (strip_first hd (isOpt_reverse h) x)
  simpa using this

/-- **strip_safe.** Adding a common prefix `p` and common suffix `s` leaves the optimum unchanged. -/
theorem strip_safe (hd : DOK d) {xs ys k} (h : IsOpt d xs ys k) (p s : List Tree) :
    IsOpt d (p ++ xs ++ s) (p ++ ys ++ s) k := by
  have hs : ∀ n, ∀ s : List Tree, s.length = n → IsOpt d (xs ++ s) (ys ++ s) k := by
    intro n
    induction n with
    | zero => intro s hl; have : s = [] := List.eq_nil_of_length_eq_zero hl; subst this; simpa using h
    | succ n ih =>
      intro s hl
      have hne : s ≠ [] := by intro e; subst e; simp at hl
      have := strip_last hd (ih s.dropLast (by simp [hl])) (s.getLast hne)
      simp only [List.append_assoc, List.dropLast_concat_getLast hne] at this
      exact this
  have hp : ∀ p : List Tree, ∀ xs0 ys0 : List Tree, IsOpt d xs0 ys0 k → IsOpt d (p ++ xs0) (p ++ ys0) k := by
    intro p
    induction p with
    | nil => intro xs0 ys0 h; simpa using h
    | cons x p ih => intro xs0 ys0 h; exact strip_first hd (ih xs0 ys0 h) x
  have := hp p _ _ (hs s.length s rfl)
  simpa [List.append_assoc] using this

/-- The optimum of the stripped problem is the optimum of the full problem. -/
theorem strip_safe_iff (hd : DOK d) {xs ys k k'} (h : IsOpt d xs ys k) (p s : List Tree) :
    IsOpt d (p ++ xs ++ s) (p ++ ys ++ s) k' ↔ k' = k :=
  ⟨fun h' => isOpt_unique h' (strip_safe hd h p s), fun e => e ▸ strip_safe hd h p s⟩

end
end Difffold
