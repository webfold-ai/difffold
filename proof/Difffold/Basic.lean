/-!
# difffold: trees, sizes, alignments, Selkow distance (model)

OBJECTIVE. Top-down (Selkow) ordered-tree edit distance, unit cost per node. A deleted node removes
its WHOLE subtree (cost = subtree size), an inserted node adds a whole subtree, and a pair of
children needs matched parents (roots always pair; label change costs 1). This is NOT classical
Zhang-Shasha, where deleting a node promotes its children. The model below is exactly that.

Everything here is about the Lean MODEL, not the Rust code.
-/
namespace Difffold

inductive Tree where
  | node (label : Nat) (kids : List Tree)

mutual
def Tree.size : Tree → Nat
  | .node _ ks => 1 + Tree.sizeF ks
def Tree.sizeF : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + Tree.sizeF ts
end

/-- Alignment of two child lists: delete a child (cost = its size), insert a child (cost = its
size), or pair two children at cost `c'` allowed by the relation `P`. -/
inductive AlignR (P : Tree → Tree → Nat → Prop) : List Tree → List Tree → Nat → Prop
  | nil : AlignR P [] [] 0
  | del {x xs ys c} : AlignR P xs ys c → AlignR P (x :: xs) ys (x.size + c)
  | ins {y xs ys c} : AlignR P xs ys c → AlignR P xs (y :: ys) (y.size + c)
  | pair {x y xs ys c c'} : P x y c' → AlignR P xs ys c → AlignR P (x :: xs) (y :: ys) (c' + c)

/-- Alignment with a pair-cost function `d`. -/
abbrev Align (d : Tree → Tree → Nat) := AlignR (fun x y c => c = d x y)

/-- `TEdit x y c`: a top-down edit of cost `c` turns `x` into `y`: roots pair (label change costs
1), children are aligned with sub-edits as pair costs. -/
inductive TEdit : Tree → Tree → Nat → Prop
  | mk {l l' ks ks' c} : AlignR TEdit ks ks' c →
      TEdit (.node l ks) (.node l' ks') ((if l = l' then 0 else 1) + c)

/-- `IsDist x y k`: `k` is the Selkow distance (an achievable cost that is least). -/
def IsDist (x y : Tree) (k : Nat) : Prop := TEdit x y k ∧ ∀ c, TEdit x y c → k ≤ c

/-- The size bound `|size x - size y| <= c`, stated without subtraction. -/
def SizeBound (x y : Tree) (c : Nat) : Prop := x.size ≤ y.size + c ∧ y.size ≤ x.size + c

theorem alignR_bound {P : Tree → Tree → Nat → Prop}
    (hP : ∀ x y c, P x y c → SizeBound x y c) :
    ∀ {xs ys c}, AlignR P xs ys c → Tree.sizeF xs ≤ Tree.sizeF ys + c ∧ Tree.sizeF ys ≤ Tree.sizeF xs + c
  | _, _, _, .nil => by simp [Tree.sizeF]
  | _, _, _, .del h => by have := alignR_bound hP h; simp [Tree.sizeF]; omega
  | _, _, _, .ins h => by have := alignR_bound hP h; simp [Tree.sizeF]; omega
  | _, _, _, .pair hp h => by
      have := alignR_bound hP h; have := hP _ _ _ hp; simp [Tree.sizeF, SizeBound] at *; omega

/-- `h_admissible` (forests): the size difference is a lower bound on the cost of ANY alignment,
provided every allowed pair cost respects the size bound. -/
theorem h_admissible {d : Tree → Tree → Nat}
    (hd : ∀ x y, SizeBound x y (d x y)) {xs ys c} (h : Align d xs ys c) :
    Tree.sizeF xs ≤ Tree.sizeF ys + c ∧ Tree.sizeF ys ≤ Tree.sizeF xs + c :=
  alignR_bound (fun x y c hc => by have e : c = d x y := hc; subst e; exact hd x y) h

mutual
/-- `dist_size_bound`: `dist >= |size x - size y|` for every top-down edit (the size lower bound C7). -/
theorem tedit_bound : ∀ {x y c}, TEdit x y c → SizeBound x y c
  | _, _, _, .mk (l := l) (l' := l') h => by
      have := align_bound h
      simp [Tree.size, SizeBound]; split <;> omega
theorem align_bound : ∀ {xs ys c}, AlignR TEdit xs ys c →
    Tree.sizeF xs ≤ Tree.sizeF ys + c ∧ Tree.sizeF ys ≤ Tree.sizeF xs + c
  | _, _, _, .nil => by simp [Tree.sizeF]
  | _, _, _, .del h => by have := align_bound h; simp [Tree.sizeF]; omega
  | _, _, _, .ins h => by have := align_bound h; simp [Tree.sizeF]; omega
  | _, _, _, .pair hp h => by
      have := align_bound h; have := tedit_bound hp; simp [Tree.sizeF, SizeBound] at *; omega
end

end Difffold
