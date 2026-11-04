/-! A Lean model of the Zhang-Shasha forest edit distance (unit insert, delete and relabel costs), plain Lean.

This is the textbook right-to-left forest recursion that `tests/ted.rs` (`fd`) checks the Rust code against:
for non-empty forests `F = F' ++ [v]` and `G = G' ++ [w]`,

  fdist F G = min (fdist (F' ++ kids v) G + 1)              -- delete the root of the last tree of F
                  (fdist F (G' ++ kids w) + 1)              -- insert the root of the last tree of G
                  (fdist F' G' + fdist (kids v) (kids w) + [label v != label w])   -- match the two roots

Forests are stored right to left (the last tree comes first) and `Tree.node a ks` stores its children `ks`
right to left too, so that "the last tree and its children" are list heads and the recursion is structural.
Nothing in `Ted/*.lean` proves that the Rust table computes this function: `Ted/Cell.lean` proves only the
one-cell step; the link from the window tables to `fdist` is **not proved**. -/
namespace Ted

inductive Tree where
  | node : Nat → List Tree → Tree

mutual
def Tree.size : Tree → Nat
  | .node _ ks => 1 + sizeF ks
def sizeF : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + sizeF ts
end

def Tree.label : Tree → Nat
  | .node a _ => a

def Tree.kids : Tree → List Tree
  | .node _ ks => ks

theorem sizeF_append (A B : List Tree) : sizeF (A ++ B) = sizeF A + sizeF B := by
  induction A with
  | nil => simp [sizeF]
  | cons t ts ih => simp [sizeF, ih]; omega

/-- The forest edit distance. -/
def fdist : List Tree → List Tree → Nat
  | [], G => sizeF G
  | v :: F, [] => sizeF (v :: F)
  | .node a ks :: F, .node b ls :: G =>
    min (min (fdist (ks ++ F) (.node b ls :: G) + 1) (fdist (.node a ks :: F) (ls ++ G) + 1))
      (fdist F G + fdist ks ls + if a = b then 0 else 1)
termination_by F G => sizeF F + sizeF G
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeF, Tree.size, sizeF_append]
  all_goals omega

theorem fdist_nil_left (G : List Tree) : fdist [] G = sizeF G := by
  rw [fdist]

theorem fdist_nil_right (F : List Tree) : fdist F [] = sizeF F := by
  cases F with
  | nil => simp [fdist, sizeF]
  | cons v F => rw [fdist]

/-- The textbook recursion, restated as an equation. -/
theorem fdist_node (a b : Nat) (ks ls F G : List Tree) :
    fdist (.node a ks :: F) (.node b ls :: G) =
      min (min (fdist (ks ++ F) (.node b ls :: G) + 1) (fdist (.node a ks :: F) (ls ++ G) + 1))
        (fdist F G + fdist ks ls + if a = b then 0 else 1) := by
  rw [fdist]

theorem fdist_leaf_leaf (a b : Nat) :
    fdist [.node a []] [.node b []] = if a = b then 0 else 1 := by
  rw [fdist_node]
  simp [fdist_nil_left, fdist_nil_right, sizeF, Tree.size]
  split <;> omega

end Ted
