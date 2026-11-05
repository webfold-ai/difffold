import Good
import Splice
import TrimSpec
open scoped List
namespace Myers

theorem Solve.lens {A B : List Nat} {da di : List Bool} (h : Solve mid A B da di) :
    da.length = A.length ∧ di.length = B.length := by
  have := (solve_optimal mid_spec h).1
  exact ⟨this.1, this.2.1⟩

theorem splice_nil (l : List Bool) (i : Nat) : splice l i [] = l := by
  unfold splice; simp [List.take_append_drop]

end Myers
