import Mid
/-! The first hit of a round, as `findSome?` over the ascending list of diagonals. -/
open scoped List
namespace Myers

theorem kl_sorted (d : Nat) : (kl d).Pairwise (· < ·) := by
  unfold kl
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.pairwise_lt_range (n := d + 1))
  intro a b h; omega

theorem findSome_first {L : List Int} (hs : L.Pairwise (· < ·)) {f : Int → Option (Int × Int)} {k : Int}
    {v : Int × Int} (hk : k ∈ L) (hfk : f k = some v) (hbefore : ∀ k', k' ∈ L → k' < k → f k' = none) :
    L.findSome? f = some v := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hk
  rw [List.findSome?_eq_some_iff]
  refine ⟨l1, k, l2, rfl, hfk, ?_⟩
  intro x hx
  apply hbefore x (by simp [hx])
  have := List.pairwise_append.mp hs
  exact this.2.2 x hx k (by simp)

theorem fwdFind_none_of (A B : List Nat) (d : Nat) (h : ∀ k, Dom d k → ¬ fhit A B d k) :
    fwdFind A B d = none := by
  unfold fwdFind
  rw [List.findSome?_eq_none_iff]
  intro k hk
  rw [if_neg (h k (mem_kl.mp hk))]

theorem bwdFind_none_of (A B : List Nat) (d : Nat) (h : ∀ k, Dom d k → ¬ bhit A B d k) :
    bwdFind A B d = none := by
  unfold bwdFind
  rw [List.findSome?_eq_none_iff]
  intro k hk
  rw [if_neg (h k (mem_kl.mp hk))]

theorem fwdFind_first (A B : List Nat) (d : Nat) (k : Int) (hk : Dom d k) (hh : fhit A B d k)
    (hb : ∀ k', Dom d k' → k' < k → ¬ fhit A B d k') : fwdFind A B d = some (fpt A B d k) := by
  unfold fwdFind
  apply findSome_first (kl_sorted d) (mem_kl.mpr hk)
  · simp [hh]
  · intro k' hk' hlt
    rw [if_neg (hb k' (mem_kl.mp hk') hlt)]

theorem bwdFind_first (A B : List Nat) (d : Nat) (k : Int) (hk : Dom d k) (hh : bhit A B d k)
    (hb : ∀ k', Dom d k' → k' < k → ¬ bhit A B d k') : bwdFind A B d = some (bpt A B d k) := by
  unfold bwdFind
  apply findSome_first (kl_sorted d) (mem_kl.mpr hk)
  · simp [hh]
  · intro k' hk' hlt
    rw [if_neg (hb k' (mem_kl.mp hk') hlt)]

end Myers
