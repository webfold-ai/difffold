import Pre
/-! The distance does not change when both trees are mirrored.

The mirror image of a tree sends node `x` to `pi x = n + 1 - pre x`: the postorder of the mirror is the reverse
of the preorder of the original. A tree edit mapping is exactly a one to one map that preserves the
preorder and the descendant relation, so it is also a mapping of the mirrors. -/
namespace Ted

def Rng (n m : Nat) (M : List (Nat × Nat)) : Prop :=
  ∀ p ∈ M, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m

def ValidQ (la lb : Nat → Nat) (n m : Nat) (M : List (Nat × Nat)) : Prop :=
  M.Nodup ∧ ∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ↔ p.2 = q.2) ∧
    (pre la n p.1 < pre la n q.1 ↔ pre lb m p.2 < pre lb m q.2) ∧ (Anc la p.1 q.1 ↔ Anc lb p.2 q.2)

section
variable {la lb : Nat → Nat} {n m : Nat}

theorem pre_iff_of_lt (hA : WfL la) (hB : WfL lb) {u v u2 v2 : Nat} (hu : 1 ≤ u) (hun : u ≤ n) (hvn : v ≤ n)
    (hu2 : 1 ≤ u2) (hv2n : v2 ≤ m) (hlt : u < v) (hlt2 : u2 < v2)
    (hanc : Anc la u v ↔ Anc lb u2 v2) :
    (pre la n u < pre la n v ↔ pre lb m u2 < pre lb m v2) := by
  by_cases ha : la v ≤ u
  · have h1 := P_anc hA hu hlt hvn ha
    have hb := hanc.mp ⟨hlt, ha⟩
    have h2 := P_anc hB hu2 hlt2 hv2n hb.2
    constructor <;> intro h <;> omega
  · have h1 := P_un hA hu hlt hvn (by omega)
    have h1' := pre_le_Qp hA hu (n := n)
    have hb : ¬ lb v2 ≤ u2 := fun h => ha (hanc.mpr ⟨hlt2, h⟩).2
    have h2 := P_un hB hu2 hlt2 hv2n (by omega)
    have h2' := pre_le_Qp hB hu2 (n := m)
    constructor <;> intro h <;> omega

theorem valid_to_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hv : Valid la lb M) : ValidQ la lb n m M := by
  refine ⟨hv.1, fun p hp q hq => ?_⟩
  obtain ⟨e, o, a⟩ := hv.2 p hp q hq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hq
  refine ⟨e, ?_, a⟩
  rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
  · exact pre_iff_of_lt hA hB hp1 hp2 hq2 hp3 hq4 h (o.mp h) a
  · have h2 := e.mp h
    rw [h, h2]; simp
  · obtain ⟨e', o', a'⟩ := hv.2 q hq p hp
    have := pre_iff_of_lt hA hB hq1 hq2 hp2 hq3 hp4 h (o'.mp h) a'
    have i1 : pre la n p.1 ≠ pre la n q.1 := fun hh => by
      have := pre_inj hA hp1 hp2 hq1 hq2 hh; omega
    have i2 : pre lb m p.2 ≠ pre lb m q.2 := fun hh => by
      have := pre_inj hB hp3 hp4 hq3 hq4 hh
      have := e.mpr this; omega
    omega

theorem order_of_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hq : ValidQ la lb n m M) : ∀ p ∈ M, ∀ q ∈ M, p.1 < q.1 → p.2 < q.2 := by
  intro p hp q hqq hlt
  obtain ⟨e, o, a⟩ := hq.2 p hp q hqq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hqq
  by_cases ha : la q.1 ≤ p.1
  · exact (a.mp ⟨hlt, ha⟩).1
  · have h1 := P_un hA hp1 hlt hq2 (by omega)
    have h1' := pre_le_Qp hA hp1 (n := n)
    have h2 : pre lb m p.2 < pre lb m q.2 := o.mp (by omega)
    rcases Nat.lt_trichotomy p.2 q.2 with h | h | h
    · exact h
    · have := e.mpr h; omega
    · by_cases hb : lb p.2 ≤ q.2
      · have := ((hq.2 q hqq p hp).2.2).mpr ⟨h, hb⟩
        have := this.1; omega
      · have := P_un hB hq3 h hp4 (by omega)
        have := pre_le_Qp hB hq3 (n := m); omega

theorem validQ_to_valid (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hq : ValidQ la lb n m M) : Valid la lb M := by
  refine ⟨hq.1, fun p hp q hqq => ?_⟩
  obtain ⟨e, o, a⟩ := hq.2 p hp q hqq
  refine ⟨e, ⟨order_of_validQ hA hB hr hq p hp q hqq, fun h => ?_⟩, a⟩
  rcases Nat.lt_trichotomy p.1 q.1 with h' | h' | h'
  · exact h'
  · have := e.mpr (by omega); omega
  · have := order_of_validQ hA hB hr hq q hqq p hp h'; omega

theorem valid_iff_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M) :
    Valid la lb M ↔ ValidQ la lb n m M :=
  ⟨valid_to_validQ hA hB hr, validQ_to_valid hA hB hr⟩

end
end Ted
