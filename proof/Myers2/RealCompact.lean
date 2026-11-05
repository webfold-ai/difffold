import RealSolve
import Compact
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- Model of `mark_ids`. -/
def markOf (xs : List Nat) (flags : List Bool) : List Bool := xs.foldl (fun f x => f.set x true) flags

theorem markOf_append (xs ys : List Nat) (f : List Bool) : markOf (xs ++ ys) f = markOf ys (markOf xs f) := by
  simp [markOf, List.foldl_append]

theorem markOf_length (xs : List Nat) (f : List Bool) : (markOf xs f).length = f.length := by
  induction xs generalizing f with
  | nil => simp [markOf]
  | cons x xs ih => simp only [markOf, List.foldl_cons] at ih ⊢; rw [ih]; simp

theorem markOf_get (xs : List Nat) : ∀ (f : List Bool), (∀ y ∈ xs, y < f.length) → ∀ x, x < f.length →
    (markOf xs f)[x]? = if x ∈ xs then some true else f[x]? := by
  induction xs with
  | nil => intro f _ x _; simp [markOf]
  | cons y ys ih =>
    intro f hb x hx
    have hy : y < f.length := hb y (by simp)
    have h1 : markOf (y :: ys) f = markOf ys (f.set y true) := rfl
    rw [h1, ih (f.set y true) (by intro z hz; simpa using hb z (by simp [hz])) x (by simpa using hx)]
    by_cases hxy : x = y
    · subst hxy; simp [List.getElem?_set_self hy]
    · simp [hxy, List.getElem?_set_ne, Ne.symm hxy]

theorem mark_ids_spec : ∀ (N : Nat) (xs : Slice U32) (flags : Slice Bool), xs.val.length = N →
    (∀ x ∈ vals xs.val, x < flags.val.length) →
    lines.mark_ids xs flags ⦃ r => r.val = markOf (vals xs.val) flags.val ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro xs flags hN hb
  rw [lines.mark_ids.eq_1]
  have hl : (Slice.len xs).val = xs.val.length := by simp [Slice.len]
  split
  · rename_i h0
    have : xs.val.length = 0 := by omega
    have e : xs.val = [] := List.length_eq_zero_iff.mp this
    simp [Aeneas.Std.WP.spec_ok, e, vals, markOf]
  · rename_i h1
    have hl1 : xs.val.length = 1 := by simpa [Slice.len] using h1
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = i.val := by rw [hi1]; scalar_tac
    obtain ⟨u, hu⟩ : ∃ u, xs.val = [u] := by
      cases hx : xs.val with
      | nil => rw [hx] at hl1; simp at hl1
      | cons u t => cases t with
        | nil => exact ⟨u, rfl⟩
        | cons _ _ => rw [hx] at hl1; simp at hl1
    have hiu : i = u := by rw [hi]; simp [hu]
    have hbd : i1.val < flags.length := by
      have := hb u.val (by simp [vals, hu]); rw [hi1v, hiu]; simpa [Slice.length] using this
    step as ⟨r, hr⟩
    rw [hr, Slice.set_val_eq]; try simp [markOf, vals, hu, hi1v, hiu]
  · rename_i hn0 hn1
    have hl2 : 2 ≤ xs.val.length := by
      have : ¬ xs.val.length = 0 := by simpa [Slice.len] using hn0
      have : ¬ xs.val.length = 1 := by simpa [Slice.len] using hn1
      omega
    step as ⟨i, hi⟩
    have hiv : i.val = xs.val.length / 2 := by rw [hi]; simp [Slice.len]
    step as ⟨s, hsv, hsl⟩
    have hsv' : s.val = xs.val.take i.val := by rw [hsv]; simp [List.slice]
    have hb1 : ∀ x ∈ vals s.val, x < flags.val.length := by
      intro x hx; apply hb; rw [hsv', vals_take] at hx; exact List.mem_of_mem_take hx
    step with (ih s.val.length (by rw [hsv']; simp; omega) s flags rfl hb1) as ⟨f1, hf1⟩
    step as ⟨s1, hs1v, hs1l⟩
    have hs1' : s1.val = xs.val.drop i.val := by rw [hs1v]
    have hf1l : f1.val.length = flags.val.length := by rw [hf1, markOf_length]
    have hb2 : ∀ x ∈ vals s1.val, x < f1.val.length := by
      intro x hx; rw [hf1l]; apply hb; rw [hs1', vals_drop] at hx; exact List.mem_of_mem_drop hx
    refine Aeneas.Std.WP.spec_mono (ih s1.val.length (by rw [hs1']; simp; omega) s1 f1 rfl hb2) ?_
    intro r hr
    have e : vals (xs.val.take i.val) ++ vals (xs.val.drop i.val) = vals xs.val := by
      unfold vals; rw [← List.map_append, List.take_append_drop]
    rw [hr, hf1, ← markOf_append, hsv', hs1', e]


def uvals (l : List Usize) : List Nat := l.map (fun u => u.val)

theorem scatter_flags_spec : ∀ (N : Nat) (r : Slice Bool) (pos : Slice Usize) (out : Slice Bool),
    r.val.length = N → pos.val.length = N → (∀ p ∈ uvals pos.val, p < out.val.length) →
    lines.scatter_flags r pos out ⦃ o => o.val = Myers.scatterOf r.val (uvals pos.val) out.val ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro r pos out hr hp hb
  rw [lines.scatter_flags.eq_1]
  split
  · rename_i h0
    have : r.val.length = 0 := by simpa [Slice.len] using h0
    have e : r.val = [] := List.length_eq_zero_iff.mp this
    simp [Aeneas.Std.WP.spec_ok, e, Myers.scatterOf]
  · rename_i h1
    have hl1 : r.val.length = 1 := by simpa [Slice.len] using h1
    obtain ⟨b, hbv⟩ : ∃ b, r.val = [b] := by
      cases hx : r.val with
      | nil => rw [hx] at hl1; simp at hl1
      | cons u t => cases t with
        | nil => exact ⟨u, rfl⟩
        | cons _ _ => rw [hx] at hl1; simp at hl1
    obtain ⟨q, hqv⟩ : ∃ q, pos.val = [q] := by
      cases hx : pos.val with
      | nil => rw [hx] at hp; simp at hp; omega
      | cons u t => cases t with
        | nil => exact ⟨u, rfl⟩
        | cons _ _ => rw [hx] at hp; simp at hp; omega
    step as ⟨b', hb'⟩
    step as ⟨i, hi⟩
    have hqb : q.val < out.val.length := hb q.val (by simp [uvals, hqv])
    step as ⟨o, ho⟩
    rw [ho, Slice.set_val_eq]
    simp [hbv, hqv, hb', hi, Myers.scatterOf, uvals]
  · rename_i hn0 hn1
    have hl2 : 2 ≤ r.val.length := by
      have : ¬ r.val.length = 0 := by simpa [Slice.len] using hn0
      have : ¬ r.val.length = 1 := by simpa [Slice.len] using hn1
      omega
    step as ⟨i, hi⟩
    have hiv : i.val = r.val.length / 2 := by rw [hi]; simp [Slice.len]
    step as ⟨s, hsv, hsl⟩
    step as ⟨s1, hs1v, hs1l⟩
    have hsv' : s.val = r.val.take i.val := by rw [hsv]; simp [List.slice]
    have hs1v' : s1.val = pos.val.take i.val := by rw [hs1v]; simp [List.slice]
    have hlen1 : s.val.length = i.val := by rw [hsv']; simp; omega
    have hlen2 : s1.val.length = i.val := by rw [hs1v']; simp; omega
    have hbs : ∀ p ∈ uvals s1.val, p < out.val.length := by
      intro p hpp; apply hb; rw [hs1v'] at hpp
      simp only [uvals, List.map_take] at hpp ⊢
      exact List.mem_of_mem_take hpp
    step with (ih s.val.length (by omega) s s1 out rfl (by omega) hbs) as ⟨out1, ho1⟩
    step as ⟨s2, hs2v, hs2l⟩
    step as ⟨s3, hs3v, hs3l⟩
    have hs2' : s2.val = r.val.drop i.val := by rw [hs2v]
    have hs3' : s3.val = pos.val.drop i.val := by rw [hs3v]
    have hout1 : out1.val.length = out.val.length := by
      rw [ho1, Myers.length_scatterOf]
    refine Aeneas.Std.WP.spec_mono (ih s2.val.length (by rw [hs2']; simp; omega) s2 s3 out1 rfl
      (by rw [hs2', hs3']; simp; omega) (by
        intro p hpp; rw [hout1]; apply hb; rw [hs3'] at hpp
        simp only [uvals, List.map_drop] at hpp ⊢
        exact List.mem_of_mem_drop hpp)) ?_
    intro o ho2
    rw [ho2, ho1, hsv', hs1v', hs2', hs3']
    have := Myers.scatterOf_append (r.val.take i.val) (r.val.drop i.val) (uvals (pos.val.take i.val)) (uvals (pos.val.drop i.val)) out.val (by simp [uvals]; omega)
    simp only [uvals, List.map_take, List.map_drop, List.take_append_drop] at this ⊢
    exact this.symm


theorem compact_ids_spec (kp : Nat → Bool) : ∀ (N : Nat) (xs : Slice U32) (base : Usize) (other : Slice Bool)
    (keep : alloc.vec.Vec U32) (pos : alloc.vec.Vec Usize) (edit : Slice Bool),
    xs.val.length = N → (∀ x ∈ vals xs.val, other.val[x]? = some (kp x)) →
    base.val + N ≤ edit.val.length → keep.val.length + N < Usize.max → pos.val.length + N < Usize.max →
    lines.compact_ids xs base other keep pos edit ⦃ r =>
      vals r.1.val = vals keep.val ++ (vals xs.val).filter kp ∧
      uvals r.2.1.val = uvals pos.val ++ Myers.posOf kp (vals xs.val) base.val ∧
      r.2.2.val = Myers.editOf kp (vals xs.val) base.val edit.val ⦄ := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro xs base other keep pos edit hN hk hbase hkeep hpos
  rw [lines.compact_ids.eq_1]
  split
  · rename_i h0
    have : xs.val.length = 0 := by simpa [Slice.len] using h0
    have e : xs.val = [] := List.length_eq_zero_iff.mp this
    simp [Aeneas.Std.WP.spec_ok, e, vals, Myers.posOf, Myers.editOf]
  · rename_i h1
    have hl1 : xs.val.length = 1 := by simpa [Slice.len] using h1
    obtain ⟨u, hu⟩ : ∃ u, xs.val = [u] := by
      cases hx : xs.val with
      | nil => rw [hx] at hl1; simp at hl1
      | cons u t => cases t with
        | nil => exact ⟨u, rfl⟩
        | cons _ _ => rw [hx] at hl1; simp at hl1
    step as ⟨i, hi⟩
    have hiu : i = u := by rw [hi]; simp [hu]
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = u.val := by rw [hi1, hiu]; scalar_tac
    have hoth : other.val[u.val]? = some (kp u.val) := hk u.val (by simp [vals, hu])
    have hlt : u.val < other.val.length := (List.getElem?_eq_some_iff.mp hoth).1
    step as ⟨b, hb⟩
    have hbv : b = kp u.val := by
      have hlt' : i1.val < other.val.length := by rw [hi1v]; exact hlt
      have e1 : other.val[i1.val]? = some (kp u.val) := by rw [hi1v]; exact hoth
      rw [List.getElem?_eq_getElem hlt'] at e1
      rw [hb]; exact Option.some.inj e1
    split
    · rename_i hbt
      have hkt : kp u.val = true := by rw [← hbv]; exact hbt
      step as ⟨keep1, hk1⟩
      step as ⟨pos1, hp1⟩
      try simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨?_, ?_, ?_⟩
      · rw [hk1, hu]; simp [vals, hkt, hiu]
      · rw [hp1]; simp [uvals, hu, Myers.posOf, vals, hkt]
      · simp [hu, vals, Myers.editOf, hkt]
    · rename_i hbf
      have hkf : kp u.val = false := by
        have : b = false := by simpa using hbf
        rw [← hbv]; exact this
      step as ⟨edit1, he1⟩
      try simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨?_, ?_, ?_⟩
      · simp [hu, vals, hkf]
      · simp [uvals, hu, Myers.posOf, vals, hkf]
      · rw [he1, Slice.set_val_eq]
        simp [hu, vals, Myers.editOf, hkf]
  · rename_i hn0 hn1
    have hl2 : 2 ≤ xs.val.length := by
      have : ¬ xs.val.length = 0 := by simpa [Slice.len] using hn0
      have : ¬ xs.val.length = 1 := by simpa [Slice.len] using hn1
      omega
    step as ⟨i, hi⟩
    have hiv : i.val = xs.val.length / 2 := by rw [hi]; simp [Slice.len]
    step as ⟨s, hsv, hsl⟩
    have hsv' : s.val = xs.val.take i.val := by rw [hsv]; simp [List.slice]
    have hlen1 : s.val.length = i.val := by rw [hsv']; simp; omega
    have hk1 : ∀ x ∈ vals s.val, other.val[x]? = some (kp x) := by
      intro x hx; apply hk; rw [hsv', vals_take] at hx; exact List.mem_of_mem_take hx
    have hlf : (List.filter kp (vals s.val)).length ≤ i.val := by
      calc _ ≤ (vals s.val).length := List.length_filter_le _ _
        _ = i.val := by simp [vals, hlen1]
    step with (ih s.val.length (by rw [hlen1]; omega) s base other keep pos edit rfl hk1
      (by omega) (by omega) (by omega)) as ⟨keep1, pos1, edit1, r1, r2, r3⟩
    step as ⟨s1, hs1v, hs1l⟩
    step as ⟨i1, hi1⟩
    have hs1' : s1.val = xs.val.drop i.val := by rw [hs1v]
    have hlen2 : s1.val.length = xs.val.length - i.val := by rw [hs1']; simp
    have hk2 : ∀ x ∈ vals s1.val, other.val[x]? = some (kp x) := by
      intro x hx; apply hk; rw [hs1', vals_drop] at hx; exact List.mem_of_mem_drop hx
    have hel : edit1.val.length = edit.val.length := by
      rw [r3, Myers.length_editOf]
    have uv : ∀ l : List Usize, (uvals l).length = l.length := by intro l; simp [uvals]
    have hk1l : keep1.val.length = keep.val.length + (List.filter kp (vals s.val)).length := by
      have := congrArg List.length r1; rw [vals_len, List.length_append, vals_len] at this; exact this
    have hp1l : pos1.val.length = pos.val.length + (Myers.posOf kp (vals s.val) base.val).length := by
      have := congrArg List.length r2; rw [uv, List.length_append, uv] at this; exact this
    have hplen := Myers.length_posOf kp (vals s.val) base.val
    have hvl : (vals s.val).length = i.val := by simp [vals_len, hlen1]
    have hfl : (List.filter kp (vals s.val)).length ≤ i.val := by
      calc _ ≤ (vals s.val).length := List.length_filter_le _ _
        _ = i.val := hvl
    refine Aeneas.Std.WP.spec_mono (ih s1.val.length (by rw [hlen2]; omega) s1 i1 other keep1 pos1 edit1 rfl hk2
      (by rw [hel]; omega) (by omega) (by omega)) ?_
    rintro ⟨keep2, pos2, edit2⟩ ⟨q1, q2, q3⟩
    dsimp only at q1 q2 q3
    refine ⟨?_, ?_, ?_⟩
    · rw [q1, r1, hsv', hs1']
      have : vals (xs.val.take i.val) = (vals xs.val).take i.val := vals_take _ _
      rw [vals_take, vals_drop, List.append_assoc, ← List.filter_append, List.take_append_drop]
    · rw [q2, r2, hsv', hs1', hi1]
      rw [vals_take, vals_drop, List.append_assoc]
      have hap := Myers.posOf_append kp ((vals xs.val).take i.val) ((vals xs.val).drop i.val) base.val
      have hlt : ((vals xs.val).take i.val).length = i.val := by simp [vals_len]; omega
      rw [List.take_append_drop, hlt] at hap
      rw [hap]
    · rw [q3, r3, hsv', hs1', hi1]
      rw [vals_take, vals_drop]
      have hap := Myers.editOf_append kp ((vals xs.val).take i.val) ((vals xs.val).drop i.val) base.val edit.val
      have hlt : ((vals xs.val).take i.val).length = i.val := by simp [vals_len]; omega
      rw [List.take_append_drop, hlt] at hap
      rw [hap]

end difffold_myers_extract
