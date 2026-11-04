import DifffoldTed
import Basic
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! The band tables of `fill_window`. Both `td` and `fd` store the cell `(x, y)` at `x * w + (y + t - x)`
with `w = 2 t + 1`, for `|x - y| <= t`; outside the band the value is `inf = tau + 1`. -/

/-- The band index of the cell `(x, y)`. -/
def bandIdx (w t x y : Nat) : Nat := x * w + (y + t - x)

/-- `|x - y| <= t`. -/
def InBand (t x y : Nat) : Prop := x ≤ y + t ∧ y ≤ x + t

instance (t x y : Nat) : Decidable (InBand t x y) := by unfold InBand; infer_instance

/-- Reading a band table: the stored cell inside the band, `inf` outside. -/
def rd (L : List Std.U32) (w t inf x y : Nat) : Nat :=
  if InBand t x y then (L[bandIdx w t x y]!).val else inf

theorem bandIdx_lt (w t x y : Nat) (hw : w = 2 * t + 1) (h : InBand t x y) :
    bandIdx w t x y < (x + 1) * w := by
  unfold bandIdx InBand at *
  have : (x + 1) * w = x * w + w := by ring
  omega

theorem bandIdx_inj (w t x y x' y' : Nat) (hw : w = 2 * t + 1) (h : InBand t x y) (h' : InBand t x' y')
    (e : bandIdx w t x y = bandIdx w t x' y') : x = x' ∧ y = y' := by
  have h1 := bandIdx_lt w t x y hw h
  have h2 := bandIdx_lt w t x' y' hw h'
  unfold bandIdx InBand at *
  have hxx : x = x' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (x + 1) * w ≤ x' * w := Nat.mul_le_mul_right _ hl
      have : (x + 1) * w = x * w + w := by ring
      omega
    · have : (x' + 1) * w ≤ x * w := Nat.mul_le_mul_right _ hl
      have : (x' + 1) * w = x' * w + w := by ring
      omega
  subst hxx
  omega

@[step] theorem bidx_spec (w t x y : Std.Usize) (hx : x.val ≤ y.val + t.val)
    (hw1 : 1 ≤ w.val) (htot : x.val * w.val + (y.val + t.val - x.val) < 2 ^ 32) :
    ted_core.bidx w t x y ⦃ r => r.val = bandIdx w.val t.val x.val y.val ⦄ := by
  unfold ted_core.bidx bandIdx
  have hxw : x.val ≤ x.val * w.val := Nat.le_mul_of_pos_right _ hw1
  step*


theorem inBand_iff (t x y d : Nat) (hd : d = x - y + (y - x)) : d ≤ t ↔ InBand t x y := by
  unfold InBand; omega

@[step] theorem get_spec (fd : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32) (pp qq : Std.Usize)
    (hw : w.val = 2 * t.val + 1) (hlen : (pp.val + 1) * w.val ≤ fd.val.length)
    (hbig : (pp.val + 1) * w.val < 2 ^ 32) :
    ted_core.get fd w t inf pp qq ⦃ r => r.val = rd fd.val w.val t.val inf.val pp.val qq.val ⦄ := by
  unfold ted_core.get
  step as ⟨d, hd⟩
  split
  · rename_i hdt
    have hb : InBand t.val pp.val qq.val := (inBand_iff _ _ _ _ hd).mp hdt
    have hlt := bandIdx_lt w.val t.val pp.val qq.val hw hb
    have hb' := hb
    unfold InBand at hb'
    step as ⟨i, hi⟩
    have hil : i.val < fd.val.length := by omega
    step as ⟨r, hr⟩
    simp only [rd, hb, ↓reduceIte]
    rw [hr, ← hi, getU_eq _ _ hil]
  · rename_i hdt
    simp only [WP.spec_ok]
    have : ¬ InBand t.val pp.val qq.val := fun h => hdt ((inBand_iff _ _ _ _ hd).mpr h)
    simp [rd, this]


/-- Every stored value is at most `inf`, so every read is. -/
theorem rd_le (L : List Std.U32) (w t inf x y : Nat) (hw : w = 2 * t + 1) 
    (hlen : (x + 1) * w ≤ L.length) (hb : ∀ k < L.length, (L[k]!).val ≤ inf) : rd L w t inf x y ≤ inf := by
  unfold rd
  split
  · rename_i h
    have := bandIdx_lt w t x y hw h
    exact hb _ (by omega)
  · exact le_refl _

/-- The candidate of a cell for "match or relabel": the diagonal neighbour plus the relabel cost when the
cell compares two nodes on the leftmost paths, else the neighbour before the subtrees plus the stored
subtree distance. -/
def cellX (fdL tdL : List Std.U32) (w t inf li lj p q x lx ly ren : Nat) : Nat :=
  if lx = li ∧ ly = lj then rd fdL w t inf (p - 1) (q - 1) + ren
  else rd fdL w t inf (lx - li) (ly - lj) + rd tdL w t inf x (lj + q - 1)

/-- The value of a cell: the minimum of delete, insert and match, capped at `inf`. -/
def cellNew (fdL tdL : List Std.U32) (w t inf li lj p q x lx ly ren : Nat) : Nat :=
  min (min (min (rd fdL w t inf (p - 1) q + 1) (rd fdL w t inf p (q - 1) + 1))
    (cellX fdL tdL w t inf li lj p q x lx ly ren)) inf

/-- The `tdv` lookup of a cell: the stored subtree distance when the pair is inside the band, else `inf`. -/
theorem tdv_if_spec (td : Slice Std.U32) (w t x y : Std.Usize) (inf : Std.U32) (i7 : Std.Usize)
    (hw : w.val = 2 * t.val + 1) (hi7 : i7.val = x.val - y.val + (y.val - x.val))
    (htdlen : (x.val + 1) * w.val ≤ td.val.length) (htdbig : (x.val + 1) * w.val < 2 ^ 32) :
    (if i7 ≤ t then (do let i8 ← ted_core.bidx w t x y; Slice.index_usize td i8) else ok inf) ⦃ r =>
      r.val = rd td.val w.val t.val inf.val x.val y.val ⦄ := by
  split
  · rename_i hdt
    have hb : InBand t.val x.val y.val := (inBand_iff _ _ _ _ hi7).mp (by scalar_tac)
    have hlt := bandIdx_lt w.val t.val x.val y.val hw hb
    have hb' := hb
    unfold InBand at hb'
    step as ⟨i, hi⟩
    have hil : i.val < td.val.length := by omega
    step as ⟨r, hr⟩
    simp only [rd, hb, ↓reduceIte]
    rw [hr, ← hi, getU_eq _ _ hil]
  · rename_i hdt
    simp only [WP.spec_ok]
    have : ¬ InBand t.val x.val y.val := fun h => hdt (by have := (inBand_iff _ _ _ _ hi7).mpr h; scalar_tac)
    simp [rd, this]

/-- The `td` update of a leaf-pair cell: stored when the pair is inside the band. -/
theorem upd_if_spec (td : Slice Std.U32) (w t x y : Std.Usize) (v4 : Std.U32) (i13 : Std.Usize)
    (hw : w.val = 2 * t.val + 1) (hi13 : i13.val = x.val - y.val + (y.val - x.val))
    (htdlen : (x.val + 1) * w.val ≤ td.val.length) (htdbig : (x.val + 1) * w.val < 2 ^ 32) :
    (if i13 ≤ t then (do let i14 ← ted_core.bidx w t x y; Slice.update td i14 v4) else ok td) ⦃ s =>
      s.val = if InBand t.val x.val y.val then td.val.set (bandIdx w.val t.val x.val y.val) v4 else td.val ⦄ := by
  split
  · rename_i hdt
    have hb : InBand t.val x.val y.val := (inBand_iff _ _ _ _ hi13).mp (by scalar_tac)
    have hlt := bandIdx_lt w.val t.val x.val y.val hw hb
    have hb' := hb
    unfold InBand at hb'
    step as ⟨i, hi⟩
    have hil : i.val < td.val.length := by omega
    step as ⟨r, hr⟩
    simp only [hb, ↓reduceIte]
    rw [hr, Slice.set_val_eq, hi]
  · rename_i hdt
    simp only [WP.spec_ok]
    have : ¬ InBand t.val x.val y.val := fun h => hdt (by have := (inBand_iff _ _ _ _ hi13).mpr h; scalar_tac)
    simp [this]

theorem ren_spec (i8 i9 : Std.U32) :
    (if (i8 != i9) = true then ok 1#u32 else ok 0#u32) ⦃ r => r.val = if i8 = i9 then 0 else 1 ⦄ := by
  split
  · rename_i h
    simp only [bne_iff_ne, ne_eq] at h
    simp [h]
  · rename_i h
    simp only [bne_iff_ne, ne_eq, not_not] at h
    simp [h]

/-- One iteration of the inner loop of `fill_window` computes one cell of the forest-distance table. -/
theorem cell_step
    (v v1 v2 : alloc.vec.Vec Std.U32) (t : Std.Usize) (inf : Std.U32) (w li lj p qhi x lx : Std.Usize)
    (td fd : Slice Std.U32) (q : Std.Usize) (row_min : Std.U32)
    (hw : w.val = 2 * t.val + 1) (hinf : inf.val = t.val + 1)
    (hq : q.val ≤ qhi.val) (hq1 : 1 ≤ q.val) (hp1 : 1 ≤ p.val)
    (hband : InBand t.val p.val q.val) (hlj : 1 ≤ lj.val) (hli : 1 ≤ li.val)
    (hx : x.val = li.val + p.val - 1)
    (hv : x.val - 1 < v.length) (hv1 : lj.val + q.val - 2 < v1.length) (hv2 : lj.val + q.val - 2 < v2.length)
    (hlxli : li.val ≤ lx.val) (hlx : lx.val ≤ x.val)
    (hlq : lj.val + q.val < 2 ^ 32)
    (hlylj : lj.val ≤ (v2.val[lj.val + q.val - 2]!).val)
    (hfdlen : (p.val + 1) * w.val ≤ fd.val.length) (hfdbig : (p.val + 1) * w.val < 2 ^ 32)
    (htdlen : (x.val + 1) * w.val ≤ td.val.length) (htdbig : (x.val + 1) * w.val < 2 ^ 32)
    (hfdb : ∀ k < fd.val.length, (fd.val[k]!).val ≤ inf.val)
    (htdb : ∀ k < td.val.length, (td.val[k]!).val ≤ inf.val)
    (hinfbig : 2 * inf.val + 1 < 2 ^ 32) :
    ted_core.fill_window_loop2_loop0.body v v1 v2 t inf w li lj p qhi x lx td fd q row_min ⦃ r =>
      match r with
      | done _ => False
      | cont s => ∃ vv : Std.U32,
          vv.val = cellNew fd.val td.val w.val t.val inf.val li.val lj.val p.val q.val x.val lx.val
            (v2.val[lj.val + q.val - 2]!).val
            (if v.val[x.val - 1]! = v1.val[lj.val + q.val - 2]! then 0 else 1) ∧
          s.2.1.val = fd.val.set (bandIdx w.val t.val p.val q.val) vv ∧
          s.1.val = (if lx.val = li.val ∧ (v2.val[lj.val + q.val - 2]!).val = lj.val ∧
              InBand t.val x.val (lj.val + q.val - 1)
            then td.val.set (bandIdx w.val t.val x.val (lj.val + q.val - 1)) vv else td.val) ∧
          s.2.2.1.val = q.val + 1 ∧ s.2.2.2.val = min row_min.val vv.val ⦄ := by
  unfold ted_core.fill_window_loop2_loop0.body
  split
  · rename_i hqq
    have hLfd : ∀ x' y', x' ≤ p.val → rd fd.val w.val t.val inf.val x' y' ≤ inf.val := by
      intro x' y' hx'
      apply rd_le _ _ _ _ _ _ hw _ hfdb
      have : (x' + 1) * w.val ≤ (p.val + 1) * w.val := Nat.mul_le_mul_right _ (by omega)
      omega
    have hLtd : ∀ y', rd td.val w.val t.val inf.val x.val y' ≤ inf.val := by
      intro y'
      exact rd_le _ _ _ _ _ _ hw htdlen htdb
    have hbpq : p.val * w.val + (q.val + t.val - p.val) < 2 ^ 32 := by
      have := bandIdx_lt w.val t.val p.val q.val hw hband
      unfold bandIdx at this; omega
    have hbpq2 : p.val * w.val + (q.val + t.val - p.val) < fd.val.length := by
      have := bandIdx_lt w.val t.val p.val q.val hw hband
      unfold bandIdx at this; omega
    have hrow : ∀ r, r ≤ p.val → (r + 1) * w.val ≤ fd.val.length ∧ (r + 1) * w.val < 2 ^ 32 := by
      intro r hr
      have : (r + 1) * w.val ≤ (p.val + 1) * w.val := Nat.mul_le_mul_right _ (by omega)
      omega
    step as ⟨i, hi⟩
    step as ⟨y, hy⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨ly, hly⟩
    step as ⟨i3, hi3⟩
    step with get_spec fd w t inf i3 q hw (hrow i3.val (by omega)).1 (hrow i3.val (by omega)).2 as ⟨i4, hi4⟩
    step as ⟨del, hdel⟩
    step as ⟨i5, hi5⟩
    step with get_spec fd w t inf p i5 hw (hrow p.val (by omega)).1 (hrow p.val (by omega)).2 as ⟨i6, hi6⟩
    step as ⟨ins, hins⟩
    split
    · rename_i hlxeq
      split
      · rename_i hlyeq
        sorry
      · rename_i hlyne

        step as ⟨i7, hi7⟩
        step with tdv_if_spec td w t x y inf i7 hw hi7 htdlen htdbig as ⟨tdv, htdv⟩
        trace_state
        step as ⟨i8, hi8⟩
        step as ⟨i9, hi9⟩
        step with get_spec fd w t inf i8 i9 hw (hrow i8.val (by omega)).1 (hrow i8.val (by omega)).2 as ⟨i10, hi10⟩
        step as ⟨sub, hsub⟩
        step as ⟨i11, hi11⟩
        step as ⟨i12, hi12⟩
        step as ⟨v4, hv4⟩
        step as ⟨i7', hi7'⟩
        step as ⟨s, hs⟩
        step as ⟨s', hs'⟩
        step as ⟨row_min1, hrm⟩
        step as ⟨q1, hq1'⟩
        refine ⟨v4, ?_, ?_, ?_, ?_, ?_⟩
        all_goals sorry
    · rename_i hlxne

      step as ⟨i7, hi7⟩
      step with tdv_if_spec td w t x y inf i7 hw hi7 htdlen htdbig as ⟨tdv, htdv⟩
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9⟩
      step with get_spec fd w t inf i8 i9 hw (hrow i8.val (by omega)).1 (hrow i8.val (by omega)).2 as ⟨i10, hi10⟩
      step as ⟨sub, hsub⟩
      step as ⟨i11, hi11⟩
      step as ⟨i12, hi12⟩
      step as ⟨v4, hv4⟩
      step as ⟨i7', hi7'⟩
      step as ⟨s, hs⟩
      step as ⟨s', hs'⟩
      step as ⟨row_min1, hrm⟩
      step as ⟨q1, hq1'⟩
      refine ⟨v4, ?_, ?_, ?_, ?_, ?_⟩
      all_goals sorry
  · rename_i hn
    exfalso
    scalar_tac

end difffold_lines_extract
