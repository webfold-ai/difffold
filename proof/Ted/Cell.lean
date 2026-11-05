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
    ted.bidx w t x y ⦃ r => r.val = bandIdx w.val t.val x.val y.val ⦄ := by
  unfold ted.bidx bandIdx
  have hxw : x.val ≤ x.val * w.val := Nat.le_mul_of_pos_right _ hw1
  step*


theorem inBand_iff (t x y d : Nat) (hd : d = x - y + (y - x)) : d ≤ t ↔ InBand t x y := by
  unfold InBand; omega

@[step] theorem get_spec (fd : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32) (pp qq : Std.Usize)
    (hw : w.val = 2 * t.val + 1) (hlen : (pp.val + 1) * w.val ≤ fd.val.length)
    (hbig : (pp.val + 1) * w.val < 2 ^ 32) :
    ted.get_cell fd w t inf pp qq ⦃ r => r.val = rd fd.val w.val t.val inf.val pp.val qq.val ⦄ := by
  unfold ted.get_cell
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
    (if i7 ≤ t then (do let i8 ← ted.bidx w t x y; Slice.index_usize td i8) else ok inf) ⦃ r =>
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
    (if i13 ≤ t then (do let i14 ← ted.bidx w t x y; Slice.update td i14 v4) else ok td) ⦃ s =>
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

/-- The relabel cost of node `x` of `a` to node `y` of `b` (1-based). -/
def rcost (a b : ted.PostTree) (x y : Nat) : Nat :=
  if a.label.val[x - 1]! = b.label.val[y - 1]! then 0
  else if a.kind.val[x - 1]! = b.kind.val[y - 1]! then 1 else 2

theorem relabel_cost_spec (a b : ted.PostTree) (x y : Std.Usize) (hx : 1 ≤ x.val) (hy : 1 ≤ y.val)
    (hxa : x.val - 1 < a.label.length) (hxk : x.val - 1 < a.kind.length)
    (hyb : y.val - 1 < b.label.length) (hyk : y.val - 1 < b.kind.length) :
    ted.relabel_cost a b x y ⦃ r => r.val = rcost a b x.val y.val ⦄ := by
  unfold ted.relabel_cost
  have hxa' : x.val - 1 < a.label.val.length := hxa
  have hxk' : x.val - 1 < a.kind.val.length := hxk
  have hyb' : y.val - 1 < b.label.val.length := hyb
  have hyk' : y.val - 1 < b.kind.val.length := hyk
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have e1 : i1 = a.label.val[x.val - 1]! := by
    exact (hi1.trans (getU_eq' _ _ _ (by have : i.val = x.val - 1 := hi; omega) (by omega)))
  have e3 : i3 = b.label.val[y.val - 1]! := by
    exact (hi3.trans (getU_eq' _ _ _ (by have : i2.val = y.val - 1 := hi2; omega) (by omega)))
  split
  · rename_i h
    simp only [WP.spec_ok]
    simp [rcost, ← e1, ← e3, h]
  · rename_i h
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    have e4 : i4 = a.kind.val[x.val - 1]! := by
      exact (hi4.trans (getU_eq' _ _ _ (by have : i.val = x.val - 1 := hi; omega) (by omega)))
    have e5 : i5 = b.kind.val[y.val - 1]! := by
      exact (hi5.trans (getU_eq' _ _ _ (by have : i2.val = y.val - 1 := hi2; omega) (by omega)))
    split
    · rename_i h2
      simp only [WP.spec_ok]
      simp [rcost, ← e1, ← e3, ← e4, ← e5, h, h2]
    · rename_i h2
      simp only [WP.spec_ok]
      simp [rcost, ← e1, ← e3, ← e4, ← e5, h, h2]

/-- One iteration of the inner loop of `fill_window` computes one cell of the forest-distance table. -/
theorem cell_step
    (a b : ted.PostTree) (t : Std.Usize) (inf : Std.U32) (w li lj p qhi x lx : Std.Usize)
    (td fd : Slice Std.U32) (st : ted.Stats) (q : Std.Usize) (row_min : Std.U32)
    (hw : w.val = 2 * t.val + 1) (hinf : inf.val = t.val + 1)
    (hq : q.val ≤ qhi.val) (hq1 : 1 ≤ q.val) (hp1 : 1 ≤ p.val)
    (hband : InBand t.val p.val q.val) (hlj : 1 ≤ lj.val) (hli : 1 ≤ li.val)
    (hx : x.val = li.val + p.val - 1)
    (hv : x.val - 1 < a.label.length) (hv1 : lj.val + q.val - 2 < b.label.length) (hv2 : lj.val + q.val - 2 < b.lml.length)
    (hlxli : li.val ≤ lx.val) (hlx : lx.val ≤ x.val)
    (hak : x.val - 1 < a.kind.length) (hbk : lj.val + q.val - 2 < b.kind.length)
    (hlq : lj.val + q.val < 2 ^ 32)
    (hlylj : lj.val ≤ (b.lml.val[lj.val + q.val - 2]!).val)
    (hfdlen : (p.val + 1) * w.val ≤ fd.val.length) (hfdbig : (p.val + 1) * w.val < 2 ^ 32)
    (htdlen : (x.val + 1) * w.val ≤ td.val.length) (htdbig : (x.val + 1) * w.val < 2 ^ 32)
    (hfdb : ∀ k < fd.val.length, (fd.val[k]!).val ≤ inf.val)
    (htdb : ∀ k < td.val.length, (td.val[k]!).val ≤ inf.val)
    (hinfbig : 2 * inf.val + 1 < 2 ^ 32) :
    ted.fill_window_loop2_loop0.body a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind
      t inf w li lj p qhi x lx td fd st q row_min ⦃ r =>
      match r with
      | done _ => False
      | cont s => ∃ vv : Std.U32,
          vv.val = cellNew fd.val td.val w.val t.val inf.val li.val lj.val p.val q.val x.val lx.val
            (b.lml.val[lj.val + q.val - 2]!).val
            (rcost a b x.val (lj.val + q.val - 1)) ∧
          s.2.1.val = fd.val.set (bandIdx w.val t.val p.val q.val) vv ∧
          s.1.val = (if lx.val = li.val ∧ (b.lml.val[lj.val + q.val - 2]!).val = lj.val ∧
              InBand t.val x.val (lj.val + q.val - 1)
            then td.val.set (bandIdx w.val t.val x.val (lj.val + q.val - 1)) vv else td.val) ∧
          s.2.2.2.1.val = q.val + 1 ∧ s.2.2.2.2.val = min row_min.val vv.val ⦄ := by
  unfold ted.fill_window_loop2_loop0.body
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
    step as ⟨ic, hic⟩
    step as ⟨i, hi⟩
    step as ⟨y, hy⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨ly, hly⟩
    have hi1v : i1.val = lj.val + q.val - 2 := by omega
    have hlyv : ly.val = (b.lml.val[lj.val + q.val - 2]!).val := by
      have hv2' : lj.val + q.val - 2 < b.lml.val.length := hv2
      have hb : i1.val < b.lml.val.length := by omega
      have e : b.lml.val[lj.val + q.val - 2]! = b.lml.val[i1.val]'hb := by
        rw [← hi1v]; exact getU_eq _ _ hb
      rw [e, hly, U32.cast_Usize_val_eq, hi2]
    have hlyl : lj.val ≤ ly.val := by rw [hlyv]; exact hlylj
    step as ⟨i3, hi3⟩
    step with get_spec fd w t inf i3 q hw (hrow i3.val (by omega)).1 (hrow i3.val (by omega)).2 as ⟨i4, hi4⟩
    step as ⟨del, hdel⟩
    step as ⟨i5, hi5⟩
    step with get_spec fd w t inf p i5 hw (hrow p.val (by omega)).1 (hrow p.val (by omega)).2 as ⟨i6, hi6⟩
    step as ⟨ins, hins⟩
    have hyv : y.val = lj.val + q.val - 1 := by omega
    have hxv : x.val - 1 < a.label.val.length := hv
    have hv1' : lj.val + q.val - 2 < b.label.val.length := hv1
    have hdelv : del.val = rd fd.val w.val t.val inf.val (p.val - 1) q.val + 1 := by rw [hdel, hi4, hi3]
    have hinsv : ins.val = rd fd.val w.val t.val inf.val p.val (q.val - 1) + 1 := by rw [hins, hi6, hi5]
    split
    · rename_i hlxeq
      split
      · rename_i hlyeq
        step with relabel_cost_spec a b x y (by omega) (by omega) hv hak (by omega) (by omega) as ⟨ren, hren⟩
        have hyv' : y.val - 1 = lj.val + q.val - 2 := by omega
        have hren' : ren.val = rcost a b x.val (lj.val + q.val - 1) := by
          rw [hren, hyv]
        step with get_spec fd w t inf i3 i5 hw (hrow i3.val (by omega)).1 (hrow i3.val (by omega)).2 as ⟨i10, hi10⟩
        have hi10_le : i10.val ≤ inf.val := by rw [hi10]; exact hLfd _ _ (by omega)
        have hren_le : ren.val ≤ 2 := by rw [hren']; unfold rcost; split <;> (try split) <;> omega
        step as ⟨diag, hdiag⟩
        step as ⟨i11, hi11⟩
        step as ⟨i12, hi12⟩
        step as ⟨v4, hv4⟩
        step as ⟨i13, hi13⟩
        step with upd_if_spec td w t x y v4 i13 hw hi13 htdlen htdbig as ⟨s, hs⟩
        step as ⟨ib, hib⟩
        have hib_lt : ib.val < fd.val.length := by rw [hib]; unfold bandIdx; omega
        step as ⟨fd', hfd'⟩
        step as ⟨rm, hrm⟩
        step as ⟨q1, hq1'⟩
        have h1 : lx.val = li.val := congrArg Aeneas.Std.UScalar.val hlxeq
        have h2 : (b.lml.val[lj.val + q.val - 2]!).val = lj.val := by
          rw [← hlyv]; exact congrArg Aeneas.Std.UScalar.val hlyeq
        refine ⟨v4, ?_, ?_, ?_, ?_, ?_⟩
        · unfold cellNew cellX
          rw [if_pos ⟨h1, h2⟩]
          simp only [hv4, hi12, hi11, hdiag, hren', hdelv, hinsv, hi10, hi3, hi5, hren']
        · rw [hfd', Slice.set_val_eq, hib]
        · simp only [h1, h2, true_and, hs, hyv]
        · exact hq1'
        · exact hrm
      · rename_i hlyne
        step as ⟨i7, hi7⟩
        step with tdv_if_spec td w t x y inf i7 hw hi7 htdlen htdbig as ⟨tdv, htdv⟩
        have htdv_le : tdv.val ≤ inf.val := by rw [htdv]; exact hLtd _
        step as ⟨i8, hi8⟩
        step as ⟨i9, hi9⟩
        step with get_spec fd w t inf i8 i9 hw (hrow i8.val (by omega)).1 (hrow i8.val (by omega)).2 as ⟨i10, hi10⟩
        have hi10_le : i10.val ≤ inf.val := by rw [hi10]; exact hLfd _ _ (by omega)
        step as ⟨sub, hsub⟩
        step as ⟨i11, hi11⟩
        step as ⟨i12, hi12⟩
        step as ⟨v4, hv4⟩
        step as ⟨ib, hib⟩
        have hib_lt : ib.val < fd.val.length := by rw [hib]; unfold bandIdx; omega
        step as ⟨fd', hfd'⟩
        step as ⟨rm, hrm⟩
        step as ⟨q1, hq1'⟩
        have hnot : ¬ (lx.val = li.val ∧ (b.lml.val[lj.val + q.val - 2]!).val = lj.val) := by
          intro h; apply hlyne; scalar_tac
        refine ⟨v4, ?_, ?_, ?_, ?_, ?_⟩
        · unfold cellNew cellX
          rw [if_neg hnot]
          simp only [hv4, hi12, hi11, hsub, hdelv, hinsv, hi10, hi8, hi9, htdv, hlyv, hyv]
        · rw [hfd', Slice.set_val_eq, hib]
        · rw [if_neg (fun h => hnot ⟨h.1, h.2.1⟩)]
        · exact hq1'
        · exact hrm
    · rename_i hlxne
      step as ⟨i7, hi7⟩
      step with tdv_if_spec td w t x y inf i7 hw hi7 htdlen htdbig as ⟨tdv, htdv⟩
      have htdv_le : tdv.val ≤ inf.val := by rw [htdv]; exact hLtd _
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9⟩
      step with get_spec fd w t inf i8 i9 hw (hrow i8.val (by omega)).1 (hrow i8.val (by omega)).2 as ⟨i10, hi10⟩
      have hi10_le : i10.val ≤ inf.val := by rw [hi10]; exact hLfd _ _ (by omega)
      step as ⟨sub, hsub⟩
      step as ⟨i11, hi11⟩
      step as ⟨i12, hi12⟩
      step as ⟨v4, hv4⟩
      step as ⟨ib, hib⟩
      have hib_lt : ib.val < fd.val.length := by rw [hib]; unfold bandIdx; omega
      step as ⟨fd', hfd'⟩
      step as ⟨rm, hrm⟩
      step as ⟨q1, hq1'⟩
      have hnot : ¬ (lx.val = li.val ∧ (b.lml.val[lj.val + q.val - 2]!).val = lj.val) := by
        intro h; apply hlxne; scalar_tac
      refine ⟨v4, ?_, ?_, ?_, ?_, ?_⟩
      · unfold cellNew cellX
        rw [if_neg hnot]
        simp only [hv4, hi12, hi11, hsub, hdelv, hinsv, hi10, hi8, hi9, htdv, hlyv, hyv]
      · rw [hfd', Slice.set_val_eq, hib]
      · rw [if_neg (fun h => hnot ⟨h.1, h.2.1⟩)]
      · exact hq1'
      · exact hrm
  · rename_i hn
    exfalso
    scalar_tac


/-- Capping commutes with the cell recurrence. If the four values a cell reads hold `min (true value) inf`
(the delete, insert, and diagonal or subtree neighbours, and the stored subtree distance), then the cell
holds `min (recurrence on the true values) inf`. This is the algebra that lets the banded, capped table
stand for the exact forest distances; what it does not supply is the identification of the true values
with `Ted.fdist` of postorder prefixes (not proved). -/
theorem cellNew_cap (fdL tdL : List Std.U32) (w t inf li lj p q x lx ly ren D I G T : Nat)
    (hD : rd fdL w t inf (p - 1) q = min D inf) (hI : rd fdL w t inf p (q - 1) = min I inf)
    (hG : (if lx = li ∧ ly = lj then rd fdL w t inf (p - 1) (q - 1) else rd fdL w t inf (lx - li) (ly - lj))
      = min G inf)
    (hT : rd tdL w t inf x (lj + q - 1) = min T inf) (hren : ren ≤ 1) :
    cellNew fdL tdL w t inf li lj p q x lx ly ren =
      min (min (min (D + 1) (I + 1)) (if lx = li ∧ ly = lj then G + ren else G + T)) inf := by
  unfold cellNew cellX
  split
  · rename_i h
    rw [if_pos h] at hG
    rw [hD, hI, hG]
    omega
  · rename_i h
    rw [if_neg h] at hG
    rw [hD, hI, hG, hT]
    omega

end difffold_lines_extract
