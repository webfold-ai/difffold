import Model
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

/-- `|x - y|` on naturals. -/
def absd (x y : Nat) : Nat := if x ≥ y then x - y else y - x

/-- The kernel's diagonal stage: consider the pair candidate only when its lower bound can win and
can fit. `D` is the diagonal predecessor (`INF` when absent). -/
def diagStage (on : Bool) (hv tau sai sbj ddv best0 D : Nat) : Nat :=
  if D < INFn then
    (let lb := if on then D + absd sai sbj else D
     if lb < best0 then
       (if lb + hv ≤ tau then Nat.min best0 (D + ddv) else best0)
     else best0)
  else best0

/-- The kernel's cell value after the keep test. -/
def kcell (on : Bool) (hv tau sai sbj ddv del ins D : Nat) : Nat :=
  let best := diagStage on hv tau sai sbj ddv (Nat.min del ins) D
  if best + hv ≤ tau then best else INFn

/-- When the diagonal is present, skipping the pair cost is invisible after the keep test.
This is where the size bound `dd >= |sa - sb|` is used. -/
theorem stage_final (on : Bool) (hv tau sai sbj ddv best0 D : Nat) (hD : D < INFn)
    (hsize : on = true → sai ≤ sbj + ddv ∧ sbj ≤ sai + ddv) :
    (if diagStage on hv tau sai sbj ddv best0 D + hv ≤ tau then diagStage on hv tau sai sbj ddv best0 D else INFn) =
    (if Nat.min best0 (D + ddv) + hv ≤ tau then Nat.min best0 (D + ddv) else INFn) := by
  unfold diagStage absd
  simp only [hD, if_true]
  by_cases hon : on = true
  · have := hsize hon
    simp only [hon, if_true, Nat.min_def]
    split_ifs <;> omega
  · have hon' : on = false := by simpa using hon
    simp only [hon', Bool.false_eq_true, if_false, Nat.min_def]
    split_ifs <;> omega

/-- The diagonal stage never increases the candidate. -/
theorem diagStage_le (on : Bool) (hv tau sai sbj ddv best0 D : Nat) :
    diagStage on hv tau sai sbj ddv best0 D ≤ best0 := by
  unfold diagStage
  simp only [Nat.min_def]
  split_ifs <;> omega

/-- With no diagonal, the stage is the identity. -/
theorem stage_none (on : Bool) (hv tau sai sbj ddv best0 : Nat) :
    diagStage on hv tau sai sbj ddv best0 INFn = best0 := by
  unfold diagStage; simp [INFn]

/-- The model's cell after the keep test, as a kernel word. -/
def keepEnc (hv tau : Nat) : Option Nat → Nat
  | none => INFn
  | some c => if c + hv ≤ tau then c else INFn

theorem enc_keep (hv tau : Nat) (co : Option Nat) :
    enc (keep (fun _ _ => hv) tau 0 0 co) = keepEnc hv tau co := by
  cases co <;> simp [keep, keepEnc, enc] <;> split_ifs <;> simp

/-- The kernel's cell arithmetic is the model's `keep (omin (omin ..) ..)`. -/
theorem kcell_eq_model (on : Bool) (hv tau sai sbj ddv del ins : Nat) (up left dg : Option Nat)
    (hbig : tau + 2 ^ 28 < INFn) (hsa : sai ≤ 2 ^ 27)
    (hsb : (left ≠ none ∨ dg ≠ none) → sbj ≤ 2 ^ 27) (hdd : dg ≠ none → ddv ≤ 2 ^ 28)
    (hup : ∀ u, up = some u → u ≤ tau) (hlf : ∀ l, left = some l → l ≤ tau)
    (hdg : ∀ d, dg = some d → d ≤ tau)
    (hsize : on = true → dg ≠ none → sai ≤ sbj + ddv ∧ sbj ≤ sai + ddv)
    (hdel1 : ∀ u, up = some u → del = u + sai) (hdel2 : up = none → del = INFn)
    (hins1 : ∀ l, left = some l → ins = l + sbj) (hins2 : left = none → INFn ≤ ins) :
    kcell on hv tau sai sbj ddv del ins (enc dg) =
      keepEnc hv tau (omin (omin (oadd up sai) (oadd left sbj)) (oadd dg ddv)) := by
  rcases dg with _ | d
  · simp only [enc]
    unfold kcell
    rw [stage_none]
    rcases up with _ | u <;> rcases left with _ | l
    · have e1 := hdel2 rfl; have e2 := hins2 rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel2 rfl; have e2 := hins1 l rfl; have h3 := hlf l rfl
      have hsb' := hsb (Or.inl (by simp))
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel1 u rfl; have e2 := hins2 rfl; have h3 := hup u rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel1 u rfl; have e2 := hins1 l rfl; have h3 := hup u rfl; have h4 := hlf l rfl
      have hsb' := hsb (Or.inl (by simp))
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
  · have hd := hdg d rfl
    have hsb' := hsb (Or.inr (by simp))
    have hdd' := hdd (by simp)
    have hD : d < INFn := by omega
    simp only [enc]
    unfold kcell
    have hsf := stage_final on hv tau sai sbj ddv (Nat.min del ins) d hD (fun h => hsize h (by simp))
    show (if diagStage on hv tau sai sbj ddv (Nat.min del ins) d + hv ≤ tau
          then diagStage on hv tau sai sbj ddv (Nat.min del ins) d else INFn) = _
    rw [hsf]
    rcases up with _ | u <;> rcases left with _ | l
    · have e1 := hdel2 rfl; have e2 := hins2 rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel2 rfl; have e2 := hins1 l rfl; have h3 := hlf l rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel1 u rfl; have e2 := hins2 rfl; have h3 := hup u rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega
    · have e1 := hdel1 u rfl; have e2 := hins1 l rfl; have h3 := hup u rfl; have h4 := hlf l rfl
      simp only [oadd, omin, keepEnc, Option.map, Nat.min_def]
      split_ifs <;> omega

end difffold_kernel_extract
