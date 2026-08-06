import FourColorTheorem.FourColor.Reducibility.Certificate.ExecutableRange

/-! Composition and restriction of checked certificate ranges. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config
/-- Five-way range composition, matching the shape of Coq's `CatReducible`
certificate-combination tactic. -/
theorem catFiveCheckedRange
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : CheckedInRange j1 j2 cfs)
    (h23 : CheckedInRange j2 j3 cfs)
    (h34 : CheckedInRange j3 j4 cfs)
    (h45 : CheckedInRange j4 j5 cfs)
    (h56 : CheckedInRange j5 j6 cfs) :
    CheckedInRange j1 j6 cfs :=
  catCheckedRange h12
    (catCheckedRange h23
      (catCheckedRange h34
        (catCheckedRange h45 h56)))

theorem CheckedInRange.mono
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : CheckedInRange j1 j2 cfs)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    CheckedInRange k1 k2 cfs := by
  intro i hi1 hi2
  exact h i (Nat.le_trans hj1 hi1) (Nat.lt_of_lt_of_le hi2 hk2)

/-- A Boolean range checker together with its exact semantic interface. -/
private structure RangeChecker where
  check : Nat → Nat → List Config → Bool
  sound : ∀ {j1 j2 cfs}, check j1 j2 cfs = true →
    CheckedInRange j1 j2 cfs
  complete : ∀ {j1 j2 cfs}, CheckedInRange j1 j2 cfs →
    check j1 j2 cfs = true

private theorem RangeChecker.catSound
    (R : RangeChecker)
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : R.check j1 j2 cfs = true)
    (h23 : R.check j2 j3 cfs = true) :
    CheckedInRange j1 j3 cfs :=
  catCheckedRange (R.sound h12) (R.sound h23)

private theorem RangeChecker.catEqTrue
    (R : RangeChecker)
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : R.check j1 j2 cfs = true)
    (h23 : R.check j2 j3 cfs = true) :
    R.check j1 j3 cfs = true :=
  R.complete (R.catSound h12 h23)

private theorem RangeChecker.catFiveSound
    (R : RangeChecker)
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : R.check j1 j2 cfs = true)
    (h23 : R.check j2 j3 cfs = true)
    (h34 : R.check j3 j4 cfs = true)
    (h45 : R.check j4 j5 cfs = true)
    (h56 : R.check j5 j6 cfs = true) :
    CheckedInRange j1 j6 cfs :=
  catFiveCheckedRange
    (R.sound h12) (R.sound h23) (R.sound h34)
    (R.sound h45) (R.sound h56)

private theorem RangeChecker.catFiveEqTrue
    (R : RangeChecker)
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : R.check j1 j2 cfs = true)
    (h23 : R.check j2 j3 cfs = true)
    (h34 : R.check j3 j4 cfs = true)
    (h45 : R.check j4 j5 cfs = true)
    (h56 : R.check j5 j6 cfs = true) :
    R.check j1 j6 cfs = true :=
  R.complete (R.catFiveSound h12 h23 h34 h45 h56)

private theorem RangeChecker.subrangeSound
    (R : RangeChecker)
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : R.check j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    CheckedInRange k1 k2 cfs :=
  CheckedInRange.mono (R.sound h) hj1 hk2

private theorem RangeChecker.subrangeEqTrue
    (R : RangeChecker)
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : R.check j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    R.check k1 k2 cfs = true :=
  R.complete (R.subrangeSound h hj1 hk2)

private def checkRangeChecker : RangeChecker where
  check := checkRange
  sound := checkRange_sound
  complete := checkRange_complete

theorem checkRange_cat_sound
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : checkRange j1 j2 cfs = true)
    (h23 : checkRange j2 j3 cfs = true) :
    CheckedInRange j1 j3 cfs :=
  checkRangeChecker.catSound h12 h23

theorem checkRange_cat_eq_true
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : checkRange j1 j2 cfs = true)
    (h23 : checkRange j2 j3 cfs = true) :
    checkRange j1 j3 cfs = true :=
  checkRangeChecker.catEqTrue h12 h23

theorem checkRange_catFive_sound
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : checkRange j1 j2 cfs = true)
    (h23 : checkRange j2 j3 cfs = true)
    (h34 : checkRange j3 j4 cfs = true)
    (h45 : checkRange j4 j5 cfs = true)
    (h56 : checkRange j5 j6 cfs = true) :
    CheckedInRange j1 j6 cfs :=
  checkRangeChecker.catFiveSound h12 h23 h34 h45 h56

theorem checkRange_catFive_eq_true
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : checkRange j1 j2 cfs = true)
    (h23 : checkRange j2 j3 cfs = true)
    (h34 : checkRange j3 j4 cfs = true)
    (h45 : checkRange j4 j5 cfs = true)
    (h56 : checkRange j5 j6 cfs = true) :
    checkRange j1 j6 cfs = true :=
  checkRangeChecker.catFiveEqTrue h12 h23 h34 h45 h56

theorem checkRange_subrange_sound
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : checkRange j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    CheckedInRange k1 k2 cfs :=
  checkRangeChecker.subrangeSound h hj1 hk2

theorem checkRange_subrange_eq_true
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : checkRange j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    checkRange k1 k2 cfs = true :=
  checkRangeChecker.subrangeEqTrue h hj1 hk2

theorem checkRangeFast_sound
    {j1 j2 : Nat} {cfs : List Config}
    (h : checkRangeFast j1 j2 cfs = true) :
    CheckedInRange j1 j2 cfs :=
  checkRange_sound ((checkRangeFast_spec j1 j2 cfs).symm ▸ h)

theorem checkRangeFast_checkedAt
    {j1 j2 : Nat} {cfs : List Config}
    (h : checkRangeFast j1 j2 cfs = true)
    {i : Nat} (hi1 : j1 ≤ i) (hi2 : i < j2) :
    CheckedAt cfs i :=
  checkRangeFast_sound h i hi1 hi2

theorem checkRangeFast_complete
    {j1 j2 : Nat} {cfs : List Config}
    (h : CheckedInRange j1 j2 cfs) :
    checkRangeFast j1 j2 cfs = true := by
  rw [checkRangeFast_spec]
  exact checkRange_complete h

theorem checkRangeFast_true_iff_checkedInRange
    {j1 j2 : Nat} {cfs : List Config} :
    checkRangeFast j1 j2 cfs = true ↔ CheckedInRange j1 j2 cfs := by
  rw [checkRangeFast_spec]
  exact checkRange_true_iff_checkedInRange

theorem checkRangeFast_eq_true_of_right_le_left
    {j1 j2 : Nat} {cfs : List Config}
    (hji : j2 ≤ j1) :
    checkRangeFast j1 j2 cfs = true :=
  checkRangeFast_complete (checkedInRange_of_right_le_left hji)

lift_checked_range_api checkRangeFast using checkRangeFast_sound

lift_checked_normalized_api checkRangeFast

private def checkRangeFastChecker : RangeChecker where
  check := checkRangeFast
  sound := checkRangeFast_sound
  complete := checkRangeFast_complete

theorem checkRangeFast_cat_sound
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : checkRangeFast j1 j2 cfs = true)
    (h23 : checkRangeFast j2 j3 cfs = true) :
    CheckedInRange j1 j3 cfs :=
  checkRangeFastChecker.catSound h12 h23

theorem checkRangeFast_cat_eq_true
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : checkRangeFast j1 j2 cfs = true)
    (h23 : checkRangeFast j2 j3 cfs = true) :
    checkRangeFast j1 j3 cfs = true :=
  checkRangeFastChecker.catEqTrue h12 h23

theorem checkRangeFast_catFive_sound
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : checkRangeFast j1 j2 cfs = true)
    (h23 : checkRangeFast j2 j3 cfs = true)
    (h34 : checkRangeFast j3 j4 cfs = true)
    (h45 : checkRangeFast j4 j5 cfs = true)
    (h56 : checkRangeFast j5 j6 cfs = true) :
    CheckedInRange j1 j6 cfs :=
  checkRangeFastChecker.catFiveSound h12 h23 h34 h45 h56

theorem checkRangeFast_catFive_eq_true
    {j1 j2 j3 j4 j5 j6 : Nat} {cfs : List Config}
    (h12 : checkRangeFast j1 j2 cfs = true)
    (h23 : checkRangeFast j2 j3 cfs = true)
    (h34 : checkRangeFast j3 j4 cfs = true)
    (h45 : checkRangeFast j4 j5 cfs = true)
    (h56 : checkRangeFast j5 j6 cfs = true) :
    checkRangeFast j1 j6 cfs = true :=
  checkRangeFastChecker.catFiveEqTrue h12 h23 h34 h45 h56

theorem checkRangeFast_subrange_sound
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : checkRangeFast j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    CheckedInRange k1 k2 cfs :=
  checkRangeFastChecker.subrangeSound h hj1 hk2

theorem checkRangeFast_subrange_eq_true
    {j1 j2 k1 k2 : Nat} {cfs : List Config}
    (h : checkRangeFast j1 j2 cfs = true)
    (hj1 : j1 ≤ k1) (hk2 : k2 ≤ j2) :
    checkRangeFast k1 k2 cfs = true :=
  checkRangeFastChecker.subrangeEqTrue h hj1 hk2

end Config

end FourColor

end Schematic.Math.GraphTheory
