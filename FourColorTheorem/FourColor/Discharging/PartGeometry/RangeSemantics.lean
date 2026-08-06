import FourColorTheorem.FourColor.Discharging.PartGeometry.Relations
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

/-- The arity-side predicate selected by a split branch.  For the low branch
this is `n ≤ k`; for the high branch this is `k < n`. -/
def splitCondition (k : Nat) (lo : Bool) (n : Nat) : Bool :=
  if lo then decide (n ≤ k) else decide (k < n)

theorem splitIndex_bounds_of_goodRSplit
    (k : Nat) (r : PRange)
    (hgood : goodRSplit k r = true) :
    5 ≤ k ∧ k ≤ 8 := by
  by_cases h5 : k = 5
  · omega
  by_cases h6 : k = 6
  · omega
  by_cases h7 : k = 7
  · omega
  by_cases h8 : k = 8
  · omega
  cases r <;>
    simp [goodRSplit, cmpRange, rangeLo] at hgood

theorem splitRange_eq_true_iff_of_goodRSplit
    (k : Nat) (lo : Bool) (r : PRange) {n : Nat}
    (hgood : goodRSplit k r = true) :
    splitRange k lo r n = true ↔
      r n = true ∧ splitCondition k lo n = true := by
  have hk := splitIndex_bounds_of_goodRSplit k r hgood
  have hk_cases : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl <;> cases lo <;> cases r <;>
    simp_all [goodRSplit, cmpRange, splitRange, splitCondition, rangeLo,
      rangeHi, PRange.contains, meetRange] <;> omega

theorem contains_splitRange_low_or_high (k : Nat) (r : PRange) {n : Nat}
    (hr : r n = true) :
    splitRange k true r n = true ∨
      splitRange k false r n = true := by
  by_cases h5 : k = 5
  · subst k
    cases r <;>
      simp [splitRange, rangeLo, rangeHi, PRange.contains, meetRange]
        at hr ⊢ <;> omega
  by_cases h6 : k = 6
  · subst k
    cases r <;>
      simp [splitRange, rangeLo, rangeHi, PRange.contains, meetRange]
        at hr ⊢ <;> omega
  by_cases h7 : k = 7
  · subst k
    cases r <;>
      simp [splitRange, rangeLo, rangeHi, PRange.contains, meetRange]
        at hr ⊢ <;> omega
  by_cases h8 : k = 8
  · subst k
    cases r <;>
      simp [splitRange, rangeLo, rangeHi, PRange.contains, meetRange]
        at hr ⊢ <;> omega
  cases r <;>
    simp [splitRange, rangeLo, rangeHi, PRange.contains, meetRange]
      at hr ⊢ <;> omega

theorem not_both_splitRange_of_goodRSplit
    (k : Nat) (r : PRange) {n : Nat}
    (hgood : goodRSplit k r = true)
    (hlo : splitRange k true r n = true)
    (hhi : splitRange k false r n = true) :
    False := by
  have hloCondition :=
    (splitRange_eq_true_iff_of_goodRSplit k true r hgood).mp hlo
  have hhiCondition :=
    (splitRange_eq_true_iff_of_goodRSplit k false r hgood).mp hhi
  simp [splitCondition] at hloCondition hhiCondition
  omega


end

end Part

end FourColor

end Schematic.Math.GraphTheory
