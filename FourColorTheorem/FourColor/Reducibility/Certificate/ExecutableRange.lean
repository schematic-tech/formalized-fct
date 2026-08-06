import FourColorTheorem.FourColor.Reducibility.Certificate.CheckedRange

/-! Executable range checking and its semantic interface. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config
/-- Boolean range checker used by certificate chunks. -/
def checkRange (j1 j2 : Nat) (cfs : List Config) : Bool :=
  (List.range (j2 - j1)).all
    (fun k => checkReducible (cfs.getD (j1 + k) default))

/-- Boolean range checker using the optimized executable backend. -/
def checkRangeFast (j1 j2 : Nat) (cfs : List Config) : Bool :=
  (List.range (j2 - j1)).all
    (fun k => checkReducibleFast (cfs.getD (j1 + k) default))

theorem checkRangeFast_spec
    (j1 j2 : Nat) (cfs : List Config) :
    checkRangeFast j1 j2 cfs = checkRange j1 j2 cfs := by
  unfold checkRangeFast checkRange
  congr 1
  ext k
  exact checkReducibleFast_spec (cfs.getD (j1 + k) default)

theorem checkRange_sound
    {j1 j2 : Nat} {cfs : List Config}
    (h : checkRange j1 j2 cfs = true) :
    CheckedInRange j1 j2 cfs := by
  intro i hi1 hi2
  unfold CheckedAt
  unfold checkRange at h
  have hmem : i - j1 ∈ List.range (j2 - j1) := by
    simp [List.mem_range]
    omega
  have hall := (List.all_eq_true.mp h) (i - j1) hmem
  have hidx : j1 + (i - j1) = i := Nat.add_sub_of_le hi1
  simpa [hidx] using hall

theorem checkRange_checkedAt
    {j1 j2 : Nat} {cfs : List Config}
    (h : checkRange j1 j2 cfs = true)
    {i : Nat} (hi1 : j1 ≤ i) (hi2 : i < j2) :
    CheckedAt cfs i :=
  checkRange_sound h i hi1 hi2

theorem checkRange_complete
    {j1 j2 : Nat} {cfs : List Config}
    (h : CheckedInRange j1 j2 cfs) :
    checkRange j1 j2 cfs = true := by
  unfold checkRange
  apply List.all_eq_true.mpr
  intro k hk
  have hklt : k < j2 - j1 := by
    simpa [List.mem_range] using hk
  have hi1 : j1 ≤ j1 + k := Nat.le_add_right j1 k
  have hi2 : j1 + k < j2 := by omega
  simpa using h (j1 + k) hi1 hi2

theorem checkRange_true_iff_checkedInRange
    {j1 j2 : Nat} {cfs : List Config} :
    checkRange j1 j2 cfs = true ↔ CheckedInRange j1 j2 cfs :=
  ⟨checkRange_sound, checkRange_complete⟩

theorem checkedInRange_of_right_le_left
    {j1 j2 : Nat} {cfs : List Config}
    (hji : j2 ≤ j1) :
    CheckedInRange j1 j2 cfs := by
  intro i hi1 hi2
  omega

theorem checkRange_eq_true_of_right_le_left
    {j1 j2 : Nat} {cfs : List Config}
    (hji : j2 ≤ j1) :
    checkRange j1 j2 cfs = true :=
  checkRange_complete (checkedInRange_of_right_le_left hji)

/-! The executable checker exposes the complete semantic range API through
the same checked-consequence registry as the pointwise and propositional
interfaces. -/

lift_checked_range_api checkRange using checkRange_sound

lift_checked_normalized_api checkRange

theorem catCheckedRange
    {j1 j2 j3 : Nat} {cfs : List Config}
    (h12 : CheckedInRange j1 j2 cfs)
    (h23 : CheckedInRange j2 j3 cfs) :
    CheckedInRange j1 j3 cfs := by
  intro i hi1 hi3
  by_cases hlt : i < j2
  · exact h12 i hi1 hlt
  · exact h23 i (Nat.le_of_not_gt hlt) hi3


end Config

end FourColor

end Schematic.Math.GraphTheory
