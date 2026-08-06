import FourColorTheorem.FourColor.Reducibility.CFContract
import FourColorTheorem.FourColor.Reducibility.Jobs
import Mathlib.Data.List.GetD

/-!
Executable reducibility collation theorem.

This is the Lean analogue of the collation layer in Coq `present.v` and
`reducibility.v`: every translated configuration in `theConfigs` passes
`checkReducible`, and Coq `check_reducible_valid` turns each successful check
into semantic `Hypermap.CReducible`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

/-- All translated configurations pass the executable reducibility checker. -/
def ExecutableReducibility : Prop :=
  CheckedInRange 0 theConfigs.length theConfigs

/-- Coq `the_reducibility`, at the executable-checker level available here. -/
theorem theExecutableReducibility :
    ExecutableReducibility :=
  allConfigsChecked

/-- Any in-range translated configuration passes the executable checker. -/
theorem checkedAt_of_mem_theConfigs
    {i : Nat} (hi : i < theConfigs.length) :
    CheckedAt theConfigs i :=
  theExecutableReducibility i (Nat.zero_le i) hi

/-- The semantic form of an indexed executable reducibility certificate. -/
theorem cReducibleAt_of_lt_theConfigs
    {i : Nat} (hi : i < theConfigs.length) :
    let cf := theConfigs.getD i default
    cf.map.map.CReducible cf.reducibilityRingDarts cf.contractFinset := by
  dsimp only
  exact checkReducible_valid (checkedAt_of_mem_theConfigs hi)

/-- Coq `the_reducibility`: every one of the 633 listed configurations is
semantically C-reducible. -/
theorem cReducible_of_mem_theConfigs
    {cf : Config} (hcf : cf ∈ theConfigs) :
    cf.map.map.CReducible cf.reducibilityRingDarts cf.contractFinset := by
  rcases List.mem_iff_get.mp hcf with ⟨i, hi⟩
  subst cf
  have hred := cReducibleAt_of_lt_theConfigs (i := i) i.isLt
  rw [List.getD_eq_getElem (l := theConfigs) (d := default) i.isLt] at hred
  exact hred

end Config

end FourColor

end Schematic.Math.GraphTheory
