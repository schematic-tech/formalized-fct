import FourColorTheorem.FourColor.Reducibility.Jobs.Job589to610
import FourColorTheorem.FourColor.Reducibility.Jobs.Job611to617
import FourColorTheorem.FourColor.Reducibility.Jobs.Job618to622
import FourColorTheorem.FourColor.Reducibility.Jobs.Job623to633

/-!
Task collation for Coq `task589to633.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red588to633 :
    CheckedInRange 588 633 theConfigs :=
  catCheckedRange Config.red588to610
    (catCheckedRange Config.red610to617
      (catCheckedRange Config.red617to622 Config.red622to633))

theorem red633to633 :
    CheckedInRange 633 633 theConfigs := by
  intro i hi hlt
  exact False.elim ((Nat.not_lt_of_ge hi) hlt)

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
