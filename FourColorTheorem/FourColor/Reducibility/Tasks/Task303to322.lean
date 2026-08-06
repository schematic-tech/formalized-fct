import FourColorTheorem.FourColor.Reducibility.Jobs.Job303to306
import FourColorTheorem.FourColor.Reducibility.Jobs.Job307to310
import FourColorTheorem.FourColor.Reducibility.Jobs.Job311to314
import FourColorTheorem.FourColor.Reducibility.Jobs.Job315to318
import FourColorTheorem.FourColor.Reducibility.Jobs.Job319to322

/-!
Task collation for Coq `task303to322.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red302to322 :
    CheckedInRange 302 322 theConfigs :=
  catFiveCheckedRange
    Config.red302to306
    Config.red306to310
    Config.red310to314
    Config.red314to318
    Config.red318to322

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
