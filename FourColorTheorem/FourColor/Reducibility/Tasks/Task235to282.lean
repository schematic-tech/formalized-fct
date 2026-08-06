import FourColorTheorem.FourColor.Reducibility.Jobs.Job235to238
import FourColorTheorem.FourColor.Reducibility.Jobs.Job239to253
import FourColorTheorem.FourColor.Reducibility.Jobs.Job254to270
import FourColorTheorem.FourColor.Reducibility.Jobs.Job271to278
import FourColorTheorem.FourColor.Reducibility.Jobs.Job279to282

/-!
Task collation for Coq `task235to282.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red234to282 :
    CheckedInRange 234 282 theConfigs :=
  catFiveCheckedRange
    Config.red234to238
    Config.red238to253
    Config.red253to270
    Config.red270to278
    Config.red278to282

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
