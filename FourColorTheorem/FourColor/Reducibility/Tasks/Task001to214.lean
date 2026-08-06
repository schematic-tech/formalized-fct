import FourColorTheorem.FourColor.Reducibility.Jobs.Job000to164
import FourColorTheorem.FourColor.Reducibility.Jobs.Job165to189
import FourColorTheorem.FourColor.Reducibility.Jobs.Job190to206
import FourColorTheorem.FourColor.Reducibility.Jobs.Job207to214

/-!
Task collation for Coq `task001to214.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red000to214 :
    CheckedInRange 0 214 theConfigs :=
  catFiveCheckedRange
    Config.red000to106
    Config.red106to164
    Config.red164to189
    Config.red189to206
    Config.red206to214

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
