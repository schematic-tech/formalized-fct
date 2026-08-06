import FourColorTheorem.FourColor.Reducibility.Jobs.Job215to218
import FourColorTheorem.FourColor.Reducibility.Jobs.Job219to222
import FourColorTheorem.FourColor.Reducibility.Jobs.Job223to226
import FourColorTheorem.FourColor.Reducibility.Jobs.Job227to230
import FourColorTheorem.FourColor.Reducibility.Jobs.Job231to234

/-!
Task collation for Coq `task215to234.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red214to234 :
    CheckedInRange 214 234 theConfigs :=
  catFiveCheckedRange
    Config.red214to218
    Config.red218to222
    Config.red222to226
    Config.red226to230
    Config.red230to234

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
