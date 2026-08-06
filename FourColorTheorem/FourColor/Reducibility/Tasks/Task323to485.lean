import FourColorTheorem.FourColor.Reducibility.Jobs.Job323to383
import FourColorTheorem.FourColor.Reducibility.Jobs.Job384to398
import FourColorTheorem.FourColor.Reducibility.Jobs.Job399to438
import FourColorTheorem.FourColor.Reducibility.Jobs.Job439to465
import FourColorTheorem.FourColor.Reducibility.Jobs.Job466to485

/-!
Task collation for Coq `task323to485.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red322to485 :
    CheckedInRange 322 485 theConfigs :=
  catFiveCheckedRange
    Config.red322to383
    Config.red383to398
    Config.red398to438
    Config.red438to465
    Config.red465to485

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
