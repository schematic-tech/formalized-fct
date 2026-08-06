import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job466to485.v`.

The Coq theorem is `red465to485 : reducible_in_range 465 485 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red465to475Fast and red465to475 from 465 to 475

reducibility_job red475to485Fast and red475to485 from 475 to 485

theorem red465to485 :
    CheckedInRange 465 485 theConfigs :=
  catCheckedRange red465to475 red475to485

end Config

end FourColor

end Schematic.Math.GraphTheory
