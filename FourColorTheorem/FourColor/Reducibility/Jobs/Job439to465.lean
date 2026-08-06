import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job439to465.v`.

The Coq theorem is `red438to465 : reducible_in_range 438 465 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red438to448Fast and red438to448 from 438 to 448

reducibility_job red448to458Fast and red448to458 from 448 to 458

reducibility_job red458to465Fast and red458to465 from 458 to 465

theorem red438to458 :
    CheckedInRange 438 458 theConfigs :=
  catCheckedRange red438to448 red448to458

theorem red438to465 :
    CheckedInRange 438 465 theConfigs :=
  catCheckedRange red438to458 red458to465

end Config

end FourColor

end Schematic.Math.GraphTheory
