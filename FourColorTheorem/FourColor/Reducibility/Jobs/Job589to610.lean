import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job589to610.v`.

The Coq theorem is `red588to610 : reducible_in_range 588 610 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red588to598Fast and red588to598 from 588 to 598

reducibility_job red598to610Fast and red598to610 from 598 to 610

theorem red588to610 :
    CheckedInRange 588 610 theConfigs :=
  catCheckedRange red588to598 red598to610

end Config

end FourColor

end Schematic.Math.GraphTheory
