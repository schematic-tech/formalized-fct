import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job239to253.v`.

The Coq theorem is `red238to253 : reducible_in_range 238 253 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red238to246Fast and red238to246 from 238 to 246

reducibility_job red246to253Fast and red246to253 from 246 to 253

theorem red238to253 :
    CheckedInRange 238 253 theConfigs :=
  catCheckedRange red238to246 red246to253

end Config

end FourColor

end Schematic.Math.GraphTheory
