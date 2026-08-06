import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job190to206.v`.

The Coq theorem is `red189to206 : reducible_in_range 189 206 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red189to198Fast and red189to198 from 189 to 198

reducibility_job red198to206Fast and red198to206 from 198 to 206

theorem red189to206 :
    CheckedInRange 189 206 theConfigs :=
  catCheckedRange red189to198 red198to206

end Config

end FourColor

end Schematic.Math.GraphTheory
