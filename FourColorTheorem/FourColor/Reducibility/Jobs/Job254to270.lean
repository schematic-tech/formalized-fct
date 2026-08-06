import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job254to270.v`.

The Coq theorem is `red253to270 : reducible_in_range 253 270 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red253to262Fast and red253to262 from 253 to 262

reducibility_job red262to270Fast and red262to270 from 262 to 270

theorem red253to270 :
    CheckedInRange 253 270 theConfigs :=
  catCheckedRange red253to262 red262to270

end Config

end FourColor

end Schematic.Math.GraphTheory
