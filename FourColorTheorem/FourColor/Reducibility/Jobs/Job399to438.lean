import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job399to438.v`.

The Coq theorem is `red398to438 : reducible_in_range 398 438 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red398to408Fast and red398to408 from 398 to 408

reducibility_job red408to418Fast and red408to418 from 408 to 418

reducibility_job red418to428Fast and red418to428 from 418 to 428

reducibility_job red428to438Fast and red428to438 from 428 to 438

theorem red398to418 :
    CheckedInRange 398 418 theConfigs :=
  catCheckedRange red398to408 red408to418

theorem red418to438 :
    CheckedInRange 418 438 theConfigs :=
  catCheckedRange red418to428 red428to438

theorem red398to438 :
    CheckedInRange 398 438 theConfigs :=
  catCheckedRange red398to418 red418to438

end Config

end FourColor

end Schematic.Math.GraphTheory
