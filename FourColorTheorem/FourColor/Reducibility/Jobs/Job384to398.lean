import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job384to398.v`.

The Coq theorem is `red383to398 : reducible_in_range 383 398 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red383to391Fast and red383to391 from 383 to 391

reducibility_job red391to398Fast and red391to398 from 391 to 398

theorem red383to398 :
    CheckedInRange 383 398 theConfigs :=
  catCheckedRange red383to391 red391to398

end Config

end FourColor

end Schematic.Math.GraphTheory
