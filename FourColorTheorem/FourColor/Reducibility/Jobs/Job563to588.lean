import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job563to588.v`.

The Coq theorem is `red562to588 : reducible_in_range 562 588 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red562to572Fast and red562to572 from 562 to 572

reducibility_job red572to580Fast and red572to580 from 572 to 580

reducibility_job red580to588Fast and red580to588 from 580 to 588

theorem red562to580 :
    CheckedInRange 562 580 theConfigs :=
  catCheckedRange red562to572 red572to580

theorem red562to588 :
    CheckedInRange 562 588 theConfigs :=
  catCheckedRange red562to580 red580to588

end Config

end FourColor

end Schematic.Math.GraphTheory
