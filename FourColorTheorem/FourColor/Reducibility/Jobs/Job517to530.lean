import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job517to530.v`.

The Coq theorem is `red516to530 : reducible_in_range 516 530 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red516to523Fast and red516to523 from 516 to 523

reducibility_job red523to530Fast and red523to530 from 523 to 530

theorem red516to530 :
    CheckedInRange 516 530 theConfigs :=
  catCheckedRange red516to523 red523to530

end Config

end FourColor

end Schematic.Math.GraphTheory
