import FourColorTheorem.FourColor.Reducibility.Tasks

/-!
Aggregate import for executable reducibility certificate jobs.

The broad `FourColorTheorem.FourColor` import intentionally excludes these
native certificate jobs so ordinary development does not trigger the expensive
checks on a clean build.  Build this module explicitly when checking the
ported reducibility certificates.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

theorem red000to633Checked :
    CheckedInRange 0 633 theConfigs :=
  Task.red000to633

theorem allConfigsChecked :
    CheckedInRange 0 theConfigs.length theConfigs := by
  exact Task.allConfigsChecked

end Config

end FourColor

end Schematic.Math.GraphTheory
