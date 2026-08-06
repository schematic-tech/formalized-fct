import FourColorTheorem.FourColor.Reducibility.Tasks.Task001to214
import FourColorTheorem.FourColor.Reducibility.Tasks.Task215to234
import FourColorTheorem.FourColor.Reducibility.Tasks.Task235to282
import FourColorTheorem.FourColor.Reducibility.Tasks.Task283to302
import FourColorTheorem.FourColor.Reducibility.Tasks.Task303to322
import FourColorTheorem.FourColor.Reducibility.Tasks.Task323to485
import FourColorTheorem.FourColor.Reducibility.Tasks.Task486to506
import FourColorTheorem.FourColor.Reducibility.Tasks.Task507to541
import FourColorTheorem.FourColor.Reducibility.Tasks.Task542to588
import FourColorTheorem.FourColor.Reducibility.Tasks.Task589to633

/-!
Collation theorem matching Coq `reducibility.v`.

The task modules mirror Coq's intermediate `task...v` files.  This file
combines those task ranges in the same two-block shape as Coq
`the_reducibility`, still at the executable checker level.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

namespace Task

theorem red000to322 :
    CheckedInRange 0 322 theConfigs :=
  catFiveCheckedRange
    red000to214
    red214to234
    red234to282
    red282to302
    red302to322

theorem red322to633 :
    CheckedInRange 322 633 theConfigs :=
  catFiveCheckedRange
    red322to485
    red485to506
    red506to541
    red541to588
    red588to633

theorem red000to633 :
    CheckedInRange 0 633 theConfigs :=
  catCheckedRange red000to322 red322to633

theorem allConfigsChecked :
    CheckedInRange 0 theConfigs.length theConfigs := by
  simpa [length_theConfigs] using red000to633

end Task

end Config

end FourColor

end Schematic.Math.GraphTheory
