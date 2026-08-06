import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job323to383.v`.

The Coq theorem is `red322to383 : reducible_in_range 322 383 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red322to332Fast and red322to332 from 322 to 332

reducibility_job red332to342Fast and red332to342 from 332 to 342

reducibility_job red342to352Fast and red342to352 from 342 to 352

reducibility_job red352to362Fast and red352to362 from 352 to 362

reducibility_job red362to372Fast and red362to372 from 362 to 372

reducibility_job red372to383Fast and red372to383 from 372 to 383

theorem red322to342 :
    CheckedInRange 322 342 theConfigs :=
  catCheckedRange red322to332 red332to342

theorem red342to362 :
    CheckedInRange 342 362 theConfigs :=
  catCheckedRange red342to352 red352to362

theorem red362to383 :
    CheckedInRange 362 383 theConfigs :=
  catCheckedRange red362to372 red372to383

theorem red322to362 :
    CheckedInRange 322 362 theConfigs :=
  catCheckedRange red322to342 red342to362

theorem red322to383 :
    CheckedInRange 322 383 theConfigs :=
  catCheckedRange red322to362 red362to383

end Config

end FourColor

end Schematic.Math.GraphTheory
