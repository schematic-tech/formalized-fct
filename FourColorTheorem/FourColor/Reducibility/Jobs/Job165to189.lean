import FourColorTheorem.FourColor.Reducibility.Jobs.Interface

/-!
Executable reducibility job for Coq `job165to189.v`.

The Coq theorem is `red164to189 : reducible_in_range 164 189 the_configs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

reducibility_job red164to176Fast and red164to176 from 164 to 176

reducibility_job red176to189Fast and red176to189 from 176 to 189

theorem red164to189 :
    CheckedInRange 164 189 theConfigs :=
  catCheckedRange red164to176 red176to189

end Config

end FourColor

end Schematic.Math.GraphTheory
