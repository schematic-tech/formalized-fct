import FourColorTheorem.FourColor.Reducibility.Executable
import FourColorTheorem.FourColor.Presentation.Language

/-!
Optional certificate bridge for presentation reducibility.

This file intentionally imports `ExecutableReducibility`, which pulls in the
0--633 executable certificate jobs.  It is not imported by
`FourColorTheorem.FourColor`; build it explicitly when the full certificate
collation should be checked.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Presentation

noncomputable section

/-- The presentation reducibility hypothesis discharged by the executable
633-configuration certificate collation. -/
theorem reducibility_from_executable :
    Reducibility := by
  simpa [Reducibility, Config.ExecutableReducibility]
    using Config.theExecutableReducibility

end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
