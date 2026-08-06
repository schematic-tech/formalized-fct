import FourColorTheorem.FourColor.Reducibility.Certificate
import FourColorTheorem.FourColor.Configuration.Database

/-!
Shared executable-reducibility job interface. Individual ranges live in
independent modules so their certificate checks compile independently.
-/

/-- Declare one independently compiled executable range certificate together
with its semantic soundness theorem.  Keeping each invocation separate is
intentional: the native checks are staged to bound peak memory. -/
syntax (name := reducibilityJob)
  "reducibility_job " ident " and " ident " from " term " to " term : command

macro_rules
  | `(reducibility_job $fast:ident and $checked:ident
        from $lo:term to $hi:term) =>
      `(section
        theorem $fast :
            Schematic.Math.GraphTheory.FourColor.Config.checkRangeFast
              $lo $hi
              Schematic.Math.GraphTheory.FourColor.Config.theConfigs = true := by
          fct_decide

        theorem $checked :
            Schematic.Math.GraphTheory.FourColor.Config.CheckedInRange
              $lo $hi
              Schematic.Math.GraphTheory.FourColor.Config.theConfigs :=
          Schematic.Math.GraphTheory.FourColor.Config.checkRangeFast_sound $fast
        end)
