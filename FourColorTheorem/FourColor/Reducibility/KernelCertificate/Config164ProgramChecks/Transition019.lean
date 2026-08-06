import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition019.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition019.Chunk001

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition019_sound :
    TransitionRangeSound config164Stage019Length config164Stage019Source config164Stage020Length config164Stage020Source config164Stage020Count CpStep.y 0 424 := by
  have h000 : TransitionRangeSound config164Stage019Length config164Stage019Source config164Stage020Length config164Stage020Source config164Stage020Count CpStep.y 0 256 := by simpa using config164_transition019_000_sound
  have h001 : TransitionRangeSound config164Stage019Length config164Stage019Source config164Stage020Length config164Stage020Source config164Stage020Count CpStep.y 0 424 := by simpa using h000.concat config164_transition019_001_sound
  exact h001

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
