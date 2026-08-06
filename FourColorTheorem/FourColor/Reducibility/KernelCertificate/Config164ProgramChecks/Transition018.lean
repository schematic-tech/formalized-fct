import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition018.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition018.Chunk001

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition018_sound :
    TransitionRangeSound config164Stage018Length config164Stage018Source config164Stage019Length config164Stage019Source config164Stage019Count (CpStep.rotate 3) 0 424 := by
  have h000 : TransitionRangeSound config164Stage018Length config164Stage018Source config164Stage019Length config164Stage019Source config164Stage019Count (CpStep.rotate 3) 0 256 := by simpa using config164_transition018_000_sound
  have h001 : TransitionRangeSound config164Stage018Length config164Stage018Source config164Stage019Length config164Stage019Source config164Stage019Count (CpStep.rotate 3) 0 424 := by simpa using h000.concat config164_transition018_001_sound
  exact h001

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
