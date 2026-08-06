import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition017.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition017.Chunk001

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition017_sound :
    TransitionRangeSound config164Stage017Length config164Stage017Source config164Stage018Length config164Stage018Source config164Stage018Count CpStep.h 0 318 := by
  have h000 : TransitionRangeSound config164Stage017Length config164Stage017Source config164Stage018Length config164Stage018Source config164Stage018Count CpStep.h 0 256 := by simpa using config164_transition017_000_sound
  have h001 : TransitionRangeSound config164Stage017Length config164Stage017Source config164Stage018Length config164Stage018Source config164Stage018Count CpStep.h 0 318 := by simpa using h000.concat config164_transition017_001_sound
  exact h001

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
