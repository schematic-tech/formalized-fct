import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition016.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition016.Chunk001

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition016_sound :
    TransitionRangeSound config164Stage016Length config164Stage016Source config164Stage017Length config164Stage017Source config164Stage017Count (CpStep.rotate 10) 0 318 := by
  have h000 : TransitionRangeSound config164Stage016Length config164Stage016Source config164Stage017Length config164Stage017Source config164Stage017Count (CpStep.rotate 10) 0 256 := by simpa using config164_transition016_000_sound
  have h001 : TransitionRangeSound config164Stage016Length config164Stage016Source config164Stage017Length config164Stage017Source config164Stage017Count (CpStep.rotate 10) 0 318 := by simpa using h000.concat config164_transition016_001_sound
  exact h001

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
