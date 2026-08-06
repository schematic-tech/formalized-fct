import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition012.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition012_sound :
    TransitionRangeSound config164Stage012Length config164Stage012Source config164Stage013Length config164Stage013Source config164Stage013Count (CpStep.rotate 1) 0 120 := by
  have h000 : TransitionRangeSound config164Stage012Length config164Stage012Source config164Stage013Length config164Stage013Source config164Stage013Count (CpStep.rotate 1) 0 120 := by simpa using config164_transition012_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
