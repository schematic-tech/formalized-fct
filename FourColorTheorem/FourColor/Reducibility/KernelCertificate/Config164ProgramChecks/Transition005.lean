import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition005.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition005_sound :
    TransitionRangeSound config164Stage005Length config164Stage005Source config164Stage006Length config164Stage006Source config164Stage006Count (CpStep.rotate 1) 0 12 := by
  have h000 : TransitionRangeSound config164Stage005Length config164Stage005Source config164Stage006Length config164Stage006Source config164Stage006Count (CpStep.rotate 1) 0 12 := by simpa using config164_transition005_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
