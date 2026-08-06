import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition013.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition013_sound :
    TransitionRangeSound config164Stage013Length config164Stage013Source config164Stage014Length config164Stage014Source config164Stage014Count CpStep.h 0 120 := by
  have h000 : TransitionRangeSound config164Stage013Length config164Stage013Source config164Stage014Length config164Stage014Source config164Stage014Count CpStep.h 0 120 := by simpa using config164_transition013_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
