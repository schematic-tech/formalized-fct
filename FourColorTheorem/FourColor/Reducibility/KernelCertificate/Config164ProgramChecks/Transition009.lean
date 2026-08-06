import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition009.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition009_sound :
    TransitionRangeSound config164Stage009Length config164Stage009Source config164Stage010Length config164Stage010Source config164Stage010Count CpStep.h 0 48 := by
  have h000 : TransitionRangeSound config164Stage009Length config164Stage009Source config164Stage010Length config164Stage010Source config164Stage010Count CpStep.h 0 48 := by simpa using config164_transition009_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
