import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition006.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition006_sound :
    TransitionRangeSound config164Stage006Length config164Stage006Source config164Stage007Length config164Stage007Source config164Stage007Count CpStep.y 0 12 := by
  have h000 : TransitionRangeSound config164Stage006Length config164Stage006Source config164Stage007Length config164Stage007Source config164Stage007Count CpStep.y 0 12 := by simpa using config164_transition006_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
