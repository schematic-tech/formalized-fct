import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition007.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition007_sound :
    TransitionRangeSound config164Stage007Length config164Stage007Source config164Stage008Length config164Stage008Source config164Stage008Count CpStep.y 0 24 := by
  have h000 : TransitionRangeSound config164Stage007Length config164Stage007Source config164Stage008Length config164Stage008Source config164Stage008Count CpStep.y 0 24 := by simpa using config164_transition007_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
