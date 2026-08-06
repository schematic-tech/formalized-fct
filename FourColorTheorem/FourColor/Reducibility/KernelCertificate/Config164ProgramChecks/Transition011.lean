import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition011.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition011_sound :
    TransitionRangeSound config164Stage011Length config164Stage011Source config164Stage012Length config164Stage012Source config164Stage012Count CpStep.y 0 60 := by
  have h000 : TransitionRangeSound config164Stage011Length config164Stage011Source config164Stage012Length config164Stage012Source config164Stage012Count CpStep.y 0 60 := by simpa using config164_transition011_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
