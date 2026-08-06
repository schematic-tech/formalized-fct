import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition015.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition015_sound :
    TransitionRangeSound config164Stage015Length config164Stage015Source config164Stage016Length config164Stage016Source config164Stage016Count CpStep.y 0 159 := by
  have h000 : TransitionRangeSound config164Stage015Length config164Stage015Source config164Stage016Length config164Stage016Source config164Stage016Count CpStep.y 0 159 := by simpa using config164_transition015_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
