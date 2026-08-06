import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition002.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition002_sound :
    TransitionRangeSound config164Stage002Length config164Stage002Source config164Stage003Length config164Stage003Source config164Stage003Count CpStep.y 0 3 := by
  have h000 : TransitionRangeSound config164Stage002Length config164Stage002Source config164Stage003Length config164Stage003Source config164Stage003Count CpStep.y 0 3 := by simpa using config164_transition002_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
