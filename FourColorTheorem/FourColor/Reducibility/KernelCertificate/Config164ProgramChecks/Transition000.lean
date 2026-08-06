import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition000.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition000_sound :
    TransitionRangeSound config164Stage000Length config164Stage000Source config164Stage001Length config164Stage001Source config164Stage001Count CpStep.u 0 1 := by
  have h000 : TransitionRangeSound config164Stage000Length config164Stage000Source config164Stage001Length config164Stage001Source config164Stage001Count CpStep.u 0 1 := by simpa using config164_transition000_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
