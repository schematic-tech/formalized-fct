import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition001.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition001_sound :
    TransitionRangeSound config164Stage001Length config164Stage001Source config164Stage002Length config164Stage002Source config164Stage002Count (CpStep.rotate 3) 0 3 := by
  have h000 : TransitionRangeSound config164Stage001Length config164Stage001Source config164Stage002Length config164Stage002Source config164Stage002Count (CpStep.rotate 3) 0 3 := by simpa using config164_transition001_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
