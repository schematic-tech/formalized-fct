import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition008.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition008_sound :
    TransitionRangeSound config164Stage008Length config164Stage008Source config164Stage009Length config164Stage009Source config164Stage009Count (CpStep.rotate 8) 0 48 := by
  have h000 : TransitionRangeSound config164Stage008Length config164Stage008Source config164Stage009Length config164Stage009Source config164Stage009Count (CpStep.rotate 8) 0 48 := by simpa using config164_transition008_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
