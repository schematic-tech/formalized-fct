import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition003.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition003_sound :
    TransitionRangeSound config164Stage003Length config164Stage003Source config164Stage004Length config164Stage004Source config164Stage004Count (CpStep.rotate 1) 0 6 := by
  have h000 : TransitionRangeSound config164Stage003Length config164Stage003Source config164Stage004Length config164Stage004Source config164Stage004Count (CpStep.rotate 1) 0 6 := by simpa using config164_transition003_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
