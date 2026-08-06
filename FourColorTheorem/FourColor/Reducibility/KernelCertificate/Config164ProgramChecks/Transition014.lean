import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition014.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition014_sound :
    TransitionRangeSound config164Stage014Length config164Stage014Source config164Stage015Length config164Stage015Source config164Stage015Count (CpStep.rotate 2) 0 159 := by
  have h000 : TransitionRangeSound config164Stage014Length config164Stage014Source config164Stage015Length config164Stage015Source config164Stage015Count (CpStep.rotate 2) 0 159 := by simpa using config164_transition014_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
