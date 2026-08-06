import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition010.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition010_sound :
    TransitionRangeSound config164Stage010Length config164Stage010Source config164Stage011Length config164Stage011Source config164Stage011Count (CpStep.rotate 3) 0 60 := by
  have h000 : TransitionRangeSound config164Stage010Length config164Stage010Source config164Stage011Length config164Stage011Source config164Stage011Count (CpStep.rotate 3) 0 60 := by simpa using config164_transition010_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
