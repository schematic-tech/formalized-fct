import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition004.Chunk000

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition004_sound :
    TransitionRangeSound config164Stage004Length config164Stage004Source config164Stage005Length config164Stage005Source config164Stage005Count CpStep.y 0 6 := by
  have h000 : TransitionRangeSound config164Stage004Length config164Stage004Source config164Stage005Length config164Stage005Source config164Stage005Count CpStep.y 0 6 := by simpa using config164_transition004_000_sound
  exact h000

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
