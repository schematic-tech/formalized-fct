import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022.Chunk004

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition022_sound :
    TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 1139 := by
  have h000 : TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 256 := by simpa using config164_transition022_000_sound
  have h001 : TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 512 := by simpa using h000.concat config164_transition022_001_sound
  have h002 : TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 768 := by simpa using h001.concat config164_transition022_002_sound
  have h003 : TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 1024 := by simpa using h002.concat config164_transition022_003_sound
  have h004 : TransitionRangeSound config164Stage022Length config164Stage022Source config164Stage023Length config164Stage023Source config164Stage023Count (CpStep.rotate 10) 0 1139 := by simpa using h003.concat config164_transition022_004_sound
  exact h004

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
