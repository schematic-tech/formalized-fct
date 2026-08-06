import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024.Chunk005

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition024_sound :
    TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 1430 := by
  have h000 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 256 := by simpa using config164_transition024_000_sound
  have h001 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 512 := by simpa using h000.concat config164_transition024_001_sound
  have h002 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 768 := by simpa using h001.concat config164_transition024_002_sound
  have h003 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 1024 := by simpa using h002.concat config164_transition024_003_sound
  have h004 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 1280 := by simpa using h003.concat config164_transition024_004_sound
  have h005 : TransitionRangeSound config164Stage024Length config164Stage024Source config164Stage025Length config164Stage025Source config164Stage025Count (CpStep.rotate 3) 0 1430 := by simpa using h004.concat config164_transition024_005_sound
  exact h005

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
