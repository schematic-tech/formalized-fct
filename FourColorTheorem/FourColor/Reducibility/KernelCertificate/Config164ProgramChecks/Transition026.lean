import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026.Chunk006

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition026_sound :
    TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 1780 := by
  have h000 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 256 := by simpa using config164_transition026_000_sound
  have h001 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 512 := by simpa using h000.concat config164_transition026_001_sound
  have h002 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 768 := by simpa using h001.concat config164_transition026_002_sound
  have h003 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 1024 := by simpa using h002.concat config164_transition026_003_sound
  have h004 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 1280 := by simpa using h003.concat config164_transition026_004_sound
  have h005 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 1536 := by simpa using h004.concat config164_transition026_005_sound
  have h006 : TransitionRangeSound config164Stage026Length config164Stage026Source config164Stage027Length config164Stage027Source config164Stage027Count (CpStep.rotate 4) 0 1780 := by simpa using h005.concat config164_transition026_006_sound
  exact h006

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
