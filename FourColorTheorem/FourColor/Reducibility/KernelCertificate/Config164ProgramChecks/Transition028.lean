import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028.Chunk013

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition028_sound :
    TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 3560 := by
  have h000 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 256 := by simpa using config164_transition028_000_sound
  have h001 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 512 := by simpa using h000.concat config164_transition028_001_sound
  have h002 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 768 := by simpa using h001.concat config164_transition028_002_sound
  have h003 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 1024 := by simpa using h002.concat config164_transition028_003_sound
  have h004 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 1280 := by simpa using h003.concat config164_transition028_004_sound
  have h005 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 1536 := by simpa using h004.concat config164_transition028_005_sound
  have h006 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 1792 := by simpa using h005.concat config164_transition028_006_sound
  have h007 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 2048 := by simpa using h006.concat config164_transition028_007_sound
  have h008 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 2304 := by simpa using h007.concat config164_transition028_008_sound
  have h009 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 2560 := by simpa using h008.concat config164_transition028_009_sound
  have h010 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 2816 := by simpa using h009.concat config164_transition028_010_sound
  have h011 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 3072 := by simpa using h010.concat config164_transition028_011_sound
  have h012 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 3328 := by simpa using h011.concat config164_transition028_012_sound
  have h013 : TransitionRangeSound config164Stage028Length config164Stage028Source config164Stage029Length config164Stage029Source config164Stage029Count (CpStep.rotate 1) 0 3560 := by simpa using h012.concat config164_transition028_013_sound
  exact h013

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
