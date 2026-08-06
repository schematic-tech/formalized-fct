import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk013
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk014
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk015
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk016
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk017
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030.Chunk018

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition030_sound :
    TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 4612 := by
  have h000 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 256 := by simpa using config164_transition030_000_sound
  have h001 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 512 := by simpa using h000.concat config164_transition030_001_sound
  have h002 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 768 := by simpa using h001.concat config164_transition030_002_sound
  have h003 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 1024 := by simpa using h002.concat config164_transition030_003_sound
  have h004 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 1280 := by simpa using h003.concat config164_transition030_004_sound
  have h005 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 1536 := by simpa using h004.concat config164_transition030_005_sound
  have h006 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 1792 := by simpa using h005.concat config164_transition030_006_sound
  have h007 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 2048 := by simpa using h006.concat config164_transition030_007_sound
  have h008 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 2304 := by simpa using h007.concat config164_transition030_008_sound
  have h009 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 2560 := by simpa using h008.concat config164_transition030_009_sound
  have h010 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 2816 := by simpa using h009.concat config164_transition030_010_sound
  have h011 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 3072 := by simpa using h010.concat config164_transition030_011_sound
  have h012 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 3328 := by simpa using h011.concat config164_transition030_012_sound
  have h013 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 3584 := by simpa using h012.concat config164_transition030_013_sound
  have h014 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 3840 := by simpa using h013.concat config164_transition030_014_sound
  have h015 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 4096 := by simpa using h014.concat config164_transition030_015_sound
  have h016 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 4352 := by simpa using h015.concat config164_transition030_016_sound
  have h017 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 4608 := by simpa using h016.concat config164_transition030_017_sound
  have h018 : TransitionRangeSound config164Stage030Length config164Stage030Source config164Stage031Length config164Stage031Source config164Stage031Count (CpStep.rotate 11) 0 4612 := by simpa using h017.concat config164_transition030_018_sound
  exact h018

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
