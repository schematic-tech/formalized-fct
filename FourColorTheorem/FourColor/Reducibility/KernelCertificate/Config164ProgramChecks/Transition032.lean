import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk013
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk014
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk015
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk016
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk017
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk018
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk019
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk020
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk021
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032.Chunk022

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_transition032_sound :
    TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 5664 := by
  have h000 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 256 := by simpa using config164_transition032_000_sound
  have h001 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 512 := by simpa using h000.concat config164_transition032_001_sound
  have h002 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 768 := by simpa using h001.concat config164_transition032_002_sound
  have h003 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 1024 := by simpa using h002.concat config164_transition032_003_sound
  have h004 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 1280 := by simpa using h003.concat config164_transition032_004_sound
  have h005 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 1536 := by simpa using h004.concat config164_transition032_005_sound
  have h006 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 1792 := by simpa using h005.concat config164_transition032_006_sound
  have h007 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 2048 := by simpa using h006.concat config164_transition032_007_sound
  have h008 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 2304 := by simpa using h007.concat config164_transition032_008_sound
  have h009 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 2560 := by simpa using h008.concat config164_transition032_009_sound
  have h010 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 2816 := by simpa using h009.concat config164_transition032_010_sound
  have h011 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 3072 := by simpa using h010.concat config164_transition032_011_sound
  have h012 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 3328 := by simpa using h011.concat config164_transition032_012_sound
  have h013 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 3584 := by simpa using h012.concat config164_transition032_013_sound
  have h014 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 3840 := by simpa using h013.concat config164_transition032_014_sound
  have h015 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 4096 := by simpa using h014.concat config164_transition032_015_sound
  have h016 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 4352 := by simpa using h015.concat config164_transition032_016_sound
  have h017 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 4608 := by simpa using h016.concat config164_transition032_017_sound
  have h018 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 4864 := by simpa using h017.concat config164_transition032_018_sound
  have h019 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 5120 := by simpa using h018.concat config164_transition032_019_sound
  have h020 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 5376 := by simpa using h019.concat config164_transition032_020_sound
  have h021 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 5632 := by simpa using h020.concat config164_transition032_021_sound
  have h022 : TransitionRangeSound config164Stage032Length config164Stage032Source config164Stage033Length config164Stage033Source config164Stage033Count (CpStep.rotate 3) 0 5664 := by simpa using h021.concat config164_transition032_022_sound
  exact h022

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
