import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164SourceSoundness
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramData.Stage000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition013
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition014
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition015
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition016
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition017
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition018
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition019
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition020
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition021
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition022
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition023
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition024
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition025
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition026
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition027
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition028
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition029
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition030
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition031
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition032
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Transition033

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_programFold_sound
    (hsound : Config164SourceSound 67325) :
    SourceFoldSound (TargetCoclosure config164Boundary)
      config164Stage000Length config164Stage000Source
      config164Stage000Count config164ReplayProgram := by
  have h034 := (config164_final_sound hsound).sourceFoldSound
  have h033 := SourceFoldSound.step config164_transition033_sound h034
  have h032 := SourceFoldSound.step config164_transition032_sound h033
  have h031 := SourceFoldSound.step config164_transition031_sound h032
  have h030 := SourceFoldSound.step config164_transition030_sound h031
  have h029 := SourceFoldSound.step config164_transition029_sound h030
  have h028 := SourceFoldSound.step config164_transition028_sound h029
  have h027 := SourceFoldSound.step config164_transition027_sound h028
  have h026 := SourceFoldSound.step config164_transition026_sound h027
  have h025 := SourceFoldSound.step config164_transition025_sound h026
  have h024 := SourceFoldSound.step config164_transition024_sound h025
  have h023 := SourceFoldSound.step config164_transition023_sound h024
  have h022 := SourceFoldSound.step config164_transition022_sound h023
  have h021 := SourceFoldSound.step config164_transition021_sound h022
  have h020 := SourceFoldSound.step config164_transition020_sound h021
  have h019 := SourceFoldSound.step config164_transition019_sound h020
  have h018 := SourceFoldSound.step config164_transition018_sound h019
  have h017 := SourceFoldSound.step config164_transition017_sound h018
  have h016 := SourceFoldSound.step config164_transition016_sound h017
  have h015 := SourceFoldSound.step config164_transition015_sound h016
  have h014 := SourceFoldSound.step config164_transition014_sound h015
  have h013 := SourceFoldSound.step config164_transition013_sound h014
  have h012 := SourceFoldSound.step config164_transition012_sound h013
  have h011 := SourceFoldSound.step config164_transition011_sound h012
  have h010 := SourceFoldSound.step config164_transition010_sound h011
  have h009 := SourceFoldSound.step config164_transition009_sound h010
  have h008 := SourceFoldSound.step config164_transition008_sound h009
  have h007 := SourceFoldSound.step config164_transition007_sound h008
  have h006 := SourceFoldSound.step config164_transition006_sound h007
  have h005 := SourceFoldSound.step config164_transition005_sound h006
  have h004 := SourceFoldSound.step config164_transition004_sound h005
  have h003 := SourceFoldSound.step config164_transition003_sound h004
  have h002 := SourceFoldSound.step config164_transition002_sound h003
  have h001 := SourceFoldSound.step config164_transition001_sound h002
  have h000 := SourceFoldSound.step config164_transition000_sound h001
  simpa [config164ReplayProgram] using h000

theorem config164_contractSpec_sound
    (hsound : Config164SourceSound 67325)
    {et : ColSeq} (hspec : CProg.cpColorSpec config164ContractProgram et) :
    Chromogram.KempeCoclosure config164Boundary (ColSeq.ctrace et) := by
  have hproper : ColSeq.ProperTrace et :=
    ((ColSeq.not_mem_zero_ttail_iff et).1
      (CProg.cpColorSpec_ttail_not_mem_zero hspec)).1
  have hfoldSpec : CProg.cpColorFoldSpec config164ReplayProgram
      [Color.one, Color.two, Color.three] (ColSeq.ttail et) := by
    unfold CProg.cpColorSpec at hspec
    rw [config164_contractProgram_reverse] at hspec
    exact hspec
  have htarget := config164_programFold_sound hsound
    0 21 (by decide) (by decide) (ColSeq.ttail et) hfoldSpec
  exact htarget et hproper rfl

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
