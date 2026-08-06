import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk013
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk014
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk015
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk016
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk017
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk018
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk019
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk020
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk021
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk022
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk023
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk024
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk025
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks.Final.Chunk026

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

theorem config164_final_sound
    (hsound : Config164SourceSound 67325) :
    FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 6908 := by
  have h000 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 256 := by simpa using config164_final_000_sound hsound
  have h001 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 512 := by simpa using h000.concat (config164_final_001_sound hsound)
  have h002 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 768 := by simpa using h001.concat (config164_final_002_sound hsound)
  have h003 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 1024 := by simpa using h002.concat (config164_final_003_sound hsound)
  have h004 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 1280 := by simpa using h003.concat (config164_final_004_sound hsound)
  have h005 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 1536 := by simpa using h004.concat (config164_final_005_sound hsound)
  have h006 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 1792 := by simpa using h005.concat (config164_final_006_sound hsound)
  have h007 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 2048 := by simpa using h006.concat (config164_final_007_sound hsound)
  have h008 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 2304 := by simpa using h007.concat (config164_final_008_sound hsound)
  have h009 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 2560 := by simpa using h008.concat (config164_final_009_sound hsound)
  have h010 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 2816 := by simpa using h009.concat (config164_final_010_sound hsound)
  have h011 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 3072 := by simpa using h010.concat (config164_final_011_sound hsound)
  have h012 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 3328 := by simpa using h011.concat (config164_final_012_sound hsound)
  have h013 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 3584 := by simpa using h012.concat (config164_final_013_sound hsound)
  have h014 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 3840 := by simpa using h013.concat (config164_final_014_sound hsound)
  have h015 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 4096 := by simpa using h014.concat (config164_final_015_sound hsound)
  have h016 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 4352 := by simpa using h015.concat (config164_final_016_sound hsound)
  have h017 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 4608 := by simpa using h016.concat (config164_final_017_sound hsound)
  have h018 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 4864 := by simpa using h017.concat (config164_final_018_sound hsound)
  have h019 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 5120 := by simpa using h018.concat (config164_final_019_sound hsound)
  have h020 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 5376 := by simpa using h019.concat (config164_final_020_sound hsound)
  have h021 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 5632 := by simpa using h020.concat (config164_final_021_sound hsound)
  have h022 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 5888 := by simpa using h021.concat (config164_final_022_sound hsound)
  have h023 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 6144 := by simpa using h022.concat (config164_final_023_sound hsound)
  have h024 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 6400 := by simpa using h023.concat (config164_final_024_sound hsound)
  have h025 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 6656 := by simpa using h024.concat (config164_final_025_sound hsound)
  have h026 : FinalRangeSound config164Boundary config164Stage034Length config164Stage034Source 0 6908 := by simpa using h025.concat (config164_final_026_sound hsound)
  exact h026

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
