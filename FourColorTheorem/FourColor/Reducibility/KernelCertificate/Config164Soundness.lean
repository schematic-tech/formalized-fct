import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramSoundness

/-! Kernel-checked reducibility certificate for configuration 164. -/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

/-- Configuration 164 is semantically C-reducible. -/
theorem config164_reducible :
    Config.cf164.map.map.CReducible
      Config.cf164.reducibilityRingDarts Config.cf164.contractFinset := by
  apply cReducible_of_contractTree_coclosure config164_contractTree
  intro et hmem
  apply config164_contractSpec_sound config164_source_sound
  exact (CProg.cpColor_mem_iff_general config164ContractProgram et).1 hmem

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
