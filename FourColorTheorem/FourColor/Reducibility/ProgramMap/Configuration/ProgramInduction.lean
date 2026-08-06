import FourColorTheorem.FourColor.Reducibility.ProgramMap.PrefixInjection

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap
namespace ConfigProgram

/-- Induction over the four forms admitted by `CProg.config`: rotations,
the terminal `Y`, nonterminal `Y`, and `H`. -/
theorem property_of_config
    (property : CProg → Prop)
    (rotate : ∀ {n cp}, CProg.config cp = true → property cp →
      property (CpStep.rotate n :: cp))
    (terminalY : property [CpStep.y])
    (y : ∀ {s cp}, CProg.config (s :: cp) = true → property (s :: cp) →
      property (CpStep.y :: s :: cp))
    (h : ∀ {cp}, CProg.config cp = true → property cp →
      property (CpStep.h :: cp)) :
    ∀ {cp}, CProg.config cp = true → property cp
  | [], hcfg => by simp [CProg.config] at hcfg
  | CpStep.rotate n :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      exact rotate htail
        (property_of_config property rotate terminalY y h htail)
  | CpStep.reverseRotate :: _cp, hcfg => by simp [CProg.config] at hcfg
  | CpStep.y :: [], _hcfg => terminalY
  | CpStep.y :: s :: cp, hcfg => by
      have htail : CProg.config (s :: cp) = true := by
        simpa [CProg.config] using hcfg
      exact y htail
        (property_of_config property rotate terminalY y h htail)
  | CpStep.h :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      exact h htail
        (property_of_config property rotate terminalY y h htail)
  | CpStep.u :: _cp, hcfg => by simp [CProg.config] at hcfg
  | CpStep.k :: _cp, hcfg => by simp [CProg.config] at hcfg
  | CpStep.a :: _cp, hcfg => by simp [CProg.config] at hcfg

end ConfigProgram
end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
