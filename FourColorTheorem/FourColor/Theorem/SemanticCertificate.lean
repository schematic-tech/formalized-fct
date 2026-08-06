import FourColorTheorem.FourColor.Theorem.Presentations
import FourColorTheorem.FourColor.Reducibility.NoConfigPreembedding

/-!
The final semantic boundary of the executable four-colour certificate.

This module deliberately does not import the 0--633 job chain.  It proves the
hypermap theorem from the two propositions discharged by that chain: the
presentation check and semantic C-reducibility of every listed configuration.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

/-- The universe-zero hypermap four-colour theorem from the two semantic
outputs of the executable 633-configuration certificate. -/
theorem hypermapFourColorTheorem_zero_of_certificates
    (hchecked : Presentation.Reducibility)
    (hreducible : SemanticReducibilityTheConfigs) :
    HypermapFourColorTheorem.{0} :=
  hypermapFourColor_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
    Birkhoff.noShortFaceOrbitsMinimalCounterexamples_proved
    Presentation.configQuizSourceValidTheConfigs
    (noConfigPreembeddingMinimalCounterexamples_of_semanticReducibility
      hreducible)
    hchecked

/-- The hypermap four-colour theorem in any universe from the two semantic
outputs of the executable certificate. -/
theorem hypermapFourColorTheorem_of_certificates
    (hchecked : Presentation.Reducibility)
    (hreducible : SemanticReducibilityTheConfigs) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColorTheorem_of_zero
    (hypermapFourColorTheorem_zero_of_certificates hchecked hreducible)

end


end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
