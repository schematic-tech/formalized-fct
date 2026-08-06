import FourColorTheorem.FourColor.Configuration.Embedding
import FourColorTheorem.FourColor.Reducibility.CFContract
import FourColorTheorem.FourColor.Reducibility.Embedding
import FourColorTheorem.FourColor.Presentation.RedPartSoundness

/-!
Semantic exclusion of configuration preembeddings.

This is Coq `present.v`'s final use of `not_embed_reducible`, separated from
the executable 633-configuration certificate.  Keeping the semantic argument
here makes it cheap to elaborate: the certificate module only has to provide
`SemanticReducibilityTheConfigs`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CombinatorialFourColor

/-- Every listed configuration is semantically C-reducible. -/
def SemanticReducibilityTheConfigs : Prop :=
  ∀ ⦃cf : Config⦄, cf ∈ Config.theConfigs →
    cf.map.map.CReducible cf.reducibilityRingDarts cf.contractFinset

/-- Coq `present.v`'s call to `not_embed_reducible`, for every listed
configuration and in both target orientations. -/
theorem noConfigPreembeddingMinimalCounterexamples_of_semanticReducibility
    (hreducible : SemanticReducibilityTheConfigs) :
    Presentation.NoConfigPreembeddingMinimalCounterexamples := by
  intro G hG cf hmem x0G hvalid
  have hcf : cf.WellFormed := Config.wellFormed_of_mem_theConfigs hmem
  have hembeddable :
      cf.map.map.Embeddable cf.reducibilityRingDarts :=
    Config.embeddable_of_wellFormed_configQuiz_isQuizR
      hcf hvalid.rightRooted
  have hred :
      cf.map.map.CReducible
        cf.reducibilityRingDarts cf.contractFinset :=
    hreducible hmem
  have hkernel := Config.kernelSet_eq_kernel_reducibilityRingDarts hcf
  constructor
  · intro x0H hpre
    exact hembeddable.not_embed_reducible hG
      (by simpa only [← hkernel] using hpre) hred
  · intro x0H hpre
    exact hembeddable.not_embed_reducible hG.mirror
      (by simpa only [← hkernel] using hpre) hred

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
