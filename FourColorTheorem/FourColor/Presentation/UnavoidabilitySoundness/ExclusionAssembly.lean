import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.SourceBounds

/-! Presentation exclusions and the final unavoidability contradiction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

/-- Named package for the seven presentation exclusions, corresponding to
`present5.v` through `present11.v`. -/
structure SevenPresentationExclusions : Prop where
  exclude5 : Presentation.ExcludedArity.{u} 5
  exclude6 : Presentation.ExcludedArity.{u} 6
  exclude7 : Presentation.ExcludedArity.{u} 7
  exclude8 : Presentation.ExcludedArity.{u} 8
  exclude9 : Presentation.ExcludedArity.{u} 9
  exclude10 : Presentation.ExcludedArity.{u} 10
  exclude11 : Presentation.ExcludedArity.{u} 11

theorem sevenPresentationExclusions_of_fullPartSucceeds
    (hpentagonal : ValidHubPentagonal.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    SevenPresentationExclusions.{u} where
  exclude5 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h5
  exclude6 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h6
  exclude7 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h7
  exclude8 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h8
  exclude9 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h9
  exclude10 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h10
  exclude11 :=
    Presentation.excludedArity_of_full_part_succeeds_of_pentagonal
      hpentagonal h11

theorem presentationExclusions_of_seven
    (h : SevenPresentationExclusions.{u}) :
    PresentationExclusions.{u} := by
  intro n hlo hhi
  have hn :
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
        n = 9 ∨ n = 10 ∨ n = 11 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.exclude5
  · exact h.exclude6
  · exact h.exclude7
  · exact h.exclude8
  · exact h.exclude9
  · exact h.exclude10
  · exact h.exclude11

theorem no_minimalCounterexample_of_decomposed_inputs
    (hexists : PositiveHubExists.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample
    (positiveHubInPresentationRange_of_bounds hexists hpentagonal hupper)
    (presentationExclusions_of_seven hexclusions)
    hred

theorem no_minimalCounterexample_of_eulerChargeFormula
    (heuler : EulerChargeFormulaForMinimalCounterexamples.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_decomposed_inputs
    (positiveHubExists_of_eulerChargeFormula heuler)
    hpentagonal hupper hexclusions hred

theorem no_minimalCounterexample_of_countFormula
    (hcounts : EulerCountFormulaForMinimalCounterexamples.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_eulerChargeFormula
    (eulerChargeFormula_of_countFormula hcounts)
    hpentagonal hupper hexclusions hred

theorem no_minimalCounterexample_of_structuralCountFacts
    (hstruct : StructuralCountFactsForMinimalCounterexamples.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_countFormula
    (eulerCountFormula_of_structuralCountFacts hstruct)
    hpentagonal hupper hexclusions hred

theorem no_minimalCounterexample_of_structuralParts
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcubic : CubicMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_structuralCountFacts
    (structuralCountFacts_of_parts hconnected hcubic heven)
    hpentagonal hupper hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_structuralParts
    hconnected
    (cubicMinimalCounterexamples_of_noShortNodeOrbits hshort)
    heven
    (validHubPentagonal_of_minimalCounterexamples hpentagonal)
    (validHubArityUpperBound_of_dscore1LeFive hcap)
    hexclusions hred

theorem no_minimalCounterexample_of_localBranches
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hcap : Dscore1LeFiveMinimalCounterexamples.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches
    hconnected hshortNode heven
    (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hshortFace)
    (validHubDscore1LeFive_of_minimalCounterexamples hcap)
    hexclusions hred

theorem no_minimalCounterexample_of_checkSoundBranches
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hred : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hsourceSound : SmallSourceCheckSound.{u})
    (hexclusions : SevenPresentationExclusions.{u}) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_localBranches
    hconnected hshortNode heven hshortFace
    (dscore1LeFiveMinimalCounterexamples_of_checkSound
      hredpart hsourceSound)
    hexclusions hred

theorem no_minimalCounterexample_of_redpartBranches
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hred : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hexclusions : SevenPresentationExclusions.{u}) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_localBranches
    hconnected hshortNode heven hshortFace
    (dscore1LeFiveMinimalCounterexamples_of_redpart hredpart)
    hexclusions hred

theorem no_minimalCounterexample_of_reducedBranchesAndPresentations
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches
    hconnected hshort heven hpentagonal hcap
    (sevenPresentationExclusions_of_fullPartSucceeds
      (validHubPentagonal_of_minimalCounterexamples hpentagonal)
      h5 h6 h7 h8 h9 h10 h11)
    hred

theorem no_minimalCounterexample_of_localBranchesAndPresentations
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hcap : Dscore1LeFiveMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_localBranches
    hconnected hshortNode heven hshortFace hcap
    (sevenPresentationExclusions_of_fullPartSucceeds
      (validHubPentagonal_of_minimalCounterexamples
        (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hshortFace))
      h5 h6 h7 h8 h9 h10 h11)
    hred

theorem no_minimalCounterexample_of_checkSoundBranchesAndPresentations
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hred : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hsourceSound : SmallSourceCheckSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_checkSoundBranches
    hconnected hshortNode heven hshortFace hred hredpart hsourceSound
    (sevenPresentationExclusions_of_fullPartSucceeds
      (validHubPentagonal_of_minimalCounterexamples
        (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hshortFace))
      h5 h6 h7 h8 h9 h10 h11)

theorem no_minimalCounterexample_of_redpartBranchesAndPresentations
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hshortNode : NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hshortFace : NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hred : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_redpartBranches
    hconnected hshortNode heven hshortFace hred hredpart
    (sevenPresentationExclusions_of_fullPartSucceeds
      (validHubPentagonal_of_minimalCounterexamples
        (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hshortFace))
      h5 h6 h7 h8 h9 h10 h11)

end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
