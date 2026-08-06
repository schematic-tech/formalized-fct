import FourColorTheorem.FourColor.Theorem.Combinatorial.HypermapReduction

/-! Unavoidability inputs yielding the absence of minimal counterexamples. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

/-- Final bridge from unavoidability inputs to the combinatorial hypermap
four-colour theorem. -/
theorem hypermapFourColor_of_unavoidability
    (hredMin : MinimalCounterexampleReduction.{u})
    (hpos : Unavoidability.PositiveHubInPresentationRange.{u})
    (hexcl : Unavoidability.PresentationExclusions.{u})
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (Unavoidability.no_minimalCounterexample hpos hexcl hredCert)

theorem hypermapFourColor_of_unavoidability_reduction
    (hpos : Unavoidability.PositiveHubInPresentationRange.{u})
    (hexcl : Unavoidability.PresentationExclusions.{u})
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (Unavoidability.no_minimalCounterexample hpos hexcl hredCert)

/-- Direct final bridge from the currently reduced unavoidability branches and
the seven presentation scripts to the hypermap four-colour theorem. -/
theorem noMinimalCounterexample_of_reducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshort : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  Unavoidability.no_minimalCounterexample_of_reducedBranchesAndPresentations
    hconnected hshort heven hpentagonal hcap
    h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_reducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshort : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_reducedBranchesAndPresentations
      hconnected hshort heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_reducedBranchesAndPresentations_reduction
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshort : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_reducedBranchesAndPresentations
      hconnected hshort heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem noMinimalCounterexample_of_walkupReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupTwoNodePlanarPlainParts.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_reducedBranchesAndPresentations
    hconnected
    (Unavoidability.noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupEdgeExceptionalReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupTwoNodePlanarEdgeExceptionalParts.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution
      (Unavoidability.walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional
        hwalkup))
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupEdgeCoreReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupEdgeExceptionalReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupTwoNodePlanarEdgeExceptionalParts_of_core hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupEdgeDegenerateReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupTwoNodePlanarEdgeDegenerateParts.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupEdgeCoreReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupPlanarReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupTwoNodePlanarParts.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupEdgeDegenerateReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupTwoNodePlanarEdgeDegenerateParts_of_planar hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupGenusReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupEGenusNonincreasing.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupPlanarReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupTwoNodePlanarParts_of_genusNonincreasing hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupEulerDiffReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupEEulerDiffNonincreasing.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupGenusReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupEGenusNonincreasing_of_eulerDiffNonincreasing
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupStepCountReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupEStepCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupEulerDiffReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupEEulerDiffNonincreasing_of_stepCountFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeFixedStepCountReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupEStepCountNonEdgeFixedFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupStepCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupEStepCountFormula_of_nonEdgeFixedFormula hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeFixedCountReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupENonEdgeFixedCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeFixedStepCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupEStepCountNonEdgeFixedFormula_of_countFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupENonEdgeNonSelfCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeFixedCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfCoreCountReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hwalkup : Unavoidability.WalkupENonEdgeNonSelfCoreCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfCrossSplitReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hcross : Unavoidability.WalkupENonEdgeNonSelfCrossCountFormula.{u})
    (hnoncross : Unavoidability.WalkupENonEdgeNonSelfNonCrossCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_crossSplit
      hcross hnoncross)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfComponentEdgeOrbitReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hcrossComp : Unavoidability.WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : Unavoidability.WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossEdge : Unavoidability.WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
      hcrossComp hcrossEdge hnoncrossEdge)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfComponentEdgeOrbitReducedBranchesAndPresentations_nonCrossSolved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hcrossComp : Unavoidability.WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : Unavoidability.WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
      hcrossComp hcrossEdge)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupNonEdgeNonSelfCrossComponentReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hcrossComp : Unavoidability.WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_crossComponent
      hcrossComp)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_walkupCountsReducedBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hconnected
    Unavoidability.walkupENonEdgeNonSelfCountFormula_proved
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_provedConnected_walkupCountsReducedBranchesAndPresentations
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupCountsReducedBranchesAndPresentations
    Unavoidability.connectedMinimalCounterexamples_proved
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_provedConnectedEven_walkupCountsReducedBranchesAndPresentations
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_provedConnected_walkupCountsReducedBranchesAndPresentations
    Unavoidability.evenGenusMinimalCounterexamples_proved
    hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_componentPlanar_walkupCountsReducedBranchesAndPresentations
    (hcomponentPlanar : Unavoidability.ComponentEulerPlanarInherited.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_walkupCountsReducedBranchesAndPresentations
    (Unavoidability.connectedMinimalCounterexamples_of_componentEulerPlanarInherited
      hcomponentPlanar)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_componentEulerDiffAdditive_walkupCountsReducedBranchesAndPresentations
    (hdiff : Unavoidability.ComponentEulerDiffAdditive.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_componentPlanar_walkupCountsReducedBranchesAndPresentations
    (Unavoidability.componentEulerPlanarInherited_of_eulerDiffAdditive hdiff)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_componentEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
    (hnonneg : Unavoidability.ComponentEulerDiffNonnegative.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_componentEulerDiffAdditive_walkupCountsReducedBranchesAndPresentations
    (Unavoidability.componentEulerDiffAdditive_of_nonnegative hnonneg)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_connectedEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
    (hconnDiff : Unavoidability.ConnectedEulerDiffNonnegative.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hcap : Unavoidability.ValidHubDscore1LeFive.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_componentEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
    (Unavoidability.componentEulerDiffNonnegative_of_connectedEulerDiffNonnegative
      hconnDiff)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert


end

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
