import FourColorTheorem.FourColor.Theorem.Combinatorial.NoMinimalCounterexample

/-! Four-colour conclusions with an explicit minimal-counterexample reduction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

theorem hypermapFourColor_of_walkupReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupEdgeExceptionalReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupEdgeExceptionalReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupEdgeCoreReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupEdgeCoreReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupEdgeDegenerateReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupEdgeDegenerateReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupPlanarReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupPlanarReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupGenusReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupGenusReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupEulerDiffReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupEulerDiffReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupStepCountReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupStepCountReducedBranchesAndPresentations
      hconnected hwalkup heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_walkupNonEdgeFixedStepCountReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupStepCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupEStepCountFormula_of_nonEdgeFixedFormula hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeFixedCountReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeFixedStepCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupEStepCountNonEdgeFixedFormula_of_countFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeFixedCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfCoreCountReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
      hwalkup)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfCrossSplitReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_crossSplit
      hcross hnoncross)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfComponentEdgeOrbitReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
      hcrossComp hcrossEdge hnoncrossEdge)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfComponentEdgeOrbitReducedBranchesAndPresentations_nonCrossSolved
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
      hcrossComp hcrossEdge)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupNonEdgeNonSelfCrossComponentReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_walkupNonEdgeNonSelfCountReducedBranchesAndPresentations
    hredMin hconnected
    (Unavoidability.walkupENonEdgeNonSelfCountFormula_of_crossComponent
      hcrossComp)
    heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_walkupCountsReducedBranchesAndPresentations
      hconnected heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_provedConnected_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    (noMinimalCounterexample_of_provedConnected_walkupCountsReducedBranchesAndPresentations
      heven hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_provedConnectedEven_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    (noMinimalCounterexample_of_provedConnectedEven_walkupCountsReducedBranchesAndPresentations
      hpentagonal hcap h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_componentPlanar_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_componentPlanar_walkupCountsReducedBranchesAndPresentations
      hcomponentPlanar heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_componentEulerDiffAdditive_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_componentEulerDiffAdditive_walkupCountsReducedBranchesAndPresentations
      hdiff heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_componentEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_componentEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
      hnonneg heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_connectedEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
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
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_connectedEulerDiffNonnegative_walkupCountsReducedBranchesAndPresentations
      hconnDiff heven hpentagonal hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)


end

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
