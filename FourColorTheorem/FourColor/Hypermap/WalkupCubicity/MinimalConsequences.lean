import FourColorTheorem.FourColor.Hypermap.WalkupCubicity.ColorExtension
import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness

/-!
Minimal-counterexample consequences of the Walkup geometry and color extension.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

universe u

open Hypermap

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node
    (hgeom : WalkupTwoNodeGeometry.{u})
    (hext : WalkupTwoNodeColorExtension.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} := by
  intro G hG z hzz
  have hz_ne : G.node z ≠ z :=
    Hypermap.MinimalCounterexample.node_ne_self hG z
  have hsmall :
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).FourColorable :=
    hG.fourColorable_walkupE_walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
      (hgeom G hG z hz_ne hzz)
  exact hG.not_fourColorable (hext G hG z hz_ne hzz hsmall)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node
    (hgeom : WalkupTwoNodeGeometry.{u})
    (hext : WalkupTwoNodeColorExtension.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_noTwoNodeOrbits
    (noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node hgeom hext)

theorem cubicMinimalCounterexamples_of_walkup_two_node
    (hgeom : WalkupTwoNodeGeometry.{u})
    (hext : WalkupTwoNodeColorExtension.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_noShortNodeOrbits
    (noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node hgeom hext)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hext : WalkupTwoNodeColorExtension.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node
    (walkupTwoNodeGeometry_of_parts hparts) hext

theorem cubicMinimalCounterexamples_of_walkup_two_node_parts
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hext : WalkupTwoNodeColorExtension.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node
    (walkupTwoNodeGeometry_of_parts hparts) hext

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts_only
    (hparts : WalkupTwoNodeGeometryParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts hparts
    walkupTwoNodeColorExtension

theorem cubicMinimalCounterexamples_of_walkup_two_node_parts_only
    (hparts : WalkupTwoNodeGeometryParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_parts hparts
    walkupTwoNodeColorExtension

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
    (hparts : WalkupTwoNodePlanarPlainParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts_only
    (walkupTwoNodeGeometryParts_of_planarPlain hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (hparts : WalkupTwoNodePlanarEdgeInvolutionParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
    (walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (hparts : WalkupTwoNodePlanarEdgeExceptionalParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeCore
    (hparts : WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (walkupTwoNodePlanarEdgeExceptionalParts_of_core hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (hparts : WalkupTwoNodePlanarEdgeDegenerateParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeCore
    (walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planar
    (hparts : WalkupTwoNodePlanarParts.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (walkupTwoNodePlanarEdgeDegenerateParts_of_planar hparts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_genusNonincreasing
    (hle : WalkupEGenusNonincreasing.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planar
    (walkupTwoNodePlanarParts_of_genusNonincreasing hle)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_eulerDiff
    (hdiff : WalkupEEulerDiffNonincreasing.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_genusNonincreasing
    (walkupEGenusNonincreasing_of_eulerDiffNonincreasing hdiff)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_stepCountFormula
    (hcounts : WalkupEStepCountFormula.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_eulerDiff
    (walkupEEulerDiffNonincreasing_of_stepCountFormula hcounts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_stepCountFormula
    (walkupEStepCountFormula_of_nonEdgeFixedFormula hcounts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (hcounts : WalkupENonEdgeFixedCountFormula.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (walkupEStepCountNonEdgeFixedFormula_of_countFormula hcounts)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula hcounts)

theorem noTwoNodeOrbitsMinimalCounterexamples_proved :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    walkupENonEdgeNonSelfCountFormula_proved

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
    (hparts : WalkupTwoNodePlanarPlainParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_noTwoNodeOrbits
    (noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
      hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (hparts : WalkupTwoNodePlanarEdgeInvolutionParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
    (walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (hparts : WalkupTwoNodePlanarEdgeExceptionalParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeCore
    (hparts : WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (walkupTwoNodePlanarEdgeExceptionalParts_of_core hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (hparts : WalkupTwoNodePlanarEdgeDegenerateParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeCore
    (walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planar
    (hparts : WalkupTwoNodePlanarParts.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (walkupTwoNodePlanarEdgeDegenerateParts_of_planar hparts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_genusNonincreasing
    (hle : WalkupEGenusNonincreasing.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planar
    (walkupTwoNodePlanarParts_of_genusNonincreasing hle)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_eulerDiff
    (hdiff : WalkupEEulerDiffNonincreasing.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_genusNonincreasing
    (walkupEGenusNonincreasing_of_eulerDiffNonincreasing hdiff)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_stepCountFormula
    (hcounts : WalkupEStepCountFormula.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_eulerDiff
    (walkupEEulerDiffNonincreasing_of_stepCountFormula hcounts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_stepCountFormula
    (walkupEStepCountFormula_of_nonEdgeFixedFormula hcounts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (hcounts : WalkupENonEdgeFixedCountFormula.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (walkupEStepCountNonEdgeFixedFormula_of_countFormula hcounts)

theorem noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula hcounts)

theorem noShortNodeOrbitsMinimalCounterexamples_proved :
    NoShortNodeOrbitsMinimalCounterexamples.{u} :=
  noShortNodeOrbitsMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    walkupENonEdgeNonSelfCountFormula_proved

theorem cubicMinimalCounterexamples_of_walkup_two_node_planarPlain
    (hparts : WalkupTwoNodePlanarPlainParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_parts_only
    (walkupTwoNodeGeometryParts_of_planarPlain hparts)

theorem cubicMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (hparts : WalkupTwoNodePlanarEdgeInvolutionParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_planarPlain
    (walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution hparts)

theorem cubicMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (hparts : WalkupTwoNodePlanarEdgeExceptionalParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_planarEdgeInvolution
    (walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional hparts)

theorem cubicMinimalCounterexamples_of_walkup_two_node_edgeCore
    (hparts : WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_edgeExceptional
    (walkupTwoNodePlanarEdgeExceptionalParts_of_core hparts)

theorem cubicMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (hparts : WalkupTwoNodePlanarEdgeDegenerateParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_edgeCore
    (walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate hparts)

theorem cubicMinimalCounterexamples_of_walkup_two_node_planar
    (hparts : WalkupTwoNodePlanarParts.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_edgeDegenerate
    (walkupTwoNodePlanarEdgeDegenerateParts_of_planar hparts)

theorem cubicMinimalCounterexamples_of_walkup_genusNonincreasing
    (hle : WalkupEGenusNonincreasing.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_planar
    (walkupTwoNodePlanarParts_of_genusNonincreasing hle)

theorem cubicMinimalCounterexamples_of_walkup_eulerDiff
    (hdiff : WalkupEEulerDiffNonincreasing.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_genusNonincreasing
    (walkupEGenusNonincreasing_of_eulerDiffNonincreasing hdiff)

theorem cubicMinimalCounterexamples_of_walkup_stepCountFormula
    (hcounts : WalkupEStepCountFormula.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_eulerDiff
    (walkupEEulerDiffNonincreasing_of_stepCountFormula hcounts)

theorem cubicMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_stepCountFormula
    (walkupEStepCountFormula_of_nonEdgeFixedFormula hcounts)

theorem cubicMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (hcounts : WalkupENonEdgeFixedCountFormula.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_nonEdgeFixedStepCountFormula
    (walkupEStepCountNonEdgeFixedFormula_of_countFormula hcounts)

theorem cubicMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_nonEdgeFixedCountFormula
    (walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula hcounts)

theorem cubicMinimalCounterexamples_proved :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_nonEdgeNonSelfCountFormula
    walkupENonEdgeNonSelfCountFormula_proved

theorem plainCubicMinimalCounterexamples_proved :
    PlainCubicMinimalCounterexamples.{u} :=
  plainCubicMinimalCounterexamples_of_cubic
    cubicMinimalCounterexamples_proved

theorem no_minimalCounterexample_of_reducedBranches_walkup
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarPlainParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches
    hconnected
    (noShortNodeOrbitsMinimalCounterexamples_of_walkup_two_node_planarPlain
      hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupEdgeInvolution
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarEdgeInvolutionParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkup
    hconnected
    (walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupEdgeExceptional
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarEdgeExceptionalParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupEdgeInvolution
    hconnected
    (walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupEdgeCore
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupEdgeExceptional
    hconnected
    (walkupTwoNodePlanarEdgeExceptionalParts_of_core hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupEdgeDegenerate
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarEdgeDegenerateParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupEdgeCore
    hconnected
    (walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupPlanar
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hparts : WalkupTwoNodePlanarParts.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupEdgeDegenerate
    hconnected
    (walkupTwoNodePlanarEdgeDegenerateParts_of_planar hparts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupGenusNonincreasing
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hle : WalkupEGenusNonincreasing.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupPlanar
    hconnected
    (walkupTwoNodePlanarParts_of_genusNonincreasing hle)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupEulerDiff
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hdiff : WalkupEEulerDiffNonincreasing.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupGenusNonincreasing
    hconnected
    (walkupEGenusNonincreasing_of_eulerDiffNonincreasing hdiff)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupStepCountFormula
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcounts : WalkupEStepCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupEulerDiff
    hconnected
    (walkupEEulerDiffNonincreasing_of_stepCountFormula hcounts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeFixedStepCountFormula
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupStepCountFormula
    hconnected
    (walkupEStepCountFormula_of_nonEdgeFixedFormula hcounts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeFixedCountFormula
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcounts : WalkupENonEdgeFixedCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeFixedStepCountFormula
    hconnected
    (walkupEStepCountNonEdgeFixedFormula_of_countFormula hcounts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeFixedCountFormula
    hconnected
    (walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula hcounts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCoreCountFormula
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcounts : WalkupENonEdgeNonSelfCoreCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_coreCountFormula hcounts)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCrossSplit
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcross : WalkupENonEdgeNonSelfCrossCountFormula.{u})
    (hnoncross : WalkupENonEdgeNonSelfNonCrossCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_crossSplit hcross hnoncross)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfComponentEdgeOrbitSplit
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossComp : WalkupENonEdgeNonSelfNonCrossComponentCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit
      hcrossComp hcrossEdge hnoncrossComp hnoncrossEdge)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfComponentEdgeOrbitSplit_nonCrossComponent
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
      hcrossComp hcrossEdge hnoncrossEdge)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfComponentEdgeOrbitSplit_nonCrossSolved
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
      hcrossComp hcrossEdge)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCrossComponent
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected
    (walkupENonEdgeNonSelfCountFormula_of_crossComponent hcrossComp)
    heven hpentagonal hcap hexclusions hred

theorem no_minimalCounterexample_of_reducedBranches_walkupCounts
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : ValidHubDscore1LeFive.{u})
    (hexclusions : SevenPresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample :=
  no_minimalCounterexample_of_reducedBranches_walkupNonEdgeNonSelfCountFormula
    hconnected walkupENonEdgeNonSelfCountFormula_proved
    heven hpentagonal hcap hexclusions hred

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_coloring
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hext : WalkupTwoNodeColoringExtension.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts hparts
    (walkupTwoNodeColorExtension_of_coloringExtension hext)

theorem cubicMinimalCounterexamples_of_walkup_two_node_coloring
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hext : WalkupTwoNodeColoringExtension.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_parts hparts
    (walkupTwoNodeColorExtension_of_coloringExtension hext)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_local
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hlocal : WalkupTwoNodeColoringLocalCases.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_parts hparts
    (walkupTwoNodeColorExtension_of_localCases hlocal)

theorem cubicMinimalCounterexamples_of_walkup_two_node_local
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hlocal : WalkupTwoNodeColoringLocalCases.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_parts hparts
    (walkupTwoNodeColorExtension_of_localCases hlocal)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_faceClassEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hedges : WalkupTwoNodeFaceClassEdgeCases.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassEdgeCases hedges)

theorem cubicMinimalCounterexamples_of_walkup_two_node_faceClassEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hedges : WalkupTwoNodeFaceClassEdgeCases.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassEdgeCases hedges)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_faceClassExceptionalEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hexceptional : WalkupTwoNodeFaceClassExceptionalEdgeCases.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassExceptionalEdges
      hexceptional)

theorem cubicMinimalCounterexamples_of_walkup_two_node_faceClassExceptionalEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hexceptional : WalkupTwoNodeFaceClassExceptionalEdgeCases.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassExceptionalEdges
      hexceptional)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_faceClassCoreExceptionalEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hcore : WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassCoreExceptionalEdges hcore)

theorem cubicMinimalCounterexamples_of_walkup_two_node_faceClassCoreExceptionalEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hcore : WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassCoreExceptionalEdges hcore)

theorem noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_faceClassCoreDefaultEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hdefault : WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u}) :
    NoTwoNodeOrbitsMinimalCounterexamples.{u} :=
  noTwoNodeOrbitsMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassCoreDefaultEdges hdefault)

theorem cubicMinimalCounterexamples_of_walkup_two_node_faceClassCoreDefaultEdges
    (hparts : WalkupTwoNodeGeometryParts.{u})
    (hdefault : WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u}) :
    CubicMinimalCounterexamples.{u} :=
  cubicMinimalCounterexamples_of_walkup_two_node_coloring hparts
    (walkupTwoNodeColoringExtension_of_faceClassCoreDefaultEdges hdefault)

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
