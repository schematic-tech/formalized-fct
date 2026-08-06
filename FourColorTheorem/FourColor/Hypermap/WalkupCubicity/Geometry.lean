import FourColorTheorem.FourColor.Hypermap.WalkupMinimal
import FourColorTheorem.FourColor.Hypermap.WalkupColoring
import Schematic.Math.GraphTheory.Embedding.WalkupPlanarity

/-!
Walkup bridge for cubicity of minimal counterexamples.

This file isolates the two remaining geometric/coloring obligations in the
Coq proof of `minimal_counter_example_is_cubic`.  Once a two-node orbit is
assumed at `z`, minimality colours the twice-deleted Walkup map.  The remaining
local theorem must then extend that colouring back over the two deleted darts,
contradicting non-colourability of the original minimal counterexample.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Unavoidability

universe u

open Hypermap

/-- Geometry target for the twice-deleted Walkup map in the period-two node
case of Coq `minimal_counter_example_is_cubic`. -/
def WalkupTwoNodeGeometry : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      (((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
          Hypermap).PlanarBridgelessPlainPrecubic

/-- The actual geometry obligations left for the twice-deleted Walkup map:
planarity, bridgelessness, and plainness.  Precubicity is supplied by
`walkupE_walkupE_precubic`. -/
def WalkupTwoNodeGeometryParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      (((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
          Hypermap).EulerPlanar ∧
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
            Hypermap).Bridgeless ∧
          (((G.walkupE z).walkupE
            (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
              Hypermap).Plain

/-- Reduced geometry obligations for the two-node Walkup map.  Bridgelessness
is supplied by `walkupE_walkupE_bridgeless_of_node_node_eq`. -/
def WalkupTwoNodePlanarPlainParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      (((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
          Hypermap).EulerPlanar ∧
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) :
            Hypermap).Plain

/-- Further reduced geometry obligations: planarity plus edge involutivity.
The fixed-point-free half of plainness follows from the bridgelessness already
proved for the twice-deleted Walkup map. -/
def WalkupTwoNodePlanarEdgeInvolutionParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      let H := ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart))
      H.EulerPlanar ∧
        ∀ w : H.Dart, H.edge (H.edge w) = w

/-- Exceptional edge positions left after the generic two-node Walkup
edge-involution transport.  Away from these equalities,
`walkupE_walkupE_liftTwoNode_edge_edge_eq_of_plain_of_ne` proves the
involutivity equation automatically. -/
def WalkupTwoNodeEdgeInvolutionExceptional
    (G : Hypermap.{u}) (z x : G.Dart) : Prop :=
  x = G.edge z ∨
    G.edge x = z ∨
      G.edge x = G.node z ∨
        G.edge z = G.node z ∨
          G.face (G.edge x) = G.node z ∨
            G.face x = G.node z

/-- Smaller exceptional set for edge involutivity after using plainness and
the period-two node hypothesis. -/
def WalkupTwoNodeEdgeInvolutionCoreExceptional
    (G : Hypermap.{u}) (z x : G.Dart) : Prop :=
  x = G.edge z ∨
    x = G.edge (G.node z) ∨
      G.edge z = G.node z

theorem walkupTwoNodeEdgeInvolutionExceptional_core_of_plain
    {G : Hypermap.{u}} (hplain : G.Plain)
    {z x : G.Dart}
    (hxz : x ≠ z)
    (hzz : G.node (G.node z) = z)
    (hex : WalkupTwoNodeEdgeInvolutionExceptional G z x) :
    WalkupTwoNodeEdgeInvolutionCoreExceptional G z x := by
  rcases hex with hx | hx | hx | hx | hx | hx
  · exact Or.inl hx
  · exact Or.inl (Plain.eq_edge_of_edge_eq (G := G) hplain hx)
  · exact Or.inr (Or.inl
      (Plain.eq_edge_of_edge_eq (G := G) hplain hx))
  · exact Or.inr (Or.inr hx)
  · exfalso
    apply hxz
    calc
      x = G.node (G.face (G.edge x)) := (G.node_face_edge x).symm
      _ = G.node (G.node z) := by rw [hx]
      _ = z := hzz
  · exact Or.inl
      (Plain.eq_edge_of_edge_eq (G := G) hplain
        (by
          calc
            G.edge x = G.node (G.face x) :=
              (Plain.node_face_eq_edge (G := G) hplain x).symm
            _ = G.node (G.node z) := by rw [hx]
            _ = z := hzz))

/-- Reduced edge-involution target: planarity plus the finite exceptional
positions for darts that survive the two deletions. -/
def WalkupTwoNodePlanarEdgeExceptionalParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      let H := ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart))
      H.EulerPlanar ∧
        ∀ (x : G.Dart) (hxz : x ≠ z) (hxnode : x ≠ G.node z),
          WalkupTwoNodeEdgeInvolutionExceptional G z x →
            H.edge (H.edge
              (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) =
              G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode

/-- Reduced edge-involution target with the smaller core exceptional set. -/
def WalkupTwoNodePlanarEdgeCoreExceptionalParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      let H := ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart))
      H.EulerPlanar ∧
        ∀ (x : G.Dart) (hxz : x ≠ z) (hxnode : x ≠ G.node z),
          WalkupTwoNodeEdgeInvolutionCoreExceptional G z x →
            H.edge (H.edge
              (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) =
              G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode

/-- Further reduced edge-involution target: the swapped surviving darts
`edge z` and `edge (node z)` are now proved directly, so only the degenerate
local equality `edge z = node z` remains. -/
def WalkupTwoNodePlanarEdgeDegenerateParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      let H := ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart))
      H.EulerPlanar ∧
        (G.edge z = G.node z →
          ∀ (x : G.Dart) (hxz : x ≠ z) (hxnode : x ≠ G.node z),
            H.edge (H.edge
              (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) =
              G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)

/-- Final reduced geometry obligation for the twice-deleted Walkup map in the
two-node case.  Plainness and bridgelessness are now derived in Lean; only
Euler-planarity remains. -/
def WalkupTwoNodePlanarParts : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      let H := ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart))
      H.EulerPlanar


theorem walkupEGenusNonincreasing_of_nonEdgeFixedStepCountFormula
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_stepCountFormula
    (walkupEStepCountFormula_of_nonEdgeFixedFormula hcounts)

theorem walkupEGenusNonincreasing_of_nonEdgeFixedCountFormula
    (hcounts : WalkupENonEdgeFixedCountFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_nonEdgeFixedStepCountFormula
    (walkupEStepCountNonEdgeFixedFormula_of_countFormula hcounts)

theorem walkupEGenusNonincreasing_of_nonEdgeNonSelfCountFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_nonEdgeFixedCountFormula
    (walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula hcounts)

theorem walkupEGenusNonincreasing_of_nonEdgeNonSelfCoreCountFormula
    (hcounts : WalkupENonEdgeNonSelfCoreCountFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_nonEdgeNonSelfCountFormula
    (walkupENonEdgeNonSelfCountFormula_of_coreCountFormula hcounts)

theorem walkupEGenusNonincreasing_of_nonEdgeNonSelfCrossSplit
    (hcross : WalkupENonEdgeNonSelfCrossCountFormula.{u})
    (hnoncross : WalkupENonEdgeNonSelfNonCrossCountFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_nonEdgeNonSelfCountFormula
    (walkupENonEdgeNonSelfCountFormula_of_crossSplit hcross hnoncross)

theorem walkupTwoNodePlanarParts_of_genusNonincreasing
    (hle : WalkupEGenusNonincreasing.{u}) :
    WalkupTwoNodePlanarParts.{u} := by
  intro G hG z hz_ne _hzz
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  have h₁ : (G.walkupE z).genus ≤ G.genus := hle G z
  have h₂ : ((G.walkupE z).walkupE u).genus ≤
      (G.walkupE z).genus := hle (G.walkupE z) u
  exact G.walkupE_walkupE_eulerPlanar_of_genus_le h₁ h₂ hG.planar

theorem walkupTwoNodePlanarEdgeDegenerateParts_of_planar
    (hplanar : WalkupTwoNodePlanarParts.{u}) :
    WalkupTwoNodePlanarEdgeDegenerateParts.{u} := by
  intro G hG z hz_ne hzz
  refine ⟨hplanar G hG z hz_ne hzz, ?_⟩
  intro hedgeNode x hxz hxnode
  exact G.walkupE_walkupE_edge_edge_of_plain_of_edge_eq_node
    hG.plain hz_ne hedgeNode
    (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)

theorem walkupTwoNodePlanarEdgeCoreExceptionalParts_of_degenerate
    (hdegenerate : WalkupTwoNodePlanarEdgeDegenerateParts.{u}) :
    WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u} := by
  intro G hG z hz_ne hzz
  rcases hdegenerate G hG z hz_ne hzz with ⟨hplanar, hdegenerateEdge⟩
  refine ⟨hplanar, ?_⟩
  intro x hxz hxnode hcore
  by_cases hedgeNodeEq : G.edge z = G.node z
  · exact hdegenerateEdge hedgeNodeEq x hxz hxnode
  · rcases hcore with hx | hx | hx
    · subst x
      simpa using
        G.walkupE_walkupE_liftTwoNode_edge_edge_eq_edge_z
          hG.plain hz_ne hzz hedgeNodeEq
    · subst x
      simpa using
        G.walkupE_walkupE_liftTwoNode_edge_edge_eq_edge_node
          hG.plain hz_ne hzz hedgeNodeEq
    · exact False.elim (hedgeNodeEq hx)

theorem walkupTwoNodePlanarEdgeExceptionalParts_of_core
    (hcore : WalkupTwoNodePlanarEdgeCoreExceptionalParts.{u}) :
    WalkupTwoNodePlanarEdgeExceptionalParts.{u} := by
  intro G hG z hz_ne hzz
  rcases hcore G hG z hz_ne hzz with ⟨hplanar, hedgeCore⟩
  exact ⟨hplanar, fun x hxz hxnode hex =>
    hedgeCore x hxz hxnode
      (walkupTwoNodeEdgeInvolutionExceptional_core_of_plain
        hG.plain hxz hzz hex)⟩

theorem walkupTwoNodePlanarEdgeInvolutionParts_of_edgeExceptional
    (hparts : WalkupTwoNodePlanarEdgeExceptionalParts.{u}) :
    WalkupTwoNodePlanarEdgeInvolutionParts.{u} := by
  intro G hG z hz_ne hzz
  rcases hparts G hG z hz_ne hzz with ⟨hplanar, hedgeExceptional⟩
  refine ⟨hplanar, ?_⟩
  intro w
  let x : G.Dart := w.1.1
  have hxz : x ≠ z := w.1.2
  have hxnode : x ≠ G.node z := by
    intro hbad
    exact w.2 (Subtype.ext hbad)
  have hw :
      G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode = w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  classical
  by_cases hex : WalkupTwoNodeEdgeInvolutionExceptional G z x
  · simpa [hw] using hedgeExceptional x hxz hxnode hex
  · have hnot := hex
    simp only [WalkupTwoNodeEdgeInvolutionExceptional, not_or] at hnot
    rcases hnot with
      ⟨hxedgez, hexz, hexnode, hedgeNode, hfaceEdgeNode, hfaceNode⟩
    simpa [hw] using
      G.walkupE_walkupE_liftTwoNode_edge_edge_eq_of_plain_of_ne
        hG.plain hz_ne hxz hxnode hxedgez hexz hexnode
        hedgeNode hfaceEdgeNode hfaceNode

theorem walkupTwoNodePlanarPlainParts_of_planarEdgeInvolution
    (hparts : WalkupTwoNodePlanarEdgeInvolutionParts.{u}) :
    WalkupTwoNodePlanarPlainParts.{u} := by
  intro G hG z hz_ne hzz
  rcases hparts G hG z hz_ne hzz with ⟨hplanar, hedge₂⟩
  let H := (G.walkupE z).walkupE
    (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  have hbridgeless : H.Bridgeless :=
    G.walkupE_walkupE_bridgeless_of_node_node_eq
      hG.bridgeless hz_ne hzz
  exact ⟨hplanar, fun w =>
    ⟨hedge₂ w, Bridgeless.edge_ne_self (G := H) hbridgeless w⟩⟩

theorem walkupTwoNodeGeometryParts_of_planarPlain
    (hparts : WalkupTwoNodePlanarPlainParts.{u}) :
    WalkupTwoNodeGeometryParts.{u} := by
  intro G hG z hz_ne hzz
  rcases hparts G hG z hz_ne hzz with ⟨hplanar, hplain⟩
  exact ⟨hplanar,
    G.walkupE_walkupE_bridgeless_of_node_node_eq
      hG.bridgeless hz_ne hzz,
    hplain⟩

theorem walkupTwoNodeGeometry_of_parts
    (hparts : WalkupTwoNodeGeometryParts.{u}) :
    WalkupTwoNodeGeometry.{u} := by
  intro G hG z hz_ne hzz
  rcases hparts G hG z hz_ne hzz with ⟨hplanar, hbridgeless, hplain⟩
  exact G.walkupE_walkupE_planarBridgelessPlainPrecubic_of_parts
    hG.precubic (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
    hplanar hbridgeless hplain

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
