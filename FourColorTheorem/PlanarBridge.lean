import Schematic.Math.GraphTheory.Planarity.Basic
import FourColorTheorem.FourColor.Theorem.CubeBridge
import FourColorTheorem.FourColor.Theorem.SimpleGraphBridge
import FourColorTheorem.FourColor.Theorem.RotationSystemBridge
import Schematic.Math.GraphTheory.Embedding.Kuratowski
import Schematic.Math.GraphTheory.Embedding.WagnerGeneral

/-!
The graph-planarity to hypermap bridge boundary.

`Schematic.Math.GraphTheory.Planarity.Basic` defines planarity by excluding strict subdivisions
of `K5` and `K3,3`.  The four-colour development proves a hypermap theorem.
This file isolates the exact theorem needed to connect those worlds while
keeping the import graph acyclic: it imports the core planarity API and the
small graph-colouring transfer interface, not the final theorem wrapper.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

universe u v

namespace FourColor

/-- The Kuratowski/embedding/discretization bridge in one precise statement:
every finite simple graph satisfying the repository's
Kuratowski-style `IsPlanar` predicate admits a concrete hypermap bridge. -/
def KuratowskiHypermapBridgeTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsPlanar G → HasHypermapBridge.{u, v} G

/-- Rocq-facing bridge: every finite simple graph satisfying the
repository's Kuratowski-style `IsPlanar` predicate admits a representation by
an arbitrary planar bridgeless hypermap.  The `cube` layer then converts this
to the local plain/precubic theorem surface. -/
def KuratowskiPlanarHypermapBridgeTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsPlanar G → HasPlanarHypermapBridge.{u, v} G

/-- Rotation-system form of the bridge.  This is closer to a
constructive Kuratowski/embedding theorem: from the current strict-subdivision
planarity predicate, construct a graph rotation system whose dual hypermap has
the geometry required by the local hypermap four-colour theorem. -/
def KuratowskiRotationSystemTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      IsPlanar G →
        Exists fun R : RotationSystem G =>
          (R.toHypermap).dual.PlanarBridgelessPlainPrecubic

/-- Rotation-system form matching Coq before cubification: construct a
rotation system whose dual hypermap is planar and bridgeless. -/
def KuratowskiPlanarRotationSystemTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      IsPlanar G →
        Exists fun R : RotationSystem G =>
          (R.toHypermap).dual.PlanarBridgeless

/-- The reduced rotation-system form of the Kuratowski/embedding bridge.  For
finite simple graphs, bridgelessness of the dual oriented-edge
hypermap is automatic, so the embedding theorem only has to produce a rotation
system whose dual has Euler genus zero. -/
def KuratowskiEulerRotationSystemTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj],
      IsPlanar G → HasEulerRotationSystem G

/-- Unconditional strict-Kuratowski-to-rotation-system theorem, obtained by
the complete Coq `wagner` separator/contraction induction. -/
theorem kuratowskiEulerRotationSystem :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ hplanar
  exact WagnerGeneral.hasEulerRotationSystem_of_isPlanar hplanar

theorem kuratowskiEulerRotationSystem_of_cofacialDeletionSource
    (hsource : CofacialDeletionSourceTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSource
    hsource h_planar

theorem kuratowskiEulerRotationSystem_of_cofacialDeletionExtension
    (hext : CofacialDeletionExtensionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionExtension
    hext h_planar

theorem kuratowskiEulerRotationSystem_of_cofacialDeletionObstruction
    (hobstruction : CofacialDeletionObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstruction
    hobstruction h_planar

theorem kuratowskiEulerRotationSystem_of_cofacialDeletionObstructionWithContraction
    (hobstruction : CofacialDeletionObstructionWithContractionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionObstructionWithContraction
    hobstruction h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_blockProduction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hblock : DeleteEdgeEndsBlockProductionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForces_blockProduction
    htheta hblock h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_spanningCycles
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForces_spanningCycles
    htheta hcycles h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForcesWithContraction_spanningCycles
    (htheta : CofacialDeletionThetaForcesWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForcesWithContraction_spanningCycles
    htheta hcycles h_planar

theorem kuratowskiEulerRotationSystem_of_thetaDartsWithContraction_spanningCycles
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaDartsWithContraction_spanningCycles
    hdarts hcycles h_planar

theorem kuratowskiEulerRotationSystem_of_thetaDartsWithContraction_noncutAttachCycles
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact
    hasEulerRotationSystem_of_isPlanar_of_thetaDartsWithContraction_noncutAttachCycles
      hdarts hcycles h_planar

theorem kuratowskiEulerRotationSystem_of_thetaEmbeddingWithContraction_noncutAttachCycles
    (hembed : CofacialDeletionThetaEmbeddingWithContractionTheorem.{u})
    (hcycles : DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact
    hasEulerRotationSystem_of_isPlanar_of_thetaEmbeddingWithContraction_noncutAttachCycles
      hembed hcycles h_planar

/-- Current graph-side theorem specialized into the bridge wrapper.  The only
remaining input is the theta-darts/cofacial theorem. -/
theorem kuratowskiEulerRotationSystem_of_thetaDartsWithContraction
    (hdarts : CofacialDeletionThetaDartsWithContractionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} :=
  kuratowskiEulerRotationSystem_of_thetaDartsWithContraction_noncutAttachCycles
    hdarts deleteEdgeEnds_noncutAttachCycles_obstruction

/-- Preferred graph-side specialization of the bridge wrapper.  The remaining
input is the contraction-drawing theta embedding theorem; the graph-side
block/cactus theorem has been proved. -/
theorem kuratowskiEulerRotationSystem_of_thetaEmbeddingWithContraction
    (hembed : CofacialDeletionThetaEmbeddingWithContractionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} :=
  kuratowskiEulerRotationSystem_of_thetaEmbeddingWithContraction_noncutAttachCycles
    hembed deleteEdgeEnds_noncutAttachCycles_obstruction

/-- Reference-faithful specialization: the topology theorem receives both
the contraction embedding and the recursively available family of proper
edge-deletion embeddings used in the published gluing argument. -/
theorem kuratowskiEulerRotationSystem_of_referenceThetaEmbedding
    (hembed : CofacialDeletionThetaEmbeddingReferenceTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact
    hasEulerRotationSystem_of_isPlanar_of_referenceThetaEmbedding_noncutAttachCycles
      hembed deleteEdgeEnds_noncutAttachCycles_obstruction h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_degreeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeTwo
    htheta hdegree h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_degreeTwoObstruction
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree : DeleteEdgeEndsDegreeTwoObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeTwoObstruction
    htheta hdegree h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_degreeLeTwo_noLow
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hnolow : DeleteEdgeEndsNoLowDegreeObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo_noLow
    htheta hdegree_le hnolow h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u})
    (hlow : DeleteEdgeEndsLowDegreeForcesCofacialTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact
    hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo_lowDegreeForcesCofacial
      htheta hdegree_le hlow h_planar

theorem kuratowskiEulerRotationSystem_of_thetaForces_degreeLeTwo
    (htheta : CofacialDeletionThetaForcesTheorem.{u})
    (hdegree_le : DeleteEdgeEndsDegreeLeTwoObstructionTheorem.{u}) :
    KuratowskiEulerRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  exact
    hasEulerRotationSystem_of_isPlanar_of_thetaForces_degreeLeTwo
      htheta hdegree_le h_planar

theorem kuratowskiHypermapBridge_of_rotationSystem
    (hrot : KuratowskiRotationSystemTheorem.{u}) :
    KuratowskiHypermapBridgeTheorem.{u, u} := by
  intro V _ G h_planar
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hrot (G := G) h_planar with ⟨R, hgeometry⟩
  exact ⟨R.toSimpleGraphHypermapBridge hgeometry⟩

theorem kuratowskiPlanarHypermapBridge_of_rotationSystem
    (hrot : KuratowskiPlanarRotationSystemTheorem.{u}) :
    KuratowskiPlanarHypermapBridgeTheorem.{u, u} := by
  intro V _ G h_planar
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hrot (G := G) h_planar with ⟨R, hgeometry⟩
  exact ⟨R.toSimpleGraphPlanarHypermapBridge hgeometry⟩

theorem kuratowskiPlanarRotationSystem_of_eulerRotationSystem
    (hrot : KuratowskiEulerRotationSystemTheorem.{u}) :
    KuratowskiPlanarRotationSystemTheorem.{u} := by
  intro V _ _ G _ h_planar
  rcases hrot (G := G) h_planar with ⟨R, hplanar⟩
  exact ⟨R, {
    planar := hplanar
    bridgeless := R.toHypermap_dual_bridgeless }⟩

theorem kuratowskiPlanarHypermapBridge_of_eulerRotationSystem
    (hrot : KuratowskiEulerRotationSystemTheorem.{u}) :
    KuratowskiPlanarHypermapBridgeTheorem.{u, u} :=
  kuratowskiPlanarHypermapBridge_of_rotationSystem
    (kuratowskiPlanarRotationSystem_of_eulerRotationSystem hrot)

theorem colorable_four_of_kuratowskiHypermapBridge
    (hbridge : KuratowskiHypermapBridgeTheorem.{u, v})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_hasHypermapBridge hfct (hbridge G h_planar)

theorem colorable_four_of_kuratowskiPlanarHypermapBridge
    (hbridge : KuratowskiPlanarHypermapBridgeTheorem.{u, v})
    (hpres : Hypermap.Cube.PlanarBridgelessPreservation.{v})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_hasPlanarHypermapBridge
    (Hypermap.Cube.planarBridgelessFourColor_of_preservation hpres hfct)
    (hbridge G h_planar)

theorem colorable_four_of_kuratowskiPlanarHypermapBridge_of_cubeEulerPlanar
    (hbridge : KuratowskiPlanarHypermapBridgeTheorem.{u, v})
    (hplanar : Hypermap.Cube.EulerPlanarPreservation.{v})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiPlanarHypermapBridge
    hbridge
    (Hypermap.Cube.planarBridgelessPreservation_of_eulerPlanarPreservation
      hplanar)
    hfct G h_planar

theorem colorable_four_of_kuratowskiPlanarHypermapBridge_of_hypermapFourColor
    (hbridge : KuratowskiPlanarHypermapBridgeTheorem.{u, v})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_hasPlanarHypermapBridge
    (Hypermap.Cube.planarBridgelessFourColor hfct)
    (hbridge G h_planar)

theorem colorable_four_of_kuratowskiRotationSystem
    (hrot : KuratowskiRotationSystemTheorem.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiHypermapBridge
    (kuratowskiHypermapBridge_of_rotationSystem hrot)
    hfct G h_planar

theorem colorable_four_of_kuratowskiPlanarRotationSystem
    (hrot : KuratowskiPlanarRotationSystemTheorem.{u})
    (hpres : Hypermap.Cube.PlanarBridgelessPreservation.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiPlanarHypermapBridge
    (kuratowskiPlanarHypermapBridge_of_rotationSystem hrot)
    hpres hfct G h_planar

theorem colorable_four_of_kuratowskiPlanarRotationSystem_of_cubeEulerPlanar
    (hrot : KuratowskiPlanarRotationSystemTheorem.{u})
    (hplanar : Hypermap.Cube.EulerPlanarPreservation.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiPlanarRotationSystem
    hrot
    (Hypermap.Cube.planarBridgelessPreservation_of_eulerPlanarPreservation
      hplanar)
    hfct G h_planar

theorem colorable_four_of_kuratowskiPlanarRotationSystem_of_hypermapFourColor
    (hrot : KuratowskiPlanarRotationSystemTheorem.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiPlanarHypermapBridge_of_hypermapFourColor
    (kuratowskiPlanarHypermapBridge_of_rotationSystem hrot)
    hfct G h_planar

theorem colorable_four_of_kuratowskiEulerRotationSystem_of_hypermapFourColor
    (hrot : KuratowskiEulerRotationSystemTheorem.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  colorable_four_of_kuratowskiPlanarRotationSystem_of_hypermapFourColor
    (kuratowskiPlanarRotationSystem_of_eulerRotationSystem hrot)
    hfct G h_planar

end FourColor

end Schematic.Math.GraphTheory
