import Schematic.Math.GraphTheory.Embedding.RotationSystem
import FourColorTheorem.FourColor.Theorem.SimpleGraphBridge
import Schematic.Math.GraphTheory.Embedding.Coloring

/-!
Colour transfer from graph rotation systems.

Given a rotation system for a simple graph, a colouring of the dual hypermap
gives a node-colouring of the primal hypermap.  Since node orbits are the
outgoing darts at graph vertices, this induces a vertex-colouring of the
original graph.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

namespace FourColor

universe u

namespace RotationSystem

variable {V : Type u} {G : SimpleGraph V}

/-- Colour a graph vertex from any outgoing dart.  Isolated vertices are given
an arbitrary default colour; this does not affect graph-colouring validity. -/
noncomputable def vertexColor
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    (k : (R.toHypermap).Dart → Color)
    (x : V) :
    Color :=
  if h : ∃ e : OrientedEdge G, e.tail = x then
    k h.choose
  else
    Color.zero

theorem vertexColor_eq_of_tail
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {k : (R.toHypermap).Dart → Color}
    (hk : (R.toHypermap).GraphColoring k)
    {x : V} {e : OrientedEdge G}
    (he : e.tail = x) :
    R.vertexColor k x = k e := by
  classical
  unfold vertexColor
  split_ifs with h
  · let e0 : OrientedEdge G := h.choose
    have he0 : e0.tail = x := h.choose_spec
    have hreach : PermReachable R.node e0 e :=
      R.node_orbit_of_same_tail e0 e (he0.trans he.symm)
    exact
      (Hypermap.GraphColoring.eq_of_node_reachable
        (G := R.toHypermap) hk
        (by simpa [toHypermap] using hreach)).symm
  · exact False.elim (h ⟨e, he⟩)

/-- A colouring of the dual hypermap induces a vertex-colouring of the original
simple graph. -/
noncomputable def graphColoringOfDualColoring
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    {k : (R.toHypermap).dual.Dart → Color}
    (hk : (R.toHypermap).dual.Coloring k) :
    G.Coloring Color :=
  SimpleGraph.Coloring.mk
    (fun x => R.vertexColor k x)
    (by
      intro x y hxy hsame
      have hkGraph : (R.toHypermap).GraphColoring k :=
        ((R.toHypermap).coloring_dual_iff k).mp hk
      let e : OrientedEdge G := ⟨(x, y), hxy⟩
      have hx : R.vertexColor k x = k e :=
        R.vertexColor_eq_of_tail hkGraph (e := e) rfl
      have hy : R.vertexColor k y = k e.symm :=
        R.vertexColor_eq_of_tail hkGraph (e := e.symm) rfl
      have hne : k ((R.toHypermap).edge e) ≠ k e :=
        Hypermap.GraphColoring.edge_ne (G := R.toHypermap) hkGraph e
      apply hne
      calc
        k ((R.toHypermap).edge e) = k e.symm := by
          change k (OrientedEdge.edgePerm G e) = k e.symm
          rfl
        _ = R.vertexColor k y := hy.symm
        _ = R.vertexColor k x := hsame.symm
        _ = k e := hx)

/-- A rotation system whose dual hypermap has the four-colour theorem geometry
provides a concrete `SimpleGraphHypermapBridge`. -/
noncomputable def toSimpleGraphHypermapBridge
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hgeometry : (R.toHypermap).dual.PlanarBridgelessPlainPrecubic) :
    SimpleGraphHypermapBridge.{u, u} G where
  map := (R.toHypermap).dual
  geometry := hgeometry
  vertexColor := fun k x => R.vertexColor k x
  vertexColor_valid := by
    intro k hk x y hxy
    exact (R.graphColoringOfDualColoring hk).valid hxy

/-- A rotation system whose dual hypermap is planar and bridgeless provides the
Coq-facing bridge before cubification supplies plainness and precubicity. -/
noncomputable def toSimpleGraphPlanarHypermapBridge
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (R : RotationSystem G)
    (hgeometry : (R.toHypermap).dual.PlanarBridgeless) :
    SimpleGraphPlanarHypermapBridge.{u, u} G where
  map := (R.toHypermap).dual
  geometry := hgeometry
  vertexColor := fun k x => R.vertexColor k x
  vertexColor_valid := by
    intro k hk x y hxy
    exact (R.graphColoringOfDualColoring hk).valid hxy

end RotationSystem

end FourColor

end Schematic.Math.GraphTheory
