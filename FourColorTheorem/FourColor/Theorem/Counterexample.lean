import FourColorTheorem.FourColor.SimpleGraphColoring
import Schematic.Math.GraphTheory.Planarity.Basic

/-!
Minimal counterexample setup for a direct four-colour theorem proof.

This file keeps the graph-theoretic counterexample reductions separate from
the hypermap/discharging development.  The results here are background lemmas:
from any non-four-colourable planar graph one may pass to a spanning subgraph
that is still planar, still non-four-colourable, and edge-deletion-minimal.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

universe u

namespace FourColor

/-- The reusable package of hypotheses supplied by the standard minimal
counterexample reduction for the four-colour theorem. -/
structure EdgeCriticalPlanarCounterexample
    {V : Type u}
    (G : SimpleGraph V) : Prop where
  planar : IsPlanar G
  critical : EdgeDeletionMinimalNonFourColorable G

namespace EdgeCriticalPlanarCounterexample

theorem not_colorable_four
    {V : Type u} {G : SimpleGraph V}
    (hG : EdgeCriticalPlanarCounterexample G) :
    Not (G.Colorable 4) :=
  hG.critical.not_colorable

theorem delete_edge_colorable
    {V : Type u} {G : SimpleGraph V}
    (hG : EdgeCriticalPlanarCounterexample G)
    {u v : V}
    (huv : G.Adj u v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Colorable 4 :=
  hG.critical.delete_edge_colorable huv

theorem same_color_of_delete_edge_coloring
    {V : Type u} {G : SimpleGraph V}
    (hG : EdgeCriticalPlanarCounterexample G)
    {u v : V}
    (C : (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring (Fin 4)) :
    C u = C v :=
  hG.critical.same_color_of_delete_edge_coloring C

theorem card_gt_four
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : EdgeCriticalPlanarCounterexample G) :
    4 < Fintype.card V :=
  hG.critical.card_gt_four

end EdgeCriticalPlanarCounterexample

theorem exists_edgeCriticalPlanarCounterexample_subgraph
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (h_not_colorable : Not (G.Colorable 4)) :
    Exists fun H : SimpleGraph V =>
      H ≤ G ∧ EdgeCriticalPlanarCounterexample H := by
  obtain ⟨H, hHG, hH_critical⟩ :=
    exists_edgeDeletionMinimalNonFourColorable_subgraph h_not_colorable
  exact ⟨H, hHG, ⟨IsPlanar.mono hHG h_planar, hH_critical⟩⟩

theorem not_exists_edgeCriticalPlanarCounterexample_subgraph_of_colorable
    {V : Type u}
    {G : SimpleGraph V}
    (h_colorable : G.Colorable 4) :
    ¬ Exists fun H : SimpleGraph V =>
      H ≤ G ∧ EdgeCriticalPlanarCounterexample H := by
  rintro ⟨H, hHG, hH⟩
  exact hH.not_colorable_four
    (SimpleGraph.Colorable.mono_left hHG h_colorable)

theorem colorable_four_of_no_edgeCriticalPlanarCounterexample_subgraph
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (h_no_counterexample :
      ¬ Exists fun H : SimpleGraph V =>
        H ≤ G ∧ EdgeCriticalPlanarCounterexample H) :
    G.Colorable 4 := by
  by_contra h_not_colorable
  exact h_no_counterexample
    (exists_edgeCriticalPlanarCounterexample_subgraph
      h_planar h_not_colorable)

theorem colorable_four_iff_no_edgeCriticalPlanarCounterexample_subgraph
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G) :
    G.Colorable 4 ↔
      ¬ Exists fun H : SimpleGraph V =>
        H ≤ G ∧ EdgeCriticalPlanarCounterexample H := by
  constructor
  · exact not_exists_edgeCriticalPlanarCounterexample_subgraph_of_colorable
  · exact colorable_four_of_no_edgeCriticalPlanarCounterexample_subgraph
      h_planar

theorem colorable_four_of_no_edgeCriticalPlanarCounterexample_below
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (h_no_counterexample :
      ∀ H : SimpleGraph V, H ≤ G → ¬ EdgeCriticalPlanarCounterexample H) :
    G.Colorable 4 :=
  colorable_four_of_no_edgeCriticalPlanarCounterexample_subgraph
    h_planar (by
      rintro ⟨H, hHG, hH⟩
      exact h_no_counterexample H hHG hH)

theorem colorable_four_iff_no_edgeCriticalPlanarCounterexample_below
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G) :
    G.Colorable 4 ↔
      ∀ H : SimpleGraph V, H ≤ G → ¬ EdgeCriticalPlanarCounterexample H := by
  constructor
  · intro h_colorable H hHG hH
    exact hH.not_colorable_four
      (SimpleGraph.Colorable.mono_left hHG h_colorable)
  · exact colorable_four_of_no_edgeCriticalPlanarCounterexample_below
      h_planar

end FourColor

end Schematic.Math.GraphTheory
