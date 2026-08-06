import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Preorder.Finite
import Schematic.Math.GraphTheory.Basic
import Schematic.Math.GraphTheory.Embedding.Color

/-!
Basic non-planar-specific infrastructure for a direct four-colour theorem
development.

This file contains facts about edge-critical non-four-colourable graphs.  These
are independent of embeddings, discharging, and the paper-specific dominating
model argument.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

universe u

variable {V : Type u}

namespace FourColor

theorem colorable_four_iff_coloring_Color
    {G : SimpleGraph V} :
    G.Colorable 4 ↔ Nonempty (G.Coloring Color) := by
  constructor
  · rintro ⟨C⟩
    refine ⟨Coloring.mk (fun v => Color.ofFin4 (C v)) ?_⟩
    intro a b hab hsame
    apply C.valid hab
    simpa using (congrArg Color.toFin4 hsame)
  · rintro ⟨C⟩
    refine ⟨Coloring.mk (fun v => Color.toFin4 (C v)) ?_⟩
    intro a b hab hsame
    apply C.valid hab
    exact Color.equivFin4.injective hsame

theorem not_colorable_four_iff_not_coloring_Color
    {G : SimpleGraph V} :
    Not (G.Colorable 4) ↔ Not (Nonempty (G.Coloring Color)) := by
  simpa using not_congr (colorable_four_iff_coloring_Color (G := G))

def Coloring.of_deleteEdge_of_endpoint_ne
    {G : SimpleGraph V}
    {α : Type*}
    {u v : V}
    (C : (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring α)
    (huv_color : C u ≠ C v) :
    G.Coloring α := by
  refine Coloring.mk (fun x => C x) ?_
  intro a b hab hsame
  by_cases h_edge : s(a, b) = s(u, v)
  · have hcases :
        (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
      simpa [Sym2.eq_iff] using h_edge
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv_color hsame
    · exact huv_color hsame.symm
  · have hdel :
        (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Adj a b := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hab, by simpa using h_edge⟩
    exact C.valid hdel hsame

theorem colorable_of_deleteEdge_colorable_of_endpoint_ne
    {G : SimpleGraph V}
    {n : Nat}
    {u v : V}
    (C : (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring (Fin n))
    (huv_color : C u ≠ C v) :
    G.Colorable n :=
  ⟨Coloring.of_deleteEdge_of_endpoint_ne C huv_color⟩

structure EdgeDeletionMinimalNonFourColorable
    (G : SimpleGraph V) : Prop where
  not_colorable : Not (G.Colorable 4)
  delete_edge_colorable :
    forall {u v : V}, G.Adj u v ->
      (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Colorable 4

theorem EdgeDeletionMinimalNonFourColorable.same_color_of_delete_edge_coloring
    {G : SimpleGraph V}
    (hG : EdgeDeletionMinimalNonFourColorable G)
    {u v : V}
    (C : (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring (Fin 4)) :
    C u = C v := by
  by_contra hne
  exact hG.not_colorable
    (colorable_of_deleteEdge_colorable_of_endpoint_ne C hne)

theorem EdgeDeletionMinimalNonFourColorable.exists_delete_edge_coloring
    {G : SimpleGraph V}
    (hG : EdgeDeletionMinimalNonFourColorable G)
    {u v : V}
    (huv : G.Adj u v) :
    Nonempty ((G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring (Fin 4)) :=
  hG.delete_edge_colorable huv

theorem EdgeDeletionMinimalNonFourColorable.same_color_for_some_delete_edge_coloring
    {G : SimpleGraph V}
    (hG : EdgeDeletionMinimalNonFourColorable G)
    {u v : V}
    (huv : G.Adj u v) :
    Exists fun C : (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Coloring (Fin 4) =>
      C u = C v := by
  rcases hG.exists_delete_edge_coloring huv with ⟨C⟩
  exact ⟨C, hG.same_color_of_delete_edge_coloring C⟩

theorem not_edgeDeletionMinimalNonFourColorable_of_colorable
    {G : SimpleGraph V}
    (hcolor : G.Colorable 4) :
    Not (EdgeDeletionMinimalNonFourColorable G) := by
  intro hG
  exact hG.not_colorable hcolor

theorem EdgeDeletionMinimalNonFourColorable.not_colorable_four
    {G : SimpleGraph V}
    (hG : EdgeDeletionMinimalNonFourColorable G) :
    FiveChromaticOrMore G :=
  hG.not_colorable

theorem EdgeDeletionMinimalNonFourColorable.card_gt_four
    {G : SimpleGraph V}
    [Fintype V]
    (hG : EdgeDeletionMinimalNonFourColorable G) :
    4 < Fintype.card V :=
  card_gt_four_of_not_colorable_four (G := G) hG.not_colorable

theorem exists_edgeDeletionMinimalNonFourColorable_subgraph
    {G : SimpleGraph V}
    [Fintype V]
    (hG : Not (G.Colorable 4)) :
    Exists fun H : SimpleGraph V =>
      H ≤ G ∧ EdgeDeletionMinimalNonFourColorable H := by
  classical
  let S : Set (SimpleGraph V) := {H | H ≤ G ∧ Not (H.Colorable 4)}
  have hS_finite : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hH_min⟩ := hS_finite.exists_minimal hS_nonempty
  refine ⟨H, hH_min.prop.1, ?_⟩
  refine
    { not_colorable := hH_min.prop.2
      delete_edge_colorable := ?_ }
  intro u v huv
  by_contra hdel_not_colorable
  have hdel_mem : H.deleteEdges ({s(u, v)} : Set (Sym2 V)) ∈ S := by
    exact ⟨(SimpleGraph.deleteEdges_le _).trans hH_min.prop.1, hdel_not_colorable⟩
  have hH_le_del :
      H ≤ H.deleteEdges ({s(u, v)} : Set (Sym2 V)) :=
    hH_min.le_of_le hdel_mem (SimpleGraph.deleteEdges_le _)
  have hdel_adj :
      (H.deleteEdges ({s(u, v)} : Set (Sym2 V))).Adj u v :=
    hH_le_del huv
  rw [SimpleGraph.deleteEdges_adj] at hdel_adj
  exact hdel_adj.2 (Set.mem_singleton (s(u, v)))

theorem not_exists_edgeDeletionMinimalNonFourColorable_subgraph_of_colorable
    {G : SimpleGraph V}
    (hcolor : G.Colorable 4) :
    ¬ Exists fun H : SimpleGraph V =>
      H ≤ G ∧ EdgeDeletionMinimalNonFourColorable H := by
  rintro ⟨H, hHG, hH⟩
  exact hH.not_colorable
    (SimpleGraph.Colorable.mono_left hHG hcolor)

theorem colorable_four_of_no_edgeDeletionMinimalNonFourColorable_subgraph
    {G : SimpleGraph V}
    [Fintype V]
    (hno :
      ¬ Exists fun H : SimpleGraph V =>
        H ≤ G ∧ EdgeDeletionMinimalNonFourColorable H) :
    G.Colorable 4 := by
  by_contra hnot
  exact hno (exists_edgeDeletionMinimalNonFourColorable_subgraph hnot)

theorem colorable_four_iff_no_edgeDeletionMinimalNonFourColorable_subgraph
    {G : SimpleGraph V}
    [Fintype V] :
    G.Colorable 4 ↔
      ¬ Exists fun H : SimpleGraph V =>
        H ≤ G ∧ EdgeDeletionMinimalNonFourColorable H := by
  constructor
  · exact not_exists_edgeDeletionMinimalNonFourColorable_subgraph_of_colorable
  · exact colorable_four_of_no_edgeDeletionMinimalNonFourColorable_subgraph

end FourColor

end Schematic.Math.GraphTheory
