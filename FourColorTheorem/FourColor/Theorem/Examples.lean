import FourColorTheorem.FourColor.SimpleGraphColoring
import Schematic.Math.GraphTheory.Subdivisions

/-!
Small critical examples for the four-colour development.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

namespace FourColor

theorem K5Graph_not_colorable_four :
    Not (K5Graph.Colorable 4) := by
  intro hcolor
  have hclique : K5Graph.IsClique (Finset.univ : Finset (Fin 5)) := by
    intro u _hu v _hv huv
    simpa [K5Graph, CompleteGraphOn] using huv
  have hcard := hclique.card_le_of_colorable hcolor
  simp at hcard

theorem K5Graph_delete_edge_colorable_four
    {u v : Fin 5}
    (huv : K5Graph.Adj u v) :
    (K5Graph.deleteEdges ({s(u, v)} : Set (Sym2 (Fin 5)))).Colorable 4 := by
  classical
  have huv_ne : u ≠ v := huv.ne
  refine colorable_four_of_card_le_five_of_nonadjacent
    (G := K5Graph.deleteEdges ({s(u, v)} : Set (Sym2 (Fin 5))))
    u v huv_ne ?_ ?_
  · intro hdel
    rw [SimpleGraph.deleteEdges_adj] at hdel
    exact hdel.2 (Set.mem_singleton (s(u, v)))
  · simp

theorem K5Graph_edgeDeletionMinimalNonFourColorable :
    EdgeDeletionMinimalNonFourColorable K5Graph where
  not_colorable := K5Graph_not_colorable_four
  delete_edge_colorable := by
    intro u v huv
    exact K5Graph_delete_edge_colorable_four huv

end FourColor

end Schematic.Math.GraphTheory
