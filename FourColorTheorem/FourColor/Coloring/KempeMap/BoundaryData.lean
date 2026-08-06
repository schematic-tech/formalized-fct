import FourColorTheorem.FourColor.Coloring.KempeMap.ProjectionGeometry

/-!
Boundary data and aligned projected cycles for the recursive Kempe map.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- All perimeter information needed to run the recursive `Kempe_map` call
after deleting `z` and `edge z`. -/
structure KempeBoundaryData
    (G : Hypermap.{u}) (z : G.Dart) (r : List G.Dart) : Type u where
  projected : List G.Dart
  survives : forall x, x ∈ projected -> x ≠ z ∧ x ≠ G.edge z
  nodup : projected.Nodup
  spliceCycle : FunctionCycle (G.kempeSpliceNode z) projected
  coversOld : forall x, x ∈ r -> x ≠ z -> x ≠ G.edge z -> x ∈ projected
  faceCovered : G.face z = z ∨ G.face z ∈ projected

namespace KempeBoundaryData

def lifted
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain) :
    List (G.kempeReduction z hplain).Dart :=
  G.kempeLiftList z hplain D.projected D.survives

@[simp]
theorem lifted_projection
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain) :
    (D.lifted hplain).map (G.kempeProjection z hplain) = D.projected :=
  G.kempeLiftList_projection z hplain D.projected D.survives

/-- Mapping source data over a lifted boundary through the reduction
projection recovers the map over the projected source boundary. -/
theorem lifted_map_projection
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain)
    {α : Type _} (f : G.Dart -> α) :
    (D.lifted hplain).map
        (f ∘ G.kempeProjection z hplain) =
      D.projected.map f := by
  rw [← D.lifted_projection hplain, List.map_map]

theorem lifted_cycle
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x) :
    FunctionCycle (G.kempeReduction z hplain).node (D.lifted hplain) :=
  G.kempeLiftList_cycle z hplain hnode D.projected D.survives
    D.nodup D.spliceCycle

theorem lifted_nodup
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain) :
    (D.lifted hplain).Nodup :=
  G.kempeLiftList_nodup z hplain D.projected D.survives D.nodup

theorem lifted_quasicubic
    {G : Hypermap.{u}}
    {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x)
    (hrcycle : FunctionCycle G.node r) (hzr : z ∈ r)
    (hrquasi : G.Quasicubic r) :
    (G.kempeReduction z hplain).Quasicubic (D.lifted hplain) :=
  G.kempeLiftList_quasicubic z hplain hnode r D.projected
    hrcycle hzr hrquasi D.survives D.nodup D.spliceCycle
    D.coversOld D.faceCovered

end KempeBoundaryData

/-- The first two right-trace entries distinguish the second color from the
cyclic last color. -/
theorem ne_last_of_take_two_urtrace_nodup
    (a b : Color) (cs : ColSeq)
    (hn : (ColSeq.urtrace (a :: b :: cs)).take 2 |>.Nodup) :
    b ≠ (a :: b :: cs).getLastD Color.zero := by
  have hne :
      (a :: b :: cs).getLastD Color.zero + a ≠ a + b := by
    simpa [ColSeq.urtrace, ColSeq.pairSums] using hn
  intro h
  apply hne
  rw [← h, Color.add_comm]

/-- Construct Coq `s` and `h_s` for a boundary already rotated to start at
the selected dart `z`. -/
def kempeBoundaryData_aligned
    (G : Hypermap.{u}) (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hquasi : G.Quasicubic (z :: G.node z :: p))
    (hselect : G.face z = z ∨ G.face z ∉ z :: G.node z :: p) :
    KempeBoundaryData G z (z :: G.node z :: p) := by
  by_cases hfixed : G.face z = z
  · have hdata :=
      G.kempeSpliceCycle_of_face_fixed z p hplain hcycle hnodup hfixed
    refine ⟨p, hdata.2.2, hdata.2.1, hdata.1, ?_, Or.inl hfixed⟩
    intro x hx hxz hxe
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact False.elim (hxz rfl)
    · have hnodeEdge : G.node z = G.edge z := by
        rw [← Plain.node_face_eq_edge (G := G) hplain z, hfixed]
      exact False.elim (hxe hnodeEdge)
    · exact hx
  · have hfaceOut : G.face z ∉ z :: G.node z :: p :=
      hselect.resolve_left hfixed
    let q := G.node (G.edge z) :: G.face z :: G.node z :: p
    have hdata := G.kempeSpliceCycle_of_face_not_mem z p hplain hnode
      hcycle hnodup hquasi hfaceOut
    change FunctionCycle (G.kempeSpliceNode z) q ∧ q.Nodup ∧
      (forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z) at hdata
    refine ⟨q, hdata.2.2, hdata.2.1, hdata.1, ?_, Or.inr ?_⟩
    · intro x hx hxz _
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact False.elim (hxz rfl)
      · simp only [q, List.mem_cons]
        exact Or.inr (Or.inr hx)
    · simp [q]


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
