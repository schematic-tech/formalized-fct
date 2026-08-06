import FourColorTheorem.FourColor.Coloring.KempeMap.BoundaryData

/-!
Lifting reduced boundary colorings and compatibility with projection.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The unique reduced dart over a surviving source dart. -/
def kempeLiftDart
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : G.Dart) (hxz : x ≠ z) (hxe : x ≠ G.edge z) :
    (G.kempeReduction z hplain).Dart :=
  (G.kempeRemainingEquiv z hplain).symm ⟨x, hxz, hxe⟩

@[simp]
theorem kempeLiftDart_projection
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : G.Dart) (hxz : x ≠ z) (hxe : x ≠ G.edge z) :
    G.kempeProjection z hplain
      (G.kempeLiftDart z hplain x hxz hxe) = x :=
  rfl

/-- Fill the two deleted darts with prescribed colors and use the reduced
coloring everywhere else. -/
def kempeFillColor
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (k : (G.kempeReduction z hplain).Dart -> Color)
    (cz ce : Color) (x : G.Dart) : Color :=
  if hxz : x = z then cz
  else if hxe : x = G.edge z then ce
  else k (G.kempeLiftDart z hplain x hxz hxe)

@[simp]
theorem kempeFillColor_z
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (k : (G.kempeReduction z hplain).Dart -> Color)
    (cz ce : Color) :
    G.kempeFillColor z hplain k cz ce z = cz := by
  simp [kempeFillColor]

theorem kempeFillColor_edge
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (k : (G.kempeReduction z hplain).Dart -> Color)
    (cz ce : Color) :
    G.kempeFillColor z hplain k cz ce (G.edge z) = ce := by
  simp [kempeFillColor, Plain.edge_ne (G := G) hplain z]

theorem kempeFillColor_of_ne
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (k : (G.kempeReduction z hplain).Dart -> Color)
    (cz ce : Color) (x : G.Dart)
    (hxz : x ≠ z) (hxe : x ≠ G.edge z) :
    G.kempeFillColor z hplain k cz ce x =
      k (G.kempeLiftDart z hplain x hxz hxe) := by
  simp [kempeFillColor, hxz, hxe]

namespace KempeBoundaryData

theorem lifted_colors_eq_projected
    {G : Hypermap.{u}} {z : G.Dart} {r : List G.Dart}
    (D : KempeBoundaryData G z r) (hplain : G.Plain)
    (k : (G.kempeReduction z hplain).Dart -> Color)
    (fallback : Color) :
    (D.lifted hplain).map k =
      D.projected.map
        (G.kempeFillColor z hplain k fallback fallback) := by
  rw [← D.lifted_projection hplain]
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  have hx := G.kempeProjection_ne_deleted z hplain x
  change k x = G.kempeFillColor z hplain k fallback fallback
    (G.kempeProjection z hplain x)
  rw [G.kempeFillColor_of_ne z hplain k fallback fallback
    (G.kempeProjection z hplain x) hx.1 hx.2]
  congr 1

end KempeBoundaryData

/-- The face relation dual to Coq's `hE`/`hN` calculation. -/
theorem kempeProjection_face_relation
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (x : (G.kempeReduction z hplain).Dart) :
    G.edge (G.kempeSpliceNode z
      (G.kempeProjection z hplain
        ((G.kempeReduction z hplain).face x))) =
      G.kempeProjection z hplain x := by
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  let y := proj (H.face x)
  have hprojectNode :
      proj (H.node (H.face x)) = G.kempeSpliceNode z y :=
    G.kempeProjection_node_eq_splice z hplain hnode (H.face x)
  have hprojectEdge :
      proj (H.edge (H.node (H.face x))) =
        G.edge (proj (H.node (H.face x))) :=
    G.kempeProjection_edge z hplain (H.node (H.face x))
  change G.edge (G.kempeSpliceNode z y) = proj x
  calc
    G.edge (G.kempeSpliceNode z y) =
        G.edge (proj (H.node (H.face x))) := by rw [hprojectNode]
    _ = proj (H.edge (H.node (H.face x))) := hprojectEdge.symm
    _ = proj x := by rw [H.edge_node_face]

/-- Coq `khE`, `khF`: restricting a source coloring along the reduction
projection gives a coloring of the reduced map. -/
theorem Coloring.comp_kempeProjection
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    {k : G.Dart -> Color} (hk : G.Coloring k) :
    (G.kempeReduction z hplain).Coloring
      (k ∘ G.kempeProjection z hplain) := by
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  have hnode : forall x : G.Dart, G.node x ≠ x :=
    Coloring.node_ne_self G hk
  constructor
  · intro x
    change
      k (G.kempeProjection z hplain
        ((G.kempeReduction z hplain).edge x)) ≠
      k (G.kempeProjection z hplain x)
    rw [G.kempeProjection_edge]
    exact Coloring.edge_ne (G := G) hk
      (G.kempeProjection z hplain x)
  · intro x
    change k (proj (H.face x)) = k (proj x)
    let y := proj (H.face x)
    have hp : G.edge (G.kempeSpliceNode z y) = proj x := by
      exact G.kempeProjection_face_relation z hplain hnode x
    by_cases hyz : G.node y = z
    · have hp' : G.edge (G.node (G.edge z)) = proj x := by
        simpa [kempeSpliceNode, hyz] using hp
      have hyFace : G.face (G.edge z) = y := by
        rw [← hyz]
        exact G.face_edge_node y
      have hky : k y = k (G.edge z) := by
        rw [← hyFace]
        exact Coloring.face_eq (G := G) hk (G.edge z)
      have hkproj : k (proj x) = k (G.edge z) := by
        rw [← hp']
        symm
        simpa using Coloring.face_eq (G := G) hk
          (G.edge (G.node (G.edge z)))
      exact hky.trans hkproj.symm
    · by_cases hye : G.node y = G.edge z
      · have hp' : G.edge (G.node z) = proj x := by
          rw [kempeSpliceNode, if_neg hyz, if_pos hye] at hp
          exact hp
        have hyFace : G.face (G.edge (G.edge z)) = y := by
          rw [← hye]
          exact G.face_edge_node y
        have hky : k y = k z := by
          rw [← hyFace, Plain.edge_edge (G := G) hplain z]
          exact Coloring.face_eq (G := G) hk z
        have hkproj : k (proj x) = k z := by
          rw [← hp']
          symm
          simpa using Coloring.face_eq (G := G) hk
            (G.edge (G.node z))
        exact hky.trans hkproj.symm
      · have hp' : G.edge (G.node y) = proj x := by
          rw [kempeSpliceNode, if_neg hyz, if_neg hye] at hp
          exact hp
        calc
          k y = k (G.edge (G.node y)) := by
            simpa using Coloring.face_eq (G := G) hk
              (G.edge (G.node y))
          _ = k (proj x) := congrArg k hp'


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
