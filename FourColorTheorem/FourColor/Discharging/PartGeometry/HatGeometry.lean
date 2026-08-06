import FourColorTheorem.FourColor.Discharging.PartGeometry.FixedSpokes

/-! Final hat-position arity identities for constrained sectors. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace SubpartLoc

theorem arity_phat_face_face_edge_face_face_eq_node_edge_node_edge_node_spoke
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (move Phat G
      (G.face (G.face (G.edge (G.face (G.face x)))))) =
    G.arity (G.node (G.edge (G.node (G.edge (G.node (G.edge (G.face x))))))) := by
  dsimp [move]
  have eEnf (y : G.Dart) : G.edge y = G.node (G.face y) := by
    exact (Hypermap.Plain.node_face_eq_edge (G := G) hPlain y).symm
  have fEnne (y : G.Dart) : G.face y = G.node (G.node (G.edge y)) := by
    exact Hypermap.Plain.face_eq_node_node_edge_of_cubic
      (G := G) hPlain hCubic y
  rw [fEnne]
  rw [← Hypermap.arity_face]
  rw [Hypermap.face_edge_node]
  rw [fEnne]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [← eEnf]
  rw [fEnne]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [← eEnf]

theorem arity_phat_face_face_edge_face_face_eq_phat_face_of_spoke5
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 5) :
    G.arity (move Phat G
      (G.face (G.face (G.edge (G.face (G.face x)))))) =
      G.arity (move Phat G (G.face x)) := by
  rw [arity_phat_face_face_edge_face_face_eq_node_edge_node_edge_node_spoke
    (G := G) hPlain hCubic x]
  dsimp [move] at hspoke ⊢
  have hsub :
      (G.face : G.Dart → G.Dart)^[3]
          ((G.face : G.Dart → G.Dart)^[2] (G.edge (G.face x))) =
        G.edge (G.face x) := by
    have h := Hypermap.face_iter_sub_arity
      (G := G) (x := G.edge (G.face x)) (n := 2) (by omega)
    simpa [hspoke] using h
  nth_rewrite 1 [← hsub]
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3 (G := G) hPlain]
  simp [Function.iterate_succ_apply]

theorem arity_phat_face_face_edge_face_face_eq_fan1_face_of_spoke6
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 6) :
    G.arity (move Phat G
      (G.face (G.face (G.edge (G.face (G.face x)))))) =
      G.arity (move Pfan1 G (G.face x)) := by
  rw [arity_phat_face_face_edge_face_face_eq_node_edge_node_edge_node_spoke
    (G := G) hPlain hCubic x]
  dsimp [move] at hspoke ⊢
  have hsub :
      (G.face : G.Dart → G.Dart)^[4]
          ((G.face : G.Dart → G.Dart)^[2] (G.edge (G.face x))) =
        G.edge (G.face x) := by
    have h := Hypermap.face_iter_sub_arity
      (G := G) (x := G.edge (G.face x)) (n := 2) (by omega)
    simpa [hspoke] using h
  nth_rewrite 1 [← hsub]
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3 (G := G) hPlain]
  simp [Function.iterate_succ_apply]

theorem arity_phat_face_face_edge_face_face_eq_fan2_face_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 7) :
    G.arity (move Phat G
      (G.face (G.face (G.edge (G.face (G.face x)))))) =
      G.arity (move Pfan2 G (G.face x)) := by
  rw [arity_phat_face_face_edge_face_face_eq_node_edge_node_edge_node_spoke
    (G := G) hPlain hCubic x]
  dsimp [move] at hspoke ⊢
  have hsub :
      (G.face : G.Dart → G.Dart)^[5]
          ((G.face : G.Dart → G.Dart)^[2] (G.edge (G.face x))) =
        G.edge (G.face x) := by
    have h := Hypermap.face_iter_sub_arity
      (G := G) (x := G.edge (G.face x)) (n := 2) (by omega)
    simpa [hspoke] using h
  nth_rewrite 1 [← hsub]
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3 (G := G) hPlain]
  simp [Function.iterate_succ_apply]

end SubpartLoc


end FourColor

end Schematic.Math.GraphTheory
