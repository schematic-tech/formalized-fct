import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.SoundnessInternal.LocalMoves

/-! Coordinate identities for fan positions. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

namespace SoundnessInternal
theorem zfan1r_face_eq_edge_face3_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan1r (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_node_face3_edge_eq_zfan1r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[3])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[3]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zfan1r_face_eq_edge_face3_edge (G := G) hPlain x]

theorem edge_face_symm_edge_eq_node_node_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.edge (G.face.symm (G.edge x)) = G.node (G.node (G.face x)) := by
  rw [Hypermap.Plain.edge_eq_node_face
    (G := G) hPlain (G.face.symm (G.edge x))]
  simp
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem qstepR_face4_edge_eq_zhatr_face_of_spoke6
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 6) :
    qstepR G (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) =
      zmove G ZPartLoc.Zhatr (G.face x) := by
  have hcycle :
      ((G.face : G.Dart → G.Dart)^[5]) (G.edge x) =
        G.face.symm (G.edge x) := by
    have hle : 1 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 1) hle
    simpa [hspoke] using h.symm
  calc
    qstepR G (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))
        = G.face
            (G.edge (((G.face : G.Dart → G.Dart)^[5])
              (G.edge x))) := by
          rw [qstepR]
          rw [node_edge_eq_face_edge_face_of_plain_cubic
            (G := G) hPlain hCubic]
          simp [Function.iterate_succ_apply]
    _ = G.face (G.edge (G.face.symm (G.edge x))) := by
          rw [hcycle]
    _ = G.face (G.node (G.node (G.face x))) := by
          rw [edge_face_symm_edge_eq_node_node_face (G := G) hPlain x]
    _ = zmove G ZPartLoc.Zhatr (G.face x) := by
          rfl

theorem qstepR_face4_edge_eq_zfan0l_face_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 7) :
    qstepR G (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) =
      zmove G ZPartLoc.Zfan0l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan0l_face_eq_face_edge_face_symm2_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[2]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[5]) (G.edge x) := by
    have hle : 2 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 2) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]

theorem qstepR_face4_edge_eq_zfan1l_face_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 8) :
    qstepR G (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) =
      zmove G ZPartLoc.Zfan1l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan1l_face_eq_face_edge_face_symm3_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[3]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[5]) (G.edge x) := by
    have hle : 3 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 3) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]

theorem qstepR_node_face4_edge_eq_zfan0r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.node (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))) =
      zmove G ZPartLoc.Zfan0r (G.face x) := by
  simp [qstepR, zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain (G.face (G.face (G.edge x)))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem node_face4_edge_eq_zfan1r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.node (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) =
      zmove G ZPartLoc.Zfan1r (G.face x) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain (G.face (G.face (G.face (G.edge x))))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_face4_edge_eq_zfan1r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.arity (G.node (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))) =
      G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) := by
  rw [node_face4_edge_eq_zfan1r_face (G := G) hPlain x]

theorem zfan2r_face_eq_edge_face4_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan2r (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_node_face4_edge_eq_zfan2r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[4])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zfan2r (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zfan2r_face_eq_edge_face4_edge (G := G) hPlain x]

theorem qstepR_face5_edge_eq_zhatr_face_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 7) :
    qstepR G (((G.face : G.Dart → G.Dart)^[5]) (G.edge x)) =
      zmove G ZPartLoc.Zhatr (G.face x) := by
  have hcycle :
      ((G.face : G.Dart → G.Dart)^[6]) (G.edge x) =
        G.face.symm (G.edge x) := by
    have hle : 1 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 1) hle
    simpa [hspoke] using h.symm
  calc
    qstepR G (((G.face : G.Dart → G.Dart)^[5]) (G.edge x))
        = G.face
            (G.edge (((G.face : G.Dart → G.Dart)^[6])
              (G.edge x))) := by
          rw [qstepR]
          rw [node_edge_eq_face_edge_face_of_plain_cubic
            (G := G) hPlain hCubic]
          simp [Function.iterate_succ_apply]
    _ = G.face (G.edge (G.face.symm (G.edge x))) := by
          rw [hcycle]
    _ = G.face (G.node (G.node (G.face x))) := by
          rw [edge_face_symm_edge_eq_node_node_face (G := G) hPlain x]
    _ = zmove G ZPartLoc.Zhatr (G.face x) := by
          rfl

theorem qstepR_face5_edge_eq_zfan0l_face_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 8) :
    qstepR G (((G.face : G.Dart → G.Dart)^[5]) (G.edge x)) =
      zmove G ZPartLoc.Zfan0l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan0l_face_eq_face_edge_face_symm2_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[2]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[6]) (G.edge x) := by
    have hle : 2 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 2) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]

theorem qstepR_node_face5_edge_eq_zfan1r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.node (((G.face : G.Dart → G.Dart)^[5]) (G.edge x))) =
      zmove G ZPartLoc.Zfan1r (G.face x) := by
  simp [qstepR, zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain (G.face (G.face (G.face (G.edge x))))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem node_face5_edge_eq_zfan2r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.node (((G.face : G.Dart → G.Dart)^[5]) (G.edge x)) =
      zmove G ZPartLoc.Zfan2r (G.face x) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain (G.face (G.face (G.face (G.face (G.edge x)))))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_face5_edge_eq_zfan2r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.arity (G.node (((G.face : G.Dart → G.Dart)^[5]) (G.edge x))) =
      G.arity (zmove G ZPartLoc.Zfan2r (G.face x)) := by
  rw [node_face5_edge_eq_zfan2r_face (G := G) hPlain x]

theorem zhat_face_eq_edge_face5_edge_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hspoke : G.arity (G.edge x) = 7) :
    zmove G ZPartLoc.Zhat (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[5]) (G.edge x)) := by
  apply G.edge.injective
  calc
    G.edge (zmove G ZPartLoc.Zhat (G.face x))
        = G.edge (G.node (G.edge (G.node (G.edge x)))) := by
          simp [zmove]
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    _ = G.face.symm (G.face.symm (G.edge x)) := by
          rw [Hypermap.edge_node_eq_face_symm]
          rw [Hypermap.edge_node_eq_face_symm]
    _ = ((G.face : G.Dart → G.Dart)^[5]) (G.edge x) := by
          have hle : 2 ≤ G.arity (G.edge x) := by omega
          have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
            (G := G) (x := G.edge x) (n := 2) hle
          simpa [Function.iterate_succ_apply, hspoke] using h
    _ = G.edge (G.edge (((G.face : G.Dart → G.Dart)^[5])
          (G.edge x))) := by
          rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem arity_node_node_face5_edge_eq_zhat_face_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 7) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[5])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zhat (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[5]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zhat_face_eq_edge_face5_edge_of_spoke7 (G := G) hPlain hspoke]

theorem zfan3r_face_eq_edge_face5_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan3r (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[5]) (G.edge x)) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_node_face5_edge_eq_zfan3r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[5])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zfan3r (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[5]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zfan3r_face_eq_edge_face5_edge (G := G) hPlain x]

theorem qstepR_face6_edge_eq_zhatr_face_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 8) :
    qstepR G (((G.face : G.Dart → G.Dart)^[6]) (G.edge x)) =
      zmove G ZPartLoc.Zhatr (G.face x) := by
  have hcycle :
      ((G.face : G.Dart → G.Dart)^[7]) (G.edge x) =
        G.face.symm (G.edge x) := by
    have hle : 1 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 1) hle
    simpa [hspoke] using h.symm
  calc
    qstepR G (((G.face : G.Dart → G.Dart)^[6]) (G.edge x))
        = G.face
            (G.edge (((G.face : G.Dart → G.Dart)^[7])
              (G.edge x))) := by
          rw [qstepR]
          rw [node_edge_eq_face_edge_face_of_plain_cubic
            (G := G) hPlain hCubic]
          simp [Function.iterate_succ_apply]
    _ = G.face (G.edge (G.face.symm (G.edge x))) := by
          rw [hcycle]
    _ = G.face (G.node (G.node (G.face x))) := by
          rw [edge_face_symm_edge_eq_node_node_face (G := G) hPlain x]
    _ = zmove G ZPartLoc.Zhatr (G.face x) := by
          rfl

theorem qstepR_node_face6_edge_eq_zfan2r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.node (((G.face : G.Dart → G.Dart)^[6]) (G.edge x))) =
      zmove G ZPartLoc.Zfan2r (G.face x) := by
  simp [qstepR, zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain
    (G.face (G.face (G.face (G.face (G.edge x)))))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem node_face6_edge_eq_zfan3r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.node (((G.face : G.Dart → G.Dart)^[6]) (G.edge x)) =
      zmove G ZPartLoc.Zfan3r (G.face x) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain
    (G.face (G.face (G.face (G.face (G.face (G.edge x))))))]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_node_face6_edge_eq_zfan3r_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.arity (G.node (((G.face : G.Dart → G.Dart)^[6]) (G.edge x))) =
      G.arity (zmove G ZPartLoc.Zfan3r (G.face x)) := by
  rw [node_face6_edge_eq_zfan3r_face (G := G) hPlain x]

theorem zhat_face_eq_edge_face6_edge_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hspoke : G.arity (G.edge x) = 8) :
    zmove G ZPartLoc.Zhat (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[6]) (G.edge x)) := by
  apply G.edge.injective
  calc
    G.edge (zmove G ZPartLoc.Zhat (G.face x))
        = G.edge (G.node (G.edge (G.node (G.edge x)))) := by
          simp [zmove]
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    _ = G.face.symm (G.face.symm (G.edge x)) := by
          rw [Hypermap.edge_node_eq_face_symm]
          rw [Hypermap.edge_node_eq_face_symm]
    _ = ((G.face : G.Dart → G.Dart)^[6]) (G.edge x) := by
          have hle : 2 ≤ G.arity (G.edge x) := by omega
          have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
            (G := G) (x := G.edge x) (n := 2) hle
          simpa [Function.iterate_succ_apply, hspoke] using h
    _ = G.edge (G.edge (((G.face : G.Dart → G.Dart)^[6])
          (G.edge x))) := by
          rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem arity_node_node_face6_edge_eq_zhat_face_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 8) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[6])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zhat (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[6]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zhat_face_eq_edge_face6_edge_of_spoke8 (G := G) hPlain hspoke]

theorem zhat_face_eq_edge_face4_edge_of_spoke6
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hspoke : G.arity (G.edge x) = 6) :
    zmove G ZPartLoc.Zhat (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[4]) (G.edge x)) := by
  apply G.edge.injective
  calc
    G.edge (zmove G ZPartLoc.Zhat (G.face x))
        = G.edge (G.node (G.edge (G.node (G.edge x)))) := by
          simp [zmove]
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    _ = G.face.symm (G.face.symm (G.edge x)) := by
          rw [Hypermap.edge_node_eq_face_symm]
          rw [Hypermap.edge_node_eq_face_symm]
    _ = ((G.face : G.Dart → G.Dart)^[4]) (G.edge x) := by
          have hle : 2 ≤ G.arity (G.edge x) := by omega
          have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
            (G := G) (x := G.edge x) (n := 2) hle
          simpa [Function.iterate_succ_apply, hspoke] using h
    _ = G.edge (G.edge (((G.face : G.Dart → G.Dart)^[4])
          (G.edge x))) := by
          rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem arity_node_node_face4_edge_eq_zhat_face_of_spoke6
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 6) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[4])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zhat (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zhat_face_eq_edge_face4_edge_of_spoke6 (G := G) hPlain hspoke]


end SoundnessInternal

end Schematic.Math.GraphTheory.FourColor.RedPart
