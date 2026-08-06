import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Fit

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

namespace SoundnessInternal
theorem arity_edge_node_eq
    {G : Hypermap.{u}} (x : G.Dart) :
    G.arity (G.edge (G.node x)) = G.arity x := by
  rw [Hypermap.edge_node_eq_face_symm (G := G) x]
  exact Hypermap.arity_face_symm (G := G) x

theorem qstepL_zmove_zhatr_eq_zmove_zhub_of_cubic
    {G : Hypermap.{u}} (hCubic : G.Cubic) (x : G.Dart) :
    qstepL G (zmove G Zhatr x) = zmove G Zhub x := by
  rw [Hypermap.qstepL_eq_node_face_symm]
  simp [zmove]
  exact (hCubic x).1

theorem qstepR_zmove_zhatl_eq_zmove_zhub_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    qstepR G (zmove G Zhatl x) = zmove G Zhub x := by
  rw [qstepR]
  simp [zmove]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  exact (hCubic x).1

theorem qstepL_leftFan_succ_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (n : Nat) (x : G.Dart) :
    qstepL G
        (G.face
          (G.edge
            (((fun y : G.Dart => G.edge (G.node y))^[n + 1])
              (G.node x)))) =
      G.face
        (G.edge
          (((fun y : G.Dart => G.edge (G.node y))^[n])
            (G.node x))) := by
  rw [Hypermap.qstepL_eq_node_face_symm]
  simp only [Equiv.symm_apply_apply]
  rw [Function.iterate_succ_apply']
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  exact Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic _

theorem qstepL_zfan0l_eq_zhatr_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    qstepL G (zmove G Zfan0l x) = zmove G Zhatr x := by
  change
    qstepL G
        (G.face
          (G.edge
            (((fun y : G.Dart => G.edge (G.node y))^[1 + 1])
              (G.node x)))) =
      G.face (G.node (G.node x))
  rw [qstepL_leftFan_succ_of_plain_cubic
    (G := G) hPlain hCubic 1 x]
  simp [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem qstepR_rightFan_succ_of_plain
    {G : Hypermap.{u}} (hPlain : G.Plain) (n : Nat) (x : G.Dart) :
    qstepR G
        (G.edge (((G.face : G.Dart → G.Dart)^[n + 1]) (G.node x))) =
      G.edge (((G.face : G.Dart → G.Dart)^[n]) (G.node x)) := by
  rw [qstepR]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [Function.iterate_succ_apply']
  exact Hypermap.Plain.node_face_eq_edge (G := G) hPlain _

theorem qstepR_zfan0r_face_eq_zhatl_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    qstepR G (zmove G Zfan0r (G.face x)) = zmove G Zhatl x := by
  change
    G.node
        (G.edge
          (G.edge (((G.face : G.Dart → G.Dart)^[2])
            (G.node (G.face x))))) =
      G.edge (G.node (G.node x))
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  change G.node (G.face (G.face (G.edge x))) =
    G.edge (G.node (G.node x))
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain
    (G.face (G.edge x))]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]

theorem qstepR_zhat_eq_zfan0r_of_node_arity_five
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hnode : G.arity (G.node x) = 5) :
    qstepR G (zmove G Zhat x) = zmove G Zfan0r x := by
  change
    G.node (G.edge (G.node (G.edge (G.node (G.node x))))) =
      G.edge (((G.face : G.Dart → G.Dart)^[2]) (G.node x))
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3
    (G := G) hPlain (G.node x)]
  rw [Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.node x) (n := 3) (by omega)]
  simp [hnode]

theorem qstepR_zhat_eq_zfan1r_of_node_arity_six
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hnode : G.arity (G.node x) = 6) :
    qstepR G (zmove G Zhat x) = zmove G Zfan1r x := by
  change
    G.node (G.edge (G.node (G.edge (G.node (G.node x))))) =
      G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.node x))
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3
    (G := G) hPlain (G.node x)]
  rw [Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.node x) (n := 3) (by omega)]
  simp [hnode]

theorem qstepR_zhat_eq_zfan2r_of_node_arity_seven
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hnode : G.arity (G.node x) = 7) :
    qstepR G (zmove G Zhat x) = zmove G Zfan2r x := by
  change
    G.node (G.edge (G.node (G.edge (G.node (G.node x))))) =
      G.edge (((G.face : G.Dart → G.Dart)^[4]) (G.node x))
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3
    (G := G) hPlain (G.node x)]
  rw [Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.node x) (n := 3) (by omega)]
  simp [hnode]

theorem qstepR_zhat_eq_zfan3r_of_node_arity_eight
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hnode : G.arity (G.node x) = 8) :
    qstepR G (zmove G Zhat x) = zmove G Zfan3r x := by
  change
    G.node (G.edge (G.node (G.edge (G.node (G.node x))))) =
      G.edge (((G.face : G.Dart → G.Dart)^[5]) (G.node x))
  rw [Hypermap.node_edge_node_edge_node_eq_edge_face_symm3
    (G := G) hPlain (G.node x)]
  rw [Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.node x) (n := 3) (by omega)]
  simp [hnode]

theorem qstepR_face3_mid_eq_zhatr_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.node (G.node (G.face.symm (G.edge x))) =
      G.face (G.node (G.node (G.face x))) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge
    (G := G) hCubic (G.face.symm (G.edge x))]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic (G.face x)]
  calc
    G.face (G.edge (G.face.symm (G.edge x)))
        = G.face (G.node (G.face (G.face.symm (G.edge x)))) := by
          rw [Hypermap.Plain.edge_eq_node_face (G := G) hPlain]
    _ = G.face (G.node (G.edge x)) := by simp
    _ = G.face (G.node (G.node (G.face x))) := by
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    _ = G.face (G.node.symm (G.face x)) := by
          rw [(Hypermap.Cubic.node_symm_eq_node_node
            hCubic (G.face x)).symm]
    _ = G.face (G.face (G.edge (G.face x))) := by
          rw [(Hypermap.face_edge_eq_node_symm G (G.face x)).symm]

theorem qstepR_face3_edge_eq_zhatr_face_of_spoke5
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 5) :
    qstepR G (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) =
      zmove G Zhatr (G.face x) := by
  rw [Hypermap.qstepR_eq_node_node_face_of_plain (G := G) hPlain]
  change G.node (G.node (((G.face : G.Dart → G.Dart)^[4]) (G.edge x))) =
    G.face (G.node (G.node (G.face x)))
  have hle : 1 ≤ G.arity (G.edge x) := by omega
  have hcycle := Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.edge x) (n := 1) hle
  have hcycle' : ((G.face : G.Dart → G.Dart)^[4]) (G.edge x) =
      G.face.symm (G.edge x) := by
    simpa [hspoke] using hcycle.symm
  rw [hcycle']
  exact qstepR_face3_mid_eq_zhatr_face (G := G) hPlain hCubic x

theorem qstepR_node_face3_edge_eq_zhatl
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    qstepR G (G.node (((G.face : G.Dart → G.Dart)^[3]) (G.edge x))) =
      zmove G Zhatl x := by
  simp [qstepR, zmove, Function.iterate_succ_apply]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
  exact (Hypermap.Plain.edge_eq_node_face
    (G := G) hPlain (G.face (G.edge x))).symm

theorem arity_node_face3_edge_eq_zhat
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (G.node (((G.face : G.Dart → G.Dart)^[3]) (G.edge x))) =
      G.arity (zmove G ZPartLoc.Zhat x) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge
    (G := G) hPlain (G.face (G.face (G.edge x)))]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
  rw [Hypermap.Plain.edge_eq_node_face
    (G := G) hPlain (G.face (G.edge x))]
  rw [Hypermap.Cubic.node_node_eq_face_edge
    (G := G) hCubic (G.face (G.face (G.edge x)))]
  rw [Hypermap.arity_face]

theorem zhat_face_eq_edge_face3_edge_of_spoke5
    {G : Hypermap.{u}} (hPlain : G.Plain) {x : G.Dart}
    (hspoke : G.arity (G.edge x) = 5) :
    zmove G ZPartLoc.Zhat (G.face x) =
      G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) := by
  apply G.edge.injective
  calc
    G.edge (zmove G ZPartLoc.Zhat (G.face x))
        = G.edge (G.node (G.edge (G.node (G.edge x)))) := by
          simp [zmove]
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    _ = G.face.symm (G.face.symm (G.edge x)) := by
          rw [Hypermap.edge_node_eq_face_symm]
          rw [Hypermap.edge_node_eq_face_symm]
    _ = ((G.face : G.Dart → G.Dart)^[3]) (G.edge x) := by
          have hle : 2 ≤ G.arity (G.edge x) := by omega
          have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
            (G := G) (x := G.edge x) (n := 2) hle
          simpa [Function.iterate_succ_apply, hspoke] using h
    _ = G.edge (G.edge (((G.face : G.Dart → G.Dart)^[3])
          (G.edge x))) := by
          rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem arity_node_node_face3_edge_eq_zhat_face_of_spoke5
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 5) :
    G.arity (G.node (G.node (((G.face : G.Dart → G.Dart)^[3])
      (G.edge x)))) =
      G.arity (zmove G ZPartLoc.Zhat (G.face x)) := by
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (((G.face : G.Dart → G.Dart)^[3]) (G.edge x))]
  rw [Hypermap.arity_face]
  rw [zhat_face_eq_edge_face3_edge_of_spoke5 (G := G) hPlain hspoke]

theorem node_edge_eq_face_edge_face_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.node (G.edge x) = G.face (G.edge (G.face x)) := by
  rw [Hypermap.Plain.edge_eq_node_face (G := G) hPlain x]
  exact Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic (G.face x)

theorem zfan0l_face_eq_face_edge_face_symm2_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan0l (G.face x) =
      G.face
        (G.edge (((G.face.symm : G.Dart → G.Dart)^[2])
          (G.edge x))) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]

theorem qstepR_face3_edge_eq_zfan0l_face_of_spoke6
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 6) :
    qstepR G (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) =
      zmove G ZPartLoc.Zfan0l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan0l_face_eq_face_edge_face_symm2_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[2]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[4]) (G.edge x) := by
    have hle : 2 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 2) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]

theorem zfan1l_face_eq_face_edge_face_symm3_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan1l (G.face x) =
      G.face
        (G.edge (((G.face.symm : G.Dart → G.Dart)^[3])
          (G.edge x))) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]

theorem qstepR_face3_edge_eq_zfan1l_face_of_spoke7
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 7) :
    qstepR G (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) =
      zmove G ZPartLoc.Zfan1l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan1l_face_eq_face_edge_face_symm3_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[3]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[4]) (G.edge x) := by
    have hle : 3 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 3) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]

theorem zfan2l_face_eq_face_edge_face_symm4_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    zmove G ZPartLoc.Zfan2l (G.face x) =
      G.face
        (G.edge (((G.face.symm : G.Dart → G.Dart)^[4])
          (G.edge x))) := by
  simp [zmove, Function.iterate_succ_apply]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]
  rw [Hypermap.edge_node_eq_face_symm]

theorem qstepR_face3_edge_eq_zfan2l_face_of_spoke8
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {x : G.Dart} (hspoke : G.arity (G.edge x) = 8) :
    qstepR G (((G.face : G.Dart → G.Dart)^[3]) (G.edge x)) =
      zmove G ZPartLoc.Zfan2l (G.face x) := by
  rw [qstepR]
  rw [node_edge_eq_face_edge_face_of_plain_cubic (G := G) hPlain hCubic]
  rw [zfan2l_face_eq_face_edge_face_symm4_edge (G := G) hPlain x]
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[4]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[4]) (G.edge x) := by
    have hle : 4 ≤ G.arity (G.edge x) := by omega
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := 4) hle
    simpa [hspoke] using h
  rw [hsymm]
  simp [Function.iterate_succ_apply]


end SoundnessInternal

end Schematic.Math.GraphTheory.FourColor.RedPart
