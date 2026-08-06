import FourColorTheorem.FourColor.Discharging.PartGeometry.RangeRelations

/-! Spoke, hat, and fan geometry before sector specialization. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace SubpartLoc

noncomputable def spokeRayArity (G : Hypermap.{u}) (n : Nat)
    (x : G.Dart) : Nat :=
  G.arity (G.edge ((G.face : G.Dart → G.Dart)^[n] (G.edge x)))

theorem spokeRayArity_two
    {G : Hypermap.{u}} (x : G.Dart) :
    spokeRayArity G 2 x = G.arity (move Phat G x) := by
  rfl

theorem spokeRayArity_three
    {G : Hypermap.{u}} (x : G.Dart) :
    spokeRayArity G 3 x = G.arity (move Pfan1 G x) := by
  rfl

theorem spokeRayArity_four
    {G : Hypermap.{u}} (x : G.Dart) :
    spokeRayArity G 4 x = G.arity (move Pfan2 G x) := by
  rfl

theorem spokeRayArity_five
    {G : Hypermap.{u}} (x : G.Dart) :
    spokeRayArity G 5 x = G.arity (move Pfan3 G x) := by
  rfl

theorem spokeRayArity_mirror_face_symm
    {G : Hypermap.{u}} (hPlain : G.Plain) (n : Nat) (x : G.Dart) :
    spokeRayArity G.mirror n (G.face x) =
      G.arity (G.edge
        ((G.face.symm : G.Dart → G.Dart)^[n] (G.edge x))) := by
  unfold spokeRayArity
  rw [G.arity_mirror]
  change G.arity
      (G.face
        (G.node
          ((G.face.symm : G.Dart → G.Dart)^[n]
            (G.face (G.node (G.face x)))))) =
    G.arity (G.edge
      ((G.face.symm : G.Dart → G.Dart)^[n] (G.edge x)))
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  rw [Equiv.symm_iterate_apply_self G.face n (G.edge x)]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
  exact Hypermap.arity_face (G := G) _

theorem spokeRayArity_mirror_face
    {G : Hypermap.{u}} (hPlain : G.Plain) {n m : Nat}
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = m)
    (hn : n ≤ m) :
    spokeRayArity G.mirror n (G.face x) =
      spokeRayArity G (m - n) x := by
  rw [spokeRayArity_mirror_face_symm (G := G) hPlain n x]
  unfold spokeRayArity
  have hspoke' : G.arity (G.edge x) = m := by
    simpa [move] using hspoke
  have hle : n ≤ G.arity (G.edge x) := by
    rw [hspoke']
    exact hn
  have hsymm := Hypermap.face_symm_iter_eq_face_iter_sub_arity
    (G := G) (x := G.edge x) (n := n) hle
  rw [hsymm]
  rw [hspoke']

theorem spokeRayArity_mirror_face_iter_succ
    {G : Hypermap.{u}} (hPlain : G.Plain) {n m k : Nat}
    (x : G.Dart)
    (hspoke :
      G.arity (move Pspoke G ((G.face : G.Dart → G.Dart)^[k] x)) = m)
    (hn : n ≤ m) :
    spokeRayArity G.mirror n
        ((G.face : G.Dart → G.Dart)^[k + 1] x) =
      spokeRayArity G (m - n)
        ((G.face : G.Dart → G.Dart)^[k] x) := by
  rw [show ((G.face : G.Dart → G.Dart)^[k + 1] x) =
      G.face (((G.face : G.Dart → G.Dart)^[k] x)) by
    rw [Function.iterate_succ_apply']]
  exact spokeRayArity_mirror_face (G := G) hPlain
    (n := n) (m := m) (((G.face : G.Dart → G.Dart)^[k] x)) hspoke hn

theorem spokeRayArity_mirror_face_iter_of_hub
    {G : Hypermap.{u}} (hPlain : G.Plain) {hub i n m : Nat}
    {x : G.Dart}
    (hHub : G.arity x = hub)
    (hi : i < hub)
    (hspoke :
      G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)) = m)
    (hn : n ≤ m) :
    spokeRayArity G.mirror n ((G.mirror.face : G.Dart → G.Dart)^[i] x) =
      spokeRayArity G (m - n)
        ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x) := by
  have hi_le_arity : i ≤ G.arity x := by
    omega
  rw [Hypermap.mirror_face_iter_eq_face_iter_sub_arity (G := G) hi_le_arity]
  rw [hHub]
  have hsub : hub - i = hub - (i + 1) + 1 := by
    omega
  rw [hsub]
  rw [Function.iterate_succ_apply']
  exact spokeRayArity_mirror_face (G := G) hPlain
    (n := n) (m := m)
    (((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)) hspoke hn

theorem move_spoke_face_edge_face_face_eq_face_symm_spoke_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    move Pspoke G (G.face (G.edge (G.face (G.face x)))) =
      G.face.symm (move Pspoke G (G.face x)) := by
  dsimp [move]
  calc
    G.edge (G.face (G.edge (G.face (G.face x)))) =
        G.edge (G.node (G.edge (G.face x))) := by
          congr 1
          calc
            G.face (G.edge (G.face (G.face x))) =
                G.node.symm (G.face (G.face x)) :=
                  Hypermap.face_edge_eq_node_symm G _
            _ = G.node (G.node (G.face (G.face x))) :=
                  Hypermap.Cubic.node_symm_eq_node_node hCubic _
            _ = G.node (G.edge (G.face x)) := by
                  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain
                    (G.face x)]
    _ = G.face.symm (G.edge (G.face x)) := G.edge_node_eq_face_symm _

theorem arity_spoke_face_edge_face_face_eq_spoke_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (move Pspoke G (G.face (G.edge (G.face (G.face x))))) =
      G.arity (move Pspoke G (G.face x)) := by
  rw [move_spoke_face_edge_face_face_eq_face_symm_spoke_face
    (G := G) hPlain hCubic x]
  exact Hypermap.arity_face_symm (G := G) _

theorem move_hat_face_edge_face_face_eq_face_symm_spoke
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    move Phat G (G.face (G.edge (G.face (G.face x)))) =
      G.face.symm (move Pspoke G x) := by
  dsimp [move]
  apply G.face.injective
  simp only [Equiv.apply_symm_apply]
  simp [Hypermap.face_edge_eq_node_symm G,
    Hypermap.Cubic.node_symm_eq_node_node hCubic,
    Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
  rw [(hCubic (G.edge (G.face x))).1]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]

theorem arity_hat_face_edge_face_face_eq_spoke
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (move Phat G (G.face (G.edge (G.face (G.face x))))) =
      G.arity (move Pspoke G x) := by
  rw [move_hat_face_edge_face_face_eq_face_symm_spoke
    (G := G) hPlain hCubic x]
  exact Hypermap.arity_face_symm (G := G) _

theorem move_fan1_face_edge_face_face_eq_hat_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    move Pfan1 G (G.face (G.edge (G.face (G.face x)))) =
      move Phat G (G.face x) := by
  dsimp [move]
  simp [Hypermap.face_edge_eq_node_symm G,
    Hypermap.Cubic.node_symm_eq_node_node hCubic,
    Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
  rw [(hCubic (G.edge (G.face x))).1]
  rw [Hypermap.face_edge_eq_node_symm G]
  rw [Hypermap.Cubic.node_symm_eq_node_node hCubic]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_fan1_face_edge_face_face_eq_hat_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (move Pfan1 G (G.face (G.edge (G.face (G.face x))))) =
      G.arity (move Phat G (G.face x)) := by
  rw [move_fan1_face_edge_face_face_eq_hat_face
    (G := G) hPlain hCubic x]

theorem move_fan2_face_edge_face_face_eq_fan1_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    move Pfan2 G (G.face (G.edge (G.face (G.face x)))) =
      move Pfan1 G (G.face x) := by
  dsimp [move]
  simp [Hypermap.face_edge_eq_node_symm G,
    Hypermap.Cubic.node_symm_eq_node_node hCubic,
    Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
  rw [(hCubic (G.edge (G.face x))).1]
  rw [Hypermap.face_edge_eq_node_symm G]
  rw [Hypermap.Cubic.node_symm_eq_node_node hCubic]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem arity_fan2_face_edge_face_face_eq_fan1_face
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (move Pfan2 G (G.face (G.edge (G.face (G.face x))))) =
      G.arity (move Pfan1 G (G.face x)) := by
  rw [move_fan2_face_edge_face_face_eq_fan1_face
    (G := G) hPlain hCubic x]

theorem node_face_symm_node_eq_face_edge_face_face_edge
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.node (G.face.symm (G.node x)) =
      G.face (G.edge (G.face (G.face (G.edge x)))) := by
  rw [← Hypermap.edge_node_eq_face_symm (G := G) (G.node x)]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
  rw [Hypermap.Plain.edge_eq_node_face (G := G) hPlain
    (G.face (G.edge x))]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (G.face (G.face (G.edge x)))]

theorem arity_mirror_hat
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.mirror.arity (move Phat G.mirror x) =
      G.arity (move Phat G x) := by
  dsimp [move]
  rw [G.arity_mirror]
  change G.arity
      (G.face
        (G.node
          (G.face.symm (G.face.symm (G.face (G.node x)))))) =
    G.arity (G.edge (G.face (G.face (G.edge x))))
  have hinner :
      G.face.symm (G.face (G.node x)) = G.node x := by
    simp
  rw [hinner]
  rw [Hypermap.arity_face]
  rw [node_face_symm_node_eq_face_edge_face_face_edge
    (G := G) hPlain hCubic x]
  rw [Hypermap.arity_face]

theorem spokeRayArity_mirror_two
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    spokeRayArity G.mirror 2 x = spokeRayArity G 2 x := by
  rw [spokeRayArity_two, spokeRayArity_two]
  exact arity_mirror_hat (G := G) hPlain hCubic x

theorem arity_mirror_spoke_face
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart) :
    G.mirror.arity (move Pspoke G.mirror (G.face x)) =
      G.arity (move Pspoke G x) := by
  dsimp [move]
  rw [G.arity_mirror]
  change G.arity (G.face (G.node (G.face x))) =
    G.arity (G.edge x)
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  exact Hypermap.arity_face (G := G) _

theorem arity_mirror_spoke_of_arity_two
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2) :
    G.mirror.arity (move Pspoke G.mirror x) =
      G.arity (move Pspoke G (G.face x)) := by
  rw [arity_mirror_spoke (G := G) hPlain x]
  rw [Hypermap.face_symm_eq_face_of_arity_two (G := G) hx]

theorem arity_mirror_spoke_face_iter_of_hub
    {G : Hypermap.{u}} (hPlain : G.Plain) {hub i : Nat}
    {x : G.Dart}
    (hHub : G.arity x = hub)
    (hi : i < hub) :
    G.mirror.arity
        (move Pspoke G.mirror ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
      G.arity
        (move Pspoke G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)) := by
  have hi_le_arity : i ≤ G.arity x := by
    omega
  rw [Hypermap.mirror_face_iter_eq_face_iter_sub_arity (G := G) hi_le_arity]
  rw [hHub]
  have hsub : hub - i = hub - (i + 1) + 1 := by
    omega
  rw [hsub]
  rw [Function.iterate_succ_apply']
  exact arity_mirror_spoke_face (G := G) hPlain
    (((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))

theorem arity_mirror_hat_face_iter_of_hub
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub)
    (hi : i ≤ hub) :
    G.mirror.arity
        (move Phat G.mirror ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
      G.arity
        (move Phat G ((G.face : G.Dart → G.Dart)^[hub - i] x)) := by
  have hi_le_arity : i ≤ G.arity x := by
    omega
  rw [Hypermap.mirror_face_iter_eq_face_iter_sub_arity (G := G) hi_le_arity]
  rw [hHub]
  exact arity_mirror_hat (G := G) hPlain hCubic
    (((G.face : G.Dart → G.Dart)^[hub - i] x))

end SubpartLoc

end FourColor

end Schematic.Math.GraphTheory
