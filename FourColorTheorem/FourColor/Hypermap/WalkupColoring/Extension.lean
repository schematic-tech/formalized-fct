import FourColorTheorem.FourColor.Hypermap.WalkupColoring.FaceClassColoring

/-!
Extension of a twice-deleted Walkup coloring to the original hypermap.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

/-- Extend a colouring of the twice-deleted map to the original dart set by
choosing arbitrary colours for the two deleted darts. -/
def walkupE_walkupE_extendColorTwoNode
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (cz cnode : Color) (x : G.Dart) : Color :=
  if hxz : x = z then cz
  else if hxnode : x = G.node z then cnode
  else k (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)

@[simp]
theorem walkupE_walkupE_extendColorTwoNode_z
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (cz cnode : Color) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode z = cz := by
  simp [walkupE_walkupE_extendColorTwoNode]

theorem walkupE_walkupE_extendColorTwoNode_node
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (cz cnode : Color) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode (G.node z) =
      cnode := by
  have hzne : G.node z ≠ z := hz_ne
  simp [walkupE_walkupE_extendColorTwoNode, hzne]

theorem walkupE_walkupE_extendColorTwoNode_of_ne
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (cz cnode : Color)
    (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x =
      k (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) := by
  simp [walkupE_walkupE_extendColorTwoNode, hxz, hxnode]

theorem Coloring.extendColorTwoNode_eq_of_face_reachable
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (cz cnode : Color)
    {x y : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hyz : y ≠ z) (hynode : y ≠ G.node z)
    (hxy : PermReachable G.face x y) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode y =
      G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x := by
  rw [G.walkupE_walkupE_extendColorTwoNode_of_ne hz_ne k cz cnode hyz hynode,
    G.walkupE_walkupE_extendColorTwoNode_of_ne hz_ne k cz cnode hxz hxnode]
  exact Coloring.eq_of_walkupE_walkupE_face_project_reachable (G := G) hk hxy

theorem Coloring.extendColorTwoNode_edge_ne_of_edge_lift
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (cz cnode : Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedge :
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
          (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) =
        G.walkupE_walkupE_liftTwoNode hz_ne (G.edge x) hexz hexnode) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode (G.edge x) ≠
      G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x := by
  rw [G.walkupE_walkupE_extendColorTwoNode_of_ne hz_ne k cz cnode hexz hexnode,
    G.walkupE_walkupE_extendColorTwoNode_of_ne hz_ne k cz cnode hxz hxnode]
  intro hsame
  have hsame' :
      k (((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
          (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) =
        k (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) := by
    simpa [hedge] using hsame
  exact Coloring.edge_ne (G := (G.walkupE z).walkupE
    (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) hk
    (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) hsame'

theorem walkupE_walkupE_liftTwoNode_edge_eq_of_plain_of_ne
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hxedgez : x ≠ G.edge z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedgeNode : G.edge z ≠ G.node z)
    (hfaceEdgeNode : G.face (G.edge x) ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.edge x) hexz hexnode := by
  apply Subtype.ext
  apply Subtype.ext
  exact G.walkupE_walkupE_edge_apply_coe_of_plain_of_ne
    hG hz_ne hxz hxnode hxedgez hexz hexnode hedgeNode hfaceEdgeNode

theorem walkupE_walkupE_liftTwoNode_edge_eq_edge_z
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hedgeNode : G.edge z ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (G.walkupE_walkupE_liftTwoNode hz_ne (G.edge z)
          (Plain.edge_ne (G := G) hG z) hedgeNode) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.edge (G.node z))
        (by
          intro hbad
          apply hedgeNode
          calc
            G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
            _ = G.node z := Plain.edge_edge (G := G) hG (G.node z))
        (Plain.edge_ne (G := G) hG (G.node z)) := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  let w : H.Dart :=
    G.walkupE_walkupE_liftTwoNode hz_ne (G.edge z)
      (Plain.edge_ne (G := G) hG z) hedgeNode
  have hedge_u_val : ((G.walkupE z).edge u).1 = G.edge z := by
    exact G.walkupE_edge_apply_coe_of_plain_of_eq_node hG hz_ne
  have hedge_u_ne : (G.walkupE z).edge u ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_u_val] at hval
    exact hedgeNode hval
  have hedge_node_ne_z : G.edge (G.node z) ≠ z := by
    intro hbad
    apply hedgeNode
    calc
      G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
      _ = G.node z := Plain.edge_edge (G := G) hG (G.node z)
  have hedge_w_val : ((G.walkupE z).edge w.1).1 =
      G.edge (G.node z) := by
    exact G.walkupE_edge_apply_coe_of_plain_of_eq_edge
      hG w.1 hedgeNode rfl
  have hedge_w_eq :
      (G.walkupE z).edge w.1 =
        (⟨G.edge (G.node z), hedge_node_ne_z⟩ :
          (G.walkupE z).Dart) := by
    apply Subtype.ext
    exact hedge_w_val
  have hedge_w_ne_u : (G.walkupE z).edge w.1 ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_w_val] at hval
    exact Plain.edge_ne (G := G) hG (G.node z) hval
  have hface_edge_node :
      G.face (G.edge (G.node z)) = z := by
    apply G.node.injective
    exact G.node_face_edge (G.node z)
  have hface_z_ne_node : G.face z ≠ G.node z := by
    intro hbad
    exact Plain.edge_ne (G := G) hG z
      (by
        calc
          G.edge z = G.node (G.face z) :=
            (Plain.node_face_eq_edge (G := G) hG z).symm
          _ = G.node (G.node z) := by rw [hbad]
          _ = z := hzz)
  have hface_inner_val :
      ((G.walkupE z).face ((G.walkupE z).edge w.1)).1 =
        G.face z := by
    rw [hedge_w_eq]
    exact G.walkupE_face_apply_coe_of_eq
      (⟨G.edge (G.node z), hedge_node_ne_z⟩ : (G.walkupE z).Dart)
      hface_edge_node
  have hface_outer_ne :
      (G.walkupE z).face ((G.walkupE z).edge w.1) ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hface_inner_val] at hval
    exact hface_z_ne_node hval
  apply Subtype.ext
  apply Subtype.ext
  change (((G.walkupE z).walkupE u).edge w).1.1 =
    G.edge (G.node z)
  rw [G.walkupE_walkupE_edge_apply_coe]
  unfold walkupSkipEdgeAux
  rw [if_neg hedge_u_ne]
  rw [if_neg hface_outer_ne]
  rw [if_neg hedge_w_ne_u]
  exact hedge_w_val

theorem walkupE_walkupE_liftTwoNode_edge_eq_edge_node
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hedgeNode : G.edge z ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (G.walkupE_walkupE_liftTwoNode hz_ne (G.edge (G.node z))
          (by
            intro hbad
            apply hedgeNode
            calc
              G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
              _ = G.node z := Plain.edge_edge (G := G) hG (G.node z))
          (Plain.edge_ne (G := G) hG (G.node z))) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.edge z)
        (Plain.edge_ne (G := G) hG z) hedgeNode := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  have hedge_node_ne_z : G.edge (G.node z) ≠ z := by
    intro hbad
    apply hedgeNode
    calc
      G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
      _ = G.node z := Plain.edge_edge (G := G) hG (G.node z)
  let w : H.Dart :=
    G.walkupE_walkupE_liftTwoNode hz_ne (G.edge (G.node z))
      hedge_node_ne_z (Plain.edge_ne (G := G) hG (G.node z))
  have hedge_u_val : ((G.walkupE z).edge u).1 = G.edge z := by
    exact G.walkupE_edge_apply_coe_of_plain_of_eq_node hG hz_ne
  have hedge_u_ne : (G.walkupE z).edge u ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_u_val] at hval
    exact hedgeNode hval
  have hedge_node_ne_edge_z :
      G.edge (G.node z) ≠ G.edge z := by
    intro hbad
    exact hz_ne (G.edge.injective hbad)
  have hedge_w_val : ((G.walkupE z).edge w.1).1 = G.node z := by
    calc
      ((G.walkupE z).edge w.1).1 =
          G.edge (G.edge (G.node z)) := by
            exact G.walkupE_edge_apply_coe_of_plain_of_ne
              hG w.1
              (Plain.edge_ne (G := G) hG (G.node z))
              hedge_node_ne_edge_z
      _ = G.node z := Plain.edge_edge (G := G) hG (G.node z)
  have hedge_w_eq : (G.walkupE z).edge w.1 = u := by
    apply Subtype.ext
    exact hedge_w_val
  have hnode_u_eq : (G.walkupE z).node u = u := by
    apply Subtype.ext
    exact G.walkupE_node_apply_coe_of_eq u hzz
  have hedge_node_u_val :
      ((G.walkupE z).edge ((G.walkupE z).node u)).1 = G.edge z := by
    rw [hnode_u_eq]
    exact hedge_u_val
  have hface_z_ne_node : G.face z ≠ G.node z := by
    intro hbad
    exact Plain.edge_ne (G := G) hG z
      (by
        calc
          G.edge z = G.node (G.face z) :=
            (Plain.node_face_eq_edge (G := G) hG z).symm
          _ = G.node (G.node z) := by rw [hbad]
          _ = z := hzz)
  have hface_node_ne_node : G.face (G.node z) ≠ G.node z := by
    intro hbad
    apply hedgeNode
    calc
      G.edge z = G.edge (G.edge (G.node z)) := by
        have hEdgeNode :
            G.edge (G.node z) = z := by
          calc
            G.edge (G.node z) = G.node (G.face (G.node z)) :=
              (Plain.node_face_eq_edge (G := G) hG (G.node z)).symm
            _ = G.node (G.node z) := by rw [hbad]
            _ = z := hzz
        rw [hEdgeNode]
      _ = G.node z := Plain.edge_edge (G := G) hG (G.node z)
  have hface_u_ne : (G.walkupE z).face u ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    by_cases hface_node_z : G.face (G.node z) = z
    · have hface_u_val : ((G.walkupE z).face u).1 = G.face z := by
        exact G.walkupE_face_apply_coe_of_eq u hface_node_z
      rw [hface_u_val] at hval
      exact hface_z_ne_node hval
    · have hface_u_val :
          ((G.walkupE z).face u).1 = G.face (G.node z) := by
        exact G.walkupE_face_apply_coe_of_ne u hface_node_z
      rw [hface_u_val] at hval
      exact hface_node_ne_node hval
  apply Subtype.ext
  apply Subtype.ext
  change (((G.walkupE z).walkupE u).edge w).1.1 = G.edge z
  rw [G.walkupE_walkupE_edge_apply_coe]
  unfold walkupSkipEdgeAux
  rw [if_neg hedge_u_ne]
  rw [hedge_w_eq]
  rw [if_neg hface_u_ne]
  rw [if_pos rfl]
  exact hedge_node_u_val

theorem walkupE_walkupE_liftTwoNode_edge_edge_eq_edge_z
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hedgeNode : G.edge z ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
            (G.walkupE_walkupE_liftTwoNode hz_ne (G.edge z)
              (Plain.edge_ne (G := G) hG z) hedgeNode)) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.edge z)
        (Plain.edge_ne (G := G) hG z) hedgeNode := by
  rw [G.walkupE_walkupE_liftTwoNode_edge_eq_edge_z
      hG hz_ne hzz hedgeNode]
  exact G.walkupE_walkupE_liftTwoNode_edge_eq_edge_node
    hG hz_ne hzz hedgeNode

theorem walkupE_walkupE_liftTwoNode_edge_edge_eq_edge_node
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hedgeNode : G.edge z ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
            (G.walkupE_walkupE_liftTwoNode hz_ne (G.edge (G.node z))
              (by
                intro hbad
                apply hedgeNode
                calc
                  G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
                  _ = G.node z :=
                    Plain.edge_edge (G := G) hG (G.node z))
              (Plain.edge_ne (G := G) hG (G.node z)))) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.edge (G.node z))
        (by
          intro hbad
          apply hedgeNode
          calc
            G.edge z = G.edge (G.edge (G.node z)) := by rw [hbad]
            _ = G.node z := Plain.edge_edge (G := G) hG (G.node z))
        (Plain.edge_ne (G := G) hG (G.node z)) := by
  rw [G.walkupE_walkupE_liftTwoNode_edge_eq_edge_node
      hG hz_ne hzz hedgeNode]
  exact G.walkupE_walkupE_liftTwoNode_edge_eq_edge_z
    hG hz_ne hzz hedgeNode

theorem walkupE_walkupE_liftTwoNode_edge_edge_eq_of_plain_of_ne
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hxedgez : x ≠ G.edge z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedgeNode : G.edge z ≠ G.node z)
    (hfaceEdgeNode : G.face (G.edge x) ≠ G.node z)
    (hfaceNode : G.face x ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
            (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) =
      G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode := by
  have hEdgeEdgeX : G.edge (G.edge x) = x :=
    Plain.edge_edge (G := G) hG x
  have hyedgez : G.edge x ≠ G.edge z := by
    intro hbad
    exact hxz (G.edge.injective hbad)
  have heyxz : G.edge (G.edge x) ≠ z := by
    simpa [hEdgeEdgeX] using hxz
  have heyxnode : G.edge (G.edge x) ≠ G.node z := by
    simpa [hEdgeEdgeX] using hxnode
  have hfaceEdgeEdgeNode :
      G.face (G.edge (G.edge x)) ≠ G.node z := by
    simpa [hEdgeEdgeX] using hfaceNode
  rw [G.walkupE_walkupE_liftTwoNode_edge_eq_of_plain_of_ne
      hG hz_ne hxz hxnode hxedgez hexz hexnode hedgeNode hfaceEdgeNode]
  rw [G.walkupE_walkupE_liftTwoNode_edge_eq_of_plain_of_ne
      hG hz_ne hexz hexnode hyedgez heyxz heyxnode
      hedgeNode hfaceEdgeEdgeNode]
  apply Subtype.ext
  apply Subtype.ext
  exact hEdgeEdgeX

theorem Coloring.extendColorTwoNode_edge_ne_of_plain_of_ne
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hG : G.Plain)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (cz cnode : Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hxedgez : x ≠ G.edge z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedgeNode : G.edge z ≠ G.node z)
    (hfaceEdgeNode : G.face (G.edge x) ≠ G.node z) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode (G.edge x) ≠
      G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x :=
  Coloring.extendColorTwoNode_edge_ne_of_edge_lift
    (G := G) hz_ne hk cz cnode hxz hxnode hexz hexnode
    (G.walkupE_walkupE_liftTwoNode_edge_eq_of_plain_of_ne
      hG hz_ne hxz hxnode hxedgez hexz hexnode hedgeNode hfaceEdgeNode)

theorem walkupE_walkupE_liftTwoNode_face_eq_of_ne
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hfacez : G.face x ≠ z) (hfacenode : G.face x ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).face
        (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) =
      G.walkupE_walkupE_liftTwoNode hz_ne (G.face x) hfacez hfacenode := by
  apply Subtype.ext
  apply Subtype.ext
  exact G.walkupE_walkupE_face_apply_coe_of_ne
    hz_ne hxz hxnode hfacez hfacenode

theorem Coloring.extendColorTwoNode_face_eq_of_ne
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (cz cnode : Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hfacez : G.face x ≠ z) (hfacenode : G.face x ≠ G.node z) :
    G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode (G.face x) =
      G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x := by
  rw [G.walkupE_walkupE_extendColorTwoNode_of_ne
      hz_ne k cz cnode hfacez hfacenode,
    G.walkupE_walkupE_extendColorTwoNode_of_ne
      hz_ne k cz cnode hxz hxnode]
  have hface_eq :=
    G.walkupE_walkupE_liftTwoNode_face_eq_of_ne
      hz_ne hxz hxnode hfacez hfacenode
  calc
    k (G.walkupE_walkupE_liftTwoNode hz_ne (G.face x) hfacez hfacenode) =
        k (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).face
            (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)) := by
          rw [hface_eq]
    _ = k (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) :=
      Coloring.face_eq (G := (G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)) hk
        (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode)

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
