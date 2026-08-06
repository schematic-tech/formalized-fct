import FourColorTheorem.FourColor.Hypermap.WalkupColoring.FaceFibers

/-!
Face-class coloring on the twice-deleted Walkup map.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

theorem Coloring.faceClassColor_face_eq
    (hG : G.Bridgeless)
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (fallback : G.Dart → Color) (x : G.Dart) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.face x) =
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x := by
  classical
  by_cases hx : ∃ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w
  · have hy : ∃ w : ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
          G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.face x) w := by
      rcases hx with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      have hback : PermReachable G.face (G.face x) x := by
        simpa using PermReachable.backward G.face (G.face x)
      exact PermReachable.trans G.face hback hw
    have hxspec :
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne x (Classical.choose hx) :=
      Classical.choose_spec hx
    have hyspec :
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.face x)
          (Classical.choose hy) :=
      Classical.choose_spec hy
    have hreach :
        PermReachable G.face (Classical.choose hx).1.1
          (Classical.choose hy).1.1 := by
      have hleft : PermReachable G.face (Classical.choose hx).1.1 x :=
        PermReachable.symm G.face hxspec
      have hstep : PermReachable G.face x (G.face x) :=
        PermReachable.forward G.face x
      exact PermReachable.trans G.face hleft
        (PermReachable.trans G.face hstep hyspec)
    have hcolor :=
      Coloring.eq_of_walkupE_walkupE_face_project_reachable
        (G := G) hk hreach
    simpa [walkupE_walkupE_faceClassColor, hx, hy] using hcolor
  · have hy : ¬ ∃ w : ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
          G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.face x) w := by
      rintro ⟨w, hw⟩
      apply hx
      refine ⟨w, ?_⟩
      exact PermReachable.trans G.face (PermReachable.forward G.face x) hw
    have hsame : x = G.face x :=
      G.walkupE_walkupE_twoNodeFaceFiber_eq_of_empty_of_reachable
        hG hz_ne hzz (by
          intro w hw
          exact hx ⟨w, hw⟩) (PermReachable.forward G.face x)
    have hfallback : fallback (G.face x) = fallback x := by
      rw [← hsame]
    simpa [walkupE_walkupE_faceClassColor, hx, hy] using hfallback

theorem Coloring.faceClassColor_eq_of_fiber
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (fallback : G.Dart → Color)
    (h : ∃ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w)
    {w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart}
    (hw : G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback x = k w := by
  classical
  have hchoose :
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne x (Classical.choose h) :=
    Classical.choose_spec h
  have hreach : PermReachable G.face (Classical.choose h).1.1 w.1.1 :=
    PermReachable.trans G.face (PermReachable.symm G.face hchoose) hw
  have hcolor :=
    Coloring.eq_of_walkupE_walkupE_face_project_reachable
      (G := G) hk hreach
  simpa [walkupE_walkupE_faceClassColor, h] using hcolor.symm

theorem Coloring.faceClassColor_edge_ne_of_edge_lift
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (fallback : G.Dart → Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedge :
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
          (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode) =
        G.walkupE_walkupE_liftTwoNode hz_ne (G.edge x) hexz hexnode) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.edge x) ≠
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  let wx := G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode
  let wex := G.walkupE_walkupE_liftTwoNode hz_ne (G.edge x) hexz hexnode
  have hxFiber : ∃ w : H.Dart,
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w :=
    G.walkupE_walkupE_twoNodeFaceFiber_nonempty_of_ne hz_ne hxz hxnode
  have hexFiber : ∃ w : H.Dart,
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.edge x) w :=
    G.walkupE_walkupE_twoNodeFaceFiber_nonempty_of_ne
      hz_ne hexz hexnode
  have hxColor :
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x = k wx :=
    Coloring.faceClassColor_eq_of_fiber
      (G := G) hz_ne hk fallback hxFiber
      (w := wx) (PermReachable.refl G.face x)
  have hexColor :
      G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.edge x) =
        k wex :=
    Coloring.faceClassColor_eq_of_fiber
      (G := G) hz_ne hk fallback hexFiber
      (w := wex) (PermReachable.refl G.face (G.edge x))
  intro hsame
  have hedgeColor : k (H.edge wx) = k wx := by
    calc
      k (H.edge wx) = k wex := by rw [hedge]
      _ = G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.edge x) :=
        hexColor.symm
      _ = G.walkupE_walkupE_faceClassColor hz_ne k fallback x := hsame
      _ = k wx := hxColor
  exact Coloring.edge_ne (G := H) hk wx hedgeColor

theorem Coloring.faceClassColor_edge_ne_of_plain_of_ne
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hG : G.Plain)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (fallback : G.Dart → Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hxedgez : x ≠ G.edge z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedgeNode : G.edge z ≠ G.node z)
    (hfaceEdgeNode : G.face (G.edge x) ≠ G.node z) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.edge x) ≠
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x :=
  Coloring.faceClassColor_edge_ne_of_edge_lift
    (G := G) hz_ne hk fallback hxz hxnode hexz hexnode
    (by
      apply Subtype.ext
      apply Subtype.ext
      exact G.walkupE_walkupE_edge_apply_coe_of_plain_of_ne
        hG hz_ne hxz hxnode hxedgez hexz hexnode
        hedgeNode hfaceEdgeNode)

theorem walkupE_walkupE_liftTwoNode_face_edge_coe_of_node_node_eq
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    let H := (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
    let wx := G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode
    ((H.face (H.edge wx)).1.1 = G.face (G.edge x)) := by
  intro H wx
  apply G.node.injective
  have hnode :=
    G.walkupE_walkupE_node_apply_coe_of_node_node_eq
      hz_ne hzz (H.face (H.edge wx))
  calc
    G.node ((H.face (H.edge wx)).1.1) =
        (H.node (H.face (H.edge wx))).1.1 := hnode.symm
    _ = wx.1.1 := by
      rw [H.node_face_edge]
    _ = x := rfl
    _ = G.node (G.face (G.edge x)) := (G.node_face_edge x).symm

theorem Coloring.faceClassColor_edge_ne_of_outside
    (hG : G.Bridgeless)
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k)
    (fallback : G.Dart → Color)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback (G.edge x) ≠
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  let wx := G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode
  let fwex : H.Dart := H.face (H.edge wx)
  have hxFiber : ∃ w : H.Dart,
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w :=
    G.walkupE_walkupE_twoNodeFaceFiber_nonempty_of_ne hz_ne hxz hxnode
  have hproj :
      fwex.1.1 = G.face (G.edge x) :=
    G.walkupE_walkupE_liftTwoNode_face_edge_coe_of_node_node_eq
      hz_ne hzz hxz hxnode
  have hfaceEdgeFiber : ∃ w : H.Dart,
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.face (G.edge x)) w := by
    refine ⟨fwex, ?_⟩
    change PermReachable G.face (G.face (G.edge x)) fwex.1.1
    rw [hproj]
    exact PermReachable.refl G.face (G.face (G.edge x))
  have hxColor :
      G.walkupE_walkupE_faceClassColor hz_ne k fallback x = k wx :=
    Coloring.faceClassColor_eq_of_fiber
      (G := G) hz_ne hk fallback hxFiber
      (w := wx) (PermReachable.refl G.face x)
  have hfaceEdgeColor :
      G.walkupE_walkupE_faceClassColor hz_ne k fallback
          (G.face (G.edge x)) = k fwex :=
    Coloring.faceClassColor_eq_of_fiber
      (G := G) hz_ne hk fallback hfaceEdgeFiber
      (w := fwex) (by
        change PermReachable G.face (G.face (G.edge x)) fwex.1.1
        rw [hproj]
        exact PermReachable.refl G.face (G.face (G.edge x)))
  intro hsame
  have hfaceStep :
      G.walkupE_walkupE_faceClassColor hz_ne k fallback
          (G.face (G.edge x)) =
        G.walkupE_walkupE_faceClassColor hz_ne k fallback
          (G.edge x) :=
    Coloring.faceClassColor_face_eq (G := G)
      hG hz_ne hzz hk fallback (G.edge x)
  have hedgeColor : k (H.edge wx) = k wx := by
    calc
      k (H.edge wx) = k (H.face (H.edge wx)) := by
        exact (Coloring.face_eq (G := H) hk (H.edge wx)).symm
      _ = G.walkupE_walkupE_faceClassColor hz_ne k fallback
            (G.face (G.edge x)) := hfaceEdgeColor.symm
      _ = G.walkupE_walkupE_faceClassColor hz_ne k fallback
            (G.edge x) := hfaceStep
      _ = G.walkupE_walkupE_faceClassColor hz_ne k fallback x := hsame
      _ = k wx := hxColor
  exact Coloring.edge_ne (G := H) hk wx hedgeColor

theorem walkupE_walkupE_twoNodeFaceFiber_empty_z_of_face_fixed
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hfacez : G.face z = z) :
    ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne z w := by
  intro w hw
  exact PermSkip.not_permReachable_fixed_of_ne G.face hfacez w.1.2
    (PermReachable.symm G.face hw)

theorem walkupE_walkupE_twoNodeFaceFiber_empty_node_of_face_fixed
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hfacenode : G.face (G.node z) = G.node z) :
    ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.node z) w := by
  intro w hw
  have hw_ne : w.1.1 ≠ G.node z := by
    intro hbad
    exact w.2 (Subtype.ext hbad)
  exact PermSkip.not_permReachable_fixed_of_ne G.face hfacenode hw_ne
    (PermReachable.symm G.face hw)

theorem Plain.face_z_eq_self_of_edge_z_eq_node
    (hG : G.Plain) {z : G.Dart}
    (hedgeNode : G.edge z = G.node z) :
    G.face z = z := by
  apply G.node.injective
  calc
    G.node (G.face z) = G.edge z :=
      Plain.node_face_eq_edge (G := G) hG z
    _ = G.node z := hedgeNode

theorem Plain.face_node_eq_self_of_edge_z_eq_node
    (hG : G.Plain) {z : G.Dart}
    (hzz : G.node (G.node z) = z)
    (hedgeNode : G.edge z = G.node z) :
    G.face (G.node z) = G.node z := by
  have hedge_node : G.edge (G.node z) = z := by
    rw [← hedgeNode]
    exact Plain.edge_edge (G := G) hG z
  apply G.node.injective
  calc
    G.node (G.face (G.node z)) = G.edge (G.node z) :=
      Plain.node_face_eq_edge (G := G) hG (G.node z)
    _ = z := hedge_node
    _ = G.node (G.node z) := hzz.symm

theorem Coloring.faceClassColor_edge_ne_z
    (hPlain : G.Plain) (hBridgeless : G.Bridgeless)
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k) :
    G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) (G.edge z) ≠
      G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) z := by
  by_cases hedgeNode : G.edge z = G.node z
  · have hfacez : G.face z = z :=
      Plain.face_z_eq_self_of_edge_z_eq_node (G := G) hPlain hedgeNode
    have hfacenode : G.face (G.node z) = G.node z :=
      Plain.face_node_eq_self_of_edge_z_eq_node
        (G := G) hPlain hzz hedgeNode
    have hsep :=
      G.walkupE_walkupE_faceClassColor_twoNodeFallback_self_ne_node_of_empty
        hz_ne k
        (G.walkupE_walkupE_twoNodeFaceFiber_empty_z_of_face_fixed
          hz_ne hfacez)
        (G.walkupE_walkupE_twoNodeFaceFiber_empty_node_of_face_fixed
          hz_ne hfacenode)
    rw [hedgeNode]
    exact hsep.symm
  · have hy :=
      Coloring.faceClassColor_edge_ne_of_outside
        (G := G) hBridgeless hz_ne hzz hk
        (G.walkupE_walkupE_twoNodeFallback z)
        (x := G.edge z)
        (Plain.edge_ne (G := G) hPlain z) hedgeNode
    intro hsame
    apply hy
    rw [Plain.edge_edge (G := G) hPlain z]
    exact hsame.symm

theorem Coloring.faceClassColor_edge_ne_node
    (hPlain : G.Plain) (hBridgeless : G.Bridgeless)
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    {k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color}
    (hk : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k) :
    G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) (G.edge (G.node z)) ≠
      G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) (G.node z) := by
  by_cases hedgeNode : G.edge z = G.node z
  · have hedge_node : G.edge (G.node z) = z := by
      rw [← hedgeNode]
      exact Plain.edge_edge (G := G) hPlain z
    have hfacez : G.face z = z :=
      Plain.face_z_eq_self_of_edge_z_eq_node (G := G) hPlain hedgeNode
    have hfacenode : G.face (G.node z) = G.node z :=
      Plain.face_node_eq_self_of_edge_z_eq_node
        (G := G) hPlain hzz hedgeNode
    have hsep :=
      G.walkupE_walkupE_faceClassColor_twoNodeFallback_self_ne_node_of_empty
        hz_ne k
        (G.walkupE_walkupE_twoNodeFaceFiber_empty_z_of_face_fixed
          hz_ne hfacez)
        (G.walkupE_walkupE_twoNodeFaceFiber_empty_node_of_face_fixed
          hz_ne hfacenode)
    rw [hedge_node]
    exact hsep
  · have hyz : G.edge (G.node z) ≠ z := by
      intro hbad
      have hsame : G.edge (G.node z) = G.edge (G.edge z) := by
        rw [hbad, Plain.edge_edge (G := G) hPlain z]
      exact hedgeNode (G.edge.injective hsame).symm
    have hynode : G.edge (G.node z) ≠ G.node z :=
      Plain.edge_ne (G := G) hPlain (G.node z)
    have hy :=
      Coloring.faceClassColor_edge_ne_of_outside
        (G := G) hBridgeless hz_ne hzz hk
        (G.walkupE_walkupE_twoNodeFallback z)
        (x := G.edge (G.node z)) hyz hynode
    intro hsame
    apply hy
    rw [Plain.edge_edge (G := G) hPlain (G.node z)]
    exact hsame.symm

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
