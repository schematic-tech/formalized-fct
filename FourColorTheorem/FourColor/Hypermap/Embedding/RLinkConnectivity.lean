import FourColorTheorem.FourColor.Hypermap.Embedding.FaceIndex

/-! Connectivity of selected face classes by `rlink` paths. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

/-- Coq `rlink_connected`: each pair of selected darts can be joined by an
`rlink` path that starts at `node (face x)`, ends at `y`, and whose listed
intermediate darts remain in the selected predicate.  This faithful port is
kept separate from `RLinkConnected`, the earlier reachability-style helper. -/
def RLinkPathConnected (G : Hypermap.{u}) (A : G.Dart → Prop) : Prop :=
  ∀ x y : G.Dart, A x → A y →
    ∃ p : List G.Dart,
      G.RLinkPath (G.node (G.face x)) (p ++ [y]) ∧
        ∀ z : G.Dart, z ∈ p → A z

theorem RLinkPathConnected.of_direct
    {A : G.Dart → Prop}
    (hlink : ∀ ⦃x y : G.Dart⦄, A x → A y →
      G.RLink (G.node (G.face x)) y) :
    G.RLinkPathConnected A := by
  intro x y hx hy
  exact ⟨[], by simpa using RLinkPath.singleton (G := G) (hlink hx hy),
    by simp⟩

theorem RLinkPathConnected.face_orbit (x : G.Dart) :
    G.RLinkPathConnected
      (fun y : G.Dart => PermReachable G.face x y) := by
  apply RLinkPathConnected.of_direct (G := G)
  intro y z hy hz
  exact RLink.node_face_of_faceReachable (G := G)
    (PermReachable.trans G.face (PermReachable.symm G.face hy) hz)

theorem RLinkPathConnected.faceBand_singleton (x : G.Dart) :
    G.RLinkPathConnected (G.FaceBand [x]) := by
  apply RLinkPathConnected.of_direct (G := G)
  intro y z hy hz
  have hy' : PermReachable G.face x y :=
    (Hypermap.FaceBand.singleton (G := G)).1 hy
  have hz' : PermReachable G.face x z :=
    (Hypermap.FaceBand.singleton (G := G)).1 hz
  exact RLink.node_face_of_faceReachable (G := G)
    (PermReachable.trans G.face (PermReachable.symm G.face hy') hz')

theorem RLinkPathConnected.faceBand_pair_edge_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    G.RLinkPathConnected (G.FaceBand [x, G.edge x]) := by
  intro y z hy hz
  have hxmem : G.FaceBand [x, G.edge x] x :=
    (Hypermap.FaceBand.pair (G := G)).2
      (Or.inl (PermReachable.refl G.face x))
  have hexmem : G.FaceBand [x, G.edge x] (G.edge x) :=
    (Hypermap.FaceBand.pair (G := G)).2
      (Or.inr (PermReachable.refl G.face (G.edge x)))
  rcases (Hypermap.FaceBand.pair (G := G)).1 hy with hyx | hyex
  · rcases (Hypermap.FaceBand.pair (G := G)).1 hz with hzx | hzex
    · have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hyx) hzx
      exact ⟨[], by
        simpa using RLinkPath.singleton (G := G)
          (RLink.node_face_of_faceReachable (G := G) hyz),
        by simp⟩
    · have hstart : G.RLink (G.node (G.face y)) x :=
        RLink.node_face_of_faceReachable (G := G)
          (PermReachable.symm G.face hyx)
      have hxz : G.RLink x z :=
        RLink.of_faceReachable_right (G := G)
          (RLink.self_edge (G := G) x) hzex
      refine ⟨[x], ?_, ?_⟩
      · simp [RLinkPath, hstart, hxz]
      · intro t ht
        simp at ht
        subst t
        exact hxmem
  · rcases (Hypermap.FaceBand.pair (G := G)).1 hz with hzx | hzex
    · have hstart : G.RLink (G.node (G.face y)) (G.edge x) :=
        RLink.node_face_of_faceReachable (G := G)
          (PermReachable.symm G.face hyex)
      have hexz : G.RLink (G.edge x) z :=
        RLink.of_faceReachable_right (G := G)
          (RLink.edge_self_of_plain (G := G) hPlain x) hzx
      refine ⟨[G.edge x], ?_, ?_⟩
      · simp [RLinkPath, hstart, hexz]
      · intro t ht
        simp at ht
        subst t
        exact hexmem
    · have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hyex) hzex
      exact ⟨[], by
        simpa using RLinkPath.singleton (G := G)
          (RLink.node_face_of_faceReachable (G := G) hyz),
        by simp⟩

theorem RLinkPathConnected.faceBand_pair_edge_with_property_of_plain
    (hPlain : G.Plain) (x : G.Dart) {C : G.Dart → Prop}
    (hxC : C x) (hexC : C (G.edge x)) :
    G.RLinkPathConnected
      (fun y : G.Dart => G.FaceBand [x, G.edge x] y ∧ C y) := by
  intro y z hy hz
  have hxmem : G.FaceBand [x, G.edge x] x ∧ C x :=
    ⟨(Hypermap.FaceBand.pair (G := G)).2
        (Or.inl (PermReachable.refl G.face x)),
      hxC⟩
  have hexmem : G.FaceBand [x, G.edge x] (G.edge x) ∧ C (G.edge x) :=
    ⟨(Hypermap.FaceBand.pair (G := G)).2
        (Or.inr (PermReachable.refl G.face (G.edge x))),
      hexC⟩
  rcases (Hypermap.FaceBand.pair (G := G)).1 hy.1 with hyx | hyex
  · rcases (Hypermap.FaceBand.pair (G := G)).1 hz.1 with hzx | hzex
    · have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hyx) hzx
      exact ⟨[], by
        simpa using RLinkPath.singleton (G := G)
          (RLink.node_face_of_faceReachable (G := G) hyz),
        by simp⟩
    · have hstart : G.RLink (G.node (G.face y)) x :=
        RLink.node_face_of_faceReachable (G := G)
          (PermReachable.symm G.face hyx)
      have hxz : G.RLink x z :=
        RLink.of_faceReachable_right (G := G)
          (RLink.self_edge (G := G) x) hzex
      refine ⟨[x], ?_, ?_⟩
      · simp [RLinkPath, hstart, hxz]
      · intro t ht
        simp at ht
        subst t
        exact hxmem
  · rcases (Hypermap.FaceBand.pair (G := G)).1 hz.1 with hzx | hzex
    · have hstart : G.RLink (G.node (G.face y)) (G.edge x) :=
        RLink.node_face_of_faceReachable (G := G)
          (PermReachable.symm G.face hyex)
      have hexz : G.RLink (G.edge x) z :=
        RLink.of_faceReachable_right (G := G)
          (RLink.edge_self_of_plain (G := G) hPlain x) hzx
      refine ⟨[G.edge x], ?_, ?_⟩
      · simp [RLinkPath, hstart, hexz]
      · intro t ht
        simp at ht
        subst t
        exact hexmem
    · have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hyex) hzex
      exact ⟨[], by
        simpa using RLinkPath.singleton (G := G)
          (RLink.node_face_of_faceReachable (G := G) hyz),
        by simp⟩

theorem RLinkPathConnected.faceBand_concat_node_of_bridge
    (hPlain : G.Plain) {a : List G.Dart} {x : G.Dart}
    {C : G.Dart → Prop}
    (hconn : G.RLinkPathConnected
      (fun y : G.Dart => G.FaceBand a y ∧ C y))
    (hbridgeBand : G.FaceBand a (G.edge (G.node x)))
    (hnodeC : C (G.node x))
    (hbridgeC : C (G.edge (G.node x))) :
    G.RLinkPathConnected
      (fun y : G.Dart => G.FaceBand (a ++ [G.node x]) y ∧ C y) := by
  intro y z hy hz
  have hbridgeOld :
      G.FaceBand a (G.edge (G.node x)) ∧ C (G.edge (G.node x)) :=
    ⟨hbridgeBand, hbridgeC⟩
  have hnodeNew :
      G.FaceBand (a ++ [G.node x]) (G.node x) ∧ C (G.node x) :=
    ⟨(Hypermap.FaceBand.concat (G := G)).2
        (Or.inr (PermReachable.refl G.face (G.node x))),
      hnodeC⟩
  have hbridgeNew :
      G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) ∧
        C (G.edge (G.node x)) :=
    ⟨(Hypermap.FaceBand.concat (G := G)).2 (Or.inl hbridgeBand),
      hbridgeC⟩
  rcases (Hypermap.FaceBand.concat (G := G)).1 hy.1 with hyOld | hyNew
  · rcases (Hypermap.FaceBand.concat (G := G)).1 hz.1 with hzOld | hzNew
    · rcases hconn y z ⟨hyOld, hy.2⟩ ⟨hzOld, hz.2⟩ with
        ⟨p, hp, hall⟩
      refine ⟨p, hp, ?_⟩
      intro w hw
      exact ⟨(Hypermap.FaceBand.concat (G := G)).2
          (Or.inl (hall w hw).1),
        (hall w hw).2⟩
    · rcases hconn y (G.edge (G.node x)) ⟨hyOld, hy.2⟩
        hbridgeOld with ⟨p, hp, hall⟩
      have hlast : G.RLink (G.edge (G.node x)) z :=
        RLink.of_faceReachable_right (G := G)
          (RLink.edge_self_of_plain (G := G) hPlain (G.node x)) hzNew
      refine ⟨p ++ [G.edge (G.node x)], ?_, ?_⟩
      · simpa [List.append_assoc] using
          RLinkPath.snoc (G := G) p hp hlast
      · intro w hw
        rw [List.mem_append] at hw
        rcases hw with hw | hw
        · exact ⟨(Hypermap.FaceBand.concat (G := G)).2
              (Or.inl (hall w hw).1),
            (hall w hw).2⟩
        · simp at hw
          subst w
          exact hbridgeNew
  · rcases (Hypermap.FaceBand.concat (G := G)).1 hz.1 with hzOld | hzNew
    · have hstart : G.RLink (G.node (G.face y)) (G.node x) :=
        RLink.node_face_of_faceReachable (G := G)
          (PermReachable.symm G.face hyNew)
      rcases hconn (G.edge (G.node x)) z hbridgeOld
        ⟨hzOld, hz.2⟩ with ⟨p, hp, hall⟩
      have hp' : G.RLinkPath (G.node x) (p ++ [z]) := by
        simpa [Hypermap.face_edge_node] using hp
      refine ⟨G.node x :: p, ?_, ?_⟩
      · simp [hstart, hp']
      · intro w hw
        simp at hw
        rcases hw with hw | hw
        · subst w
          exact hnodeNew
        · exact ⟨(Hypermap.FaceBand.concat (G := G)).2
              (Or.inl (hall w hw).1),
            (hall w hw).2⟩
    · have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hyNew) hzNew
      exact ⟨[], by
        simpa using RLinkPath.singleton (G := G)
          (RLink.node_face_of_faceReachable (G := G) hyz),
        by simp⟩

theorem RLinkPathConnected.faceBand_concat_of_node_eq_bridge
    (hPlain : G.Plain) {a : List G.Dart} {u v : G.Dart}
    {C : G.Dart → Prop}
    (huv : G.node u = v)
    (hconn : G.RLinkPathConnected
      (fun y : G.Dart => G.FaceBand a y ∧ C y))
    (hbridgeBand : G.FaceBand a (G.edge v))
    (hvC : C v)
    (hbridgeC : C (G.edge v)) :
    G.RLinkPathConnected
      (fun y : G.Dart => G.FaceBand (a ++ [v]) y ∧ C y) := by
  simpa [huv] using
    (RLinkPathConnected.faceBand_concat_node_of_bridge (G := G)
      hPlain (a := a) (x := u) (C := C) hconn
      (by simpa [huv] using hbridgeBand)
      (by simpa [huv] using hvC)
      (by simpa [huv] using hbridgeC))

/-- Connectivity using `rlink` steps inside a predicate. -/
def RLinkConnected (A : G.Dart → Prop) : Prop :=
  ∀ x y : G.Dart, A x → A y →
    Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) x y

theorem RLinkPathConnected.to_RLinkConnected_of_plain
    {A : G.Dart → Prop}
    (hPlain : G.Plain)
    (hconn : G.RLinkPathConnected A) :
    G.RLinkConnected A := by
  intro x y hx hy
  rcases hconn x y hx hy with ⟨p, hp, _hall⟩
  have hstart :
      Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b)
        x (G.node (G.face x)) := by
    rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
    exact Relation.ReflTransGen.single (RLink.self_edge (G := G) x)
  exact Relation.ReflTransGen.trans hstart
    (RLinkPath.to_reflTransGen (G := G) hp)

theorem RLinkConnected.of_center
    {A : G.Dart → Prop} (c : G.Dart)
    (hto : ∀ ⦃x : G.Dart⦄, A x →
      Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) x c)
    (hfrom : ∀ ⦃y : G.Dart⦄, A y →
      Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) c y) :
    G.RLinkConnected A := by
  intro x y hx hy
  exact Relation.ReflTransGen.trans (hto hx) (hfrom hy)

theorem RLinkConnected.mono
    {A B : G.Dart → Prop}
    (hconn : G.RLinkConnected A)
    (hsub : ∀ x : G.Dart, B x → A x) :
    G.RLinkConnected B := by
  intro x y hx hy
  exact hconn x y (hsub x hx) (hsub y hy)

theorem RLinkConnected.union_of_bridges
    {A B : G.Dart → Prop}
    (hconnA : G.RLinkConnected A)
    (htoA : ∀ ⦃x : G.Dart⦄, B x →
      ∃ a : G.Dart, A a ∧
        Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) x a)
    (hfromA : ∀ ⦃x : G.Dart⦄, B x →
      ∃ a : G.Dart, A a ∧
        Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) a x) :
    G.RLinkConnected (fun x : G.Dart => A x ∨ B x) := by
  intro x y hx hy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact hconnA x y hxA hyA
  · rcases hfromA hyB with ⟨a, haA, hay⟩
    exact Relation.ReflTransGen.trans (hconnA x a hxA haA) hay
  · rcases htoA hxB with ⟨a, haA, hxa⟩
    exact Relation.ReflTransGen.trans hxa (hconnA a y haA hyA)
  · rcases htoA hxB with ⟨a, haA, hxa⟩
    rcases hfromA hyB with ⟨b, hbA, hby⟩
    exact Relation.ReflTransGen.trans hxa
      (Relation.ReflTransGen.trans (hconnA a b haA hbA) hby)

theorem RLinkConnected.union_with_property_of_bridges
    {A B C : G.Dart → Prop}
    (hconnA : G.RLinkConnected (fun x : G.Dart => A x ∧ C x))
    (htoA : ∀ ⦃x : G.Dart⦄, B x → C x →
      ∃ a : G.Dart, A a ∧ C a ∧
        Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) x a)
    (hfromA : ∀ ⦃x : G.Dart⦄, B x → C x →
      ∃ a : G.Dart, A a ∧ C a ∧
        Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) a x) :
    G.RLinkConnected (fun x : G.Dart => (A x ∨ B x) ∧ C x) := by
  exact RLinkConnected.mono (G := G)
    (RLinkConnected.union_of_bridges (G := G)
      (A := fun x : G.Dart => A x ∧ C x)
      (B := fun x : G.Dart => B x ∧ C x)
      hconnA
      (by
        intro x hx
        rcases htoA hx.1 hx.2 with ⟨a, haA, haC, hxa⟩
        exact ⟨a, ⟨haA, haC⟩, hxa⟩)
      (by
        intro x hx
        rcases hfromA hx.1 hx.2 with ⟨a, haA, haC, hax⟩
        exact ⟨a, ⟨haA, haC⟩, hax⟩))
    (by
      intro x hx
      rcases hx.1 with hxA | hxB
      · exact Or.inl ⟨hxA, hx.2⟩
      · exact Or.inr ⟨hxB, hx.2⟩)

theorem RLinkConnected.faceBand_concat_of_bridges
    {a : List G.Dart} {x : G.Dart} {C : G.Dart → Prop}
    (hconn : G.RLinkConnected
      (fun y : G.Dart => G.FaceBand a y ∧ C y))
    (hto : ∀ ⦃y : G.Dart⦄,
      PermReachable G.face x y → C y →
        ∃ b : G.Dart, G.FaceBand a b ∧ C b ∧
          Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfrom : ∀ ⦃y : G.Dart⦄,
      PermReachable G.face x y → C y →
        ∃ b : G.Dart, G.FaceBand a b ∧ C b ∧
          Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y) :
    G.RLinkConnected
      (fun y : G.Dart => G.FaceBand (a ++ [x]) y ∧ C y) := by
  exact RLinkConnected.mono (G := G)
    (RLinkConnected.union_with_property_of_bridges (G := G)
      (A := fun y : G.Dart => G.FaceBand a y)
      (B := fun y : G.Dart => PermReachable G.face x y)
      (C := C) hconn
      (by
        intro y hy hC
        exact hto hy hC)
      (by
        intro y hy hC
        exact hfrom hy hC))
    (by
      intro y hy
      exact ⟨(Hypermap.FaceBand.concat (G := G)).1 hy.1, hy.2⟩)

theorem RLinkConnected.faceBand_append_of_bridges
    {a s : List G.Dart} {C : G.Dart → Prop}
    (hconn : G.RLinkConnected
      (fun y : G.Dart => G.FaceBand a y ∧ C y))
    (hto : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → C y →
        ∃ b : G.Dart, G.FaceBand a b ∧ C b ∧
          Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfrom : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → C y →
        ∃ b : G.Dart, G.FaceBand a b ∧ C b ∧
          Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y) :
    G.RLinkConnected
      (fun y : G.Dart => G.FaceBand (a ++ s) y ∧ C y) := by
  exact RLinkConnected.mono (G := G)
    (RLinkConnected.union_with_property_of_bridges (G := G)
      (A := fun y : G.Dart => G.FaceBand a y)
      (B := fun y : G.Dart => G.FaceBand s y)
      (C := C) hconn
      (by
        intro y hy hC
        exact hto hy hC)
      (by
        intro y hy hC
        exact hfrom hy hC))
    (by
      intro y hy
      exact ⟨(Hypermap.FaceBand.append (G := G)).1 hy.1, hy.2⟩)

theorem RLinkConnected.pair_edge
    (hPlain : G.Plain) (x : G.Dart) :
    G.RLinkConnected (fun y : G.Dart => y = x ∨ y = G.edge x) := by
  intro y z hy hz
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · subst y
    subst z
    exact Relation.ReflTransGen.refl
  · subst y
    subst z
    exact Relation.ReflTransGen.single (RLink.self_edge (G := G) x)
  · subst y
    subst z
    exact Relation.ReflTransGen.single
      (RLink.edge_self_of_plain (G := G) hPlain x)
  · subst y
    subst z
    exact Relation.ReflTransGen.refl

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
