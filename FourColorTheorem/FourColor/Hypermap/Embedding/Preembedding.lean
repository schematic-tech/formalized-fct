import FourColorTheorem.FourColor.Hypermap.Embedding.RadiusTwo

/-!
Partial hypermap embeddings and their face-orbit properties.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G H : Hypermap.{u})

/-- Darts where a partial map commutes with edge. -/
def EdgeCentral (h : G.Dart → H.Dart) (x : G.Dart) : Prop :=
  h (G.edge x) = H.edge (h x)

theorem edgeCentral_edge_iff
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (h : G.Dart → H.Dart) (x : G.Dart) :
    EdgeCentral G H h (G.edge x) ↔ EdgeCentral G H h x := by
  unfold EdgeCentral
  rw [Hypermap.Plain.edge_edge (G := G) hPlainG x]
  constructor
  · intro hx
    calc
      h (G.edge x) = H.edge (H.edge (h (G.edge x))) := by
        rw [Hypermap.Plain.edge_edge (G := H) hPlainH]
      _ = H.edge (h x) := by rw [← hx]
  · intro hx
    calc
      h x = H.edge (H.edge (h x)) := by
        rw [Hypermap.Plain.edge_edge (G := H) hPlainH]
      _ = H.edge (h (G.edge x)) := by rw [← hx]

/-- Coq `preembedding`: a partial morphism on `A`, preserving face and arity,
whose edge-central darts face-cover `A` and are `rlink`-connected. -/
structure Preembedding (A : G.Dart → Prop) (h : G.Dart → H.Dart) : Prop where
  face :
    ∀ ⦃x : G.Dart⦄, A x → h (G.face x) = H.face (h x)
  arity :
    ∀ ⦃x : G.Dart⦄, A x → H.arity (h x) = G.arity x
  cover :
    ∀ ⦃x : G.Dart⦄, A x → G.FaceClosure (EdgeCentral G H h) x
  rlinked :
    G.RLinkPathConnected (fun x => A x ∧ EdgeCentral G H h x)

namespace Preembedding

variable {G H}

/-- Coq `preembedding_simple_path`: edge-central face covers and internal
`rlink` connectivity produce a nonempty face-simple path whose darts remain
inside the preembedded predicate. -/
theorem simplePath
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart}
    (hex : A (G.edge x)) (hy : A y) :
    ∃ p : List G.Dart,
      G.RLinkPath x p ∧
        PermReachable G.face ((x :: p).getLastD x) y ∧
          p ≠ [] ∧ G.FaceSimple p ∧
            ∀ z : G.Dart, z ∈ p →
              A z ∧ EdgeCentral G H h z := by
  rcases hembed.cover hex with ⟨z, hexz, hzCentral⟩
  rcases hembed.cover hy with ⟨t, hyt, htCentral⟩
  have hzA : A z := hclosed hex hexz
  have htA : A t := hclosed hy hyt
  rcases hembed.rlinked z t ⟨hzA, hzCentral⟩ ⟨htA, htCentral⟩ with
    ⟨p, hp, hall⟩
  have hsource : ∀ w : G.Dart,
      G.RLink (G.node (G.face z)) w → G.RLink x w := by
    intro w hzw
    apply RLink.of_faceReachable_right (G := G)
      (RLink.of_faceReachable_right (G := G)
        (RLink.self_edge (G := G) x) hexz)
    simpa [RLink, Hypermap.edge_node_eq_face_symm] using hzw
  have hxp : G.RLinkPath x (p ++ [t]) := by
    cases hpq : p ++ [t] with
    | nil => simp at hpq
    | cons w q =>
        have hp' :
            G.RLink (G.node (G.face z)) w ∧ G.RLinkPath w q := by
          simpa [hpq, RLinkPath] using hp
        exact ⟨hsource w hp'.1, hp'.2⟩
  rcases RLinkPath.simplifyFace (G := G) hxp with
    ⟨q, hq, hsimple, hlast, hnil, hsub⟩
  have hqne : q ≠ [] := by
    intro hqnil
    have : p ++ [t] = [] := hnil.mpr hqnil
    simp at this
  refine ⟨q, hq, ?_, hqne, hsimple, ?_⟩
  · have hlastT : (x :: (p ++ [t])).getLastD x = t := by
      simp [List.getLastD]
    rw [hlast, hlastT]
    exact PermReachable.symm G.face hyt
  · intro w hw
    have hw' : w ∈ p ++ [t] := hsub w hw
    rw [List.mem_append] at hw'
    rcases hw' with hw' | hw'
    · exact hall w hw'
    · simp at hw'
      subst w
      exact ⟨htA, htCentral⟩

/-- The first reduction in Coq `embed_functor`: if both ends of an edge lie in
the selected face-closed set, the preembedding supplies a face-simple
`rlink` cycle based at that edge whose tail is entirely edge-central. -/
theorem exists_simpleCycle_tail_edgeCentral
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x : G.Dart}
    (hex : A (G.edge x)) (hx : A x) :
    ∃ p : List G.Dart,
      G.SimpleRLinkCycle (x :: p) ∧
        ∀ z : G.Dart, z ∈ p →
          A z ∧ EdgeCentral G H h z := by
  rcases hembed.simplePath hclosed hex hx with
    ⟨q, hpath, hlastFace, hqne, hsimple, hall⟩
  let p := q.dropLast
  let y := q.getLast hqne
  have hq : p ++ [y] = q := by
    exact List.dropLast_append_getLast hqne
  have hpath' : G.RLinkPath x (p ++ [y]) := by
    simpa [hq] using hpath
  have hprefix : G.RLinkPath x p :=
    RLinkPath.prefix_of_append (G := G) hpath'
  have hlastLink : G.RLink ((x :: p).getLastD x) y := by
    simpa using
      (RLinkPath.last_link_of_append_cons (G := G)
        (p := p) (q := []) hpath')
  have hlastEq : (x :: q).getLastD x = y := by
    rw [← hq]
    simp [List.getLastD]
  have hyx : PermReachable G.face y x := by
    rw [hlastEq] at hlastFace
    exact hlastFace
  have hclosing : G.RLink ((x :: p).getLastD x) x :=
    RLink.of_faceReachable_right (G := G) hlastLink hyx
  have horbit : PermOrbit.of G.face y = PermOrbit.of G.face x :=
    PermOrbit.of_eq_of G.face hyx
  have hsimpleOrbit :
      (q.map (PermOrbit.of G.face)).Nodup :=
    (faceSimple_iff_nodup_faceOrbit_map (G := G)).1 hsimple
  have hcycleSimple : G.FaceSimple (x :: p) := by
    apply (faceSimple_iff_nodup_faceOrbit_map (G := G)).2
    rw [← hq] at hsimpleOrbit
    have hs :
        (p.map (PermOrbit.of G.face) ++ [PermOrbit.of G.face x]).Nodup := by
      simpa [List.map_append, horbit] using hsimpleOrbit
    rcases List.nodup_append.mp hs with ⟨hp, _, hdisjoint⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, hp⟩
    intro hxmem
    exact hdisjoint (PermOrbit.of G.face x) hxmem
      (PermOrbit.of G.face x) (by simp) rfl
  refine ⟨p, ⟨⟨hprefix, hclosing⟩, hcycleSimple⟩, ?_⟩
  intro z hz
  apply hall z
  rw [← hq]
  exact List.mem_append_left [y] hz

theorem mono
    {A B : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hsub : ∀ x : G.Dart, B x → A x)
    (hrlinked :
      G.RLinkPathConnected (fun x => B x ∧ EdgeCentral G H h x)) :
    Preembedding G H B h where
  face := by
    intro x hx
    exact hembed.face (hsub x hx)
  arity := by
    intro x hx
    exact hembed.arity (hsub x hx)
  cover := by
    intro x hx
    exact hembed.cover (hsub x hx)
  rlinked := hrlinked

theorem edgeCentral_of_mem
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    {x : G.Dart} (hx : A x) :
    ∃ y : G.Dart,
      PermReachable G.face x y ∧ EdgeCentral G H h y :=
  hembed.cover hx

theorem edgeCentral_of_faceReachable_of_mem
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    {x x' : G.Dart}
    (hx : A x)
    (hxx' : PermReachable G.face x' x) :
    G.FaceClosure (EdgeCentral G H h) x' := by
  exact faceClosure_of_faceReachable (G := G) (hembed.cover hx)
    (PermReachable.symm G.face hxx')

theorem rlink_between_face_covers
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hPlain : G.Plain)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart}
    (hx : A x) (hy : A y) :
    ∃ z t : G.Dart,
      PermReachable G.face x z ∧
        EdgeCentral G H h z ∧
          A z ∧
            PermReachable G.face t y ∧
              EdgeCentral G H h t ∧
                A t ∧
                  Relation.ReflTransGen
                    (fun a b : G.Dart => G.RLink a b) z t := by
  rcases hembed.cover hx with ⟨z, hxz, hcz⟩
  rcases hembed.cover hy with ⟨t, hyt, hct⟩
  have hzA : A z := hclosed hx hxz
  have htA : A t := hclosed hy hyt
  have hconnected :=
    RLinkPathConnected.to_RLinkConnected_of_plain (G := G)
      hPlain hembed.rlinked
  exact
    ⟨z, t, hxz, hcz, hzA, PermReachable.symm G.face hyt,
      hct, htA, hconnected z t ⟨hzA, hcz⟩ ⟨htA, hct⟩⟩

theorem rlink_path_from_edge_to_face_cover
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hPlain : G.Plain)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart}
    (hx : A (G.edge x)) (hy : A y) :
    ∃ z t : G.Dart,
      G.RLink x z ∧
        Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) z t ∧
          Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) x t ∧
            PermReachable G.face t y ∧
              A z ∧ EdgeCentral G H h z ∧ A t ∧ EdgeCentral G H h t := by
  rcases hembed.rlink_between_face_covers hPlain hclosed hx hy with
    ⟨z, t, hxz, hcz, hzA, hty, hct, htA, hzt⟩
  have hxzLink : G.RLink x z := hxz
  have hxt :
      Relation.ReflTransGen (fun a b : G.Dart => G.RLink a b) x t :=
    Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single hxzLink) hzt
  exact ⟨z, t, hxzLink, hzt, hxt, hty, hzA, hcz, htA, hct⟩

theorem face_iter
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A) :
    ∀ (n : Nat) {x : G.Dart}, A x →
      h ((G.face : G.Dart → G.Dart)^[n] x) =
        (H.face : H.Dart → H.Dart)^[n] (h x)
  | 0, _x, _hx => rfl
  | n + 1, x, hx => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hx' : A ((G.face : G.Dart → G.Dart)^[n] x) :=
        hclosed hx (permReachable_of_iterate_eq G.face rfl)
      rw [hembed.face hx']
      rw [face_iter hembed hclosed n hx]

theorem map_faceIndex
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart}
    (hx : A x)
    (hxy : PermReachable G.face x y) :
    h y = ((H.face : H.Dart → H.Dart)^[G.faceIndex hxy]) (h x) := by
  calc
    h y =
        h (((G.face : G.Dart → G.Dart)^[G.faceIndex hxy]) x) := by
          rw [G.face_iter_faceIndex hxy]
    _ = ((H.face : H.Dart → H.Dart)^[G.faceIndex hxy]) (h x) := by
          exact hembed.face_iter hclosed (G.faceIndex hxy) hx

theorem faceReachable_map
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart}
    (hx : A x)
    (hxy : PermReachable G.face x y) :
    PermReachable H.face (h x) (h y) := by
  have hmap := hembed.map_faceIndex hclosed hx hxy
  exact permReachable_of_iterate_eq H.face hmap.symm

/-- Edge centrality at `node x`, together with face commutation, forces the
partial map to commute with the node step at `x`.  This is the local algebra
used repeatedly in Coq `embed_functor`. -/
theorem map_node_of_edgeCentral_node
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x : G.Dart} (hx : A x)
    (hcentral : EdgeCentral G H h (G.node x)) :
    h (G.node x) = H.node (h x) := by
  have hfaceSymmA : A (G.face.symm x) :=
    hclosed hx (PermReachable.backward G.face x)
  have hfaceSymm : h (G.face.symm x) = H.face.symm (h x) := by
    apply H.face.injective
    calc
      H.face (h (G.face.symm x)) = h (G.face (G.face.symm x)) :=
        (hembed.face hfaceSymmA).symm
      _ = h x := by simp
      _ = H.face (H.face.symm (h x)) := by simp
  apply H.edge.injective
  calc
    H.edge (h (G.node x)) = h (G.edge (G.node x)) := hcentral.symm
    _ = h (G.face.symm x) := by rw [G.edge_node_eq_face_symm]
    _ = H.face.symm (h x) := hfaceSymm
    _ = H.edge (H.node (h x)) := (H.edge_node_eq_face_symm (h x)).symm

/-- Coq `cface_h_ac`: every target dart in the face orbit of an embedded
source dart is the image of a dart in the corresponding source face orbit. -/
theorem faceReachable_lift
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x : G.Dart} (hx : A x) {u : H.Dart}
    (hxu : PermReachable H.face (h x) u) :
    ∃ y : G.Dart, PermReachable G.face x y ∧ h y = u := by
  rcases permReachable_exists_iterate H.face hxu with ⟨n, hn⟩
  let y := ((G.face : G.Dart → G.Dart)^[n]) x
  have hxy : PermReachable G.face x y :=
    permReachable_of_iterate_eq G.face rfl
  refine ⟨y, hxy, ?_⟩
  calc
    h y = ((H.face : H.Dart → H.Dart)^[n]) (h x) :=
      hembed.face_iter hclosed n hx
    _ = u := hn

/-- Coq `cface_inj_embed`: a preembedding is injective within every selected
source face orbit. -/
theorem injective_of_faceReachable
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    (hclosed : G.FaceClosed A)
    {x y : G.Dart} (hx : A x)
    (hxy : PermReachable G.face x y)
    (hEq : h x = h y) :
    x = y := by
  have hxyMap : PermReachable H.face (h x) (h y) :=
    hembed.faceReachable_map hclosed hx hxy
  have hidxLt : G.faceIndex hxy < H.arity (h x) := by
    rw [hembed.arity hx]
    exact G.faceIndex_lt_arity hxy
  have hidxMap : H.faceIndex hxyMap = G.faceIndex hxy := by
    apply H.faceIndex_eq_of_iterate_eq_lt_arity hxyMap hidxLt
    calc
      ((H.face : H.Dart → H.Dart)^[G.faceIndex hxy]) (h x) =
          h y := (hembed.map_faceIndex hclosed hx hxy).symm
      _ = h y := rfl
  have hidxZero : G.faceIndex hxy = 0 := by
    rw [← hidxMap]
    exact H.faceIndex_eq_zero_of_eq hxyMap hEq
  calc
    x = ((G.face : G.Dart → G.Dart)^[0]) x := by simp
    _ = ((G.face : G.Dart → G.Dart)^[G.faceIndex hxy]) x := by
      rw [hidxZero]
    _ = y := G.face_iter_faceIndex hxy

theorem goodRingArity_map
    {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hembed : Preembedding G H A h)
    {x : G.Dart}
    (hx : A x)
    (hgood : G.GoodRingArity x) :
    H.GoodRingArity (h x) := by
  rcases hgood with h3 | h4 | h5 | h6
  · left
    rw [hembed.arity hx, h3]
  · right
    left
    rw [hembed.arity hx, h4]
  · right
    right
    left
    rw [hembed.arity hx, h5]
  · right
    right
    right
    rw [hembed.arity hx, h6]

end Preembedding

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
