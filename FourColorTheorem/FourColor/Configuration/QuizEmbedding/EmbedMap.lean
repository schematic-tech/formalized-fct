import FourColorTheorem.FourColor.Configuration.QuizEmbedding.Kernel

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}

/-- The total map induced by a valid quiz.  Outside the kernel predicate it
uses the target root as an arbitrary default; all morphism facts below are
restricted to the kernel, so the default value is irrelevant. -/
noncomputable def embedMap
    {A : G.Dart → Prop} {x0G : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (H : Hypermap.{u}) (x0H : H.Dart) (y : G.Dart) : H.Dart := by
  classical
  exact
    if hy : A y then
      G.embedQuiz H x0G x0H qz y ((hvalid.covers y).2 hy)
    else
      x0H

theorem embedMap_of_mem
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {y : G.Dart}
    (hy : A y) :
    hvalid.embedMap H x0H y =
      G.embedQuiz H x0G x0H qz y ((hvalid.covers y).2 hy) := by
  classical
  simp [embedMap, hy]

theorem embedMap_face
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    hvalid.embedMap H x0H (G.face x) =
      H.face (hvalid.embedMap H x0H x) := by
  rw [hvalid.embedMap_of_mem (H := H) (x0H := x0H)
      (hvalid.face_step_kernel hx)]
  rw [hvalid.embedMap_of_mem (H := H) (x0H := x0H) hx]
  exact hvalid.embedQuiz_face_cover (H := H) hfitH hx

theorem embedMap_face_iter
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true) :
    ∀ (n : Nat) {x : G.Dart}, A x →
      hvalid.embedMap H x0H
          (((G.face : G.Dart → G.Dart)^[n]) x) =
        ((H.face : H.Dart → H.Dart)^[n])
          (hvalid.embedMap H x0H x)
  | 0, _x, _hx => rfl
  | n + 1, x, hx => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hx' : A (((G.face : G.Dart → G.Dart)^[n]) x) :=
        hvalid.faceClosed hx (permReachable_of_iterate_eq G.face rfl)
      rw [hvalid.embedMap_face (H := H) hfitH hx']
      rw [embedMap_face_iter hvalid hfitH n hx]

theorem embedMap_faceReachable
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x y : G.Dart}
    (hx : A x)
    (hxy : PermReachable G.face x y) :
    PermReachable H.face
      (hvalid.embedMap H x0H x)
      (hvalid.embedMap H x0H y) := by
  have hiter :=
    hvalid.embedMap_face_iter (H := H) hfitH
      (G.faceIndex hxy) hx
  rw [G.face_iter_faceIndex hxy] at hiter
  exact permReachable_of_iterate_eq H.face hiter.symm

theorem embedMap_arity
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    H.arity (hvalid.embedMap H x0H x) = G.arity x := by
  rw [hvalid.embedMap_of_mem (H := H) (x0H := x0H) hx]
  exact hvalid.embedQuiz_arity (H := H) hfitH hx

theorem embedMap_root
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    hvalid.embedMap H x0H x0G = x0H := by
  have hposG : 0 < (G.walkQuiz x0G qz).length :=
    Hypermap.walkQuiz_length_pos_of_isQuizR (G := G) hvalid.rightRooted
  have hposH : 0 < (H.walkQuiz x0H qz).length :=
    Hypermap.walkQuiz_length_pos_of_isQuizR (G := H) hvalid.rightRooted
  have hgetG :
      (G.walkQuiz x0G qz).get ⟨0, hposG⟩ = x0G :=
    Hypermap.walkQuiz_get_zero_of_isQuizR (G := G)
      hvalid.rightRooted hposG
  have hgetH :
      (H.walkQuiz x0H qz).get ⟨0, hposH⟩ = x0H :=
    Hypermap.walkQuiz_get_zero_of_isQuizR (G := H)
      hvalid.rightRooted hposH
  calc
    hvalid.embedMap H x0H x0G =
        G.embedQuiz H x0G x0H qz x0G
          ((hvalid.covers x0G).2 hvalid.root_kernel) := by
          exact hvalid.embedMap_of_mem (H := H) (x0H := x0H)
            hvalid.root_kernel
    _ = (H.walkQuiz x0H qz).get ⟨0, hposH⟩ := by
          exact G.embedQuiz_walk_get_of_eq (H := H)
            (x0G := x0G) (x0H := x0H) (qz := qz)
            hvalid.simple hposG hposH
            ((hvalid.covers x0G).2 hvalid.root_kernel)
            hgetG.symm
    _ = x0H := hgetH

theorem embedMap_edge_root
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    hvalid.embedMap H x0H (G.edge x0G) = H.edge x0H := by
  let i := qz.left.flat.length
  have hiG : i < (G.walkQuiz x0G qz).length := by
    simpa [i] using
      Hypermap.walkQuiz_left_length_lt_of_isQuizR (G := G)
        (x := x0G) hvalid.rightRooted
  have hiH : i < (H.walkQuiz x0H qz).length := by
    simpa [i] using
      Hypermap.walkQuiz_left_length_lt_of_isQuizR (G := H)
        (x := x0H) hvalid.rightRooted
  have hgetG :
      (G.walkQuiz x0G qz).get ⟨i, hiG⟩ = G.edge x0G := by
    simpa [i] using
      Hypermap.walkQuiz_get_left_length_of_isQuizR (G := G)
        (x := x0G) hvalid.rightRooted
        (Hypermap.walkQuiz_left_length_lt_of_isQuizR (G := G)
          (x := x0G) hvalid.rightRooted)
  have hgetH :
      (H.walkQuiz x0H qz).get ⟨i, hiH⟩ = H.edge x0H := by
    simpa [i] using
      Hypermap.walkQuiz_get_left_length_of_isQuizR (G := H)
        (x := x0H) hvalid.rightRooted
        (Hypermap.walkQuiz_left_length_lt_of_isQuizR (G := H)
          (x := x0H) hvalid.rightRooted)
  calc
    hvalid.embedMap H x0H (G.edge x0G) =
        G.embedQuiz H x0G x0H qz (G.edge x0G)
          ((hvalid.covers (G.edge x0G)).2 hvalid.edge_root_kernel) := by
          exact hvalid.embedMap_of_mem (H := H) (x0H := x0H)
            hvalid.edge_root_kernel
    _ = (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
          exact G.embedQuiz_walk_get_of_eq (H := H)
            (x0G := x0G) (x0H := x0H) (qz := qz)
            hvalid.simple hiG hiH
            ((hvalid.covers (G.edge x0G)).2 hvalid.edge_root_kernel)
            hgetG.symm
    _ = H.edge x0H := hgetH

theorem embedMap_edgeCentral_root
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    EdgeCentral G H (hvalid.embedMap H x0H) x0G := by
  unfold EdgeCentral
  rw [hvalid.embedMap_edge_root (H := H) (x0H := x0H),
    hvalid.embedMap_root (H := H) (x0H := x0H)]

theorem embedMap_edgeCentral_edge_root
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    EdgeCentral G H (hvalid.embedMap H x0H) (G.edge x0G) :=
  (edgeCentral_edge_iff (G := G) (H := H) hPlainG hPlainH
    (hvalid.embedMap H x0H) x0G).2
    (hvalid.embedMap_edgeCentral_root (H := H) (x0H := x0H))

theorem embedMap_edgeCentral_qstepR_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G x : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hex : A (G.edge x))
    (hcentral : EdgeCentral G H (hvalid.embedMap H x0H) x)
    (hmap :
      hvalid.embedMap H x0H (qstepR G x) =
        qstepR H (hvalid.embedMap H x0H x)) :
    EdgeCentral G H (hvalid.embedMap H x0H) (qstepR G x) :=
  edgeCentral_qstepR_of_map (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H) hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)
    hex hcentral hmap

theorem embedMap_edgeCentral_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G x : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hx : A x)
    (hmap :
      hvalid.embedMap H x0H (G.node x) =
        H.node (hvalid.embedMap H x0H x)) :
    EdgeCentral G H (hvalid.embedMap H x0H) (G.node x) :=
  edgeCentral_node_of_map (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H) hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)
    hx hmap

theorem embedMap_edgeCentral_edge_node_node_of_map_node
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G x : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hex : A (G.edge x))
    (hnx : A (G.node x))
    (hcentral : EdgeCentral G H (hvalid.embedMap H x0H) x)
    (hmapNode :
      hvalid.embedMap H x0H (G.node x) =
        H.node (hvalid.embedMap H x0H x)) :
    EdgeCentral G H (hvalid.embedMap H x0H)
      (G.edge (G.node (G.node x))) :=
  edgeCentral_edge_node_node_of_map_node
    (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H)
    hPlainG hPlainH hCubicG hCubicH hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)
    hex hnx hcentral hmapNode

theorem embedMap_edgeCentral_qstepR_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G x : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hx : A x)
    (hmap :
      hvalid.embedMap H x0H (qstepR G (G.node x)) =
        qstepR H (H.node (hvalid.embedMap H x0H x))) :
    EdgeCentral G H (hvalid.embedMap H x0H) (qstepR G (G.node x)) :=
  edgeCentral_qstepR_node_of_map (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H) hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)
    hx hmap

theorem embedMap_edgeCentral_edge_node_qstepL_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G x : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hex : A (G.edge x))
    (hcentral : EdgeCentral G H (hvalid.embedMap H x0H) x)
    (hmapHead :
      hvalid.embedMap H x0H
          (G.edge (G.node (qstepL G (G.node x)))) =
        H.edge
          (H.node (qstepL H (H.node (hvalid.embedMap H x0H x))))) :
    EdgeCentral G H (hvalid.embedMap H x0H)
      (G.edge (G.node (qstepL G (G.node x)))) :=
  edgeCentral_edge_node_qstepL_node_of_map
    (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H)
    hPlainG hPlainH hCubicG hCubicH hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)
    hex hcentral hmapHead

theorem embedMap_edgeCentral_walkQ_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    ∀ {q : Question} {x : G.Dart},
      A x → A (G.edge x) →
      EdgeCentral G H (hvalid.embedMap H x0H) x →
      (∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) q → A y) →
      (G.walkQ (G.node x) q).map (hvalid.embedMap H x0H) =
        H.walkQ (H.node (hvalid.embedMap H x0H x)) q →
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) q →
        EdgeCentral G H (hvalid.embedMap H x0H) y :=
  edgeCentral_walkQ_node_of_map
    (G := G) (H := H) (A := A)
    (h := hvalid.embedMap H x0H)
    hPlainG hPlainH hCubicG hCubicH hvalid.faceClosed
    (fun {_z} hz => hvalid.embedMap_face (H := H) hfitH hz)

theorem embedMap_seed_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain) :
    G.RLinkConnected
      (fun y : G.Dart =>
        (y = x0G ∨ y = G.edge x0G) ∧
          A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) :=
  RLinkConnected.mono (G := G)
    (RLinkConnected.pair_edge (G := G) hPlainG x0G)
    (fun _ hy => hy.1)

theorem embedMap_seed_path_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand [x0G, G.edge x0G] y ∧
          A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) :=
  RLinkPathConnected.faceBand_pair_edge_with_property_of_plain (G := G)
    hPlainG x0G
    (C := fun y : G.Dart =>
      A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y)
    ⟨hvalid.root_kernel,
      hvalid.embedMap_edgeCentral_root (H := H) (x0H := x0H)⟩
    ⟨hvalid.edge_root_kernel,
      hvalid.embedMap_edgeCentral_edge_root (H := H)
        (x0H := x0H) hPlainG hPlainH⟩

theorem embedMap_seed_root_mem
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    ((fun y : G.Dart =>
        (y = x0G ∨ y = G.edge x0G) ∧
          A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) x0G) :=
  ⟨Or.inl rfl, hvalid.root_kernel,
    hvalid.embedMap_edgeCentral_root (H := H) (x0H := x0H)⟩

theorem embedMap_seed_edge_mem
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    ((fun y : G.Dart =>
        (y = x0G ∨ y = G.edge x0G) ∧
          A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) (G.edge x0G)) :=
  ⟨Or.inr rfl, hvalid.edge_root_kernel,
    hvalid.embedMap_edgeCentral_edge_root (H := H)
      (x0H := x0H) hPlainG hPlainH⟩

theorem embedMap_seed_faceClosure
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    {x : G.Dart}
    (hx : G.FaceBand [x0G, G.edge x0G] x) :
    G.FaceClosure
      (EdgeCentral G H (hvalid.embedMap H x0H)) x := by
  rcases hx with ⟨y, hy, hyx⟩
  simp at hy
  rcases hy with rfl | rfl
  · exact G.faceClosure_of_faceReachable
      (G.faceClosure_of_mem
        (hvalid.embedMap_edgeCentral_root (H := H) (x0H := x0H)))
      hyx
  · exact G.faceClosure_of_faceReachable
      (G.faceClosure_of_mem
          (hvalid.embedMap_edgeCentral_edge_root (H := H)
            (x0H := x0H) hPlainG hPlainH))
      hyx


end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
