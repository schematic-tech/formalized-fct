import FourColorTheorem.FourColor.Configuration.QuizEmbedding.EmbedMap

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}
theorem seed_faceBand_kernel
    {A : G.Dart → Prop} {x0G : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : G.FaceBand [x0G, G.edge x0G] x) :
    A x := by
  rcases (FaceBand.pair (G := G)).1 hx with hx0 | hex0
  · exact hvalid.faceClosed hvalid.root_kernel hx0
  · exact hvalid.faceClosed hvalid.edge_root_kernel hex0

theorem seed_faceBand_faceBand_walk
    {A : G.Dart → Prop} {x0G : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : G.FaceBand [x0G, G.edge x0G] x) :
    G.FaceBand (G.walkQuiz x0G qz) x :=
  (hvalid.covers x).2 (hvalid.seed_faceBand_kernel hx)

theorem root_edge_pair_subset_walkQuiz
    {A : G.Dart → Prop} {x0G : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    ∀ y : G.Dart, y ∈ [x0G, G.edge x0G] →
      y ∈ G.walkQuiz x0G qz := by
  intro y hy
  simp at hy
  rcases hy with rfl | rfl
  · exact Hypermap.mem_walkQuiz_root_of_isQuizR (G := G)
      hvalid.rightRooted
  · exact Hypermap.mem_walkQuiz_edge_root_of_isQuizR (G := G)
      hvalid.rightRooted

theorem seed_faceBand_subset_walkQuiz_faceBand
    {A : G.Dart → Prop} {x0G : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : G.FaceBand [x0G, G.edge x0G] x) :
    G.FaceBand (G.walkQuiz x0G qz) x :=
  hvalid.seed_faceBand_faceBand_walk hx

theorem embedMap_seed_preembedding
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    Preembedding G H
      (fun y : G.Dart => G.FaceBand [x0G, G.edge x0G] y ∧ A y)
      (hvalid.embedMap H x0H) where
  face := by
    intro x hx
    exact hvalid.embedMap_face (H := H) hfitH hx.2
  arity := by
    intro x hx
    exact hvalid.embedMap_arity (H := H) hfitH hx.2
  cover := by
    intro x hx
    exact hvalid.embedMap_seed_faceClosure
      (H := H) (x0H := x0H) hPlainG hPlainH hx.1
  rlinked := by
    simpa [and_assoc] using
      hvalid.embedMap_seed_path_rlinked
        (H := H) (x0H := x0H) hPlainG hPlainH

theorem embedMap_preembedding_of_cover_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hcover :
      ∀ ⦃x : G.Dart⦄, A x →
        G.FaceClosure (EdgeCentral G H (hvalid.embedMap H x0H)) x)
    (hrlinked :
      G.RLinkPathConnected
        (fun x : G.Dart =>
          A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x)) :
    Preembedding G H A (hvalid.embedMap H x0H) where
  face := by
    intro x hx
    exact hvalid.embedMap_face (H := H) hfitH hx
  arity := by
    intro x hx
    exact hvalid.embedMap_arity (H := H) hfitH hx
  cover := by
    intro x hx
    exact hcover hx
  rlinked := hrlinked

theorem embedMap_cover_of_walk_edgeCentral
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hcentral :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQuiz x0G qz →
        EdgeCentral G H (hvalid.embedMap H x0H) y)
    {x : G.Dart}
    (hx : A x) :
    G.FaceClosure (EdgeCentral G H (hvalid.embedMap H x0H)) x := by
  rcases (hvalid.covers x).2 hx with ⟨y, hy, hyx⟩
  exact ⟨y, PermReachable.symm G.face hyx, hcentral hy⟩

theorem embedMap_preembedding_of_walk_edgeCentral_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hcentral :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQuiz x0G qz →
        EdgeCentral G H (hvalid.embedMap H x0H) y)
    (hrlinked :
      G.RLinkPathConnected
        (fun x : G.Dart =>
          A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x)) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_cover_rlinked (H := H) hfitH
    (fun {_x} hx => hvalid.embedMap_cover_of_walk_edgeCentral
      (H := H) hcentral hx)
    hrlinked

theorem embedQuiz_walk_get
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {i : Nat}
    (hiG : i < (G.walkQuiz x0G qz).length)
    (hiH : i < (H.walkQuiz x0H qz).length) :
    G.embedQuiz H x0G x0H qz
        ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)
        (Hypermap.FaceBand.of_mem (G := G)
          (List.get_mem (G.walkQuiz x0G qz) ⟨i, hiG⟩)
          (PermReachable.refl G.face
            ((G.walkQuiz x0G qz).get ⟨i, hiG⟩))) =
      (H.walkQuiz x0H qz).get ⟨i, hiH⟩ :=
  G.embedQuiz_walk_get_of_faceSimple (H := H)
    (x0G := x0G) (x0H := x0H) (qz := qz)
    hvalid.simple hiG hiH

theorem embedMap_walk_get
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {i : Nat}
    (hiG : i < (G.walkQuiz x0G qz).length)
    (hiH : i < (H.walkQuiz x0H qz).length) :
    hvalid.embedMap H x0H
        ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) =
      (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
  have hxA :
      A ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) :=
    hvalid.mem_walkQuiz_kernel
      (List.get_mem (G.walkQuiz x0G qz) ⟨i, hiG⟩)
  calc
    hvalid.embedMap H x0H
        ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) =
        G.embedQuiz H x0G x0H qz
          ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)
          ((hvalid.covers
            ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)).2 hxA) := by
          exact hvalid.embedMap_of_mem (H := H) (x0H := x0H) hxA
    _ = (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
          exact G.embedQuiz_walk_get_of_eq (H := H)
            (x0G := x0G) (x0H := x0H) (qz := qz)
            hvalid.simple hiG hiH
            ((hvalid.covers
              ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)).2 hxA)
            rfl

theorem map_embedMap_walkQuiz
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    (G.walkQuiz x0G qz).map (hvalid.embedMap H x0H) =
      H.walkQuiz x0H qz := by
  apply List.ext_get
  · simp [Hypermap.length_walkQuiz]
  · intro i hiMap hiH
    have hiG : i < (G.walkQuiz x0G qz).length := by
      simpa using hiMap
    calc
      ((G.walkQuiz x0G qz).map (hvalid.embedMap H x0H)).get
          ⟨i, hiMap⟩ =
          hvalid.embedMap H x0H
            ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) := by
            simp [List.getElem_map]
      _ = (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
            exact hvalid.embedMap_walk_get (H := H) hiG hiH

theorem map_embedMap_walkQuiz_eq_rightRooted
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz) :
    ∃ qaL qL qaR qR,
      qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ ∧
        (((x0G :: G.walkQ (qstepR G x0G) qL) ++
              (G.edge x0G ::
                G.walkQ (qstepR G (G.edge x0G)) qR)).map
            (hvalid.embedMap H x0H)) =
          (x0H :: H.walkQ (qstepR H x0H) qL) ++
            (H.edge x0H ::
              H.walkQ (qstepR H (H.edge x0H)) qR) := by
  rcases hvalid.exists_rightRooted_decomp with
    ⟨qaL, qL, qaR, qR, hqz⟩
  refine ⟨qaL, qL, qaR, qR, hqz, ?_⟩
  subst qz
  simpa [Hypermap.walkQuiz, Hypermap.walkQ] using
    hvalid.map_embedMap_walkQuiz (H := H) (x0H := x0H)

theorem map_embedMap_left_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    (G.walkQ (qstepR G x0G) qL).map (hvalid.embedMap H x0H) =
      H.walkQ (qstepR H x0H) qL := by
  subst qz
  let f := hvalid.embedMap H x0H
  have hmap := hvalid.map_embedMap_walkQuiz (H := H) (x0H := x0H)
  have hmap' :
      ((x0H :: (G.walkQ (qstepR G x0G) qL).map f) ++
          (H.edge x0H ::
            (G.walkQ (qstepR G (G.edge x0G)) qR).map f)) =
        (x0H :: H.walkQ (qstepR H x0H) qL) ++
          (H.edge x0H ::
            H.walkQ (qstepR H (H.edge x0H)) qR) := by
    simpa [f, Hypermap.walkQuiz, Hypermap.walkQ,
      hvalid.embedMap_root (H := H) (x0H := x0H),
      hvalid.embedMap_edge_root (H := H) (x0H := x0H)] using hmap
  exact left_tail_eq_of_cons_append_eq hmap'
    (by simp [Hypermap.length_walkQ])

theorem map_embedMap_right_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    (G.walkQ (qstepR G (G.edge x0G)) qR).map
        (hvalid.embedMap H x0H) =
      H.walkQ (qstepR H (H.edge x0H)) qR := by
  subst qz
  let f := hvalid.embedMap H x0H
  have hmap := hvalid.map_embedMap_walkQuiz (H := H) (x0H := x0H)
  have hmap' :
      ((x0H :: (G.walkQ (qstepR G x0G) qL).map f) ++
          (H.edge x0H ::
            (G.walkQ (qstepR G (G.edge x0G)) qR).map f)) =
        (x0H :: H.walkQ (qstepR H x0H) qL) ++
          (H.edge x0H ::
            H.walkQ (qstepR H (H.edge x0H)) qR) := by
    simpa [f, Hypermap.walkQuiz, Hypermap.walkQ,
      hvalid.embedMap_root (H := H) (x0H := x0H),
      hvalid.embedMap_edge_root (H := H) (x0H := x0H)] using hmap
  exact right_tail_eq_of_cons_append_eq hmap'
    (by simp [Hypermap.length_walkQ])

theorem embedMap_edgeCentral_walkQuiz
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    ∀ ⦃y : G.Dart⦄, y ∈ G.walkQuiz x0G qz →
      EdgeCentral G H (hvalid.embedMap H x0H) y := by
  rcases hvalid.exists_rightRooted_decomp with
    ⟨qaL, qL, qaR, qR, hqz⟩
  have hleftEq : qz.left = Question.QaskR qaL qL := by
    rw [hqz]
  have hrightEq : qz.right = Question.QaskR qaR qR := by
    rw [hqz]
  have hrootCentral :
      EdgeCentral G H (hvalid.embedMap H x0H) x0G :=
    hvalid.embedMap_edgeCentral_root (H := H) (x0H := x0H)
  have hedgeCentral :
      EdgeCentral G H (hvalid.embedMap H x0H) (G.edge x0G) :=
    hvalid.embedMap_edgeCentral_edge_root (H := H)
      (x0H := x0H) hPlainG hPlainH
  have hleftMap :
      (G.walkQ (G.node (G.edge x0G)) qL).map
          (hvalid.embedMap H x0H) =
        H.walkQ
          (H.node (hvalid.embedMap H x0H (G.edge x0G))) qL := by
    simpa [qstepR,
      hvalid.embedMap_edge_root (H := H) (x0H := x0H)] using
      hvalid.map_embedMap_left_tail_of_decomp
        (H := H) (x0H := x0H) hqz
  have hleftAll :
      ∀ ⦃y : G.Dart⦄,
        y ∈ G.walkQ (G.node (G.edge x0G)) qL → A y := by
    intro y hy
    have hy' : y ∈ G.walkQ (qstepR G x0G) qL := by
      simpa [qstepR] using hy
    exact hvalid.left_tail_kernel_of_eq hleftEq hy'
  have hleftCentral :
      ∀ ⦃y : G.Dart⦄,
        y ∈ G.walkQ (qstepR G x0G) qL →
          EdgeCentral G H (hvalid.embedMap H x0H) y := by
    intro y hy
    have hy' : y ∈ G.walkQ (G.node (G.edge x0G)) qL := by
      simpa [qstepR] using hy
    have hEdgeEdgeRoot : A (G.edge (G.edge x0G)) := by
      rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
      exact hvalid.root_kernel
    exact hvalid.embedMap_edgeCentral_walkQ_node_of_map
      (H := H) (x0H := x0H) hfitH
      hPlainG hPlainH hCubicG hCubicH
      hvalid.edge_root_kernel hEdgeEdgeRoot hedgeCentral
      hleftAll hleftMap hy'
  have hrightMap :
      (G.walkQ (G.node x0G) qR).map
          (hvalid.embedMap H x0H) =
        H.walkQ (H.node (hvalid.embedMap H x0H x0G)) qR := by
    simpa [
      qstepR_edge_eq_node_of_plain (G := G) hPlainG x0G,
      qstepR_edge_eq_node_of_plain (G := H) hPlainH x0H,
      hvalid.embedMap_root (H := H) (x0H := x0H)] using
      hvalid.map_embedMap_right_tail_of_decomp
        (H := H) (x0H := x0H) hqz
  have hrightAll :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x0G) qR → A y := by
    intro y hy
    have hy' : y ∈ G.walkQ (qstepR G (G.edge x0G)) qR := by
      simpa [qstepR_edge_eq_node_of_plain (G := G) hPlainG x0G]
        using hy
    exact hvalid.right_tail_kernel_of_eq hrightEq hy'
  have hrightCentral :
      ∀ ⦃y : G.Dart⦄,
        y ∈ G.walkQ (qstepR G (G.edge x0G)) qR →
          EdgeCentral G H (hvalid.embedMap H x0H) y := by
    intro y hy
    have hy' : y ∈ G.walkQ (G.node x0G) qR := by
      simpa [qstepR_edge_eq_node_of_plain (G := G) hPlainG x0G]
        using hy
    exact hvalid.embedMap_edgeCentral_walkQ_node_of_map
      (H := H) (x0H := x0H) hfitH
      hPlainG hPlainH hCubicG hCubicH
      hvalid.root_kernel hvalid.edge_root_kernel hrootCentral
      hrightAll hrightMap hy'
  exact edgeCentral_walkQuiz_of_rightRooted_decomp
    (G := G) (H := H) (h := hvalid.embedMap H x0H)
    hqz hrootCentral hedgeCentral hleftCentral hrightCentral


end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
