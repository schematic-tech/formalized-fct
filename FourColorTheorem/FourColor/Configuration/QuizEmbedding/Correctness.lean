import FourColorTheorem.FourColor.Configuration.QuizEmbedding.Preembedding

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}
theorem embedMap_cover
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    {x : G.Dart}
    (hx : A x) :
    G.FaceClosure (EdgeCentral G H (hvalid.embedMap H x0H)) x :=
  hvalid.embedMap_cover_of_walk_edgeCentral (H := H)
    (hvalid.embedMap_edgeCentral_walkQuiz (H := H) (x0H := x0H)
      hfitH hPlainG hPlainH hCubicG hCubicH)
    hx

theorem embedMap_walk_kernel_edgeCentral
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    {x : G.Dart}
    (hx : x ∈ G.walkQuiz x0G qz) :
    A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x :=
  ⟨hvalid.mem_walkQuiz_kernel hx,
    hvalid.embedMap_edgeCentral_walkQuiz (H := H) (x0H := x0H)
      hfitH hPlainG hPlainH hCubicG hCubicH hx⟩

theorem embedMap_left_tail_kernel_edgeCentral_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G x0G) qL) :
    A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y :=
  hvalid.embedMap_walk_kernel_edgeCentral (H := H) (x0H := x0H)
    hfitH hPlainG hPlainH hCubicG hCubicH
    (Hypermap.mem_walkQuiz_left_tail_of_eq (G := G)
      (x := x0G) (qz := qz) (by rw [hqz]) hy)

theorem embedMap_right_tail_kernel_edgeCentral_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x0G)) qR) :
    A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y :=
  hvalid.embedMap_walk_kernel_edgeCentral (H := H) (x0H := x0H)
    hfitH hPlainG hPlainH hCubicG hCubicH
    (Hypermap.mem_walkQuiz_right_tail_of_eq (G := G)
      (x := x0G) (qz := qz) (by rw [hqz]) hy)

theorem embedMap_left_tail_faceBand_kernel_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : G.FaceBand (G.walkQ (qstepR G x0G) qL) y) :
    A y :=
  FaceClosed.of_faceBand_sources (G := G) hvalid.faceClosed
    (s := G.walkQ (qstepR G x0G) qL)
    (fun _z hz =>
      (hvalid.embedMap_left_tail_kernel_edgeCentral_of_decomp
        (H := H) (x0H := x0H) hfitH
        hPlainG hPlainH hCubicG hCubicH hqz hz).1)
    hy

theorem embedMap_right_tail_faceBand_kernel_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : G.FaceBand (G.walkQ (qstepR G (G.edge x0G)) qR) y) :
    A y :=
  FaceClosed.of_faceBand_sources (G := G) hvalid.faceClosed
    (s := G.walkQ (qstepR G (G.edge x0G)) qR)
    (fun _z hz =>
      (hvalid.embedMap_right_tail_kernel_edgeCentral_of_decomp
        (H := H) (x0H := x0H) hfitH
        hPlainG hPlainH hCubicG hCubicH hqz hz).1)
    hy

theorem embedMap_preembedding_of_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hrlinked :
      G.RLinkPathConnected
        (fun x : G.Dart =>
          A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x)) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_cover_rlinked (H := H) hfitH
    (fun {_x} hx => hvalid.embedMap_cover (H := H) (x0H := x0H)
      hfitH hPlainG hPlainH hCubicG hCubicH hx)
    hrlinked

theorem embedMap_rlinked_of_path_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hPlainG : G.Plain)
    (hpath :
      G.RLinkPathConnected
        (fun x : G.Dart =>
          A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x)) :
    G.RLinkConnected
      (fun x : G.Dart =>
        A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x) :=
  RLinkPathConnected.to_RLinkConnected_of_plain (G := G) hPlainG hpath

theorem embedMap_preembedding_of_path_rlinked
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hpath :
      G.RLinkPathConnected
        (fun x : G.Dart =>
          A x ∧ EdgeCentral G H (hvalid.embedMap H x0H) x)) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_rlinked
    (H := H) (x0H := x0H) hfitH
    hPlainG hPlainH hCubicG hCubicH hpath

theorem embedMap_rlinked_of_staged_faceBand_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand
              (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
                G.walkQ (qstepR G (G.edge x0G)) qR) y ∧
            A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) := by
  intro x y hx hy
  have hxStaged :
      G.FaceBand
          (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
            G.walkQ (qstepR G (G.edge x0G)) qR) x :=
    (faceBand_walkQuiz_rightRooted_staged_decomp
      (G := G) (x0 := x0G) (qz := qz) hqz).1
      ((hvalid.covers x).2 hx.1)
  have hyStaged :
      G.FaceBand
          (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
            G.walkQ (qstepR G (G.edge x0G)) qR) y :=
    (faceBand_walkQuiz_rightRooted_staged_decomp
      (G := G) (x0 := x0G) (qz := qz) hqz).1
      ((hvalid.covers y).2 hy.1)
  rcases hconn x y ⟨hxStaged, hx.1, hx.2⟩
      ⟨hyStaged, hy.1, hy.2⟩ with ⟨p, hp, hall⟩
  exact ⟨p, hp, fun z hz => (hall z hz).2⟩

theorem embedMap_path_rlinked_of_staged_faceBand_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand
              (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
                G.walkQ (qstepR G (G.edge x0G)) qR) y ∧
            A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) :=
  embedMap_rlinked_of_staged_faceBand_decomp
    (G := G) hvalid hqz hconn

theorem embedMap_preembedding_of_staged_faceBand_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand
              (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
                G.walkQ (qstepR G (G.edge x0G)) qR) y ∧
            A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y)) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_rlinked
    (H := H) (x0H := x0H) hfitH
    hPlainG hPlainH hCubicG hCubicH
    (hvalid.embedMap_rlinked_of_staged_faceBand_decomp
      (H := H) (x0H := x0H) hqz hconn)

theorem embedMap_preembedding_of_staged_path_faceBand_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand
              (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
                G.walkQ (qstepR G (G.edge x0G)) qR) y ∧
            A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y)) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_staged_faceBand_decomp
    (H := H) (x0H := x0H) hfitH hPlainG hPlainH hCubicG hCubicH hqz hconn

theorem embedMap_path_rlinked_of_staged_walks_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand
            (([x0G, G.edge x0G] ++ G.walkQ (qstepR G x0G) qL) ++
              G.walkQ (qstepR G (G.edge x0G)) qR) y ∧
          A y ∧ EdgeCentral G H (hvalid.embedMap H x0H) y) := by
  let seed : List G.Dart := [x0G, G.edge x0G]
  let f := hvalid.embedMap H x0H
  have hseed :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand seed y ∧ A y ∧ EdgeCentral G H f y) := by
    simpa [seed, f] using
      hvalid.embedMap_seed_path_rlinked
        (H := H) (x0H := x0H) hPlainG hPlainH
  have hseedSources : ∀ y : G.Dart, y ∈ seed → A y := by
    intro y hy
    dsimp [seed] at hy
    simp at hy
    rcases hy with rfl | rfl
    · exact hvalid.root_kernel
    · exact hvalid.edge_root_kernel
  have hleftRoot : G.FaceBand seed (G.edge x0G) := by
    dsimp [seed]
    exact (Hypermap.FaceBand.pair (G := G)).2
      (Or.inr (PermReachable.refl G.face (G.edge x0G)))
  have hleftEdgeRoot : G.FaceBand seed (G.edge (G.edge x0G)) := by
    dsimp [seed]
    rw [Hypermap.Plain.edge_edge (G := G) hPlainG x0G]
    exact (Hypermap.FaceBand.pair (G := G)).2
      (Or.inl (PermReachable.refl G.face x0G))
  have hleftTail :
      ∀ ⦃y : G.Dart⦄,
        y ∈ G.walkQ (G.node (G.edge x0G)) qL →
          A y ∧ EdgeCentral G H f y := by
    intro y hy
    have hy' : y ∈ G.walkQ (qstepR G x0G) qL := by
      simpa [qstepR] using hy
    simpa [f] using
      hvalid.embedMap_left_tail_kernel_edgeCentral_of_decomp
        (H := H) (x0H := x0H) hfitH
        hPlainG hPlainH hCubicG hCubicH hqz hy'
  have hleft0 :=
    rlinkPathConnected_walkQ_node_edgeCentral
      (G := G) (H := H) (h := f) (A := A)
      hPlainG hPlainH hCubicG hvalid.faceClosed
      (q := qL) (x := G.edge x0G) (a := seed)
      hleftRoot hleftEdgeRoot hseedSources hseed hleftTail
  have hleft :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (seed ++ G.walkQ (qstepR G x0G) qL) y ∧
            A y ∧ EdgeCentral G H f y) := by
    simpa [qstepR] using hleft0
  let leftStage : List G.Dart := seed ++ G.walkQ (qstepR G x0G) qL
  have hrootBandLeft : G.FaceBand leftStage x0G := by
    apply FaceBand.subset (G := G)
      (r := seed) (s := leftStage)
    · intro z hz
      dsimp [leftStage]
      exact List.mem_append_left _ hz
    · dsimp [seed]
      exact (Hypermap.FaceBand.pair (G := G)).2
        (Or.inl (PermReachable.refl G.face x0G))
  have hedgeBandLeft : G.FaceBand leftStage (G.edge x0G) := by
    apply FaceBand.subset (G := G)
      (r := seed) (s := leftStage)
    · intro z hz
      dsimp [leftStage]
      exact List.mem_append_left _ hz
    · dsimp [seed]
      exact (Hypermap.FaceBand.pair (G := G)).2
        (Or.inr (PermReachable.refl G.face (G.edge x0G)))
  have hleftStageSources : ∀ y : G.Dart, y ∈ leftStage → A y := by
    intro y hy
    dsimp [leftStage] at hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact hseedSources y hy
    · exact
        (hvalid.embedMap_left_tail_kernel_edgeCentral_of_decomp
          (H := H) (x0H := x0H) hfitH
          hPlainG hPlainH hCubicG hCubicH hqz hy).1
  have hrightTail :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x0G) qR →
        A y ∧ EdgeCentral G H f y := by
    intro y hy
    have hy' : y ∈ G.walkQ (qstepR G (G.edge x0G)) qR := by
      simpa [qstepR_edge_eq_node_of_plain (G := G) hPlainG x0G]
        using hy
    simpa [f] using
      hvalid.embedMap_right_tail_kernel_edgeCentral_of_decomp
        (H := H) (x0H := x0H) hfitH
        hPlainG hPlainH hCubicG hCubicH hqz hy'
  have hright0 :=
    rlinkPathConnected_walkQ_node_edgeCentral
      (G := G) (H := H) (h := f) (A := A)
      hPlainG hPlainH hCubicG hvalid.faceClosed
      (q := qR) (x := x0G) (a := leftStage)
      hrootBandLeft hedgeBandLeft hleftStageSources hleft hrightTail
  simpa [leftStage, seed, f, List.append_assoc,
    qstepR_edge_eq_node_of_plain (G := G) hPlainG x0G] using hright0

theorem embedMap_preembedding_of_staged_walks_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding_of_staged_path_faceBand_decomp
    (H := H) (x0H := x0H) hfitH
    hPlainG hPlainH hCubicG hCubicH hqz
    (hvalid.embedMap_path_rlinked_of_staged_walks_decomp
      (H := H) (x0H := x0H) hfitH
      hPlainG hPlainH hCubicG hCubicH hqz)

theorem embedMap_preembedding
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    Preembedding G H A (hvalid.embedMap H x0H) := by
  rcases hvalid.exists_rightRooted_decomp with
    ⟨qaL, qL, qaR, qR, hqz⟩
  exact hvalid.embedMap_preembedding_of_staged_walks_decomp
    (H := H) (x0H := x0H)
    (qaL := qaL) (qaR := qaR) (qL := qL) (qR := qR)
    hfitH hPlainG hPlainH hCubicG hCubicH hqz

theorem embedMap_mem_left_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G x0G) qL) :
    hvalid.embedMap H x0H y ∈
      H.walkQ (qstepR H x0H) qL := by
  have hmem :
      hvalid.embedMap H x0H y ∈
        (G.walkQ (qstepR G x0G) qL).map
          (hvalid.embedMap H x0H) :=
    List.mem_map_of_mem hy
  simpa [hvalid.map_embedMap_left_tail_of_decomp
    (H := H) (x0H := x0H) hqz] using hmem

theorem embedMap_mem_right_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x0G)) qR) :
    hvalid.embedMap H x0H y ∈
      H.walkQ (qstepR H (H.edge x0H)) qR := by
  have hmem :
      hvalid.embedMap H x0H y ∈
        (G.walkQ (qstepR G (G.edge x0G)) qR).map
          (hvalid.embedMap H x0H) :=
    List.mem_map_of_mem hy
  simpa [hvalid.map_embedMap_right_tail_of_decomp
    (H := H) (x0H := x0H) hqz] using hmem

theorem embedMap_faceBand_left_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G x0G) qL) :
    H.FaceBand (H.walkQ (qstepR H x0H) qL)
      (hvalid.embedMap H x0H y) :=
  Hypermap.FaceBand.of_mem (G := H)
    (hvalid.embedMap_mem_left_tail_of_decomp
      (H := H) (x0H := x0H) hqz hy)
    (PermReachable.refl H.face (hvalid.embedMap H x0H y))

theorem embedMap_faceBand_right_tail_of_decomp
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G y : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x0G)) qR) :
    H.FaceBand (H.walkQ (qstepR H (H.edge x0H)) qR)
      (hvalid.embedMap H x0H y) :=
  Hypermap.FaceBand.of_mem (G := H)
    (hvalid.embedMap_mem_right_tail_of_decomp
      (H := H) (x0H := x0H) hqz hy)
    (PermReachable.refl H.face (hvalid.embedMap H x0H y))

theorem embedMap_mem_walkQuiz
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : x ∈ G.walkQuiz x0G qz) :
    hvalid.embedMap H x0H x ∈ H.walkQuiz x0H qz := by
  have hxmap :
      hvalid.embedMap H x0H x ∈
        (G.walkQuiz x0G qz).map (hvalid.embedMap H x0H) :=
    List.mem_map_of_mem hx
  simpa [hvalid.map_embedMap_walkQuiz (H := H) (x0H := x0H)] using hxmap

theorem embedMap_firstFaceHit_mem_walkQuiz
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : A x) :
    hvalid.embedMap H x0H
        ((G.walkQuiz x0G qz).get
          ⟨G.firstFaceHitIndex (G.walkQuiz x0G qz) x,
            G.firstFaceHitIndex_lt_length_of_faceBand
              ((hvalid.covers x).2 hx)⟩) ∈
      H.walkQuiz x0H qz :=
  hvalid.embedMap_mem_walkQuiz (H := H)
    (hvalid.firstFaceHit_walk_mem hx)

theorem embedMap_firstFaceHit_eq_walk_get
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    {x : G.Dart}
    (hx : A x)
    (hiH :
      G.firstFaceHitIndex (G.walkQuiz x0G qz) x <
        (H.walkQuiz x0H qz).length) :
    hvalid.embedMap H x0H
        ((G.walkQuiz x0G qz).get
          ⟨G.firstFaceHitIndex (G.walkQuiz x0G qz) x,
            G.firstFaceHitIndex_lt_length_of_faceBand
              ((hvalid.covers x).2 hx)⟩) =
      (H.walkQuiz x0H qz).get
        ⟨G.firstFaceHitIndex (G.walkQuiz x0G qz) x, hiH⟩ :=
  hvalid.embedMap_walk_get (H := H)
    (G.firstFaceHitIndex_lt_length_of_faceBand
      ((hvalid.covers x).2 hx))
    hiH

theorem embedMap_firstFaceHit_faceReachable
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    PermReachable H.face
      (hvalid.embedMap H x0H
        ((G.walkQuiz x0G qz).get
          ⟨G.firstFaceHitIndex (G.walkQuiz x0G qz) x,
            G.firstFaceHitIndex_lt_length_of_faceBand
              ((hvalid.covers x).2 hx)⟩))
      (hvalid.embedMap H x0H x) :=
  hvalid.embedMap_faceReachable (H := H) hfitH
    (hvalid.firstFaceHit_kernel hx)
    (hvalid.firstFaceHit_reaches hx)

theorem faceBand_iff
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    G.FaceBand (G.walkQuiz x0 qz) y ↔ A y :=
  hvalid.covers y

theorem flat_eq_map_arity
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    qz.flat = (G.walkQuiz x0 qz).map G.arity :=
  Hypermap.fitQuiz_flat_eq_map_arity (G := G) hvalid.fits

theorem flat_length_eq_walk_length
    {x0 : G.Dart} {qz : Quiz} :
    qz.flat.length = (G.walkQuiz x0 qz).length :=
  Hypermap.fitQuiz_length_eq (G := G)

end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
