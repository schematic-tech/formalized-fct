import FourColorTheorem.FourColor.Configuration.QuizEmbedding.WalkQuestions

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}

theorem fitQuiz_rightRooted_decomp
    {x0 : G.Dart} {qaL qaR : QArity} {qL qR : Question}
    (hfit :
      G.fitQuiz x0
        ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ = true) :
    G.arity x0 = qaL.toNat ∧
      G.fitQ (qstepR G x0) qL = true ∧
        G.arity (G.edge x0) = qaR.toNat ∧
          G.fitQ (qstepR G (G.edge x0)) qR = true := by
  have hfit' := hfit
  simp [Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
    Quiz.flat, Question.flat, List.map_append] at hfit'
  rcases hfit' with ⟨hroot, htail⟩
  have hsplit := append_cons_tails_eq_of_length htail
    (by simp [Hypermap.length_walkQ])
  rcases hsplit with ⟨hL, hedge, hR⟩
  refine ⟨hroot.symm, ?_, hedge.symm, ?_⟩
  · simpa [Hypermap.fitQ] using
      congrArg (fun xs => qL.flat == xs) hL.symm
  · simpa [Hypermap.fitQ] using
      congrArg (fun xs => qR.flat == xs) hR.symm

theorem faceBand_walkQuiz_rightRooted_decomp
    {x0 y : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.FaceBand (G.walkQuiz x0 qz) y ↔
      PermReachable G.face x0 y ∨
        G.FaceBand (G.walkQ (qstepR G x0) qL) y ∨
          PermReachable G.face (G.edge x0) y ∨
            G.FaceBand (G.walkQ (qstepR G (G.edge x0)) qR) y := by
  subst qz
  simp [Hypermap.walkQuiz, Hypermap.walkQ, FaceBand.append,
    FaceBand.cons]

theorem faceBand_walkQuiz_rightRooted_staged_decomp
    {x0 y : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.FaceBand (G.walkQuiz x0 qz) y ↔
      G.FaceBand
        (([x0, G.edge x0] ++ G.walkQ (qstepR G x0) qL) ++
          G.walkQ (qstepR G (G.edge x0)) qR) y := by
  subst qz
  simp [Hypermap.walkQuiz, Hypermap.walkQ, FaceBand.append,
    FaceBand.cons]
  tauto

theorem edgeCentral_walkQuiz_of_rightRooted_decomp
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {x0G : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩)
    (hroot : EdgeCentral G H h x0G)
    (hedge : EdgeCentral G H h (G.edge x0G))
    (hleft :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (qstepR G x0G) qL →
        EdgeCentral G H h y)
    (hright :
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (qstepR G (G.edge x0G)) qR →
        EdgeCentral G H h y) :
    ∀ ⦃y : G.Dart⦄, y ∈ G.walkQuiz x0G qz →
      EdgeCentral G H h y := by
  subst qz
  intro y hy
  simp [Hypermap.walkQuiz, Hypermap.walkQ] at hy
  rcases hy with rfl | hyL | rfl | hyR
  · exact hroot
  · exact hleft hyL
  · exact hedge
  · exact hright hyR

theorem mem_walkQuiz_kernel
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    {y : G.Dart}
    (hy : y ∈ G.walkQuiz x0 qz) :
    A y := by
  exact (hvalid.covers y).1
    (Hypermap.FaceBand.of_mem (G := G) hy
      (PermReachable.refl G.face y))

theorem faceReachable_kernel
    {A : G.Dart → Prop} {x0 y z : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hy : y ∈ G.walkQuiz x0 qz)
    (hyz : PermReachable G.face y z) :
    A z := by
  exact (hvalid.covers z).1
    (Hypermap.FaceBand.of_mem (G := G) hy hyz)

theorem faceClosed
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    G.FaceClosed A := by
  intro y z hy hyz
  exact (hvalid.covers z).1
    (Hypermap.FaceBand.of_faceReachable (G := G)
      ((hvalid.covers y).2 hy) hyz)

theorem root_kernel
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    A x0 :=
  hvalid.mem_walkQuiz_kernel
    (Hypermap.mem_walkQuiz_root_of_isQuizR (G := G) hvalid.rightRooted)

theorem edge_root_kernel
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    A (G.edge x0) :=
  hvalid.mem_walkQuiz_kernel
    (Hypermap.mem_walkQuiz_edge_root_of_isQuizR (G := G) hvalid.rightRooted)

theorem exists_rightRooted_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    ∃ qaL qL qaR qR,
      qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ :=
  Quiz.exists_qaskR_left_right_of_isQuizR hvalid.rightRooted

theorem walkQuiz_eq_rightRooted
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz) :
    ∃ qaL qL qaR qR,
      qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ ∧
        G.walkQuiz x0 qz =
          (x0 :: G.walkQ (qstepR G x0) qL) ++
            (G.edge x0 :: G.walkQ (qstepR G (G.edge x0)) qR) :=
  Hypermap.walkQuiz_eq_of_isQuizR (G := G) hvalid.rightRooted

theorem root_arity_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.arity x0 = qaL.toNat := by
  subst qz
  exact (fitQuiz_rightRooted_decomp (G := G) hvalid.fits).1

theorem left_tail_fit_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.fitQ (qstepR G x0) qL = true := by
  subst qz
  exact (fitQuiz_rightRooted_decomp (G := G) hvalid.fits).2.1

theorem edge_root_arity_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.arity (G.edge x0) = qaR.toNat := by
  subst qz
  exact (fitQuiz_rightRooted_decomp (G := G) hvalid.fits).2.2.1

theorem right_tail_fit_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    G.fitQ (qstepR G (G.edge x0)) qR = true := by
  subst qz
  exact (fitQuiz_rightRooted_decomp (G := G) hvalid.fits).2.2.2

theorem left_tail_flat_eq_map_arity_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    qL.flat = (G.walkQ (qstepR G x0) qL).map G.arity :=
  Hypermap.fitQ_flat_eq_map_arity (G := G)
    (hvalid.left_tail_fit_of_decomp hqz)

theorem right_tail_flat_eq_map_arity_of_decomp
    {A : G.Dart → Prop} {x0 : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    qR.flat = (G.walkQ (qstepR G (G.edge x0)) qR).map G.arity :=
  Hypermap.fitQ_flat_eq_map_arity (G := G)
    (hvalid.right_tail_fit_of_decomp hqz)

theorem left_tail_kernel_of_eq
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    {qa : QArity} {q : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hleft : qz.left = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G x0) q) :
    A y :=
  hvalid.mem_walkQuiz_kernel
    (Hypermap.mem_walkQuiz_left_tail_of_eq (G := G)
      (x := x0) (qz := qz) hleft hy)

theorem right_tail_kernel_of_eq
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    {qa : QArity} {q : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hright : qz.right = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x0)) q) :
    A y :=
  hvalid.mem_walkQuiz_kernel
    (Hypermap.mem_walkQuiz_right_tail_of_eq (G := G)
      (x := x0) (qz := qz) hright hy)

theorem left_tail_faceBand_of_eq
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    {qa : QArity} {q : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hleft : qz.left = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G x0) q) :
    G.FaceBand (G.walkQuiz x0 qz) y :=
  (hvalid.covers y).2
    (hvalid.left_tail_kernel_of_eq hleft hy)

theorem right_tail_faceBand_of_eq
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    {qa : QArity} {q : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hright : qz.right = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x0)) q) :
    G.FaceBand (G.walkQuiz x0 qz) y :=
  (hvalid.covers y).2
    (hvalid.right_tail_kernel_of_eq hright hy)

theorem kernel_iff_rightRooted_decomp
    {A : G.Dart → Prop} {x0 y : G.Dart} {qz : Quiz}
    {qaL qaR : QArity} {qL qR : Question}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hqz : qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩) :
    A y ↔
      PermReachable G.face x0 y ∨
        G.FaceBand (G.walkQ (qstepR G x0) qL) y ∨
          PermReachable G.face (G.edge x0) y ∨
            G.FaceBand (G.walkQ (qstepR G (G.edge x0)) qR) y := by
  rw [← hvalid.covers y]
  exact faceBand_walkQuiz_rightRooted_decomp (G := G) hqz

theorem firstFaceHit_walk_mem
    {A : G.Dart → Prop} {x0 x : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hx : A x) :
    ((G.walkQuiz x0 qz).get
      ⟨G.firstFaceHitIndex (G.walkQuiz x0 qz) x,
        G.firstFaceHitIndex_lt_length_of_faceBand
          ((hvalid.covers x).2 hx)⟩) ∈
      G.walkQuiz x0 qz :=
  G.firstFaceHitIndex_get_mem ((hvalid.covers x).2 hx)

theorem firstFaceHit_kernel
    {A : G.Dart → Prop} {x0 x : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hx : A x) :
    A ((G.walkQuiz x0 qz).get
      ⟨G.firstFaceHitIndex (G.walkQuiz x0 qz) x,
        G.firstFaceHitIndex_lt_length_of_faceBand
          ((hvalid.covers x).2 hx)⟩) :=
  hvalid.mem_walkQuiz_kernel (hvalid.firstFaceHit_walk_mem hx)

theorem firstFaceHit_reaches
    {A : G.Dart → Prop} {x0 x : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hx : A x) :
    PermReachable G.face
      ((G.walkQuiz x0 qz).get
        ⟨G.firstFaceHitIndex (G.walkQuiz x0 qz) x,
          G.firstFaceHitIndex_lt_length_of_faceBand
            ((hvalid.covers x).2 hx)⟩)
      x :=
  G.firstFaceHitIndex_get_faceReachable ((hvalid.covers x).2 hx)

theorem face_step_kernel
    {A : G.Dart → Prop} {x0 x : G.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0 qz)
    (hx : A x) :
    A (G.face x) :=
  hvalid.faceClosed hx (PermReachable.forward G.face x)

theorem embedQuiz_arity
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    H.arity
        (G.embedQuiz H x0G x0H qz x ((hvalid.covers x).2 hx)) =
      G.arity x :=
  G.embedQuiz_arity_of_fitQuiz (H := H)
    (x0G := x0G) (x0H := x0H) (qz := qz)
    hvalid.fits hfitH ((hvalid.covers x).2 hx)

theorem embedQuiz_face
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    G.embedQuiz H x0G x0H qz (G.face x)
        (Hypermap.FaceBand.of_faceReachable (G := G)
          ((hvalid.covers x).2 hx)
          (PermReachable.forward G.face x)) =
      H.face
        (G.embedQuiz H x0G x0H qz x ((hvalid.covers x).2 hx)) :=
  G.embedQuiz_face_of_fitQuiz (H := H)
    (x0G := x0G) (x0H := x0H) (qz := qz)
    hvalid.fits hfitH ((hvalid.covers x).2 hx)

theorem embedQuiz_face_cover
    {H : Hypermap.{u}} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hvalid : G.ValidQuizFor A x0G qz)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : A x) :
    G.embedQuiz H x0G x0H qz (G.face x)
        ((hvalid.covers (G.face x)).2
          (hvalid.face_step_kernel hx)) =
      H.face
        (G.embedQuiz H x0G x0H qz x ((hvalid.covers x).2 hx)) := by
  calc
    G.embedQuiz H x0G x0H qz (G.face x)
        ((hvalid.covers (G.face x)).2
          (hvalid.face_step_kernel hx)) =
        G.embedQuiz H x0G x0H qz (G.face x)
          (Hypermap.FaceBand.of_faceReachable (G := G)
            ((hvalid.covers x).2 hx)
            (PermReachable.forward G.face x)) := by
          exact G.embedQuiz_eq_of_faceBand_proof (H := H)
            ((hvalid.covers (G.face x)).2
              (hvalid.face_step_kernel hx))
            (Hypermap.FaceBand.of_faceReachable (G := G)
              ((hvalid.covers x).2 hx)
              (PermReachable.forward G.face x))
    _ = H.face
        (G.embedQuiz H x0G x0H qz x ((hvalid.covers x).2 hx)) :=
          hvalid.embedQuiz_face (H := H) hfitH hx

end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
