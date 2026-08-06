import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations.FitSemantics

namespace Schematic.Math.GraphTheory
namespace FourColor

open Question
open QArity

namespace QuizTree

namespace Hypermap

variable (G : Hypermap)
theorem quizTreeFitList_get3_eq_false_of_quizTreeFit_eq_false
    {x1 : G.Dart} {t : QuizTree}
    (hfit : quizTreeFit G x1 t = false)
    (harities : quizTreeFitsArities G x1 = true) :
    let x2 := G.node x1
    let x3 := G.node x2
    let ax1 := QArity.ofNatCode (G.arity x1)
    let ax2 := QArity.ofNatCode (G.arity x2)
    let ax3 := QArity.ofNatCode (G.arity x3)
    quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = false := by
  simpa [quizTreeFit, harities] using hfit

theorem quizTreeFit_eq_true_of_fitList_get3
    {x1 : G.Dart} {t : QuizTree}
    (harities : quizTreeFitsArities G x1 = true)
    (hlist :
      let x2 := G.node x1
      let x3 := G.node x2
      let ax1 := QArity.ofNatCode (G.arity x1)
      let ax2 := QArity.ofNatCode (G.arity x2)
      let ax3 := QArity.ofNatCode (G.arity x3)
      quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = true) :
    quizTreeFit G x1 t = true := by
  simpa [quizTreeFit, harities] using hlist

theorem quizTreeFit_put3_at
    {x1 : G.Dart} {qa1 qa2 qa3 : QArity} {q1 q2 q3 : Question}
    {t : QuizTree}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit :
      quizTreeFit G x1 (put3 qa1 qa2 qa3 q1 q2 q3 t) = true) :
    G.fitQuiz (G.edge (G.node x1)) (quiz3 qa1 qa2 qa3 q1 q2 q3) = true ∨
      quizTreeFit G x1 t = true := by
  let ax1 := QArity.ofNatCode (G.arity x1)
  let ax2 := QArity.ofNatCode (G.arity (G.node x1))
  let ax3 := QArity.ofNatCode (G.arity (G.node (G.node x1)))
  have hparts :
      quizTreeFitsArities G x1 = true ∧
        quizTreeFitList G x1
          (get3 ax1 ax2 ax3 (put3 qa1 qa2 qa3 q1 q2 q3 t)) = true := by
    simpa [quizTreeFit, ax1, ax2, ax3, Bool.and_eq_true] using hfit
  have hax :
      ax1.toNat = G.arity x1 ∧
        ax2.toNat = G.arity (G.node x1) ∧
          ax3.toNat = G.arity (G.node (G.node x1)) := by
    have hraw := hparts.1
    simp [quizTreeFitsArities, Bool.and_eq_true] at hraw
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have old_of_list :
      quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = true →
        quizTreeFit G x1 t = true := by
    intro hlist
    exact quizTreeFit_eq_true_of_fitList_get3
      (G := G) (x1 := x1) (t := t) hparts.1
      (by simpa [ax1, ax2, ax3] using hlist)
  rcases get1_put1_eq_or_same ax1 qa1
      (put1 qa2 (put1 qa3 (QuizTree.leaf q1 q2 q3))) t with
    ⟨hqa1, hget1⟩ | hsame1
  · rcases get1_put1_eq_or_same ax2 qa2
        (put1 qa3 (QuizTree.leaf q1 q2 q3)) (get1 ax1 t) with
      ⟨hqa2, hget2⟩ | hsame2
    · rcases get1_put1_eq_or_same ax3 qa3
          (QuizTree.leaf q1 q2 q3)
          (get1 ax2 (get1 ax1 t)) with
        ⟨hqa3, hget3⟩ | hsame3
      · have hlistLeaf :
            quizTreeFitList G x1
              (QuizTree.leaf q1 q2 q3 (get3 ax1 ax2 ax3 t)) = true := by
          simpa [put3, get3, get2, hget1, hget2, hget3] using hparts.2
        rcases quizTreeFitList_leaf_eq_true (G := G) hlistLeaf with
          hhead | htail
        · have hx1 : G.arity x1 = qa1.toNat := by
            rw [← hax.1, hqa1]
          have hx2 : G.arity (G.node x1) = qa2.toNat := by
            rw [← hax.2.1, hqa2]
          have hx3 : G.arity (G.node (G.node x1)) = qa3.toNat := by
            rw [← hax.2.2, hqa3]
          exact Or.inl (fitQuiz_quiz3_of_leafTripleFits
            (G := G) (x1 := x1)
            hPlain hCubic hx1 hx2 hx3 hhead)
        · exact Or.inr (old_of_list htail)
      · have hlistOld :
            quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = true := by
          simpa [put3, get3, get2, hget1, hget2, hsame3] using hparts.2
        exact Or.inr (old_of_list hlistOld)
    · have hlistOld :
          quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = true := by
        simpa [put3, get3, get2, hget1, hsame2] using hparts.2
      exact Or.inr (old_of_list hlistOld)
  · have hlistOld :
        quizTreeFitList G x1 (get3 ax1 ax2 ax3 t) = true := by
      simpa [put3, get3, get2, hsame1] using hparts.2
    exact Or.inr (old_of_list hlistOld)

theorem quizTreeFit_put3
    {x1 : G.Dart} {qa1 qa2 qa3 : QArity} {q1 q2 q3 : Question}
    {t : QuizTree}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit :
      quizTreeFit G x1 (put3 qa1 qa2 qa3 q1 q2 q3 t) = true) :
    (∃ y : G.Dart, G.fitQuiz y (quiz3 qa1 qa2 qa3 q1 q2 q3) = true) ∨
      quizTreeFit G x1 t = true := by
  rcases quizTreeFit_put3_at (G := G) (x1 := x1)
      hPlain hCubic hfit with hhead | htail
  · exact Or.inl ⟨G.edge (G.node x1), hhead⟩
  · exact Or.inr htail

theorem quizTreeFit_put
    {x1 : G.Dart} {qa1 qa2 qa3 : QArity} {q1 q2 q3 : Question}
    {t : QuizTree}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit :
      quizTreeFit G x1 (put qa1 qa2 qa3 q1 q2 q3 t) = true) :
    (∃ y : G.Dart, G.fitQuiz y (quiz3 qa1 qa2 qa3 q1 q2 q3) = true) ∨
      quizTreeFit G x1 t = true := by
  by_cases hlarge : 8 < qa1.toNat
  · have hput3 :
        quizTreeFit G x1 (put3 qa1 qa2 qa3 q1 q2 q3 t) = true := by
      simpa [put, hlarge] using hfit
    exact quizTreeFit_put3 (G := G) (x1 := x1)
      hPlain hCubic hput3
  · have hrot :
        quizTreeFit G x1 (put3rot qa1 qa2 qa3 q1 q2 q3 t) = true := by
      simpa [put, hlarge] using hfit
    rcases quizTreeFit_put3_at (G := G) (x1 := x1)
        (qa1 := qa1) (qa2 := qa2) (qa3 := qa3)
        (q1 := q1) (q2 := q2) (q3 := q3)
        hPlain hCubic (by simpa [put3rot] using hrot) with hhead1 | htail1
    · exact Or.inl ⟨G.edge (G.node x1), hhead1⟩
    · rcases quizTreeFit_put3_at (G := G) (x1 := x1)
          (qa1 := qa2) (qa2 := qa3) (qa3 := qa1)
          (q1 := q2) (q2 := q3) (q3 := q1)
          hPlain hCubic htail1 with hhead2 | htail2
      · have hrot2 := fitQuiz_quiz3_rot
            (G := G) hPlain hCubic (G.edge (G.node x1))
            qa2 qa3 qa1 q2 q3 q1
        have horig :
            G.fitQuiz (G.edge x1)
              (quiz3 qa1 qa2 qa3 q1 q2 q3) = true := by
          rw [hrot2] at hhead2
          simpa [Hypermap.face_edge_node] using hhead2
        exact Or.inl ⟨G.edge x1, horig⟩
      · rcases quizTreeFit_put3_at (G := G) (x1 := x1)
            (qa1 := qa3) (qa2 := qa1) (qa3 := qa2)
            (q1 := q3) (q2 := q1) (q3 := q2)
            hPlain hCubic htail2 with hhead3 | htail3
        · have hrot3a := fitQuiz_quiz3_rot
              (G := G) hPlain hCubic (G.edge (G.node x1))
              qa3 qa1 qa2 q3 q1 q2
          have hmid :
              G.fitQuiz (G.edge x1)
                (quiz3 qa2 qa3 qa1 q2 q3 q1) = true := by
            rw [hrot3a] at hhead3
            simpa [Hypermap.face_edge_node] using hhead3
          have hrot3b := fitQuiz_quiz3_rot
              (G := G) hPlain hCubic (G.edge x1)
              qa2 qa3 qa1 q2 q3 q1
          have horig :
              G.fitQuiz (G.edge (G.node (G.node x1)))
                (quiz3 qa1 qa2 qa3 q1 q2 q3) = true := by
            rw [hrot3b] at hmid
            simpa [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic] using hmid
          exact Or.inl ⟨G.edge (G.node (G.node x1)), horig⟩
        · exact Or.inr htail3

end Hypermap

end QuizTree

end FourColor

end Schematic.Math.GraphTheory
