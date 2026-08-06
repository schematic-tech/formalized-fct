import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations.PutSemantics

namespace Schematic.Math.GraphTheory
namespace FourColor

open Question
open QArity

namespace QuizTree

namespace Hypermap

variable (G : Hypermap)
theorem quizTreeFit_empty_eq_false (x1 : G.Dart) :
    quizTreeFit G x1 QuizTree.empty = false := by
  simp only [quizTreeFit]
  generalize h1 : QArity.ofNatCode (G.arity x1) = qa1
  generalize h2 : QArity.ofNatCode (G.arity (G.node x1)) = qa2
  generalize h3 :
    QArity.ofNatCode (G.arity (G.node (G.node x1))) = qa3
  cases qa1 <;> cases qa2 <;> cases qa3 <;>
    simp [QuizTree.empty, get3, get2, get1]

theorem quizTreeFit_nil_eq_false (x1 : G.Dart) :
    quizTreeFit G x1 QuizTree.nil = false := by
  simp only [quizTreeFit]
  generalize h1 : QArity.ofNatCode (G.arity x1) = qa1
  generalize h2 : QArity.ofNatCode (G.arity (G.node x1)) = qa2
  generalize h3 :
    QArity.ofNatCode (G.arity (G.node (G.node x1))) = qa3
  cases qa1 <;> cases qa2 <;> cases qa3 <;>
    simp [get3, get2, get1]

theorem quizTreeFit_storeQuiz_of_isQuizR_eq_false
    {x1 : G.Dart} {qz : Quiz} {t : QuizTree}
    (hR : qz.isQuizR = false) :
    quizTreeFit G x1 (storeQuiz qz t) = quizTreeFit G x1 t := by
  rw [storeQuiz_eq_self_of_isQuizR_eq_false hR]

theorem quizTreeFit_storeQuiz
    {x1 : G.Dart} {qz : Quiz} {t : QuizTree}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (storeQuiz qz t) = true) :
    (qz.isQuizR = true ∧ ∃ y : G.Dart, G.fitQuiz y qz = true) ∨
      quizTreeFit G x1 t = true := by
  by_cases hR : qz.isQuizR = true
  · rcases qz with ⟨left, right⟩
    cases left <;> cases right <;>
      simp [Quiz.isQuizR, Question.isQaskR] at hR
    rename_i qa1 q1 qa2 q2
    have fit_q1LR :
        ∀ (qa1r : QArity) (q1l q1r : Question),
          normQ q1 = QaskLR qa1r q1l q1r →
          quizTreeFit G x1 (put qa1 qa2 qa1r q1l q2 q1r t) = true →
            ((Quiz.mk (QaskR qa1 q1) (QaskR qa2 q2)).isQuizR = true ∧
                ∃ y : G.Dart,
                  G.fitQuiz y (Quiz.mk (QaskR qa1 q1) (QaskR qa2 q2)) = true) ∨
              quizTreeFit G x1 t = true := by
      intro qa1r q1l q1r hnorm hput
      rcases quizTreeFit_put (G := G) (x1 := x1)
          hPlain hCubic hput with hquiz | htail
      · rcases hquiz with ⟨y, hy⟩
        have hnormFit := fitQuiz_quiz3_left_norm
          (G := G) y qa1 qa2 qa1r q1 q1l q2 q1r hnorm
        rw [hnormFit] at hy
        exact Or.inl ⟨by simp [Quiz.isQuizR, Question.isQaskR], ⟨y, hy⟩⟩
      · exact Or.inr htail
    have fit_q2LR :
        ∀ (qa2r : QArity) (q2l q2r : Question),
          normQ q2 = QaskLR qa2r q2l q2r →
          quizTreeFit G x1 (put qa1 qa2r qa2 q1 q2r q2l t) = true →
            ((Quiz.mk (QaskR qa1 q1) (QaskR qa2 q2)).isQuizR = true ∧
                ∃ y : G.Dart,
                  G.fitQuiz y (Quiz.mk (QaskR qa1 q1) (QaskR qa2 q2)) = true) ∨
              quizTreeFit G x1 t = true := by
      intro qa2r q2l q2r hnorm hput
      rcases quizTreeFit_put (G := G) (x1 := x1)
          hPlain hCubic hput with hquiz | htail
      · rcases hquiz with ⟨y, hy⟩
        have hnormFit := fitQuiz_quiz3_right_norm
          (G := G) hPlain hCubic y qa1 qa2 qa2r q1 q2 q2l q2r hnorm
        rw [hnormFit] at hy
        exact Or.inl ⟨by simp [Quiz.isQuizR, Question.isQaskR], ⟨G.face y, hy⟩⟩
      · exact Or.inr htail
    generalize hq1n : normQ q1 = nq1 at hfit
    generalize hq2n : normQ q2 = nq2 at hfit
    cases nq1 <;> cases nq2
    all_goals simp [storeQuiz, hq1n, hq2n] at hfit
    all_goals first
      | exact Or.inr hfit
      | exact fit_q1LR _ _ _ hq1n hfit
      | exact fit_q2LR _ _ _ hq2n hfit
      | rename_i qa1r q1l q1r qa2r q2l q2r
        by_cases hlt : qa1r.toNat < qa2r.toNat
        · exact fit_q1LR _ _ _ hq1n (by simpa [hlt] using hfit)
        · exact fit_q2LR _ _ _ hq2n (by simpa [hlt] using hfit)
  · have hRfalse : qz.isQuizR = false := by
      cases hq : qz.isQuizR <;> simp [hq] at hR ⊢
    exact Or.inr (by
      simpa [quizTreeFit_storeQuiz_of_isQuizR_eq_false
        (G := G) (x1 := x1) (qz := qz) (t := t) hRfalse] using hfit)

theorem quizTreeFit_storeConfigQuiz_raw
    {x1 : G.Dart} {qz : Quiz} {sym : Bool} {t : QuizTree}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (storeConfigQuiz qz sym t) = true) :
    (qz.isQuizR = true ∧
        ((∃ y : G.Dart, G.fitQuiz y qz = true) ∨
          ∃ y : G.Dart, G.fitQuiz y qz.flip = true)) ∨
      quizTreeFit G x1 t = true := by
  by_cases hsym : sym = true
  · have hstore :
        quizTreeFit G x1 (storeQuiz qz t) = true := by
      simpa [storeConfigQuiz, hsym] using hfit
    rcases quizTreeFit_storeQuiz (G := G) (x1 := x1)
        hPlain hCubic hstore with hnew | hold
    · exact Or.inl ⟨hnew.1, Or.inl hnew.2⟩
    · exact Or.inr hold
  · have hsymFalse : sym = false := by
      cases sym <;> simp at hsym ⊢
    have hstore :
        quizTreeFit G x1 (storeQuiz qz (storeQuiz qz.flip t)) = true := by
      simpa [storeConfigQuiz, hsymFalse] using hfit
    rcases quizTreeFit_storeQuiz (G := G) (x1 := x1)
        hPlain hCubic hstore with hnew | hflipStore
    · exact Or.inl ⟨hnew.1, Or.inl hnew.2⟩
    · rcases quizTreeFit_storeQuiz (G := G) (x1 := x1)
          (qz := qz.flip) (t := t)
          hPlain hCubic hflipStore with hflip | hold
      · exact Or.inl
          ⟨Quiz.isQuizR_of_flip_isQuizR hflip.1, Or.inr hflip.2⟩
      · exact Or.inr hold

end Hypermap

end QuizTree

end FourColor

end Schematic.Math.GraphTheory
