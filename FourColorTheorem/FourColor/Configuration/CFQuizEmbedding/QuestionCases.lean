import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.Arity

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap


/-- The question selected by Coq `cfquiz_Y` when the removed middle ring
face belongs to the kernel. -/
def yKernelQuestion (qa : QArity) (q1 q2 : Question) : Question :=
  match q1, q2 with
  | Question.Qask0, Question.Qask0 => Question.Qask1 qa
  | Question.Qask0, _ => Question.QaskL qa q2
  | _, Question.Qask0 => Question.QaskR qa q1
  | _, _ => Question.QaskLR qa q2 q1

theorem yKernelQuestion_flat
    (qa : QArity) (q1 q2 : Question) :
    (yKernelQuestion qa q1 q2).flat =
      (Question.QaskLR qa q2 q1).flat := by
  cases q1 <;> cases q2 <;>
    simp [yKernelQuestion, Question.flat]

theorem yKernelQuestion_walk
    (G : Hypermap) (x : G.Dart)
    (qa : QArity) (q1 q2 : Question) :
    G.walkQ x (yKernelQuestion qa q1 q2) =
      G.walkQ x (Question.QaskLR qa q2 q1) := by
  cases q1 <;> cases q2 <;>
    simp [yKernelQuestion, Hypermap.walkQ]

theorem fitQ_yKernelQuestion_iff
    (G : Hypermap) (x : G.Dart)
    (qa : QArity) (q1 q2 : Question) :
    G.fitQ x (yKernelQuestion qa q1 q2) = true ↔
      G.fitQ x (Question.QaskLR qa q2 q1) = true := by
  simp only [Hypermap.fitQ]
  rw [yKernelQuestion_flat, yKernelQuestion_walk]

theorem smallQArity_not_bad_iff {n : Nat} :
    badSmallArity (smallQArity n) = false ↔ 3 ≤ n ∧ n ≤ 6 := by
  constructor
  · intro hgood
    have hn : n < 8 := by
      by_contra hnot
      have hn8 : 8 ≤ n := by omega
      obtain ⟨k, hk⟩ : ∃ k, n = k + 8 := by
        exact ⟨n - 8, by omega⟩
      subst n
      simp [smallQArity, badSmallArity] at hgood
    have hcases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
          n = 5 ∨ n = 6 ∨ n = 7 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [smallQArity, badSmallArity] at hgood ⊢
  · rintro ⟨hn3, hn6⟩
    have hcases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      decide

theorem smallQArity_toNat_eq_add_two_of_not_bad
    {n : Nat}
    (hgood : badSmallArity (smallQArity n) = false) :
    (smallQArity n).toNat = n + 2 := by
  have hn := smallQArity_not_bad_iff.mp hgood
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    decide

/-- The four successful branches of Coq `cfquiz_Y`: one kernel branch and
the three nonkernel question shapes that survive the executable guards. -/
def YQuestionCase (rq1 rq2 : RingQuestion) (q' : Question) : Prop :=
  (rq2.isKernel = true ∧
      badSmallArity (smallQArity rq2.outerArity) = false ∧
        q' = yKernelQuestion (smallQArity rq2.outerArity)
          rq1.nodeQuestion rq2.nodeQuestion) ∨
    (rq2.isKernel = false ∧ badRingArity rq2.outerArity = false ∧
      ((rq1.nodeQuestion = Question.Qask0 ∧
          rq2.nodeQuestion = Question.Qask0 ∧
            q' = Question.Qask0) ∨
        (∃ qa q,
          rq1.nodeQuestion = Question.QaskR qa q ∧
            rq2.nodeQuestion = Question.Qask0 ∧
              q' = Question.QaskRR qa q) ∨
        (∃ qa q,
          rq1.nodeQuestion = Question.Qask0 ∧
            rq2.nodeQuestion = Question.QaskL qa q ∧
              q' = Question.QaskLL qa q)))

theorem cfquizY_case_of_isQuizR
    (rq1 rq2 rq3 : RingQuestion) (qs : RqSeq) (cp : CProg)
    (hR :
      (cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs)) cp).isQuizR = true) :
    ∃ q' : Question,
      cfquizY rq1 rq2 (rqsY rq1 rq3 qs) = rqsY rq1 rq3 qs q' ∧
        YQuestionCase rq1 rq2 q' := by
  cases hk : rq2.isKernel with
  | true =>
      cases hb : badSmallArity (smallQArity rq2.outerArity) with
      | true =>
          simp [cfquizY, hk, hb, cfquizRec, noQuiz,
            Quiz.isQuizR, Question.isQaskR] at hR
      | false =>
          refine ⟨yKernelQuestion (smallQArity rq2.outerArity)
            rq1.nodeQuestion rq2.nodeQuestion, ?_, ?_⟩
          · simp [cfquizY, hk, hb, yKernelQuestion]
            rfl
          · exact Or.inl ⟨hk, hb, rfl⟩
  | false =>
      cases hb : badRingArity rq2.outerArity with
      | true =>
          simp [cfquizY, hk, hb, cfquizRec, noQuiz,
            Quiz.isQuizR, Question.isQaskR] at hR
      | false =>
          cases hq1 : rq1.nodeQuestion <;>
            cases hq2 : rq2.nodeQuestion <;>
              simp [cfquizY, hk, hb, YQuestionCase, hq1, hq2,
                cfquizRec, noQuiz, Quiz.isQuizR, Question.isQaskR]
                at hR ⊢

/-- The five successful branches of Coq `cfquiz_H`: four placements of the
guarded kernel question and the single nonkernel zero-question branch. -/
def HQuestionCase (rq1 rq2 : RingQuestion)
    (q1' q2' : Question) : Prop :=
  (rq2.isKernel = true ∧
      badSmallArity (smallQArity (rq2.outerArity + 1)) = false ∧
      ((rq1.nodeQuestion = Question.Qask0 ∧
          rq2.nodeQuestion = Question.Qask0 ∧ rq1.isKernel = true ∧
          q1' = Question.Qask1
            (smallQArity (rq2.outerArity + 1)) ∧
          q2' = Question.Qask0) ∨
        (rq1.nodeQuestion = Question.Qask0 ∧
          rq2.nodeQuestion = Question.Qask0 ∧ rq1.isKernel = false ∧
          q1' = Question.Qask0 ∧
          q2' = Question.Qask1
            (smallQArity (rq2.outerArity + 1))) ∨
        (rq1.nodeQuestion = Question.Qask0 ∧
          rq2.nodeQuestion ≠ Question.Qask0 ∧
          q1' = Question.Qask0 ∧
          q2' = Question.QaskL
            (smallQArity (rq2.outerArity + 1)) rq2.nodeQuestion) ∨
        (rq1.nodeQuestion ≠ Question.Qask0 ∧
          rq2.nodeQuestion = Question.Qask0 ∧
          q1' = Question.QaskR
            (smallQArity (rq2.outerArity + 1)) rq1.nodeQuestion ∧
          q2' = Question.Qask0))) ∨
    (rq2.isKernel = false ∧
      badRingArity (rq2.outerArity + 1) = false ∧
      rq1.nodeQuestion = Question.Qask0 ∧
      rq2.nodeQuestion = Question.Qask0 ∧
      q1' = Question.Qask0 ∧ q2' = Question.Qask0)

theorem cfquizH_case_of_isQuizR
    (rq1 rq2 rq3 : RingQuestion) (qs : RqSeq) (cp : CProg)
    (hR :
      (cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs)) cp).isQuizR = true) :
    ∃ q1' q2' : Question,
      cfquizH rq1 rq2 (rqsH rq1 rq3 qs) =
          rqsH rq1 rq3 qs q1' q2' ∧
        HQuestionCase rq1 rq2 q1' q2' := by
  cases hk : rq2.isKernel with
  | false =>
      cases hb : badRingArity (rq2.outerArity + 1) with
      | true =>
          simp [cfquizH, hk, hb, cfquizRec, noQuiz,
            Quiz.isQuizR, Question.isQaskR] at hR
      | false =>
          cases hq1 : rq1.nodeQuestion <;>
            cases hq2 : rq2.nodeQuestion <;>
              simp [cfquizH, hk, hb, HQuestionCase, hq1, hq2,
                cfquizRec, noQuiz, Quiz.isQuizR, Question.isQaskR]
                at hR ⊢
  | true =>
      cases hb : badSmallArity
          (smallQArity (rq2.outerArity + 1)) with
      | true =>
          simp [cfquizH, hk, hb, cfquizRec, noQuiz,
            Quiz.isQuizR, Question.isQaskR] at hR
      | false =>
          cases hk1 : rq1.isKernel <;>
            cases hq1 : rq1.nodeQuestion <;>
              cases hq2 : rq2.nodeQuestion <;>
                simp [cfquizH, hk, hb, hk1, HQuestionCase, hq1, hq2,
                  cfquizRec, noQuiz, Quiz.isQuizR, Question.isQaskR]
                  at hR ⊢

theorem badRingArity_eq_false_iff {n : Nat} :
    badRingArity n = false ↔ n ≠ 0 ∧ n < 5 := by
  simp [badRingArity]

theorem badRingArity_eq_true_iff {n : Nat} :
    badRingArity n = true ↔ n = 0 ∨ 5 ≤ n := by
  simp [badRingArity]

/-- Coq `not_bad_ring_arity`, translated through the Lean `GoodRingArity`
predicate. -/
theorem goodRingArity_of_badRingArity_sub_two_eq_false
    {G : Hypermap} {x : G.Dart}
    (hbad : badRingArity (G.arity x - 2) = false) :
    G.GoodRingArity x := by
  have hinfo := (badRingArity_eq_false_iff).1 hbad
  have hpos : 0 < G.arity x := G.arity_pos x
  have harity :
      G.arity x = 3 ∨ G.arity x = 4 ∨
        G.arity x = 5 ∨ G.arity x = 6 := by
    omega
  simpa [Hypermap.GoodRingArity] using harity

/-- Coq `rqs_fit`: a ring-question sequence fits a list of source ring darts
through an injection into the full configuration map. -/
noncomputable def rqSeqFits (G0 G : Hypermap) (h : G.Dart → G0.Dart) :
    RqSeq → List G.Dart → Bool
  | rq :: qs, x :: xs =>
      (G0.arity (h x) == rq.outerArity + G.arity x) &&
        G0.fitQ (G0.node (h x)) rq.nodeQuestion &&
          rqSeqFits G0 G h qs xs
  | [], [] => true
  | _, _ => false

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
