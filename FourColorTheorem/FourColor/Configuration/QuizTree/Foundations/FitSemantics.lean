import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations.TreeOperations

namespace Schematic.Math.GraphTheory
namespace FourColor

open Question
open QArity

namespace QuizTree

namespace Hypermap

variable (G : Hypermap)
/-- The three central node arities lie in the quiz-tree coding range. -/
noncomputable def quizTreeFitsArities (x1 : G.Dart) : Bool :=
  let x2 := G.node x1
  let x3 := G.node x2
  let ax1 := QArity.ofNatCode (G.arity x1)
  let ax2 := QArity.ofNatCode (G.arity x2)
  let ax3 := QArity.ofNatCode (G.arity x3)
  (ax1.toNat == G.arity x1) &&
    (ax2.toNat == G.arity x2) &&
      (ax3.toNat == G.arity x3)

theorem quizTreeFitsArities_eq_true_of_bounds
    {x1 : G.Dart}
    (h1lo : 5 ≤ G.arity x1) (h1hi : G.arity x1 ≤ 11)
    (h2lo : 5 ≤ G.arity (G.node x1)) (h2hi : G.arity (G.node x1) ≤ 11)
    (h3lo : 5 ≤ G.arity (G.node (G.node x1)))
    (h3hi : G.arity (G.node (G.node x1)) ≤ 11) :
    quizTreeFitsArities G x1 = true := by
  simp [quizTreeFitsArities,
    QArity.toNat_ofNatCode_eq_of_le h1lo h1hi,
    QArity.toNat_ofNatCode_eq_of_le h2lo h2hi,
    QArity.toNat_ofNatCode_eq_of_le h3lo h3hi]

/-- Leaf-list fit predicate for a fixed central node triple. -/
noncomputable def quizTreeFitList (x1 : G.Dart) : QuizTree → Bool
  | QuizTree.leaf q1 q2 q3 t =>
      let x2 := G.node x1
      let x3 := G.node x2
      (G.fitQ (qstepR G x1) q1) &&
        (G.fitQ (qstepR G x2) q2) &&
          (G.fitQ (qstepR G x3) q3) ||
            quizTreeFitList x1 t
  | _ => false

def LeafTripleFits (x1 : G.Dart) (q1 q2 q3 : Question) : Prop :=
  G.fitQ (qstepR G x1) q1 = true ∧
    G.fitQ (qstepR G (G.node x1)) q2 = true ∧
      G.fitQ (qstepR G (G.node (G.node x1))) q3 = true

def LeafListFits (x1 : G.Dart) : QuizTree → Prop
  | QuizTree.leaf q1 q2 q3 t =>
      LeafTripleFits G x1 q1 q2 q3 ∨ LeafListFits x1 t
  | _ => False

theorem quizTreeFitList_leaf_eq_true
    {x1 : G.Dart} {q1 q2 q3 : Question} {t : QuizTree}
    (hfit :
      quizTreeFitList G x1 (QuizTree.leaf q1 q2 q3 t) = true) :
    (G.fitQ (qstepR G x1) q1 = true ∧
        G.fitQ (qstepR G (G.node x1)) q2 = true ∧
          G.fitQ (qstepR G (G.node (G.node x1))) q3 = true) ∨
      quizTreeFitList G x1 t = true := by
  have h :
      (G.fitQ (qstepR G x1) q1 = true ∧
          G.fitQ (qstepR G (G.node x1)) q2 = true) ∧
        G.fitQ (qstepR G (G.node (G.node x1))) q3 = true ∨
          quizTreeFitList G x1 t = true := by
    simpa [quizTreeFitList, Bool.or_eq_true, Bool.and_eq_true] using hfit
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | htail
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr htail

theorem quizTreeFitList_leaf_of_head
    {x1 : G.Dart} {q1 q2 q3 : Question} {t : QuizTree}
    (h1 : G.fitQ (qstepR G x1) q1 = true)
    (h2 : G.fitQ (qstepR G (G.node x1)) q2 = true)
    (h3 : G.fitQ (qstepR G (G.node (G.node x1))) q3 = true) :
    quizTreeFitList G x1 (QuizTree.leaf q1 q2 q3 t) = true := by
  simp [quizTreeFitList, h1, h2, h3]

theorem quizTreeFitList_leaf_of_tail
    {x1 : G.Dart} {q1 q2 q3 : Question} {t : QuizTree}
    (hfit : quizTreeFitList G x1 t = true) :
    quizTreeFitList G x1 (QuizTree.leaf q1 q2 q3 t) = true := by
  simp [quizTreeFitList, hfit]

@[simp]
theorem quizTreeFitList_nil (x1 : G.Dart) :
    quizTreeFitList G x1 QuizTree.nil = false := rfl

@[simp]
theorem quizTreeFitList_node
    (x1 : G.Dart) (t5 t6 t7 t8 : QuizTree) :
    quizTreeFitList G x1 (QuizTree.node t5 t6 t7 t8) = false := rfl

@[simp]
theorem quizTreeFitList_hubNode
    (x1 : G.Dart) (t58 t9 t10 t11 : QuizTree) :
    quizTreeFitList G x1 (QuizTree.hubNode t58 t9 t10 t11) = false := rfl

theorem quizTreeFitList_eq_true_iff
    {x1 : G.Dart} {t : QuizTree} :
    quizTreeFitList G x1 t = true ↔ LeafListFits G x1 t := by
  induction t with
  | nil =>
      simp [LeafListFits]
  | leaf q1 q2 q3 t ih =>
      constructor
      · intro hfit
        rcases quizTreeFitList_leaf_eq_true (G := G) hfit with hhead | htail
        · exact Or.inl hhead
        · exact Or.inr (ih.mp htail)
      · intro hfit
        rcases hfit with hhead | htail
        · exact quizTreeFitList_leaf_of_head
            (G := G) hhead.1 hhead.2.1 hhead.2.2
        · exact quizTreeFitList_leaf_of_tail (G := G) (ih.mpr htail)
  | node t5 t6 t7 t8 ih5 ih6 ih7 ih8 =>
      simp [LeafListFits]
  | hubNode t58 t9 t10 t11 ih58 ih9 ih10 ih11 =>
      simp [LeafListFits]

theorem fitQ_append_beq
    (x : G.Dart) (q : Question) (rest rhs : List Nat) :
    ((q.flat ++ rest) == ((G.walkQ x q).map G.arity ++ rhs)) =
      (G.fitQ x q && (rest == rhs)) :=
  FourColor.Hypermap.fitQ_append_beq G x q rest rhs

theorem fitQuiz_quiz3_of_leafTripleFits
    {x1 : G.Dart} {qa1 qa2 qa3 : QArity} {q1 q2 q3 : Question}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h1 : G.arity x1 = qa1.toNat)
    (h2 : G.arity (G.node x1) = qa2.toNat)
    (h3 : G.arity (G.node (G.node x1)) = qa3.toNat)
    (hfit : LeafTripleFits G x1 q1 q2 q3) :
    G.fitQuiz (G.edge (G.node x1)) (quiz3 qa1 qa2 qa3 q1 q2 q3) = true := by
  let y := G.edge (G.node x1)
  have hyarity : G.arity y = qa1.toNat := by
    calc
      G.arity y = G.arity (G.face y) :=
        (Hypermap.arity_face (G := G) y).symm
      _ = G.arity x1 := by
        simp [y]
      _ = qa1.toNat := h1
  have hyedge : G.edge y = G.node x1 := by
    simp [y, Hypermap.Plain.edge_edge (G := G) hPlain]
  have hyqstepR : qstepR G y = G.node (G.node x1) := by
    simp [qstepR, y, Hypermap.Plain.edge_edge (G := G) hPlain]
  have hleft :
      qstepL G (G.node (G.node x1)) = qstepR G x1 := by
    simp [qstepL, qstepR, (hCubic x1).1]
  have hfit1eq :
      q1.flat = (G.walkQ (qstepR G x1) q1).map G.arity := by
    have hb :
        (q1.flat == (G.walkQ (qstepR G x1) q1).map G.arity) = true := by
      simpa [Hypermap.fitQ] using hfit.1
    exact eq_of_beq hb
  have hfit2eq :
      q2.flat = (G.walkQ (qstepR G (G.node x1)) q2).map G.arity := by
    have hb :
        (q2.flat == (G.walkQ (qstepR G (G.node x1)) q2).map G.arity) =
          true := by
      simpa [Hypermap.fitQ] using hfit.2.1
    exact eq_of_beq hb
  have hfit3eq :
      q3.flat =
        (G.walkQ (qstepR G (G.node (G.node x1))) q3).map G.arity := by
    have hb :
        (q3.flat ==
            (G.walkQ (qstepR G (G.node (G.node x1))) q3).map G.arity) =
          true := by
      simpa [Hypermap.fitQ] using hfit.2.2
    exact eq_of_beq hb
  simp [Hypermap.fitQuiz, Hypermap.walkQuiz,
    Hypermap.walkQ, Quiz.flat, Question.flat, quiz3, List.map_append,
    y, hyarity, hyedge, hyqstepR, hleft, h2, h3,
    hfit1eq, hfit2eq, hfit3eq]

private theorem arity_edge_face_eq_node_edge
    (hPlain : G.Plain) (hCubic : G.Cubic) (y : G.Dart) :
    G.arity (G.edge (G.face y)) = G.arity (G.node (G.edge y)) := by
  have hfaceEdgeFace :
      G.face (G.edge (G.face y)) = G.node (G.edge y) := by
    apply G.node.injective
    calc
      G.node (G.face (G.edge (G.face y))) = G.face y :=
        G.node_face_edge (G.face y)
      _ = G.node (G.node (G.edge y)) := by
        rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic (G.edge y),
          Hypermap.Plain.edge_edge (G := G) hPlain y]
  simpa [hfaceEdgeFace] using
    (Hypermap.arity_face (G := G) (G.edge (G.face y))).symm

theorem fitQuiz_quiz3_rot
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (y : G.Dart) (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question) :
    G.fitQuiz y (quiz3 qa1 qa2 qa3 q1 q2 q3) =
      G.fitQuiz (G.edge (G.face y)) (quiz3 qa3 qa1 qa2 q3 q1 q2) := by
  simp [Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
    Quiz.flat, Question.flat, quiz3, List.map_append,
    fitQ_append_beq, Hypermap.fitQ, qstepL, qstepR,
    arity_edge_face_eq_node_edge G hPlain hCubic y,
    Hypermap.Plain.edge_edge (G := G) hPlain,
    Hypermap.Plain.node_face_eq_edge (G := G) hPlain,
    Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic,
    Hypermap.arity_face, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem fitQuiz_quiz3_swap
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (y : G.Dart) (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question) :
    G.fitQuiz y (quiz3 qa1 qa2 qa3 q1 q2 q3) =
      G.fitQuiz (G.face y)
        ⟨QaskR qa1 q1, QaskR qa3 (QaskLR qa2 q3 q2)⟩ := by
  simp [Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
    Quiz.flat, Question.flat, quiz3, List.map_append,
    fitQ_append_beq, Hypermap.fitQ, qstepL, qstepR,
    arity_edge_face_eq_node_edge G hPlain hCubic y,
    Hypermap.Plain.edge_edge (G := G) hPlain,
    Hypermap.Plain.node_face_eq_edge (G := G) hPlain,
    Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic,
    Hypermap.arity_face, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem fitQuiz_quiz3_left_norm
    (y : G.Dart) (qa1 qa2 qa1r : QArity)
    (q1 q1l q2 q1r : Question)
    (hnorm : normQ q1 = QaskLR qa1r q1l q1r) :
    G.fitQuiz y (quiz3 qa1 qa2 qa1r q1l q2 q1r) =
      G.fitQuiz y ⟨QaskR qa1 q1, QaskR qa2 q2⟩ := by
  change
    G.fitQuiz y ⟨QaskR qa1 (QaskLR qa1r q1l q1r), QaskR qa2 q2⟩ =
      G.fitQuiz y ⟨QaskR qa1 q1, QaskR qa2 q2⟩
  rw [← hnorm]
  cases q1 <;>
    simp [normQ, Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
      Quiz.flat, Question.flat, List.map_append]

theorem fitQuiz_quiz3_right_norm
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (y : G.Dart) (qa1 qa2 qa2r : QArity)
    (q1 q2 q2l q2r : Question)
    (hnorm : normQ q2 = QaskLR qa2r q2l q2r) :
    G.fitQuiz y (quiz3 qa1 qa2r qa2 q1 q2r q2l) =
      G.fitQuiz (G.face y) ⟨QaskR qa1 q1, QaskR qa2 q2⟩ := by
  rw [fitQuiz_quiz3_swap (G := G) hPlain hCubic]
  rw [← hnorm]
  cases q2 <;>
    simp [normQ, Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
      Quiz.flat, Question.flat, List.map_append]

/-- Query a quiz tree at the central node triple of `x1`. -/
noncomputable def quizTreeFit (x1 : G.Dart) (t : QuizTree) : Bool :=
  let x2 := G.node x1
  let x3 := G.node x2
  let ax1 := QArity.ofNatCode (G.arity x1)
  let ax2 := QArity.ofNatCode (G.arity x2)
  let ax3 := QArity.ofNatCode (G.arity x3)
  quizTreeFitsArities G x1 && quizTreeFitList G x1 (get3 ax1 ax2 ax3 t)

end Hypermap

end QuizTree

end FourColor

end Schematic.Math.GraphTheory
