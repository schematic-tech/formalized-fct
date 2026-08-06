
import FourColorTheorem.FourColor.Discharging.Part

/-!
Quiz questions for configuration matching.

This ports the executable front of Coq `quiz.v`: finite arity codes, question
trees, mirrored quizzes, and the semantic walk/fit predicates.  The embedding
correctness lemmas come later, after the patch/embedding layers have been
ported.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

/-- Explicit arity codes used by configuration quizzes. -/
inductive QArity
  | Qa5 | Qa6 | Qa7 | Qa8 | Qa9 | Qa10 | Qa11
  deriving DecidableEq, Repr, Inhabited

namespace QArity

def toNat : QArity → Nat
  | Qa5 => 5
  | Qa6 => 6
  | Qa7 => 7
  | Qa8 => 8
  | Qa9 => 9
  | Qa10 => 10
  | Qa11 => 11

instance : Coe QArity Nat :=
  ⟨toNat⟩

def ofNatCode : Nat → QArity
  | 5 => Qa5
  | 6 => Qa6
  | 7 => Qa7
  | 8 => Qa8
  | 9 => Qa9
  | 10 => Qa10
  | _ => Qa11

@[simp]
theorem ofNat_toNat (qa : QArity) :
    ofNatCode qa.toNat = qa := by
  cases qa <;> rfl

theorem toNat_ofNatCode_eq_of_le {n : Nat}
    (h5 : 5 ≤ n) (h11 : n ≤ 11) :
    (ofNatCode n).toNat = n := by
  have hcases :
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toNat_bounds (qa : QArity) :
    5 ≤ qa.toNat ∧ qa.toNat ≤ 11 := by
  cases qa <;> simp [toNat]

theorem bounds_of_sizeCheck {n : Nat}
    (hcheck : (n == (ofNatCode n).toNat) = true) :
    5 ≤ n ∧ n ≤ 11 := by
  have hn : n = (ofNatCode n).toNat := by
    have hbeq : n.beq (ofNatCode n).toNat = true := by
      simpa [BEq.beq] using hcheck
    exact Nat.eq_of_beq_eq_true hbeq
  rw [hn]
  exact toNat_bounds (ofNatCode n)

end QArity

/-- Question tree for one side of a configuration quiz. -/
inductive Question
  | Qask0
  | Qask1 (qa : QArity)
  | QaskL (qa : QArity) (q : Question)
  | QaskR (qa : QArity) (q : Question)
  | QaskLR (qa : QArity) (ql qr : Question)
  | QaskLL (qa : QArity) (q : Question)
  | QaskRR (qa : QArity) (q : Question)
  deriving DecidableEq, Repr, Inhabited

namespace Question

def isQaskR : Question → Bool
  | QaskR _ _ => true
  | _ => false

theorem exists_eq_qaskR_of_isQaskR
    {q : Question}
    (h : q.isQaskR = true) :
    ∃ qa q', q = QaskR qa q' := by
  cases q <;> simp [isQaskR] at h ⊢

/-- Prefix-order list of arities tested by a question. -/
def flat : Question → List Nat
  | Qask0 => []
  | Qask1 qa => [qa]
  | QaskL qa q => qa :: flat q
  | QaskR qa q => qa :: flat q
  | QaskLR qa ql qr => qa :: (flat ql ++ flat qr)
  | QaskLL qa q => qa :: flat q
  | QaskRR qa q => qa :: flat q

/-- Mirror image of a question, exchanging left and right branches. -/
def flip : Question → Question
  | QaskL qa q => QaskR qa q.flip
  | QaskR qa q => QaskL qa q.flip
  | QaskLR qa ql qr => QaskLR qa qr.flip ql.flip
  | QaskLL qa q => QaskRR qa q.flip
  | QaskRR qa q => QaskLL qa q.flip
  | q => q

@[simp]
theorem length_flat_flip (q : Question) :
    q.flip.flat.length = q.flat.length := by
  induction q with
  | Qask0 => rfl
  | Qask1 _ => rfl
  | QaskL _ q ih | QaskR _ q ih | QaskLL _ q ih | QaskRR _ q ih =>
      simp [flat, flip, ih]
  | QaskLR _ ql qr ihl ihr =>
      simp [flat, flip, ihl, ihr, Nat.add_comm]

end Question

/-- Left move at a cubic hypermap node. -/
def qstepL (G : Hypermap) (x : G.Dart) : G.Dart :=
  G.node (G.edge (G.node x))

/-- Right move at a cubic hypermap node. -/
def qstepR (G : Hypermap) (x : G.Dart) : G.Dart :=
  G.node (G.edge x)

/-- A quiz consists of the two question trees rooted at the initial edge. -/
structure Quiz where
  left : Question
  right : Question
  deriving DecidableEq, Repr, Inhabited

namespace Quiz

def isQuizR (qz : Quiz) : Bool :=
  qz.left.isQaskR && qz.right.isQaskR

theorem exists_qaskR_left_right_of_isQuizR
    {qz : Quiz}
    (h : qz.isQuizR = true) :
    ∃ qaL qL qaR qR,
      qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ := by
  cases qz with
  | mk ql qr =>
      cases ql <;> cases qr <;>
        simp [isQuizR, Question.isQaskR] at h ⊢

def flat (qz : Quiz) : List Nat :=
  qz.left.flat ++ qz.right.flat

/-- Mirror image of a quiz, matching Coq `flipqz`. -/
def flip (qz : Quiz) : Quiz :=
  match qz.left, qz.right with
  | Question.QaskR qa0 q01, Question.QaskR qa1 q10 =>
      ⟨Question.QaskR qa0 q10.flip, Question.QaskR qa1 q01.flip⟩
  | _, _ => qz

end Quiz

namespace Hypermap

variable (G : Hypermap)

/-- Darts visited while testing a question at a pointed dart. -/
def walkQ (x : G.Dart) : Question → List G.Dart
  | Question.Qask0 => []
  | Question.Qask1 _ => [x]
  | Question.QaskL _ q => x :: walkQ (qstepL G x) q
  | Question.QaskR _ q => x :: walkQ (qstepR G x) q
  | Question.QaskLR _ ql qr =>
      x :: (walkQ (qstepL G x) ql ++ walkQ (qstepR G x) qr)
  | Question.QaskLL _ q =>
      let xl := qstepL G x
      G.edge (G.node xl) :: walkQ (qstepL G xl) q
  | Question.QaskRR _ q =>
      let xr := qstepR G x
      xr :: walkQ (qstepR G xr) q

@[simp]
theorem length_walkQ (x : G.Dart) (q : Question) :
    (walkQ G x q).length = q.flat.length := by
  induction q generalizing x with
  | Qask0 => rfl
  | Qask1 _ => rfl
  | QaskL _ q ih =>
      simp [walkQ, Question.flat, ih]
  | QaskR _ q ih =>
      simp [walkQ, Question.flat, ih]
  | QaskLL _ q ih =>
      simp [walkQ, Question.flat, ih]
  | QaskRR _ q ih =>
      simp [walkQ, Question.flat, ih]
  | QaskLR _ ql qr ihl ihr =>
      simp [walkQ, Question.flat, ihl, ihr]

/-- A question fits when its arity list matches the walked darts. -/
noncomputable def fitQ (x : G.Dart) (q : Question) : Bool :=
  q.flat == (walkQ G x q).map G.arity

@[simp]
theorem fitQ_qask0 (x : G.Dart) :
    fitQ G x Question.Qask0 = true := by
  simp [fitQ, Question.flat, walkQ]

theorem fitQ_qask1_of_arity
    {x : G.Dart} {qa : QArity}
    (hroot : G.arity x = qa.toNat) :
    fitQ G x (Question.Qask1 qa) = true := by
  simp [fitQ, Question.flat, walkQ, hroot]

theorem fitQ_qaskL_of_arity
    {x : G.Dart} {qa : QArity} {q : Question}
    (hroot : G.arity x = qa.toNat)
    (hfit : fitQ G (qstepL G x) q = true) :
    fitQ G x (Question.QaskL qa q) = true := by
  simp [fitQ, Question.flat, walkQ, hroot] at hfit ⊢
  exact hfit

theorem fitQ_qaskR_of_arity
    {x : G.Dart} {qa : QArity} {q : Question}
    (hroot : G.arity x = qa.toNat)
    (hfit : fitQ G (qstepR G x) q = true) :
    fitQ G x (Question.QaskR qa q) = true := by
  simp [fitQ, Question.flat, walkQ, hroot] at hfit ⊢
  exact hfit

theorem fitQ_qaskLR_of_arity
    {x : G.Dart} {qa : QArity} {ql qr : Question}
    (hroot : G.arity x = qa.toNat)
    (hfitL : fitQ G (qstepL G x) ql = true)
    (hfitR : fitQ G (qstepR G x) qr = true) :
    fitQ G x (Question.QaskLR qa ql qr) = true := by
  simp [fitQ, Question.flat, walkQ, hroot, List.map_append] at hfitL hfitR ⊢
  rw [hfitL, hfitR]

theorem fitQ_qaskLL_of_arity
    {x : G.Dart} {qa : QArity} {q : Question}
    (hroot : G.arity (G.edge (G.node (qstepL G x))) = qa.toNat)
    (hfit : fitQ G (qstepL G (qstepL G x)) q = true) :
    fitQ G x (Question.QaskLL qa q) = true := by
  simp [fitQ, Question.flat, walkQ, hroot] at hfit ⊢
  exact hfit

theorem fitQ_qaskRR_of_arity
    {x : G.Dart} {qa : QArity} {q : Question}
    (hroot : G.arity (qstepR G x) = qa.toNat)
    (hfit : fitQ G (qstepR G (qstepR G x)) q = true) :
    fitQ G x (Question.QaskRR qa q) = true := by
  simp [fitQ, Question.flat, walkQ, hroot] at hfit ⊢
  exact hfit

theorem fitQ_qask1_decomp
    {x : G.Dart} {qa : QArity}
    (hfit : fitQ G x (Question.Qask1 qa) = true) :
    G.arity x = qa.toNat := by
  have hfit' := hfit
  simp [fitQ, Question.flat, walkQ] at hfit'
  exact hfit'.symm

theorem fitQ_qaskL_decomp
    {x : G.Dart} {qa : QArity} {q : Question}
    (hfit : fitQ G x (Question.QaskL qa q) = true) :
    G.arity x = qa.toNat ∧ fitQ G (qstepL G x) q = true := by
  simp [fitQ, Question.flat, walkQ] at hfit ⊢
  exact ⟨hfit.1.symm, hfit.2⟩

theorem fitQ_qaskR_decomp
    {x : G.Dart} {qa : QArity} {q : Question}
    (hfit : fitQ G x (Question.QaskR qa q) = true) :
    G.arity x = qa.toNat ∧ fitQ G (qstepR G x) q = true := by
  simp [fitQ, Question.flat, walkQ] at hfit ⊢
  exact ⟨hfit.1.symm, hfit.2⟩

theorem fitQ_qaskLR_decomp
    {x : G.Dart} {qa : QArity} {ql qr : Question}
    (hfit : fitQ G x (Question.QaskLR qa ql qr) = true) :
    G.arity x = qa.toNat ∧
      fitQ G (qstepL G x) ql = true ∧
        fitQ G (qstepR G x) qr = true := by
  simp [fitQ, Question.flat, walkQ, List.map_append] at hfit ⊢
  rcases hfit with ⟨hroot, htail⟩
  have hsplit := List.append_inj htail
    (by simp [Hypermap.length_walkQ])
  exact ⟨hroot.symm, hsplit.1, hsplit.2⟩

theorem fitQ_qaskLL_decomp
    {x : G.Dart} {qa : QArity} {q : Question}
    (hfit : fitQ G x (Question.QaskLL qa q) = true) :
    G.arity (G.edge (G.node (qstepL G x))) = qa.toNat ∧
      fitQ G (qstepL G (qstepL G x)) q = true := by
  simp [fitQ, Question.flat, walkQ] at hfit ⊢
  exact ⟨hfit.1.symm, hfit.2⟩

theorem fitQ_qaskRR_decomp
    {x : G.Dart} {qa : QArity} {q : Question}
    (hfit : fitQ G x (Question.QaskRR qa q) = true) :
    G.arity (qstepR G x) = qa.toNat ∧
      fitQ G (qstepR G (qstepR G x)) q = true := by
  simp [fitQ, Question.flat, walkQ] at hfit ⊢
  exact ⟨hfit.1.symm, hfit.2⟩

/-- Darts visited while testing a quiz. -/
def walkQuiz (x : G.Dart) (qz : Quiz) : List G.Dart :=
  walkQ G x qz.left ++ walkQ G (G.edge x) qz.right

theorem walkQuiz_eq_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true) :
    ∃ qaL qL qaR qR,
      qz = ⟨Question.QaskR qaL qL, Question.QaskR qaR qR⟩ ∧
        G.walkQuiz x qz =
          (x :: G.walkQ (qstepR G x) qL) ++
            (G.edge x :: G.walkQ (qstepR G (G.edge x)) qR) := by
  rcases Quiz.exists_qaskR_left_right_of_isQuizR hR with
    ⟨qaL, qL, qaR, qR, hqz⟩
  refine ⟨qaL, qL, qaR, qR, hqz, ?_⟩
  subst qz
  rfl

theorem mem_walkQuiz_left_tail_of_eq
    {x y : G.Dart} {qz : Quiz} {qa : QArity} {q : Question}
    (hleft : qz.left = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G x) q) :
    y ∈ G.walkQuiz x qz := by
  cases qz with
  | mk ql qr =>
      simp at hleft
      subst ql
      simp [walkQuiz, walkQ, hy]

theorem mem_walkQuiz_right_tail_of_eq
    {x y : G.Dart} {qz : Quiz} {qa : QArity} {q : Question}
    (hright : qz.right = Question.QaskR qa q)
    (hy : y ∈ G.walkQ (qstepR G (G.edge x)) q) :
    y ∈ G.walkQuiz x qz := by
  cases qz with
  | mk ql qr =>
      simp at hright
      subst qr
      simp [walkQuiz, walkQ, hy]

@[simp]
theorem length_walkQuiz (x : G.Dart) (qz : Quiz) :
    (walkQuiz G x qz).length = qz.flat.length := by
  cases qz
  simp [walkQuiz, Quiz.flat]

/-- A quiz fits when its arity list matches all walked darts. -/
noncomputable def fitQuiz (x : G.Dart) (qz : Quiz) : Bool :=
  qz.flat == (walkQuiz G x qz).map G.arity

theorem qstepL_mirror_eq_qstepR
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    qstepL G.mirror x = qstepR G x := by
  rw [qstepL, qstepR]
  change G.node.symm (G.face (G.node (G.node.symm x))) = G.node (G.edge x)
  simp only [Equiv.apply_symm_apply]
  apply G.node.injective
  simp [Hypermap.Plain.face_eq_node_node_edge_of_cubic
    (G := G) hPlain hCubic x]

theorem qstepR_mirror_eq_qstepL
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    qstepR G.mirror x = qstepL G x := by
  rw [qstepL, qstepR]
  change G.node.symm (G.face (G.node x)) =
    G.node (G.edge (G.node x))
  apply G.node.injective
  simp [Hypermap.Plain.face_eq_node_node_edge_of_cubic
    (G := G) hPlain hCubic (G.node x)]

theorem qstepL_face_eq_node_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    qstepL G (G.face x) = G.node x := by
  rw [qstepL]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem qstepR_edge_eq_node_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.edge x) = G.node x := by
  rw [qstepR]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem qstepL_eq_node_face_symm
    (x : G.Dart) :
    qstepL G x = G.node (G.face.symm x) := by
  simp [qstepL, Hypermap.edge_node_eq_face_symm]

theorem qstepR_eq_node_node_face_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    qstepR G x = G.node (G.node (G.face x)) := by
  rw [qstepR]
  rw [Hypermap.Plain.edge_eq_node_face (G := G) hPlain x]

theorem qstepR_face_symm_eq_node_node_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.face.symm x) = G.node (G.node x) := by
  rw [qstepR_eq_node_node_face_of_plain (G := G) hPlain]
  simp

theorem qstepR_node_eq_node_face_symm
    (x : G.Dart) :
    qstepR G (G.node x) = G.node (G.face.symm x) := by
  simp [qstepR, Hypermap.edge_node_eq_face_symm]

theorem qstepR_node_face_eq_node_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    qstepR G (G.node (G.face x)) = G.node x := by
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  simp [qstepR, Hypermap.Plain.edge_edge (G := G) hPlain x]

theorem qstepL_node_node_eq_node_node_face_of_plain_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    qstepL G (G.node (G.node x)) = G.node (G.node (G.face x)) := by
  rw [qstepL]
  rw [(hCubic x).1]
  rw [Hypermap.Plain.edge_eq_node_face (G := G) hPlain x]

theorem mirror_edge_face_eq_face_edge_of_plain
    (hPlain : G.Plain) (x : G.Dart) :
    G.mirror.edge (G.face x) = G.face (G.edge x) := by
  change G.face (G.node (G.face x)) = G.face (G.edge x)
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]

theorem qstepR_mirror_face_eq_node
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    qstepR G.mirror (G.face x) = G.node x := by
  rw [qstepR_mirror_eq_qstepL (G := G) hPlain hCubic]
  exact qstepL_face_eq_node_of_plain (G := G) hPlain x

theorem qstepR_mirror_edge_face_eq_qstepR
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    qstepR G.mirror (G.mirror.edge (G.face x)) = qstepR G x := by
  rw [mirror_edge_face_eq_face_edge_of_plain (G := G) hPlain x]
  rw [qstepR_mirror_eq_qstepL (G := G) hPlain hCubic]
  rw [qstepL_face_eq_node_of_plain (G := G) hPlain (G.edge x)]
  rfl

theorem arity_edge_node_eq_arity (x : G.Dart) :
    G.arity (G.edge (G.node x)) = G.arity x := by
  simpa [Hypermap.face_edge_node] using
    (Hypermap.arity_face (G := G) (G.edge (G.node x))).symm

theorem arity_mirror_edge_node_eq_arity (x : G.Dart) :
    G.arity (G.mirror.edge (G.mirror.node x)) = G.arity x := by
  calc
    G.arity (G.mirror.edge (G.mirror.node x)) =
        G.mirror.arity (G.mirror.edge (G.mirror.node x)) := by
          exact (G.arity_mirror (G.mirror.edge (G.mirror.node x))).symm
    _ = G.mirror.arity x := arity_edge_node_eq_arity (G := G.mirror) x
    _ = G.arity x := G.arity_mirror x

private theorem listNat_beq_append_eq_and
    (xs ys zs ws : List Nat)
    (hlen : xs.length = zs.length) :
    ((xs ++ ys) == (zs ++ ws)) = ((xs == zs) && (ys == ws)) := by
  induction xs generalizing zs with
  | nil =>
      cases zs <;> simp at hlen ⊢
  | cons x xs ih =>
      cases zs with
      | nil =>
          simp at hlen
      | cons z zs =>
          simp at hlen ⊢
          rw [ih zs hlen]
          by_cases hxz : x = z
          · subst z
            simp
          · have hbeq : (x == z) = false := beq_false_of_ne hxz
            simp [hbeq]

theorem fitQ_append_beq
    (x : G.Dart) (q : Question) (rest rhs : List Nat) :
    ((q.flat ++ rest) == ((G.walkQ x q).map G.arity ++ rhs)) =
      (G.fitQ x q && (rest == rhs)) := by
  rw [listNat_beq_append_eq_and]
  · simp [Hypermap.fitQ]
  · simp [Hypermap.length_walkQ]

theorem fitQ_flip_mirror
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) (q : Question) :
    G.fitQ x q.flip = G.mirror.fitQ x q := by
  induction q generalizing x with
  | Qask0 =>
      simp [Hypermap.fitQ, Hypermap.walkQ, Question.flat, Question.flip]
  | Qask1 qa =>
      simp [Hypermap.fitQ, Hypermap.walkQ, Question.flat, Question.flip,
        G.arity_mirror x]
  | QaskL qa q ih =>
      have hrec := ih (qstepR G x)
      have hstep := qstepL_mirror_eq_qstepR (G := G) hPlain hCubic x
      simpa [Question.flip, Hypermap.fitQ, Hypermap.walkQ, Question.flat,
        G.arity_mirror x, hstep] using
        congrArg (fun b => (qa.toNat == G.arity x) && b) hrec
  | QaskR qa q ih =>
      have hrec := ih (qstepL G x)
      have hstep := qstepR_mirror_eq_qstepL (G := G) hPlain hCubic x
      simpa [Question.flip, Hypermap.fitQ, Hypermap.walkQ, Question.flat,
        G.arity_mirror x, hstep] using
        congrArg (fun b => (qa.toNat == G.arity x) && b) hrec
  | QaskLR qa ql qr ihl ihr =>
      have hrecL := ihl (qstepR G x)
      have hrecR := ihr (qstepL G x)
      have hrecL' :
          (ql.flip.flat == (G.walkQ (qstepR G x) ql.flip).map G.arity) =
            (ql.flat ==
              (G.mirror.walkQ (qstepR G x) ql).map G.mirror.arity) := by
        simpa [Hypermap.fitQ] using hrecL
      have hrecR' :
          (qr.flip.flat == (G.walkQ (qstepL G x) qr.flip).map G.arity) =
            (qr.flat ==
              (G.mirror.walkQ (qstepL G x) qr).map G.mirror.arity) := by
        simpa [Hypermap.fitQ] using hrecR
      have hstepL := qstepL_mirror_eq_qstepR (G := G) hPlain hCubic x
      have hstepR := qstepR_mirror_eq_qstepL (G := G) hPlain hCubic x
      simp [Question.flip, Hypermap.fitQ, Hypermap.walkQ, Question.flat,
        List.map_append, fitQ_append_beq,
        G.arity_mirror x, hstepL, hstepR, hrecL', hrecR', Bool.and_comm]
  | QaskLL qa q ih =>
      have hrec := ih (qstepR G (qstepR G x))
      have hstep0 := qstepL_mirror_eq_qstepR (G := G) hPlain hCubic x
      have hstep1 :=
        qstepL_mirror_eq_qstepR (G := G) hPlain hCubic (qstepR G x)
      have harity := arity_mirror_edge_node_eq_arity (G := G) (qstepR G x)
      simpa [Question.flip, Hypermap.fitQ, Hypermap.walkQ, Question.flat,
        G.arity_mirror, hstep0, hstep1, harity] using
        congrArg (fun b => (qa.toNat == G.arity (qstepR G x)) && b) hrec
  | QaskRR qa q ih =>
      have hrec := ih (qstepL G (qstepL G x))
      have hstep0 := qstepR_mirror_eq_qstepL (G := G) hPlain hCubic x
      have hstep1 :=
        qstepR_mirror_eq_qstepL (G := G) hPlain hCubic (qstepL G x)
      have harity := arity_edge_node_eq_arity (G := G) (qstepL G x)
      simpa [Question.flip, Hypermap.fitQ, Hypermap.walkQ, Question.flat,
        G.arity_mirror, hstep0, hstep1, harity] using
        congrArg (fun b => (qa.toNat == G.arity (qstepL G x)) && b) hrec

theorem fitQuiz_flip
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) (qz : Quiz)
    (hR : qz.isQuizR = true) :
    G.fitQuiz x qz.flip = G.mirror.fitQuiz (G.face x) qz := by
  cases qz with
  | mk left right =>
      cases left <;> cases right <;>
        simp [Quiz.isQuizR, Question.isQaskR] at hR
      rename_i qa0 q01 qa1 q10
      have hq10 :=
        fitQ_flip_mirror (G := G) hPlain hCubic (qstepR G x) q10
      have hq01 :=
        fitQ_flip_mirror (G := G) hPlain hCubic (G.node x) q01
      have hq10' :
          (q10.flip.flat ==
              (G.walkQ (qstepR G x) q10.flip).map G.arity) =
            (q10.flat ==
              (G.mirror.walkQ (qstepR G x) q10).map G.mirror.arity) := by
        simpa [Hypermap.fitQ] using hq10
      have hq01' :
          (q01.flip.flat ==
              (G.walkQ (G.node x) q01.flip).map G.arity) =
            (q01.flat ==
              (G.mirror.walkQ (G.node x) q01).map G.mirror.arity) := by
        simpa [Hypermap.fitQ] using hq01
      have hmirrorEdge :=
        mirror_edge_face_eq_face_edge_of_plain (G := G) hPlain x
      have hqstepR_edge := qstepR_edge_eq_node_of_plain (G := G) hPlain x
      have hqstepR_mirror_face :=
        qstepR_mirror_face_eq_node (G := G) hPlain hCubic x
      have hqstepR_mirror_edge_face :=
        qstepR_mirror_edge_face_eq_qstepR (G := G) hPlain hCubic x
      have hqstepR_mirror_face_edge :
          qstepR G.mirror (G.face (G.edge x)) = qstepR G x := by
        simpa [hmirrorEdge] using hqstepR_mirror_edge_face
      have harityFace : G.mirror.arity (G.face x) = G.arity x := by
        rw [G.arity_mirror, Hypermap.arity_face]
      have harityFaceEdge :
          G.mirror.arity (G.face (G.edge x)) = G.arity (G.edge x) := by
        rw [G.arity_mirror, Hypermap.arity_face]
      simp [Quiz.flip, Hypermap.fitQuiz, Hypermap.fitQ,
        Hypermap.walkQuiz, Hypermap.walkQ,
        Quiz.flat, Question.flat, List.map_append, fitQ_append_beq,
        hmirrorEdge, hqstepR_edge, hqstepR_mirror_face,
        hqstepR_mirror_face_edge, harityFace, harityFaceEdge,
        hq10', hq01', Bool.and_assoc, Bool.and_comm]

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
