
import FourColorTheorem.FourColor.Configuration.CFQuiz

/-!
Quiz trees.

This ports the executable tree structure and lookup/update operations from the
front of Coq `quiztree.v`.  Configuration quizzes are collated into these
trees; `redpart` queries them against parts.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

open Question
open QArity

/-- Compressed four-way tree storing triples of residual quiz questions. -/
inductive QuizTree
  | nil
  | leaf (q1 q2 q3 : Question) (tail : QuizTree)
  | node (t5 t6 t7 t8 : QuizTree)
  | hubNode (t58 t9 t10 t11 : QuizTree)
  deriving DecidableEq, Repr, Inhabited

namespace QuizTree

def proper : QuizTree → Bool
  | nil => false
  | _ => true

/-- Update one branch indexed by an arity. -/
def put1 (qa : QArity) (qr : QuizTree → QuizTree) : QuizTree → QuizTree
  | node t5 t6 t7 t8 =>
      match qa with
      | Qa5 => node (qr t5) t6 t7 t8
      | Qa6 => node t5 (qr t6) t7 t8
      | Qa7 => node t5 t6 (qr t7) t8
      | Qa8 => node t5 t6 t7 (qr t8)
      | _ => node t5 t6 t7 t8
  | hubNode t58 t9 t10 t11 =>
      match qa with
      | Qa9 => hubNode t58 (qr t9) t10 t11
      | Qa10 => hubNode t58 t9 (qr t10) t11
      | Qa11 => hubNode t58 t9 t10 (qr t11)
      | _ => hubNode (put1 qa qr t58) t9 t10 t11
  | t => t

def put3 (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  put1 qa1 (put1 qa2 (put1 qa3 (leaf q1 q2 q3)))

def put3rot (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question)
    (t : QuizTree) : QuizTree :=
  put3 qa1 qa2 qa3 q1 q2 q3
    (put3 qa2 qa3 qa1 q2 q3 q1
      (put3 qa3 qa1 qa2 q3 q1 q2 t))

/-- Store one triple, including rotations unless the main arity is larger than
eight. -/
def put (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  if 8 < qa1.toNat then
    put3 qa1 qa2 qa3 q1 q2 q3
  else
    put3rot qa1 qa2 qa3 q1 q2 q3

/-- Empty quiz tree with the full branching skeleton. -/
def empty : QuizTree :=
  let mkn t := node t t t t
  let n2 := mkn (mkn nil)
  hubNode (mkn n2) n2 n2 n2

/-- Normalize a question root into an explicit `QaskLR` node when possible. -/
def normQ : Question → Question
  | Qask1 qa => QaskLR qa Qask0 Qask0
  | QaskL qa ql => QaskLR qa ql Qask0
  | QaskR qa qr => QaskLR qa Qask0 qr
  | q => q

theorem Hypermap.fitQ_normQ
    (G : Hypermap) (x : G.Dart) (q : Question) :
    G.fitQ x (normQ q) = G.fitQ x q := by
  cases q <;> simp [normQ, Hypermap.fitQ, Hypermap.walkQ,
    Question.flat, List.map_append]

def quiz3 (qa1 qa2 qa3 : QArity) (q1 q2 q3 : Question) : Quiz :=
  ⟨QaskR qa1 (QaskLR qa3 q1 q3), QaskR qa2 q2⟩

/-- Store one quiz in a tree. -/
def storeQuiz (qz : Quiz) : QuizTree → QuizTree :=
  match qz.left, qz.right with
  | QaskR qa1 q1, QaskR qa2 q2 =>
      match normQ q1, normQ q2 with
      | QaskLR qa1r q1l q1r, QaskLR qa2r q2l q2r =>
          if qa1r.toNat < qa2r.toNat then
            put qa1 qa2 qa1r q1l q2 q1r
          else
            put qa1 qa2r qa2 q1 q2r q2l
      | QaskLR qa1r q1l q1r, _ =>
          put qa1 qa2 qa1r q1l q2 q1r
      | _, QaskLR qa2r q2l q2r =>
          put qa1 qa2r qa2 q1 q2r q2l
      | _, _ => id
  | _, _ => id

theorem storeQuiz_eq_self_of_isQuizR_eq_false
    {qz : Quiz} {t : QuizTree}
    (hR : qz.isQuizR = false) :
    storeQuiz qz t = t := by
  cases qz with
  | mk left right =>
      cases left <;> cases right <;>
        simp [storeQuiz, Quiz.isQuizR, Question.isQaskR] at hR ⊢

theorem Quiz.isQuizR_of_flip_isQuizR
    {qz : Quiz} (hR : qz.flip.isQuizR = true) :
    qz.isQuizR = true := by
  cases qz with
  | mk left right =>
      cases left <;> cases right <;>
        simp [Quiz.flip, Quiz.isQuizR, Question.isQaskR] at hR ⊢

/-- Store a quiz and, unless it is known symmetric, its reflected quiz. -/
def storeConfigQuiz (qz : Quiz) (sym : Bool) (t : QuizTree) : QuizTree :=
  storeQuiz qz (if sym then t else storeQuiz qz.flip t)

/-- Store all configuration quizzes in a tree, aborting to `nil` if the
top-level hub-node shape is lost. -/
def cfquizTreeRec : QuizTree → List Config → QuizTree
  | qt, [] => qt
  | qt, cf :: cfs =>
      let qt' := storeConfigQuiz (CFQuiz.configQuiz cf) cf.symmetric qt
      match qt' with
      | hubNode _ _ _ _ => cfquizTreeRec qt' cfs
      | _ => nil

def cfquizTree (cfs : List Config) : QuizTree :=
  cfquizTreeRec empty cfs

/-- Number of stored triples. -/
def size : QuizTree → Nat
  | nil => 0
  | leaf _ _ _ t => size t + 1
  | node t5 t6 t7 t8 => size t5 + (size t6 + (size t7 + size t8))
  | hubNode t58 t9 t10 t11 => size t58 + (size t9 + (size t10 + size t11))

def configMainArity (cf : Config) : Nat :=
  match CFQuiz.configQuiz cf with
  | ⟨QaskR qa _, _⟩ => qa.toNat
  | _ => 0

def configTreeSizeContribution (cf : Config) : Nat :=
  let nperm := if configMainArity cf ≤ 8 then 3 else 1
  if cf.symmetric then nperm else 2 * nperm

def expectedConfigTreeSize (cfs : List Config) : Nat :=
  cfs.foldr (fun cf acc => configTreeSizeContribution cf + acc) 0

def configsCompiled (cfs : List Config) : Prop :=
  size (cfquizTree cfs) = expectedConfigTreeSize cfs

/-- Lookup one branch, defaulting to `nil`. -/
def get1 (qa : QArity) : QuizTree → QuizTree
  | node t5 t6 t7 t8 =>
      match qa with
      | Qa5 => t5
      | Qa6 => t6
      | Qa7 => t7
      | Qa8 => t8
      | _ => nil
  | hubNode t58 t9 t10 t11 =>
      match qa with
      | Qa9 => t9
      | Qa10 => t10
      | Qa11 => t11
      | _ => get1 qa t58
  | _ => nil

theorem proper_of_get1_proper
    {qa : QArity} {t : QuizTree}
    (hproper : proper (get1 qa t) = true) :
    proper t = true := by
  cases t <;> cases qa <;>
    simp [get1, proper] at hproper ⊢

theorem get1_put1_eq_or_same
    (qa qa' : QArity) (qr : QuizTree → QuizTree) (t : QuizTree) :
    (qa = qa' ∧ qr (get1 qa t) = get1 qa (put1 qa' qr t)) ∨
      get1 qa t = get1 qa (put1 qa' qr t) := by
  induction t generalizing qa qa' qr with
  | nil =>
      cases qa <;> cases qa' <;> simp [get1, put1]
  | leaf q1 q2 q3 t ih =>
      cases qa <;> cases qa' <;> simp [get1, put1]
  | node t5 t6 t7 t8 ih5 ih6 ih7 ih8 =>
      cases qa <;> cases qa' <;> simp [get1, put1]
  | hubNode t58 t9 t10 t11 ih58 ih9 ih10 ih11 =>
      cases qa <;> cases qa' <;>
        simp [get1, put1]
      all_goals first
        | simpa using ih58 Qa5 Qa5 qr
        | simpa using ih58 Qa5 Qa6 qr
        | simpa using ih58 Qa5 Qa7 qr
        | simpa using ih58 Qa5 Qa8 qr
        | simpa using ih58 Qa6 Qa5 qr
        | simpa using ih58 Qa6 Qa6 qr
        | simpa using ih58 Qa6 Qa7 qr
        | simpa using ih58 Qa6 Qa8 qr
        | simpa using ih58 Qa7 Qa5 qr
        | simpa using ih58 Qa7 Qa6 qr
        | simpa using ih58 Qa7 Qa7 qr
        | simpa using ih58 Qa7 Qa8 qr
        | simpa using ih58 Qa8 Qa5 qr
        | simpa using ih58 Qa8 Qa6 qr
        | simpa using ih58 Qa8 Qa7 qr
        | simpa using ih58 Qa8 Qa8 qr

def get2 (qa2 qa3 : QArity) (t : QuizTree) : QuizTree :=
  get1 qa3 (get1 qa2 t)

def get3 (qa1 qa2 qa3 : QArity) (t : QuizTree) : QuizTree :=
  get2 qa2 qa3 (get1 qa1 t)

theorem get2_eq_of_get1_eq
    {qa2 qa3 : QArity} {t t2 t3 : QuizTree}
    (h2 : get1 qa2 t = t2)
    (h3 : get1 qa3 t2 = t3) :
    get2 qa2 qa3 t = t3 := by
  simp [get2, h2, h3]

theorem get3_eq_of_get1_eq
    {qa1 qa2 qa3 : QArity} {t t1 t2 t3 : QuizTree}
    (h1 : get1 qa1 t = t1)
    (h2 : get1 qa2 t1 = t2)
    (h3 : get1 qa3 t2 = t3) :
    get3 qa1 qa2 qa3 t = t3 := by
  simp [get3, get2, h1, h2, h3]

/-- Remove the top hub-node wrapper, if present. -/
def truncate : QuizTree → QuizTree
  | hubNode t58 _ _ _ => t58
  | t => t

end QuizTree

end FourColor

end Schematic.Math.GraphTheory
