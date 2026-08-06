import FourColorTheorem.FourColor.Configuration.Encoding
import FourColorTheorem.FourColor.Configuration.Quiz

/-!
Configuration quiz compilation, executable front.

This ports the executable front of Coq `cfquiz.v`: ring questions, the
recursive quiz compiler for `R`, `Y`, and `H` construction programs, and the
radius-two guard used before storing configuration quizzes.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

open Question
open QArity

/-- A question attached to a ring dart during configuration-quiz compilation. -/
structure RingQuestion where
  isKernel : Bool
  outerArity : Nat
  nodeQuestion : Question
  deriving DecidableEq, Repr, Inhabited

namespace RingQuestion

def toQuestion (rq : RingQuestion) : Question :=
  rq.nodeQuestion

end RingQuestion

namespace CFQuiz

abbrev RqSeq := List RingQuestion

/-- Small arity code for kernel faces, using the offset convention from Coq. -/
def smallQArity : Nat → QArity
  | 3 => Qa5
  | 4 => Qa6
  | 5 => Qa7
  | 6 => Qa8
  | 7 => Qa10
  | _ => Qa9

def badSmallArity : QArity → Bool
  | Qa9 | Qa10 | Qa11 => true
  | _ => false

/-- Large arity code for the central hub candidate. -/
def largeQArity : Nat → QArity
  | 7 => Qa9
  | 8 => Qa10
  | 9 => Qa11
  | a => smallQArity a

/-- Ring arities must lie in the Coq range accepted by `good_ring_arity`. -/
def badRingArity (n : Nat) : Bool :=
  n == 0 || decide (5 ≤ n)

/-- Invalid quiz value. -/
def noQuiz : Quiz :=
  ⟨Qask0, Qask0⟩

def rqsY (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' : Question) : RqSeq :=
  [
    { isKernel := rq1.isKernel
      outerArity := rq1.outerArity + 1
      nodeQuestion := q1' },
    { isKernel := rq3.isKernel
      outerArity := rq3.outerArity + 1
      nodeQuestion := rq3.nodeQuestion }
  ] ++ qs

def cfquizY (rq1 rq2 : RingQuestion)
    (rqs' : Question → RqSeq) : RqSeq :=
  let q1 := rq1.nodeQuestion
  let q2 := rq2.nodeQuestion
  if rq2.isKernel then
    let qa2 := smallQArity rq2.outerArity
    if badSmallArity qa2 then
      []
    else
      rqs' <|
        match q1, q2 with
        | Qask0, Qask0 => Qask1 qa2
        | Qask0, _ => QaskL qa2 q2
        | _, Qask0 => QaskR qa2 q1
        | _, _ => QaskLR qa2 q2 q1
  else
    if badRingArity rq2.outerArity then
      []
    else
      match q1, q2 with
      | Qask0, Qask0 => rqs' Qask0
      | QaskR qa1 q1r, Qask0 => rqs' (QaskRR qa1 q1r)
      | Qask0, QaskL qa1 q1l => rqs' (QaskLL qa1 q1l)
      | _, _ => []

def rqsH (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' q2' : Question) : RqSeq :=
  [
    { isKernel := rq1.isKernel
      outerArity := rq1.outerArity + 1
      nodeQuestion := q1' },
    { isKernel := true
      outerArity := 1
      nodeQuestion := q2' },
    { isKernel := rq3.isKernel
      outerArity := rq3.outerArity + 1
      nodeQuestion := rq3.nodeQuestion }
  ] ++ qs

def cfquizH (rq1 rq2 : RingQuestion)
    (rqs' : Question → Question → RqSeq) : RqSeq :=
  let q1 := rq1.nodeQuestion
  let q2 := rq2.nodeQuestion
  if rq2.isKernel then
    let qa2 := smallQArity (rq2.outerArity + 1)
    if badSmallArity qa2 then
      []
    else
      match q1, q2, rq1.isKernel with
      | Qask0, Qask0, true => rqs' (Qask1 qa2) q2
      | Qask0, Qask0, false => rqs' q1 (Qask1 qa2)
      | Qask0, _, _ => rqs' q1 (QaskL qa2 q2)
      | _, Qask0, _ => rqs' (QaskR qa2 q1) q2
      | _, _, _ => []
  else
    if badRingArity (rq2.outerArity + 1) then
      []
    else
      match q1, q2 with
      | Qask0, Qask0 => rqs' q1 q2
      | _, _ => []

/-- Recursive quiz compiler over the supported `R`, `Y`, and `H` program
fragment. -/
def cfquizRec : RqSeq → CProg → Quiz
  | rq1 :: rq2 :: _, [] =>
      if !(rq1.isKernel && rq2.isKernel) then
        noQuiz
      else
        let qa1 := largeQArity (rq1.outerArity - 1)
        let qa2 := smallQArity (rq2.outerArity - 1)
        if (qa1.toNat != rq1.outerArity + 1) || badSmallArity qa2 then
          noQuiz
        else
          ⟨QaskR qa1 rq2.nodeQuestion, QaskR qa2 rq1.nodeQuestion⟩
  | rq1 :: rq2 :: rq3 :: qs, s :: cp =>
      match s with
      | CpStep.rotate n => cfquizRec (CProg.rotateRight n (rq1 :: rq2 :: rq3 :: qs)) cp
      | CpStep.y => cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs)) cp
      | CpStep.h => cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs)) cp
      | _ => noQuiz
  | _, _ => noQuiz

/-- Initial ring-question sequence used by the final radius-checked wrapper. -/
def initialRingQuestions (n : Nat) : RqSeq :=
  List.replicate n
    { isKernel := false
      outerArity := 0
      nodeQuestion := Qask0 }

/-- The raw quiz compiler without the later radius-two guard. -/
def rawConfigQuiz (cf : Config) : Quiz :=
  cfquizRec (initialRingQuestions (CProg.ringSize cf.program)) cf.program

def allTrue (bs : List Bool) : Bool :=
  bs.all (fun b => b)

/-- Coq `cpradius2`: executable radius-two test for the kernel of a construction
program, using two adjacency-mask propagations from each kernel singleton. -/
def cpradius2 (cp : CProg) : Nat → Bool
  | 0 => false
  | i + 1 =>
      let cm0 := CfMask.cfmask1 cp i
      let mr1 := cm0.ring
      let mk1 := (CfMask.adjMask cm0 cp).kernel
      let mk2 := (CfMask.adjMask ⟨mr1, mk1⟩ cp).kernel
      if allTrue mk2 then true else cpradius2 cp i

/-- Radius-checked configuration quiz.  Invalid configurations compile to
`noQuiz`, matching Coq `cfquiz`. -/
def configQuiz (cf : Config) : Quiz :=
  if cpradius2 cf.program (CProg.kernelSize cf.program) then
    rawConfigQuiz cf
  else
    noQuiz

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
