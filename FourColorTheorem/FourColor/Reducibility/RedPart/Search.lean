import FourColorTheorem.FourColor.Reducibility.RedPart.QuestionSoundness

/-! Bounded quiz-tree and redpart search. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open Part
open PRange
open Question
open QArity

namespace RedPart

open ZPartLoc
def qztGetr (r : PRange) : QuizTree → QuizTree
  | QuizTree.node t5 t6 t7 t8 =>
      match r with
      | Pr55 => t5
      | Pr56 | Pr66 => t6
      | Pr57 | Pr67 | Pr77 => t7
      | Pr58 | Pr68 | Pr78 | Pr88 => t8
      | _ => QuizTree.nil
  | _ => QuizTree.nil

theorem qztGetr_fit
    {r : PRange} {qt : QuizTree}
    (hproper : QuizTree.proper (qztGetr r qt) = true) :
    fitQa r (topQa r) = true ∧
      QuizTree.get1 (topQa r) qt = qztGetr r qt ∧
        QuizTree.proper qt = true := by
  cases qt <;> cases r <;>
    simp [qztGetr, topQa, fitQa, QuizTree.get1, QuizTree.proper] at hproper ⊢

def redQztLeaf (ctx : Context) (zp1 zp2 zp3 : ZPart) : QuizTree → Bool
  | QuizTree.leaf q1 q2 q3 qtl =>
      if fitQZP ctx zp3 q3 then
        if fitQZP ctx zp2 q2 then
          if fitQZP ctx zp1 q1 then
            redPopQZP ctx zp1 q1 &&
              redPopQZP ctx zp2 q2 &&
                redPopQZP ctx zp3 q3
          else
            redQztLeaf ctx zp1 zp2 zp3 qtl
        else
          redQztLeaf ctx zp1 zp2 zp3 qtl
      else
        redQztLeaf ctx zp1 zp2 zp3 qtl
  | _ => false

theorem redQztLeaf_proper
    {ctx : Context} {zp1 zp2 zp3 : ZPart} {qt : QuizTree}
    (hred : redQztLeaf ctx zp1 zp2 zp3 qt = true) :
    QuizTree.proper qt = true := by
  cases qt <;> simp [redQztLeaf, QuizTree.proper] at hred ⊢

theorem qztGetr_fit_of_redQztLeaf
    {ctx : Context} {zp1 zp2 zp3 : ZPart} {r : PRange} {qt : QuizTree}
    (hred : redQztLeaf ctx zp1 zp2 zp3 (qztGetr r qt) = true) :
    fitQa r (topQa r) = true ∧
      QuizTree.get1 (topQa r) qt = qztGetr r qt ∧
        QuizTree.proper qt = true :=
  qztGetr_fit (redQztLeaf_proper hred)

theorem get3_eq_qztGetr_qztGetr_of_redQztLeaf
    {ctx : Context} {zp1 zp2 zp3 : ZPart}
    {qa1 : QArity} {r2 r3 : PRange} {qt : QuizTree}
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt))) = true) :
    QuizTree.get3 qa1 (topQa r2) (topQa r3) qt =
      qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt)) := by
  have h3 := qztGetr_fit_of_redQztLeaf hred
  have h2 := qztGetr_fit h3.2.2
  exact QuizTree.get3_eq_of_get1_eq
    (qa1 := qa1) (qa2 := topQa r2) (qa3 := topQa r3)
    (t := qt) (t1 := QuizTree.get1 qa1 qt)
    (t2 := qztGetr r2 (QuizTree.get1 qa1 qt))
    (t3 := qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt)))
    rfl h2.2.1 h3.2.1

theorem redQztLeaf_quizTreeFitList_of_fitQZP
    {G : Hypermap} {ctx : Context} {zp1 zp2 zp3 : ZPart}
    {qt : QuizTree} {x : G.Dart}
    (hred : redQztLeaf ctx zp1 zp2 zp3 qt = true)
    (hfit1 : ∀ q : Question,
      fitQZP ctx zp1 q = true →
        redPopQZP ctx zp1 q = true →
          G.fitQ (qstepR G x) q = true)
    (hfit2 : ∀ q : Question,
      fitQZP ctx zp2 q = true →
        redPopQZP ctx zp2 q = true →
          G.fitQ (qstepR G (G.node x)) q = true)
    (hfit3 : ∀ q : Question,
      fitQZP ctx zp3 q = true →
        redPopQZP ctx zp3 q = true →
          G.fitQ (qstepR G (G.node (G.node x))) q = true) :
    QuizTree.Hypermap.quizTreeFitList G x qt = true := by
  induction qt with
  | nil =>
      simp [redQztLeaf] at hred
  | node t5 t6 t7 t8 =>
      simp [redQztLeaf] at hred
  | hubNode t58 t9 t10 t11 =>
      simp [redQztLeaf] at hred
  | leaf q1 q2 q3 tail ih =>
      simp only [redQztLeaf] at hred
      by_cases hq3 : fitQZP ctx zp3 q3 = true
      · simp [hq3] at hred
        by_cases hq2 : fitQZP ctx zp2 q2 = true
        · simp [hq2] at hred
          by_cases hq1 : fitQZP ctx zp1 q1 = true
          · simp [hq1] at hred
            have hpop1 : redPopQZP ctx zp1 q1 = true := by
              exact hred.1.1
            have hpop2 : redPopQZP ctx zp2 q2 = true := by
              exact hred.1.2
            have hpop3 : redPopQZP ctx zp3 q3 = true := by
              exact hred.2
            have hq1' := hfit1 q1 hq1 hpop1
            have hq2' := hfit2 q2 hq2 hpop2
            have hq3' := hfit3 q3 hq3 hpop3
            simp [QuizTree.Hypermap.quizTreeFitList, hq1', hq2', hq3']
          · simp [hq1] at hred
            have htail := ih hred
            simp [QuizTree.Hypermap.quizTreeFitList, htail]
        · simp [hq2] at hred
          have htail := ih hred
          simp [QuizTree.Hypermap.quizTreeFitList, htail]
      · simp [hq3] at hred
        have htail := ih hred
        simp [QuizTree.Hypermap.quizTreeFitList, htail]

theorem false_of_redQztLeaf_of_quizTreeFitList_eq_false
    {G : Hypermap} {ctx : Context} {zp1 zp2 zp3 : ZPart}
    {qt : QuizTree} {x : G.Dart}
    (hred : redQztLeaf ctx zp1 zp2 zp3 qt = true)
    (hnofit : QuizTree.Hypermap.quizTreeFitList G x qt = false)
    (hfit1 : ∀ q : Question,
      fitQZP ctx zp1 q = true →
        redPopQZP ctx zp1 q = true →
          G.fitQ (qstepR G x) q = true)
    (hfit2 : ∀ q : Question,
      fitQZP ctx zp2 q = true →
        redPopQZP ctx zp2 q = true →
          G.fitQ (qstepR G (G.node x)) q = true)
    (hfit3 : ∀ q : Question,
      fitQZP ctx zp3 q = true →
        redPopQZP ctx zp3 q = true →
          G.fitQ (qstepR G (G.node (G.node x))) q = true) :
    False := by
  have hhit :=
    redQztLeaf_quizTreeFitList_of_fitQZP
      (G := G) (ctx := ctx) (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
      (qt := qt) (x := x) hred hfit1 hfit2 hfit3
  rw [hnofit] at hhit
  contradiction

theorem redQztLeaf_quizTreeFitList_of_zippedQuestionSound
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    {zp1 zp2 zp3 : ZPart} {qt : QuizTree} {x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid1 : zpvalid ctx zp1)
    (hvalid2 : zpvalid ctx zp2)
    (hvalid3 : zpvalid ctx zp3)
    (hzp1 : zpfit G x0 (qstepR G x) zp1)
    (hzp2 : zpfit G x0 (qstepR G (G.node x)) zp2)
    (hzp3 : zpfit G x0 (qstepR G (G.node (G.node x))) zp3)
    (hred : redQztLeaf ctx zp1 zp2 zp3 qt = true) :
    QuizTree.Hypermap.quizTreeFitList G x qt = true := by
  apply redQztLeaf_quizTreeFitList_of_fitQZP
    (G := G) (ctx := ctx) (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
    (qt := qt) (x := x) hred
  · intro q hfit hredPop
    rcases fitQZP_proper (ctx := ctx) (zp := zp1) hfit with hq0 | hproper
    · subst q
      simp [Hypermap.fitQ, Hypermap.walkQ, Question.flat]
    · have hsem := hsound hvalid1 hfit hredPop
      simpa [hzp1 hproper] using hsem
  · intro q hfit hredPop
    rcases fitQZP_proper (ctx := ctx) (zp := zp2) hfit with hq0 | hproper
    · subst q
      simp [Hypermap.fitQ, Hypermap.walkQ, Question.flat]
    · have hsem := hsound hvalid2 hfit hredPop
      simpa [hzp2 hproper] using hsem
  · intro q hfit hredPop
    rcases fitQZP_proper (ctx := ctx) (zp := zp3) hfit with hq0 | hproper
    · subst q
      simp [Hypermap.fitQ, Hypermap.walkQ, Question.flat]
    · have hsem := hsound hvalid3 hfit hredPop
      simpa [hzp3 hproper] using hsem

theorem false_of_redQztLeaf_of_quizTreeFitList_eq_false_of_zippedQuestionSound
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    {zp1 zp2 zp3 : ZPart} {qt : QuizTree} {x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid1 : zpvalid ctx zp1)
    (hvalid2 : zpvalid ctx zp2)
    (hvalid3 : zpvalid ctx zp3)
    (hzp1 : zpfit G x0 (qstepR G x) zp1)
    (hzp2 : zpfit G x0 (qstepR G (G.node x)) zp2)
    (hzp3 : zpfit G x0 (qstepR G (G.node (G.node x))) zp3)
    (hred : redQztLeaf ctx zp1 zp2 zp3 qt = true)
    (hnofit : QuizTree.Hypermap.quizTreeFitList G x qt = false) :
    False := by
  have hhit :=
    redQztLeaf_quizTreeFitList_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (zp1 := zp1) (zp2 := zp2) (zp3 := zp3) (qt := qt) (x := x)
      hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3 hred
  rw [hnofit] at hhit
  contradiction

theorem false_of_redQztLeaf_get3_of_quizTreeFit_eq_false_of_zippedQuestionSound
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    {zp1 zp2 zp3 : ZPart} {qa1 : QArity} {r2 r3 : PRange}
    {qt : QuizTree} {x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid1 : zpvalid ctx zp1)
    (hvalid2 : zpvalid ctx zp2)
    (hvalid3 : zpvalid ctx zp3)
    (hzp1 : zpfit G x0 (qstepR G x) zp1)
    (hzp2 : zpfit G x0 (qstepR G (G.node x)) zp2)
    (hzp3 : zpfit G x0 (qstepR G (G.node (G.node x))) zp3)
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt))) = true)
    (hnofit : QuizTree.Hypermap.quizTreeFit G x qt = false)
    (harities : QuizTree.Hypermap.quizTreeFitsArities G x = true)
    (hqa1 : QArity.ofNatCode (G.arity x) = qa1)
    (hqa2 : QArity.ofNatCode (G.arity (G.node x)) = topQa r2)
    (hqa3 : QArity.ofNatCode (G.arity (G.node (G.node x))) = topQa r3) :
    False := by
  have hbranch :=
    get3_eq_qztGetr_qztGetr_of_redQztLeaf
      (ctx := ctx) (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
      (qa1 := qa1) (r2 := r2) (r3 := r3) (qt := qt) hred
  have hlist :=
    QuizTree.Hypermap.quizTreeFitList_get3_eq_false_of_quizTreeFit_eq_false
      (G := G) (x1 := x) (t := qt) hnofit harities
  have hlist' :
      QuizTree.Hypermap.quizTreeFitList G x
        (qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt))) = false := by
    simpa [hqa1, hqa2, hqa3, hbranch] using hlist
  exact
    false_of_redQztLeaf_of_quizTreeFitList_eq_false_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
      (qt := qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt))) (x := x)
      hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3 hred hlist'

def redZPartStep (ctx : Context) (zp : ZPart) : Bool :=
  let zp' := zshiftR ctx Zhub zp
  let pl := zp.left
  let pr := zp.right
  let pl' := zp'.left
  let pr' := zp'.right
  let s := Part.getSpoke pr
  let sqt := qztGetr s (QuizTree.truncate ctx.qt)
  if QuizTree.proper sqt then
    let sl := Part.getSpoke pl
    if redQztLeaf ctx
        (mkZ Zhubr pl' pr')
        (zshiftL ctx Zhubl zp)
        (mkZ Zhat pl pr)
        (qztGetr s (qztGetr sl (QuizTree.get1 ctx.ahub ctx.qt))) then
      redPoprSpoke ctx pr && redPoplSpoke ctx pl pr
    else if redQztLeaf ctx
        (mkZ (zfanLt pr) pl' pr')
        zp
        (mkZ (zfanRt pl) pl pr)
        (qztGetr (Part.getHat pr) (qztGetr sl sqt)) then
      redPoprHat ctx pr && redPoplSpoke ctx pl pr && redPoprSpoke ctx pr
    else
      let zpnil := mkZ Znil pl' pr'
      match pr with
      | Pcons Pr55 h _ =>
          if redQztLeaf ctx
              (mkZ Zhatr pl' pr')
              (mkZ Zhatl pl pr)
              zpnil
              (qztGetr (Part.getHat pr') (qztGetr h sqt)) then
            redPoprHat ctx pr' && redPoprHat ctx pr
          else
            false
      | Pcons6 h f1 _ =>
          if redQztLeaf ctx
              (mkZ Zfan0l pl' pr')
              (mkZ Zhatl pl pr)
              zpnil
              (qztGetr f1 (qztGetr h sqt)) then
            redPoplFan1r ctx pl' pr' && redPoprHat ctx pr
          else if redQztLeaf ctx
              (mkZ Zhatr pl' pr')
              (mkZ Zfan0r pl' pr')
              zpnil
              (qztGetr (Part.getHat pr') (qztGetr f1 sqt)) then
            redPoprHat ctx pr' && redPoplFan1r ctx pl' pr'
          else
            false
      | Pcons7 h f1 f2 _ =>
          if redQztLeaf ctx
              (mkZ Zfan1l pl' pr')
              (mkZ Zhatl pl pr)
              zpnil
              (qztGetr f1 (qztGetr h sqt)) then
            redPoplFan1r ctx pl' pr' && redPoprHat ctx pr
          else if redQztLeaf ctx
              (mkZ Zfan0l pl' pr')
              (mkZ Zfan0r pl' pr')
              zpnil
              (qztGetr f2 (qztGetr f1 sqt)) then
            redPoplFan2r ctx pl' pr' && redPoplFan1r ctx pl' pr'
          else if redQztLeaf ctx
              (mkZ Zhatr pl' pr')
              (mkZ Zfan1r pl' pr')
              zpnil
              (qztGetr (Part.getHat pr') (qztGetr f2 sqt)) then
            redPoprHat ctx pr' && redPoplFan2r ctx pl' pr'
          else
            false
      | Pcons8 h f1 f2 f3 _ =>
          if redQztLeaf ctx
              (mkZ Zfan2l pl' pr')
              (mkZ Zhatl pl pr)
              zpnil
              (qztGetr f1 (qztGetr h sqt)) then
            redPoplFan1r ctx pl' pr' && redPoprHat ctx pr
          else if redQztLeaf ctx
              (mkZ Zfan1l pl' pr')
              (mkZ Zfan0r pl' pr')
              zpnil
              (qztGetr f2 (qztGetr f1 sqt)) then
            redPoplFan2r ctx pl' pr' && redPoplFan1r ctx pl' pr'
          else if redQztLeaf ctx
              (mkZ Zfan0l pl' pr')
              (mkZ Zfan1r pl' pr')
              zpnil
              (qztGetr f3 (qztGetr f2 sqt)) then
            redPoplFan3r ctx pl' pr' && redPoplFan2r ctx pl' pr'
          else if redQztLeaf ctx
              (mkZ Zhatr pl' pr')
              (mkZ Zfan2r pl' pr')
              zpnil
              (qztGetr (Part.getHat pr') (qztGetr f3 sqt)) then
            redPoprHat ctx pr' && redPoplFan3r ctx pl' pr'
          else
            false
      | _ => false
  else
    false

def redZPartRec (ctx : Context) : ZPart → Nat → Bool
  | _, 0 => false
  | zp, d + 1 =>
      if redZPartStep ctx zp then
        true
      else
        redZPartRec ctx (zshiftR ctx Zhub zp) d

theorem redZPartRec_exists_step
    (ctx : Context) :
    ∀ {zp : ZPart} {d : Nat},
      redZPartRec ctx zp d = true →
        ∃ i : Nat,
          i < d ∧
            redZPartStep ctx
              (((fun z : ZPart => zshiftR ctx Zhub z)^[i]) zp) = true
  | zp, 0, hred => by
      simp [redZPartRec] at hred
  | zp, d + 1, hred => by
      by_cases hstep : redZPartStep ctx zp = true
      · exact ⟨0, Nat.succ_pos d, by simpa using hstep⟩
      · have hrec : redZPartRec ctx (zshiftR ctx Zhub zp) d = true := by
          simpa [redZPartRec, hstep] using hred
        rcases redZPartRec_exists_step ctx hrec with ⟨i, hi, hstepi⟩
        refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
        change redZPartStep ctx
          (((fun z : ZPart => zshiftR ctx Zhub z)^[i])
            (zshiftR ctx Zhub zp)) = true
        exact hstepi

def redZPart (ctx : Context) : Bool :=
  redZPartRec ctx
    (mkZ Zhub (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    ctx.nhub

theorem redZPart_exists_step
    {ctx : Context}
    (hred : redZPart ctx = true) :
    ∃ i : Nat,
      i < ctx.nhub ∧
        redZPartStep ctx
          (((fun z : ZPart => zshiftR ctx Zhub z)^[i])
            (mkZ Zhub (Part.drop 1 ctx.p0l)
              (shiftPart ctx.p0l ctx.p0r))) = true := by
  exact redZPartRec_exists_step ctx hred

def redpartLoop (qt : QuizTree) (ahub : QArity) : Nat → Part → Bool
  | 0, _ => false
  | d + 1, p' =>
      let ctx : Context :=
        { qt := qt
          ahub := ahub
          redRec := fun q => redpartLoop qt ahub d q
          p0l := Part.reverse p'
          p0r := p' }
      redZPart ctx

theorem redpartLoop_succ_exists_step
    {qt : QuizTree} {ahub : QArity} {d : Nat} {p : Part}
    (hred : redpartLoop qt ahub (d + 1) p = true) :
    let ctx : Context :=
      { qt := qt
        ahub := ahub
        redRec := fun q => redpartLoop qt ahub d q
        p0l := Part.reverse p
        p0r := p }
    ∃ i : Nat,
      i < ctx.nhub ∧
        redZPartStep ctx
          (((fun z : ZPart => zshiftR ctx Zhub z)^[i])
            (mkZ Zhub (Part.drop 1 ctx.p0l)
              (shiftPart ctx.p0l ctx.p0r))) = true := by
  simpa [redpartLoop] using redZPart_exists_step (ctx :=
    { qt := qt
      ahub := ahub
      redRec := fun q => redpartLoop qt ahub d q
      p0l := Part.reverse p
      p0r := p }) hred

/-- Bounded executable redpart search for a quiz tree and a part. -/
def redpart (qt : QuizTree) (p : Part) : Bool :=
  let nhub := p.size
  let ahub := QArity.ofNatCode nhub
  (nhub == ahub.toNat) && redpartLoop qt ahub (nhub * 12) p

theorem redpart_true_size_and_loop
    {qt : QuizTree} {p : Part}
    (hred : redpart qt p = true) :
    (p.size == (QArity.ofNatCode p.size).toNat) = true ∧
      redpartLoop qt (QArity.ofNatCode p.size) (p.size * 12) p = true := by
  simpa [redpart] using hred

theorem redpart_true_size_bounds
    {qt : QuizTree} {p : Part}
    (hred : redpart qt p = true) :
    5 ≤ p.size ∧ p.size ≤ 11 :=
  QArity.bounds_of_sizeCheck (redpart_true_size_and_loop hred).1

theorem redpart_true_exists_step
    {qt : QuizTree} {p : Part}
    (hred : redpart qt p = true) :
    ∃ d : Nat,
      p.size * 12 = d + 1 ∧
        let ahub := QArity.ofNatCode p.size
        let ctx : Context :=
          { qt := qt
            ahub := ahub
            redRec := fun q => redpartLoop qt ahub d q
            p0l := Part.reverse p
            p0r := p }
        ∃ i : Nat,
          i < ctx.nhub ∧
            redZPartStep ctx
              (((fun z : ZPart => zshiftR ctx Zhub z)^[i])
                (mkZ Zhub (Part.drop 1 ctx.p0l)
                  (shiftPart ctx.p0l ctx.p0r))) = true := by
  rcases redpart_true_size_and_loop hred with ⟨_, hloop⟩
  cases hd : p.size * 12 with
  | zero =>
      simp [hd, redpartLoop] at hloop
  | succ d =>
      refine ⟨d, rfl, ?_⟩
      exact redpartLoop_succ_exists_step (by simpa [hd] using hloop)

end RedPart

end FourColor

end Schematic.Math.GraphTheory
