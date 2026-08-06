import FourColorTheorem.FourColor.Reducibility.RedPart.RangeOperations

/-! Semantic soundness of zipped question transitions. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open Part
open PRange
open Question
open QArity

namespace RedPart

open ZPartLoc
def ZippedQuestionSound
    (G : Hypermap) (ctx : Context) (x0 : G.Dart) : Prop :=
  ∀ ⦃zp : ZPart⦄ ⦃q : Question⦄,
    zpvalid ctx zp →
      fitQZP ctx zp q = true →
        redPopQZP ctx zp q = true →
          G.fitQ (zdart G x0 zp) q = true

def ZippedRootSound
    (G : Hypermap) (ctx : Context) (x0 : G.Dart) : Prop :=
  ∀ ⦃zp : ZPart⦄ ⦃qa : QArity⦄,
    zpvalid ctx zp →
      fitQa (zrange ctx zp) qa = true →
        redPop ctx zp = true →
          G.arity (zdart G x0 zp) = qa.toNat

def ZippedLeftDoubleRootSound
    (G : Hypermap) (ctx : Context) (x0 : G.Dart) : Prop :=
  ∀ ⦃zp : ZPart⦄ ⦃qa : QArity⦄,
    zpvalid ctx zp →
      fitQa (zrange ctx (zstepL ctx zp)) qa = true →
        redPop ctx (zstepL ctx zp) = true →
          G.arity (G.edge (G.node (qstepL G (zdart G x0 zp)))) = qa.toNat

def zpfitTop
    (G : Hypermap) (ctx : Context) (x0 : G.Dart) (zp : ZPart) : Prop :=
  G.arity (zdart G x0 zp) = (topQa (zrange ctx zp)).toNat

structure ZippedStepValid (ctx : Context) : Prop where
  stepL : ∀ ⦃zp : ZPart⦄, zpvalid ctx zp → zpvalid ctx (zstepL ctx zp)
  stepR : ∀ ⦃zp : ZPart⦄, zpvalid ctx zp → zpvalid ctx (zstepR ctx zp)
  stepLt : ∀ ⦃zp : ZPart⦄, zpvalid ctx zp → zpvalid ctx (zstepLt ctx zp)
  stepRt : ∀ ⦃zp : ZPart⦄, zpvalid ctx zp → zpvalid ctx (zstepRt ctx zp)

structure ZippedStepSound
    (G : Hypermap) (ctx : Context) (x0 : G.Dart) : Prop where
  stepL : ∀ ⦃zp : ZPart⦄,
    zpvalid ctx zp →
      zpfit G x0 (qstepL G (zdart G x0 zp)) (zstepL ctx zp)
  stepR : ∀ ⦃zp : ZPart⦄,
    zpvalid ctx zp →
      zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepR ctx zp)
  stepLt : ∀ ⦃zp : ZPart⦄,
    zpvalid ctx zp →
      zpfitTop G ctx x0 zp →
      zpfit G x0 (qstepL G (zdart G x0 zp)) (zstepLt ctx zp)
  stepRt : ∀ ⦃zp : ZPart⦄,
    zpvalid ctx zp →
      zpfitTop G ctx x0 zp →
      zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepRt ctx zp)

theorem zippedStepValid_of_wraps
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrapL : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (hwrapR : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r)) :
    ZippedStepValid ctx where
  stepL := by
    intro zp hvalid
    exact zpvalid_stepL hinit hwrapL hwrapR hvalid
  stepR := by
    intro zp hvalid
    exact zpvalid_stepR hinit hwrapL hwrapR hvalid
  stepLt := by
    intro zp hvalid
    exact zpvalid_stepLt hinit hwrapL hwrapR hvalid
  stepRt := by
    intro zp hvalid
    exact zpvalid_stepRt hinit hwrapL hwrapR hvalid

theorem zippedStepValid_of_reverse
    {ctx : Context}
    (hleft : ctx.p0l = Part.reverse ctx.p0r) :
    ZippedStepValid ctx :=
  zippedStepValid_of_wraps
    (ctx := ctx)
    (zvalid_init ctx hleft)
    (zvalid_wrapL ctx hleft)
    (zvalid_wrapR ctx hleft)

theorem zippedQuestionSound_qask0
    (G : Hypermap) (x0 : G.Dart) (zp : ZPart) :
    G.fitQ (zdart G x0 zp) Qask0 = true := by
  simp

theorem zippedQuestionSound_qask1
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    {zp : ZPart} {qa : QArity}
    (hvalid : zpvalid ctx zp)
    (hfit : fitQZP ctx zp (Qask1 qa) = true)
    (hred : redPopQZP ctx zp (Qask1 qa) = true) :
    G.fitQ (zdart G x0 zp) (Qask1 qa) = true :=
  Hypermap.fitQ_qask1_of_arity (G := G)
    (hroot hvalid hfit hred)

theorem fitQ_of_zpfit_of_zippedQuestionSound
    {G : Hypermap} {ctx : Context} {x0 x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {q : Question}
    (hvalid : zpvalid ctx zp)
    (hzp : zpfit G x0 x zp)
    (hfit : fitQZP ctx zp q = true)
    (hred : redPopQZP ctx zp q = true) :
    G.fitQ x q = true := by
  rcases fitQZP_proper (ctx := ctx) (zp := zp) hfit with hq0 | hproper
  · subst q
    simp
  · have hsem := hsound hvalid hfit hred
    simpa [hzp hproper] using hsem

theorem zippedQuestionSound_qaskL
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {qa : QArity} {q : Question}
    (hvalid : zpvalid ctx zp)
    (hvalidStep : zpvalid ctx (zstepLt ctx zp))
    (hzpStep : zpfit G x0 (qstepL G (zdart G x0 zp)) (zstepLt ctx zp))
    (hfit : fitQZP ctx zp (QaskL qa q) = true)
    (hred : redPopQZP ctx zp (QaskL qa q) = true) :
    G.fitQ (zdart G x0 zp) (QaskL qa q) = true := by
  simp [fitQZP] at hfit
  simp [redPopQZP] at hred
  have hrootArity := hroot hvalid hfit.1 hred.1
  have hrec :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepL G (zdart G x0 zp))
      hsound hvalidStep hzpStep hfit.2 hred.2
  exact Hypermap.fitQ_qaskL_of_arity (G := G) hrootArity hrec

theorem zippedQuestionSound_qaskR
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {qa : QArity} {q : Question}
    (hvalid : zpvalid ctx zp)
    (hvalidStep : zpvalid ctx (zstepRt ctx zp))
    (hzpStep : zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepRt ctx zp))
    (hfit : fitQZP ctx zp (QaskR qa q) = true)
    (hred : redPopQZP ctx zp (QaskR qa q) = true) :
    G.fitQ (zdart G x0 zp) (QaskR qa q) = true := by
  simp [fitQZP] at hfit
  simp [redPopQZP] at hred
  have hrootArity := hroot hvalid hfit.1 hred.1
  have hrec :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepR G (zdart G x0 zp))
      hsound hvalidStep hzpStep hfit.2 hred.2
  exact Hypermap.fitQ_qaskR_of_arity (G := G) hrootArity hrec

theorem zippedQuestionSound_qaskLR
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {qa : QArity} {ql qr : Question}
    (hvalid : zpvalid ctx zp)
    (hvalidL : zpvalid ctx (zstepL ctx zp))
    (hvalidR : zpvalid ctx (zstepR ctx zp))
    (hzpL : zpfit G x0 (qstepL G (zdart G x0 zp)) (zstepL ctx zp))
    (hzpR : zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepR ctx zp))
    (hfit : fitQZP ctx zp (QaskLR qa ql qr) = true)
    (hred : redPopQZP ctx zp (QaskLR qa ql qr) = true) :
    G.fitQ (zdart G x0 zp) (QaskLR qa ql qr) = true := by
  simp [fitQZP] at hfit
  simp [redPopQZP] at hred
  have hrootArity := hroot hvalid hfit.1 hred.1.1
  have hleft :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepL G (zdart G x0 zp))
      hsound hvalidL hzpL hfit.2.1 hred.1.2
  have hright :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepR G (zdart G x0 zp))
      hsound hvalidR hzpR hfit.2.2 hred.2
  exact Hypermap.fitQ_qaskLR_of_arity (G := G) hrootArity hleft hright

theorem zippedQuestionSound_qaskRR
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {qa : QArity} {q : Question}
    (hvalidR : zpvalid ctx (zstepR ctx zp))
    (hvalidRR : zpvalid ctx (zstepR ctx (zstepR ctx zp)))
    (hzpR : zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepR ctx zp))
    (hzpRR :
      zpfit G x0 (qstepR G (qstepR G (zdart G x0 zp)))
        (zstepR ctx (zstepR ctx zp)))
    (hfit : fitQZP ctx zp (QaskRR qa q) = true)
    (hred : redPopQZP ctx zp (QaskRR qa q) = true) :
    G.fitQ (zdart G x0 zp) (QaskRR qa q) = true := by
  let zpr := zstepR ctx zp
  simp [fitQZP, redPopQZP] at hfit hred
  have hproperR : zpr.proper = true :=
    proper_of_fitQa_zrange (ctx := ctx) (zp := zpr) hfit.1
  have hrootAtR : G.arity (qstepR G (zdart G x0 zp)) = qa.toNat := by
    have hrootZ := hroot hvalidR hfit.1 hred.1
    simpa [zpr, hzpR hproperR] using hrootZ
  have hrec :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepR G (qstepR G (zdart G x0 zp)))
      hsound hvalidRR hzpRR hfit.2 hred.2
  exact Hypermap.fitQ_qaskRR_of_arity (G := G) hrootAtR hrec

theorem zippedQuestionSound_qaskLL_of_arity
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    {zp : ZPart} {qa : QArity} {q : Question}
    (hrootAtL :
      G.arity (G.edge (G.node (qstepL G (zdart G x0 zp)))) = qa.toNat)
    (hvalidLL : zpvalid ctx (zstepL ctx (zstepL ctx zp)))
    (hzpLL :
      zpfit G x0 (qstepL G (qstepL G (zdart G x0 zp)))
        (zstepL ctx (zstepL ctx zp)))
    (hfit : fitQZP ctx zp (QaskLL qa q) = true)
    (hred : redPopQZP ctx zp (QaskLL qa q) = true) :
    G.fitQ (zdart G x0 zp) (QaskLL qa q) = true := by
  simp [fitQZP, redPopQZP] at hfit hred
  have hrec :=
    fitQ_of_zpfit_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (x := qstepL G (qstepL G (zdart G x0 zp)))
      hsound hvalidLL hzpLL hfit.2 hred.2
  exact Hypermap.fitQ_qaskLL_of_arity (G := G) hrootAtL hrec

theorem zippedQuestionSound_of_components
    {G : Hypermap} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hleftDouble : ZippedLeftDoubleRootSound G ctx x0)
    (hvalidStep : ZippedStepValid ctx)
    (hstep : ZippedStepSound G ctx x0) :
    ZippedQuestionSound G ctx x0 := by
  intro zp q hvalid hfit hred
  induction q generalizing zp with
  | Qask0 =>
      exact zippedQuestionSound_qask0 G x0 zp
  | Qask1 qa =>
      exact zippedQuestionSound_qask1
        (G := G) (ctx := ctx) (x0 := x0) hroot hvalid hfit hred
  | QaskL qa q ih =>
      simp [fitQZP] at hfit
      simp [redPopQZP] at hred
      have hrootArity := hroot hvalid hfit.1 hred.1
      have htop : zpfitTop G ctx x0 zp := by
        have htopQa := fitQa_topQa_of_fit (r := zrange ctx zp) hfit.1
        simpa [zpfitTop, htopQa] using hrootArity
      have hvalidSub := hvalidStep.stepLt hvalid
      have hfitSubZ := ih hvalidSub hfit.2 hred.2
      have hfitSub :
          G.fitQ (qstepL G (zdart G x0 zp)) q = true := by
        rcases fitQZP_proper (ctx := ctx) (zp := zstepLt ctx zp) hfit.2 with
          hq0 | hproper
        · subst q
          simp
        · simpa [hstep.stepLt hvalid htop hproper] using hfitSubZ
      exact Hypermap.fitQ_qaskL_of_arity (G := G) hrootArity hfitSub
  | QaskR qa q ih =>
      simp [fitQZP] at hfit
      simp [redPopQZP] at hred
      have hrootArity := hroot hvalid hfit.1 hred.1
      have htop : zpfitTop G ctx x0 zp := by
        have htopQa := fitQa_topQa_of_fit (r := zrange ctx zp) hfit.1
        simpa [zpfitTop, htopQa] using hrootArity
      have hvalidSub := hvalidStep.stepRt hvalid
      have hfitSubZ := ih hvalidSub hfit.2 hred.2
      have hfitSub :
          G.fitQ (qstepR G (zdart G x0 zp)) q = true := by
        rcases fitQZP_proper (ctx := ctx) (zp := zstepRt ctx zp) hfit.2 with
          hq0 | hproper
        · subst q
          simp
        · simpa [hstep.stepRt hvalid htop hproper] using hfitSubZ
      exact Hypermap.fitQ_qaskR_of_arity (G := G) hrootArity hfitSub
  | QaskLR qa ql qr ihl ihr =>
      simp [fitQZP] at hfit
      simp [redPopQZP] at hred
      have hrootArity := hroot hvalid hfit.1 hred.1.1
      have hvalidL := hvalidStep.stepL hvalid
      have hvalidR := hvalidStep.stepR hvalid
      have hfitLZ := ihl hvalidL hfit.2.1 hred.1.2
      have hfitRZ := ihr hvalidR hfit.2.2 hred.2
      have hfitL :
          G.fitQ (qstepL G (zdart G x0 zp)) ql = true := by
        rcases fitQZP_proper (ctx := ctx) (zp := zstepL ctx zp) hfit.2.1 with
          hq0 | hproper
        · subst ql
          simp
        · simpa [hstep.stepL hvalid hproper] using hfitLZ
      have hfitR :
          G.fitQ (qstepR G (zdart G x0 zp)) qr = true := by
        rcases fitQZP_proper (ctx := ctx) (zp := zstepR ctx zp) hfit.2.2 with
          hq0 | hproper
        · subst qr
          simp
        · simpa [hstep.stepR hvalid hproper] using hfitRZ
      exact Hypermap.fitQ_qaskLR_of_arity (G := G) hrootArity hfitL hfitR
  | QaskLL qa q ih =>
      simp [fitQZP, redPopQZP] at hfit hred
      have hrootArity := hleftDouble hvalid hfit.1 hred.1
      have hproperL : (zstepL ctx zp).proper = true :=
        proper_of_fitQa_zrange (ctx := ctx) (zp := zstepL ctx zp) hfit.1
      have hfirstL := hstep.stepL hvalid hproperL
      have hvalidL := hvalidStep.stepL hvalid
      have hvalidLL := hvalidStep.stepL hvalidL
      have hfitSubZ := ih hvalidLL hfit.2 hred.2
      have hfitSub :
          G.fitQ (qstepL G (qstepL G (zdart G x0 zp))) q = true := by
        rcases fitQZP_proper
            (ctx := ctx) (zp := zstepL ctx (zstepL ctx zp)) hfit.2 with
          hq0 | hproper
        · subst q
          simp
        · have hsecondL := hstep.stepL hvalidL hproper
          simpa [hfirstL, hsecondL] using hfitSubZ
      exact Hypermap.fitQ_qaskLL_of_arity (G := G) hrootArity hfitSub
  | QaskRR qa q ih =>
      simp [fitQZP, redPopQZP] at hfit hred
      let zpr := zstepR ctx zp
      have hvalidR := hvalidStep.stepR hvalid
      have hvalidRR := hvalidStep.stepR hvalidR
      have hproperR : zpr.proper = true :=
        proper_of_fitQa_zrange (ctx := ctx) (zp := zpr) hfit.1
      have hfirstR := hstep.stepR hvalid hproperR
      have hrootAtR : G.arity (qstepR G (zdart G x0 zp)) = qa.toNat := by
        have hrootZ := hroot hvalidR hfit.1 hred.1
        simpa [zpr, hfirstR] using hrootZ
      have hfitSubZ := ih hvalidRR hfit.2 hred.2
      have hfitSub :
          G.fitQ (qstepR G (qstepR G (zdart G x0 zp))) q = true := by
        rcases fitQZP_proper
            (ctx := ctx) (zp := zstepR ctx (zstepR ctx zp)) hfit.2 with
          hq0 | hproper
        · subst q
          simp
        · have hsecondR := hstep.stepR hvalidR hproper
          simpa [zpr, hfirstR, hsecondR] using hfitSubZ
      exact Hypermap.fitQ_qaskRR_of_arity (G := G) hrootAtR hfitSub


end RedPart

end FourColor

end Schematic.Math.GraphTheory
