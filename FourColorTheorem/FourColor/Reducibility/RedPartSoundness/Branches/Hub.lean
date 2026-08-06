import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Branches.Basic
import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Branches.FanOne
import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Branches.FanTwo
import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Branches.FanThree

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem false_of_redZPartStep_zhub_of_right_size
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hx0 : G.arity x0 = ctx.nhub)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr))
    (hrightSize : 1 < Part.size pr)
    (hred : redZPartStep ctx (mkZ Zhub pl pr) = true) :
    False := by
  let zp := mkZ Zhub pl pr
  by_cases hsqt :
      QuizTree.proper
        (qztGetr (Part.getSpoke pr) (QuizTree.truncate ctx.qt)) = true
  · by_cases hleafHub :
        redQztLeaf ctx
          (mkZ Zhubr
            (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
            (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
          (zshiftL ctx Zhubl (mkZ Zhub pl pr))
          (mkZ Zhat pl pr)
          (qztGetr (Part.getSpoke pr)
            (qztGetr (Part.getSpoke pl)
              (QuizTree.get1 ctx.ahub ctx.qt))) = true
    · have hpops :
          redPoprSpoke ctx pr = true ∧
            redPoplSpoke ctx pl pr = true := by
        simp_all [redZPartStep, Bool.and_eq_true, mkZ]
      exact false_of_redZPartStep_spoke_spoke_branch_of_noQuizTreeFit
        (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
        hvalidStep hroot hstep hsound hx0 hnofit hvalid
        hleafHub hpops.1 hpops.2
    · by_cases hleafHat :
        redQztLeaf ctx
          (mkZ (zfanLt pr)
            (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
            (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
          (mkZ Zhub pl pr)
          (mkZ (zfanRt pl) pl pr)
          (qztGetr (Part.getHat pr)
            (qztGetr (Part.getSpoke pl)
              (qztGetr (Part.getSpoke pr)
                (QuizTree.truncate ctx.qt)))) = true
      · have hpops :
          redPoprHat ctx pr = true ∧
              redPoplSpoke ctx pl pr = true ∧
                redPoprSpoke ctx pr = true := by
          simp_all [redZPartStep, Bool.and_eq_true, mkZ]
        exact false_of_redZPartStep_hat_spoke_spoke_branch_of_noQuizTreeFit
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          hPlain hCubic hvalidStep hroot hstep hsound hnofit hvalid
          hleafHat hpops.1 hpops.2.1 hpops.2.2
      · cases pr with
        | Pnil =>
            simp [Part.size] at hrightSize
        | Pcons s h tail =>
            cases s with
            | Pr55 =>
                by_cases hleafPr :
                    redQztLeaf ctx
                      (mkZ Zhatr
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
                      (mkZ Zhatl pl (Pcons PRange.Pr55 h tail))
                      (mkZ Znil
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
                      (qztGetr
                        (Part.getHat
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl
                              (Pcons PRange.Pr55 h tail))).right)
                        (qztGetr h
                          (qztGetr
                            (Part.getSpoke (Pcons PRange.Pr55 h tail))
                            (QuizTree.truncate ctx.qt)))) = true
                · have hpops :
                      redPoprHat ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl
                              (Pcons PRange.Pr55 h tail))).right = true ∧
                        redPoprHat ctx (Pcons PRange.Pr55 h tail) = true := by
                    simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                  exact false_of_redZPartStep_pr55_hat_hat_branch_of_noQuizTreeFit
                    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                    (tail := tail) (h := h)
                    hPlain hCubic hvalidStep hroot hstep hsound hnofit
                    hvalid hleafPr hpops.1 hpops.2
                · simp_all [redZPartStep, mkZ]
            | Pr66 =>
                simp_all [redZPartStep, mkZ]
            | Pr77 =>
                simp_all [redZPartStep, mkZ]
            | Pr88 =>
                simp_all [redZPartStep, mkZ]
            | Pr99 =>
                simp_all [redZPartStep, mkZ]
            | Pr56 =>
                simp_all [redZPartStep, mkZ]
            | Pr67 =>
                simp_all [redZPartStep, mkZ]
            | Pr78 =>
                simp_all [redZPartStep, mkZ]
            | Pr89 =>
                simp_all [redZPartStep, mkZ]
            | Pr57 =>
                simp_all [redZPartStep, mkZ]
            | Pr68 =>
                simp_all [redZPartStep, mkZ]
            | Pr79 =>
                simp_all [redZPartStep, mkZ]
            | Pr58 =>
                simp_all [redZPartStep, mkZ]
            | Pr69 =>
                simp_all [redZPartStep, mkZ]
            | Pr59 =>
                simp_all [redZPartStep, mkZ]
        | Pcons6 h f1 tail =>
            have htail : tail ≠ Pnil := by
              intro htail
              subst tail
              simp [Part.size] at hrightSize
            by_cases hleafA :
                redQztLeaf ctx
                  (mkZ Zfan0l
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                  (mkZ Zhatl pl (Pcons6 h f1 tail))
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                  (qztGetr f1
                    (qztGetr h
                      (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
                        (QuizTree.truncate ctx.qt)))) = true
            · have hpops :
                  redPoplFan1r ctx
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons6 h f1 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons6 h f1 tail))).right = true ∧
                    redPoprHat ctx (Pcons6 h f1 tail) = true := by
                simp_all [redZPartStep, Bool.and_eq_true, mkZ]
              exact false_of_redZPartStep_pcons6_fan1_hat_branch_of_tail_ne_nil
                (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                (tail := tail) (h := h) (f1 := f1)
                hPlain hCubic hvalidStep hroot hstep hsound hnofit
                hvalid htail hleafA hpops.1 hpops.2
            · by_cases hleafB :
                redQztLeaf ctx
                  (mkZ Zhatr
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                  (mkZ Zfan0r
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                  (qztGetr
                    (Part.getHat
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons6 h f1 tail))).right)
                    (qztGetr f1
                      (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
                        (QuizTree.truncate ctx.qt)))) = true
              · have hpops :
                    redPoprHat ctx
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons6 h f1 tail))).right = true ∧
                      redPoplFan1r ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons6 h f1 tail))).left
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons6 h f1 tail))).right =
                        true := by
                  simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                exact false_of_redZPartStep_pcons6_hat_fan1_branch_of_tail_ne_nil
                  (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                  (tail := tail) (h := h) (f1 := f1)
                  hPlain hCubic hvalidStep hroot hstep hsound hnofit
                  hvalid htail hleafB hpops.1 hpops.2
              · simp_all [redZPartStep, mkZ]
        | Pcons7 h f1 f2 tail =>
            have htail : tail ≠ Pnil := by
              intro htail
              subst tail
              simp [Part.size] at hrightSize
            by_cases hleafA :
                redQztLeaf ctx
                  (mkZ Zfan1l
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                  (mkZ Zhatl pl (Pcons7 h f1 f2 tail))
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                  (qztGetr f1
                    (qztGetr h
                      (qztGetr (Part.getSpoke (Pcons7 h f1 f2 tail))
                        (QuizTree.truncate ctx.qt)))) = true
            · have hpops :
                  redPoplFan1r ctx
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right = true ∧
                    redPoprHat ctx (Pcons7 h f1 f2 tail) = true := by
                simp_all [redZPartStep, Bool.and_eq_true, mkZ]
              exact false_of_redZPartStep_pcons7_fan1_hat_branch_of_tail_ne_nil
                (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                hPlain hCubic hvalidStep hroot hstep hsound hnofit
                hvalid htail hleafA hpops.1 hpops.2
            · by_cases hleafB :
                redQztLeaf ctx
                  (mkZ Zfan0l
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                  (mkZ Zfan0r
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                  (qztGetr f2
                    (qztGetr f1
                      (qztGetr (Part.getSpoke (Pcons7 h f1 f2 tail))
                        (QuizTree.truncate ctx.qt)))) = true
              · have hpops :
                    redPoplFan2r ctx
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right = true ∧
                      redPoplFan1r ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right =
                        true := by
                  simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                exact
                  false_of_redZPartStep_pcons7_fan2_fan1_branch_of_tail_ne_nil
                    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                    (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                    hPlain hCubic hvalidStep hroot hstep hsound hnofit
                    hvalid htail hleafB hpops.1 hpops.2
              · by_cases hleafC :
                  redQztLeaf ctx
                    (mkZ Zhatr
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                    (mkZ Zfan1r
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                    (mkZ Znil
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                    (qztGetr
                      (Part.getHat
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
                      (qztGetr f2
                        (qztGetr
                          (Part.getSpoke (Pcons7 h f1 f2 tail))
                          (QuizTree.truncate ctx.qt)))) = true
                · have hpops :
                      redPoprHat ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right =
                          true ∧
                        redPoplFan2r ctx
                            (zshiftR ctx Zhub
                              (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
                            (zshiftR ctx Zhub
                              (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right =
                          true := by
                    simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                  exact false_of_redZPartStep_pcons7_hat_fan2_branch_of_tail_ne_nil
                    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                    (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                    hPlain hCubic hvalidStep hroot hstep hsound hnofit
                    hvalid htail hleafC hpops.1 hpops.2
                · simp_all [redZPartStep, mkZ]
        | Pcons8 h f1 f2 f3 tail =>
            have htail : tail ≠ Pnil := by
              intro htail
              subst tail
              simp [Part.size] at hrightSize
            by_cases hleafA :
                redQztLeaf ctx
                  (mkZ Zfan2l
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                  (mkZ Zhatl pl (Pcons8 h f1 f2 f3 tail))
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                  (qztGetr f1
                    (qztGetr h
                      (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
                        (QuizTree.truncate ctx.qt)))) = true
            · have hpops :
                  redPoplFan1r ctx
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right =
                      true ∧
                    redPoprHat ctx (Pcons8 h f1 f2 f3 tail) = true := by
                simp_all [redZPartStep, Bool.and_eq_true, mkZ]
              exact false_of_redZPartStep_pcons8_fan1_hat_branch_of_tail_ne_nil
                (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                (tail := tail) (h := h) (f1 := f1) (f2 := f2) (f3 := f3)
                hPlain hCubic hvalidStep hroot hstep hsound hnofit
                hvalid htail hleafA hpops.1 hpops.2
            · by_cases hleafB :
                redQztLeaf ctx
                  (mkZ Zfan1l
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                  (mkZ Zfan0r
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                  (mkZ Znil
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                    (zshiftR ctx Zhub
                      (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                  (qztGetr f2
                    (qztGetr f1
                      (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
                        (QuizTree.truncate ctx.qt)))) = true
              · have hpops :
                    redPoplFan2r ctx
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right =
                        true ∧
                      redPoplFan1r ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right =
                        true := by
                  simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                exact
                  false_of_redZPartStep_pcons8_fan2_fan1_branch_of_tail_ne_nil
                    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                    (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                    (f3 := f3)
                    hPlain hCubic hvalidStep hroot hstep hsound hnofit
                    hvalid htail hleafB hpops.1 hpops.2
              · by_cases hleafC :
                  redQztLeaf ctx
                    (mkZ Zfan0l
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                    (mkZ Zfan1r
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                    (mkZ Znil
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
                      (zshiftR ctx Zhub
                        (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
                    (qztGetr f3
                      (qztGetr f2
                        (qztGetr
                          (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
                          (QuizTree.truncate ctx.qt)))) = true
                · have hpops :
                      redPoplFan3r ctx
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl
                              (Pcons8 h f1 f2 f3 tail))).left
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl
                              (Pcons8 h f1 f2 f3 tail))).right = true ∧
                        redPoplFan2r ctx
                            (zshiftR ctx Zhub
                              (mkZ Zhub pl
                                (Pcons8 h f1 f2 f3 tail))).left
                            (zshiftR ctx Zhub
                              (mkZ Zhub pl
                                (Pcons8 h f1 f2 f3 tail))).right = true := by
                    simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                  exact
                    false_of_redZPartStep_pcons8_fan3_fan2_branch_of_tail_ne_nil
                      (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                      (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                      (f3 := f3)
                      hPlain hCubic hvalidStep hroot hstep hsound hnofit
                      hvalid htail hleafC hpops.1 hpops.2
                · by_cases hleafD :
                    redQztLeaf ctx
                      (mkZ Zhatr
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).right)
                      (mkZ Zfan2r
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).right)
                      (mkZ Znil
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).left
                        (zshiftR ctx Zhub
                          (mkZ Zhub pl
                            (Pcons8 h f1 f2 f3 tail))).right)
                      (qztGetr
                        (Part.getHat
                          (zshiftR ctx Zhub
                            (mkZ Zhub pl
                              (Pcons8 h f1 f2 f3 tail))).right)
                        (qztGetr f3
                          (qztGetr
                            (Part.getSpoke
                              (Pcons8 h f1 f2 f3 tail))
                            (QuizTree.truncate ctx.qt)))) = true
                  · have hpops :
                        redPoprHat ctx
                            (zshiftR ctx Zhub
                              (mkZ Zhub pl
                                (Pcons8 h f1 f2 f3 tail))).right =
                            true ∧
                          redPoplFan3r ctx
                              (zshiftR ctx Zhub
                                (mkZ Zhub pl
                                  (Pcons8 h f1 f2 f3 tail))).left
                              (zshiftR ctx Zhub
                                (mkZ Zhub pl
                                  (Pcons8 h f1 f2 f3 tail))).right =
                            true := by
                      simp_all [redZPartStep, Bool.and_eq_true, mkZ]
                    exact
                      false_of_redZPartStep_pcons8_hat_fan3_branch_of_tail_ne_nil
                        (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
                        (tail := tail) (h := h) (f1 := f1) (f2 := f2)
                        (f3 := f3)
                        hPlain hCubic hvalidStep hroot hstep hsound hnofit
                        hvalid htail hleafD hpops.1 hpops.2
                  · simp_all [redZPartStep, mkZ]
  · simp_all [redZPartStep, mkZ]

theorem false_of_redZPartRec_zhub_of_right_size
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hx0 : G.arity x0 = ctx.nhub)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hshiftValid : ∀ ⦃zp : ZPart⦄,
      zpvalid ctx zp → zpvalid ctx (zshiftR ctx Zhub zp)) :
    ∀ {pl pr : Part} {d : Nat},
      zpvalid ctx (mkZ Zhub pl pr) →
        d < Part.size pr →
          redZPartRec ctx (mkZ Zhub pl pr) d = true →
            False
  | _pl, _pr, 0, _hvalid, _hrightSize, hred => by
      simp [redZPartRec] at hred
  | pl, pr, d + 1, hvalid, hrightSize, hred => by
      by_cases hstepRed : redZPartStep ctx (mkZ Zhub pl pr) = true
      · have hstepSize : 1 < Part.size pr := by omega
        exact false_of_redZPartStep_zhub_of_right_size
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          hPlain hCubic hvalidStep hroot hstep hsound hx0 hnofit
          hvalid hstepSize hstepRed
      · have hrecShift :
            redZPartRec ctx (zshiftR ctx Zhub (mkZ Zhub pl pr)) d =
              true := by
          simpa [redZPartRec, hstepRed] using hred
        have hstepSize : 1 < Part.size pr := by omega
        have hshiftEq :=
          zshiftR_zhub_eq_shiftPart_drop_of_size_gt_one
            (ctx := ctx) (pl := pl) (pr := pr) hstepSize
        have hrec :
            redZPartRec ctx
              (mkZ Zhub (shiftPart pr pl) (Part.drop 1 pr)) d = true := by
          simpa [hshiftEq] using hrecShift
        have hvalidShift :
            zpvalid ctx
              (mkZ Zhub (shiftPart pr pl) (Part.drop 1 pr)) := by
          have hv := hshiftValid (zp := mkZ Zhub pl pr) hvalid
          simpa [hshiftEq] using hv
        have hrightSizeDrop : d < Part.size (Part.drop 1 pr) := by
          rw [Part.size_drop]
          omega
        exact false_of_redZPartRec_zhub_of_right_size
          (G := G) (ctx := ctx) (x0 := x0)
          hPlain hCubic hvalidStep hroot hstep hsound hx0 hnofit
          hshiftValid hvalidShift hrightSizeDrop hrec

theorem false_of_redZPart_of_reverse_exact_and_noFit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hx0 : G.arity x0 = ctx.nhub)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hred : redZPart ctx = true) :
    False := by
  let hvalidStep : ZippedStepValid ctx :=
    zippedStepValid_of_reverse (ctx := ctx) hleft
  let hroot : ZippedRootSound G ctx x0 :=
    zippedRootSound_of_noRedRec
      (G := G) (ctx := ctx) (x0 := x0)
      hPlain hCubic hNoRedRec hx0 hfit0
  let hstep : ZippedStepSound G ctx x0 :=
    zippedStepSound_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0)
      hPlain hCubic hleft hfit0
  let hsound : ZippedQuestionSound G ctx x0 :=
    zippedQuestionSound_of_components
      (G := G) (ctx := ctx) (x0 := x0)
      hroot
      (zippedLeftDoubleRootSound_of_components
        (G := G) (ctx := ctx) (x0 := x0)
        hroot hvalidStep hstep)
      hvalidStep hstep
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hp0rSize : Part.size ctx.p0r = G.arity x0 := hparts.1.symm
  have hp0lSize : Part.size ctx.p0l = G.arity x0 := by
    rw [hleft, Part.size_reverse, hp0rSize]
  have htake :
      Part.size (Part.take 1 ctx.p0l) = 1 := by
    exact Part.size_take_of_le (p := ctx.p0l)
      (by
        rw [hp0lSize]
        exact Hypermap.arity_pos (G := G) x0)
  have hrightSize :
      ctx.nhub < Part.size (shiftPart ctx.p0l ctx.p0r) := by
    simp [shiftPart, Part.size_append, htake, hp0rSize, hx0,
      Context.nhub]
  exact false_of_redZPartRec_zhub_of_right_size
    (G := G) (ctx := ctx) (x0 := x0)
    hPlain hCubic hvalidStep hroot hstep hsound hx0 hnofit
    (fun {zp} hvalid =>
      zpvalid_zshiftR
        (zvalid_init ctx hleft)
        (zvalid_wrapR ctx hleft)
        Zhub hvalid)
    (by simpa [zpvalid, mkZ] using zvalid_wrapL ctx hleft)
    hrightSize
    (by simpa [redZPart] using hred)

end Schematic.Math.GraphTheory.FourColor.RedPart
