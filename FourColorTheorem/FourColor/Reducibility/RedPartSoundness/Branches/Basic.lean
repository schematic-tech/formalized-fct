import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Questions

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal

theorem false_of_redZPartStep_spoke_spoke_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr))
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (zdart G x0 (mkZ Zhub pl pr)) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhubr
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
        (zshiftL ctx Zhubl (mkZ Zhub pl pr))
        (mkZ Zhat pl pr)
        (qztGetr (Part.getSpoke pr)
          (qztGetr (Part.getSpoke pl)
            (QuizTree.get1 ctx.ahub ctx.qt))) = true)
    (hpopr : redPoprSpoke ctx pr = true)
    (hpopl : redPoplSpoke ctx pl pr = true) :
    False := by
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zdart G x0 zp
  have hproperR : (zstepR ctx zp).proper = true := by
    simpa [zp, zstepR, locProper] using zshiftR_proper ctx Zhubr zp
  have hproperL : (zstepL ctx zp).proper = true := by
    simpa [zp, zstepL, locProper] using zshiftL_proper ctx Zhubl zp
  have hvalid1 :
      zpvalid ctx (mkZ Zhubr zpR.left zpR.right) := by
    have h := hvalidStep.stepR (zp := zp) (by simpa [zp] using hvalid)
    simpa [zp, zpR, mkZ_zshiftR_left_right_eq] using h
  have hvalid2 :
      zpvalid ctx (zshiftL ctx Zhubl zp) :=
    hvalidStep.stepL (zp := zp) (by simpa [zp] using hvalid)
  have hvalid3 : zpvalid ctx (mkZ Zhat pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have hzp1 :
      zpfit G x0 (qstepR G x) (mkZ Zhubr zpR.left zpR.right) := by
    have h := hstep.stepR (zp := zp) (by simpa [zp] using hvalid)
    simpa [x, zp, zpR, mkZ_zshiftR_left_right_eq] using h
  have hzp2 :
      zpfit G x0 (qstepR G (G.node x)) (zshiftL ctx Zhubl zp) := by
    have h := hstep.stepL (zp := zp) (by simpa [zp] using hvalid)
    have hmove : qstepL G x = qstepR G (G.node x) := rfl
    rw [hmove] at h
    simpa [x, zp] using h
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node x))) (mkZ Zhat pl pr) := by
    intro _hproper
    simp [x, zp, mkZ, zdart, zporg, zmove, qstepR]
  have hqPr :=
    qztGetr_fit_of_redQztLeaf (by simpa [zp, zpR] using hleaf)
  have hqPl :=
    qztGetr_fit (r := Part.getSpoke pl)
      (qt := QuizTree.get1 ctx.ahub ctx.qt) hqPr.2.2
  have harity1 : G.arity x = ctx.ahub.toNat := by
    have hzorg : G.arity (zorg G x0 pl) = ctx.ahub.toNat := by
      rw [zorg, Hypermap.arity_face_iter]
      simpa [Context.nhub] using hx0
    simpa [x, zp, mkZ, zdart, zporg, zmove] using hzorg
  have harity2 :
      G.arity (G.node x) = (topQa (Part.getSpoke pl)).toNat := by
    have hroot2 :=
      hroot (zp := mkZ Zhubl pl pr) (qa := topQa (Part.getSpoke pl))
        (by simpa [zpvalid, mkZ] using hvalid) hqPl.1
        (by simpa [mkZ, redPop] using hpopl)
    simpa [x, zp, mkZ, zdart, zporg, zmove] using hroot2
  have harity3 :
      G.arity (G.node (G.node x)) = (topQa (Part.getSpoke pr)).toNat := by
    have hroot3 :=
      hroot (zp := mkZ Zhubr pl pr) (qa := topQa (Part.getSpoke pr))
        (by simpa [zpvalid, mkZ] using hvalid) hqPr.1
        (by simpa [mkZ, redPop] using hpopr)
    simpa [x, zp, mkZ, zdart, zporg, zmove] using hroot3
  exact false_of_redQztLeaf_get3_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zhubr zpR.left zpR.right)
    (zp2 := zshiftL ctx Zhubl zp)
    (zp3 := mkZ Zhat pl pr)
    (qa1 := ctx.ahub) (r2 := Part.getSpoke pl)
    (r3 := Part.getSpoke pr) (qt := ctx.qt) (x := x)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR] using hleaf) (by simpa [x, zp] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_spoke_spoke_branch_of_noQuizTreeFit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hx0 : G.arity x0 = ctx.nhub)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr))
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhubr
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
        (zshiftL ctx Zhubl (mkZ Zhub pl pr))
        (mkZ Zhat pl pr)
        (qztGetr (Part.getSpoke pr)
          (qztGetr (Part.getSpoke pl)
            (QuizTree.get1 ctx.ahub ctx.qt))) = true)
    (hpopr : redPoprSpoke ctx pr = true)
    (hpopl : redPoplSpoke ctx pl pr = true) :
    False := by
  exact false_of_redZPartStep_spoke_spoke_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
    hvalidStep hroot hstep hsound hx0 hvalid
    (hnofit (zdart G x0 (mkZ Zhub pl pr)))
    hleaf hpopr hpopl

theorem false_of_redZPartStep_hat_spoke_spoke_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr))
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (zdart G x0 (mkZ Zhatr pl pr)) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ (zfanLt pr)
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
        (mkZ Zhub pl pr)
        (mkZ (zfanRt pl) pl pr)
        (qztGetr (Part.getHat pr)
          (qztGetr (Part.getSpoke pl)
            (qztGetr (Part.getSpoke pr) (QuizTree.truncate ctx.qt)))) = true)
    (hpoph : redPoprHat ctx pr = true)
    (hpopl : redPoplSpoke ctx pl pr = true)
    (hpopr : redPoprSpoke ctx pr = true) :
    False := by
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zdart G x0 (mkZ Zhatr pl pr)
  have hvalidZhatr : zpvalid ctx (mkZ Zhatr pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have hvalidZhatl : zpvalid ctx (mkZ Zhatl pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have hvalidZhat : zpvalid ctx (mkZ Zhat pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have ⟨hqPr, hqPl, hqHat⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := Part.getSpoke pl)
      (r3 := Part.getHat pr)
      (by simpa [zp, zpR] using hleaf)
  have hrootPr :
      G.arity (zdart G x0 (mkZ Zhubr pl pr)) =
        (topQa (Part.getSpoke pr)).toNat :=
    hroot (zp := mkZ Zhubr pl pr) (qa := topQa (Part.getSpoke pr))
      (by simpa [zpvalid, mkZ] using hvalid) hqPr
      (by simpa [mkZ, redPop] using hpopr)
  have hrootPl :
      G.arity (zdart G x0 (mkZ Zhubl pl pr)) =
        (topQa (Part.getSpoke pl)).toNat :=
    hroot (zp := mkZ Zhubl pl pr) (qa := topQa (Part.getSpoke pl))
      (by simpa [zpvalid, mkZ] using hvalid) hqPl
      (by simpa [mkZ, redPop] using hpopl)
  have hrootHat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) =
        (topQa (Part.getHat pr)).toNat :=
    hroot (zp := mkZ Zhat pl pr) (qa := topQa (Part.getHat pr))
      hvalidZhat hqHat
      (by simpa [mkZ, redPop] using hpoph)
  have htopR : zpfitTop G ctx x0 (mkZ Zhatr pl pr) := by
    simpa [zpfitTop, mkZ, zdart, zporg, zrange, zmove,
      Hypermap.arity_face] using hrootPr
  have htopL : zpfitTop G ctx x0 (mkZ Zhatl pl pr) := by
    simpa [zpfitTop, mkZ, zdart, zporg, zrange,
      arity_zmove_zhatl_eq_node] using hrootPl
  have hstepRtEq :
      zstepRt ctx (mkZ Zhatr pl pr) =
        mkZ (zfanLt pr) zpR.left zpR.right := by
    calc
      zstepRt ctx (mkZ Zhatr pl pr)
          = zshiftR ctx (zfanLt pr) (mkZ Zhatr pl pr) := by rfl
      _ = zshiftR ctx (zfanLt pr) zp := by
          simpa [zp] using
            zshiftR_mkZ_loc_eq ctx (zfanLt pr) Zhatr Zhub pl pr
      _ = mkZ (zfanLt pr) zpR.left zpR.right := by
          simpa [zpR] using
            (mkZ_zshiftR_left_right_eq ctx (zfanLt pr) Zhub zp).symm
  have hvalid1 :
      zpvalid ctx (mkZ (zfanLt pr) zpR.left zpR.right) := by
    have h := hvalidStep.stepRt hvalidZhatr
    simpa [hstepRtEq] using h
  have hvalid2 : zpvalid ctx zp := by
    simpa [zp] using hvalid
  have hvalid3 : zpvalid ctx (mkZ (zfanRt pl) pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have hzp1 :
      zpfit G x0 (qstepR G x) (mkZ (zfanLt pr) zpR.left zpR.right) := by
    have h := hstep.stepRt hvalidZhatr htopR
    simpa [x, hstepRtEq] using h
  have hnodeX :
      G.node x = zdart G x0 (mkZ Zhatl pl pr) := by
    simp [x, mkZ, zdart, zporg, zmove]
    exact Hypermap.Plain.node_face_eq_edge
      (G := G) hPlain (G.node (G.node (zorg G x0 pl)))
  have hnodeNodeX :
      G.node (G.node x) = zdart G x0 (mkZ Zhat pl pr) := by
    rw [hnodeX]
    rfl
  have hzp2 :
      zpfit G x0 (qstepR G (G.node x)) zp := by
    intro _hproper
    rw [hnodeX]
    simpa [zp, mkZ, zdart, zporg] using
      (qstepR_zmove_zhatl_eq_zmove_zhub_of_plain_cubic
        (G := G) hPlain hCubic (zorg G x0 pl)).symm
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node x)))
        (mkZ (zfanRt pl) pl pr) := by
    have h := hstep.stepLt hvalidZhatl htopL
    have hmove :
        qstepL G (zdart G x0 (mkZ Zhatl pl pr)) =
          qstepR G (G.node (G.node x)) := by
      rw [hnodeNodeX]
      rfl
    rw [hmove] at h
    simpa [zstepLt, mkZ] using h
  have harity1 :
      G.arity x = (topQa (Part.getSpoke pr)).toNat := by
    simpa [x, zpfitTop] using htopR
  have harity2 :
      G.arity (G.node x) = (topQa (Part.getSpoke pl)).toNat := by
    rw [hnodeX]
    simpa [zpfitTop] using htopL
  have harity3 :
      G.arity (G.node (G.node x)) = (topQa (Part.getHat pr)).toNat := by
    rw [hnodeNodeX]
    exact hrootHat
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ (zfanLt pr) zpR.left zpR.right)
    (zp2 := zp)
    (zp3 := mkZ (zfanRt pl) pl pr)
    (r1 := Part.getSpoke pr) (r2 := Part.getSpoke pl)
    (r3 := Part.getHat pr) (qt := ctx.qt) (x := x)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR] using hleaf) (by simpa [x] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_hat_spoke_spoke_branch_of_noQuizTreeFit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr))
    (hleaf :
      redQztLeaf ctx
        (mkZ (zfanLt pr)
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).left
          (zshiftR ctx Zhub (mkZ Zhub pl pr)).right)
        (mkZ Zhub pl pr)
        (mkZ (zfanRt pl) pl pr)
        (qztGetr (Part.getHat pr)
          (qztGetr (Part.getSpoke pl)
            (qztGetr (Part.getSpoke pr) (QuizTree.truncate ctx.qt)))) = true)
    (hpoph : redPoprHat ctx pr = true)
    (hpopl : redPoplSpoke ctx pl pr = true)
    (hpopr : redPoprSpoke ctx pr = true) :
    False := by
  exact false_of_redZPartStep_hat_spoke_spoke_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (hnofit (zdart G x0 (mkZ Zhatr pl pr)))
    hleaf hpoph hpopl hpopr

theorem false_of_redZPartStep_pr55_hat_hat_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons PRange.Pr55 h tail)))
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (((G.face : G.Dart → G.Dart)^[3])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
        (mkZ Zhatl pl (Pcons PRange.Pr55 h tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons PRange.Pr55 h tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons PRange.Pr55 h tail) = true) :
    False := by
  let pr := Pcons PRange.Pr55 h tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[3]) (G.edge x)
  have hstepREq : zstepR ctx zp = mkZ Zhubr zpR.left zpR.right := by
    simpa [zp, zpR, zstepR] using
      (mkZ_zshiftR_left_right_eq ctx Zhubr Zhub zp).symm
  have hproperRhub : (mkZ Zhubr zpR.left zpR.right).proper = true := by
    simp [mkZ, ZPart.proper]
  have hvalidRhub : zpvalid ctx (mkZ Zhubr zpR.left zpR.right) := by
    have h := hvalidStep.stepR (zp := zp) (by simpa [zp, pr] using hvalid)
    simpa [hstepREq] using h
  have hvalid1 : zpvalid ctx (mkZ Zhatr zpR.left zpR.right) := by
    simpa [zpvalid, mkZ] using hvalidRhub
  have hvalid2 : zpvalid ctx (mkZ Zhatl pl pr) := by
    simpa [zpvalid, mkZ, pr] using hvalid
  have hvalid3 : zpvalid ctx (mkZ Znil zpR.left zpR.right) := by
    simpa [zpvalid, mkZ] using hvalidRhub
  have hvalidHat : zpvalid ctx (mkZ Zhat pl pr) := by
    simpa [zpvalid, mkZ, pr] using hvalid
  have hvalidHatR : zpvalid ctx (mkZ Zhat zpR.left zpR.right) := by
    simpa [zpvalid, mkZ] using hvalidRhub
  have ⟨hqSpoke, hqHat, hqHatR⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := h)
      (r3 := Part.getHat zpR.right)
      (by simpa [zp, zpR, pr] using hleaf)
  have hrootSpoke :
      G.arity (zdart G x0 (mkZ Zhubr pl pr)) =
        (topQa (Part.getSpoke pr)).toNat :=
    hroot (zp := mkZ Zhubr pl pr)
      (qa := topQa (Part.getSpoke pr))
      (by simpa [zpvalid, mkZ, pr] using hvalid)
      hqSpoke
      (by simp [mkZ, redPop, redPoprSpoke, redPcons, pr])
  have hspoke : G.arity (G.edge x) = 5 := by
    have hspokeTop :
        G.arity (G.edge x) = (topQa (Part.getSpoke pr)).toNat := by
      simpa [x] using
        arity_edge_zorg_eq_of_hubr (G := G) hCubic hrootSpoke
    have htop : (topQa (Part.getSpoke pr)).toNat = 5 := by
      change (topQa (Part.getSpoke (Pcons PRange.Pr55 h tail))).toNat = 5
      rfl
    exact hspokeTop.trans htop
  have hrootHat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) =
        (topQa h).toNat :=
    hroot (zp := mkZ Zhat pl pr) (qa := topQa h)
      hvalidHat
      (by simpa [pr, mkZ, zrange, Part.getHat] using hqHat)
      (by simpa [mkZ, redPop, pr] using hpoph)
  have hrootHatR :
      G.arity (zdart G x0 (mkZ Zhat zpR.left zpR.right)) =
        (topQa (Part.getHat zpR.right)).toNat :=
    hroot (zp := mkZ Zhat zpR.left zpR.right)
      (qa := topQa (Part.getHat zpR.right))
      hvalidHatR hqHatR
      (by simpa [mkZ, redPop, zp, zpR] using hpophR)
  have hshiftDart :
      zdart G x0 (mkZ Zhubr zpR.left zpR.right) =
        qstepR G (zdart G x0 zp) := by
    have hfit := hstep.stepR (zp := zp) (by simpa [zp, pr] using hvalid)
    have hproperStep : (zstepR ctx zp).proper = true := by
      simpa [hstepREq] using hproperRhub
    simpa [hstepREq] using hfit hproperStep
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    have hnn :
        G.node (G.node (zorg G x0 zpR.left)) =
          G.node (G.node (G.face x)) := by
      calc
        G.node (G.node (zorg G x0 zpR.left))
            = zdart G x0 (mkZ Zhubr zpR.left zpR.right) := by
              rfl
        _ = qstepR G (zdart G x0 zp) := hshiftDart
        _ = G.node (G.node (G.face x)) := by
              simpa [x, zp, mkZ, zdart, zporg, zmove]
                using Hypermap.qstepR_eq_node_node_face_of_plain
                  (G := G) hPlain x
    exact G.node.injective (G.node.injective hnn)
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zhatr zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zhatr zpR.left zpR.right)
          = zmove G Zhatr (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face3_edge_eq_zhatr_face_of_spoke5
                (G := G) hPlain hCubic (x := x) hspoke).symm
  have hzp2 :
      zpfit G x0 (qstepR G (G.node y)) (mkZ Zhatl pl pr) := by
    intro _hproper
    simpa [x, y, pr, mkZ, zdart, zporg] using
      (qstepR_node_face3_edge_eq_zhatl
        (G := G) hPlain hCubic x).symm
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node y)))
        (mkZ Znil zpR.left zpR.right) :=
    zpfit_mkZ_nil
  have harity1 :
      G.arity y = (topQa (Part.getSpoke pr)).toNat := by
    simpa [x, y] using
      arity_face_iter_edge_zorg_eq_of_hubr
        (G := G) hCubic 3 hrootSpoke
  have harity2 :
      G.arity (G.node y) = (topQa h).toNat := by
    have hgeom := arity_node_face3_edge_eq_zhat
      (G := G) hPlain hCubic x
    have hrootHat' :
        G.arity (zmove G ZPartLoc.Zhat x) = (topQa h).toNat := by
      simpa [x, pr, mkZ, zdart, zporg] using hrootHat
    exact hgeom.trans hrootHat'
  have harity3 :
      G.arity (G.node (G.node y)) =
        (topQa (Part.getHat zpR.right)).toNat := by
    have hgeom := arity_node_node_face3_edge_eq_zhat_face_of_spoke5
      (G := G) hPlain hCubic (x := x) hspoke
    have hrootHatR' :
        G.arity (zmove G ZPartLoc.Zhat (G.face x)) =
          (topQa (Part.getHat zpR.right)).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootHatR
    exact hgeom.trans hrootHatR'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zhatr zpR.left zpR.right)
    (zp2 := mkZ Zhatl pl pr)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := h)
    (r3 := Part.getHat zpR.right) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pr55_hat_hat_branch_of_noQuizTreeFit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons PRange.Pr55 h tail)))
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
        (mkZ Zhatl pl (Pcons PRange.Pr55 h tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right)
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons PRange.Pr55 h tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons PRange.Pr55 h tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons PRange.Pr55 h tail) = true) :
    False := by
  exact false_of_redZPartStep_pr55_hat_hat_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (hnofit (((G.face : G.Dart → G.Dart)^[3])
      (G.edge (zorg G x0 pl))))
    hleaf hpophR hpoph


end Schematic.Math.GraphTheory.FourColor.RedPart
