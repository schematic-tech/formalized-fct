import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Questions

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem false_of_redZPartStep_pcons6_fan1_hat_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons6 h f1 tail)))
    (hshiftLeft :
      (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left =
        Pcons6 h f1 pl)
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (((G.face : G.Dart → G.Dart)^[3])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan0l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Zhatl pl (Pcons6 h f1 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons6 h f1 tail) = true) :
    False := by
  let pr := Pcons6 h f1 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[3]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons6 h f1 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalidOriginal (loc) : zpvalid ctx (mkZ loc pl pr) := by
    simpa [pr] using (zpvalid_mkZ_loc (loc' := loc) hvalid)
  have hvalid1 := hvalidShift Zfan0l
  have hvalid2 := hvalidOriginal Zhatl
  have hvalid3 := hvalidShift Znil
  have hvalidHat := hvalidOriginal Zhat
  have hvalidFanR := hvalidShift Zfan1r
  have ⟨hqSpoke, hqHat, hqFan⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := h) (r3 := f1)
      (by simpa [zp, zpR, pr] using hleaf)
  have hrootSpoke :
      G.arity (zdart G x0 (mkZ Zhubr pl pr)) =
        (topQa (Part.getSpoke pr)).toNat :=
    hroot (zp := mkZ Zhubr pl pr)
      (qa := topQa (Part.getSpoke pr))
      (by simpa [zpvalid, mkZ, pr] using hvalid)
      hqSpoke
      (by simp [mkZ, redPop, redPoprSpoke, pr])
  have hspoke : G.arity (G.edge x) = 6 := by
    have hspokeTop :
        G.arity (G.edge x) = (topQa (Part.getSpoke pr)).toNat := by
      simpa [x] using
        arity_edge_zorg_eq_of_hubr (G := G) hCubic hrootSpoke
    have htop : (topQa (Part.getSpoke pr)).toNat = 6 := by
      change (topQa (Part.getSpoke (Pcons6 h f1 tail))).toNat = 6
      rfl
    exact hspokeTop.trans htop
  have hrootHat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) =
        (topQa h).toNat :=
    hroot (zp := mkZ Zhat pl pr) (qa := topQa h)
      hvalidHat
      (by simpa [pr, mkZ, zrange, Part.getHat] using hqHat)
      (by simpa [mkZ, redPop, pr] using hpoph)
  have hrootFan :
      G.arity (zdart G x0 (mkZ Zfan1r zpR.left zpR.right)) =
        (topQa f1).toNat :=
    hroot (zp := mkZ Zfan1r zpR.left zpR.right) (qa := topQa f1)
      hvalidFanR
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan1r] using hqFan)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan)
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    simpa [x, zp, zpR] using hshiftFacts.2
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zfan0l zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan0l zpR.left zpR.right)
          = zmove G Zfan0l (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face3_edge_eq_zfan0l_face_of_spoke6
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
      G.arity (G.node (G.node y)) = (topQa f1).toNat := by
    have hgeom := arity_node_node_face3_edge_eq_zfan1r_face
      (G := G) hPlain hCubic x
    have hrootFan' :
        G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) =
          (topQa f1).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan
    exact hgeom.trans hrootFan'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zfan0l zpR.left zpR.right)
    (zp2 := mkZ Zhatl pl pr)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := h)
    (r3 := f1) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons6_fan1_hat_branch_of_noQuizTreeFit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons6 h f1 tail)))
    (hshiftLeft :
      (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left =
        Pcons6 h f1 pl)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan0l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Zhatl pl (Pcons6 h f1 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons6 h f1 tail) = true) :
    False := by
  exact false_of_redZPartStep_pcons6_fan1_hat_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    hshiftLeft
    (hnofit (((G.face : G.Dart → G.Dart)^[3])
      (G.edge (zorg G x0 pl))))
    hleaf hpopfan hpoph

theorem false_of_redZPartStep_pcons6_fan1_hat_branch_of_tail_ne_nil
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons6 h f1 tail)))
    (htail : tail ≠ Pnil)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan0l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Zhatl pl (Pcons6 h f1 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons6 h f1 tail) = true) :
    False := by
  exact false_of_redZPartStep_pcons6_fan1_hat_branch_of_noQuizTreeFit
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1)
    hPlain hCubic hvalidStep hroot hstep hsound hnofit hvalid
    (zshiftR_left_pcons6_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) htail)
    hleaf hpopfan hpoph

theorem false_of_redZPartStep_pcons7_fan1_hat_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 f2 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons7 h f1 f2 tail)))
    (hshiftLeft :
      (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left =
        Pcons7 h f1 f2 pl)
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (((G.face : G.Dart → G.Dart)^[3])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan1l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
        (mkZ Zhatl pl (Pcons7 h f1 f2 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons7 h f1 f2 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons7 h f1 f2 tail) = true) :
    False := by
  let pr := Pcons7 h f1 f2 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[3]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons7 h f1 f2 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalidOriginal (loc) : zpvalid ctx (mkZ loc pl pr) := by
    simpa [pr] using (zpvalid_mkZ_loc (loc' := loc) hvalid)
  have hvalid1 := hvalidShift Zfan1l
  have hvalid2 := hvalidOriginal Zhatl
  have hvalid3 := hvalidShift Znil
  have hvalidHat := hvalidOriginal Zhat
  have hvalidFanR := hvalidShift Zfan1r
  have ⟨hqSpoke, hqHat, hqFan⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := h) (r3 := f1)
      (by simpa [zp, zpR, pr] using hleaf)
  have hrootSpoke :
      G.arity (zdart G x0 (mkZ Zhubr pl pr)) =
        (topQa (Part.getSpoke pr)).toNat :=
    hroot (zp := mkZ Zhubr pl pr)
      (qa := topQa (Part.getSpoke pr))
      (by simpa [zpvalid, mkZ, pr] using hvalid)
      hqSpoke
      (by simp [mkZ, redPop, redPoprSpoke, pr])
  have hspoke : G.arity (G.edge x) = 7 := by
    have hspokeTop :
        G.arity (G.edge x) = (topQa (Part.getSpoke pr)).toNat := by
      simpa [x] using
        arity_edge_zorg_eq_of_hubr (G := G) hCubic hrootSpoke
    have htop : (topQa (Part.getSpoke pr)).toNat = 7 := by
      change (topQa (Part.getSpoke (Pcons7 h f1 f2 tail))).toNat = 7
      rfl
    exact hspokeTop.trans htop
  have hrootHat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) =
        (topQa h).toNat :=
    hroot (zp := mkZ Zhat pl pr) (qa := topQa h)
      hvalidHat
      (by simpa [pr, mkZ, zrange, Part.getHat] using hqHat)
      (by simpa [mkZ, redPop, pr] using hpoph)
  have hrootFan :
      G.arity (zdart G x0 (mkZ Zfan1r zpR.left zpR.right)) =
        (topQa f1).toNat :=
    hroot (zp := mkZ Zfan1r zpR.left zpR.right) (qa := topQa f1)
      hvalidFanR
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan1r] using hqFan)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan)
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    simpa [x, zp, zpR] using hshiftFacts.2
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zfan1l zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan1l zpR.left zpR.right)
          = zmove G Zfan1l (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face3_edge_eq_zfan1l_face_of_spoke7
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
      G.arity (G.node (G.node y)) = (topQa f1).toNat := by
    have hgeom := arity_node_node_face3_edge_eq_zfan1r_face
      (G := G) hPlain hCubic x
    have hrootFan' :
        G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) =
          (topQa f1).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan
    exact hgeom.trans hrootFan'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zfan1l zpR.left zpR.right)
    (zp2 := mkZ Zhatl pl pr)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := h)
    (r3 := f1) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons7_fan1_hat_branch_of_tail_ne_nil
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 f2 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons7 h f1 f2 tail)))
    (htail : tail ≠ Pnil)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan1l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
        (mkZ Zhatl pl (Pcons7 h f1 f2 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons7 h f1 f2 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons7 h f1 f2 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons7 h f1 f2 tail) = true) :
    False := by
  exact false_of_redZPartStep_pcons7_fan1_hat_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1) (f2 := f2)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (zshiftR_left_pcons7_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) (f2 := f2)
      htail)
    (hnofit (((G.face : G.Dart → G.Dart)^[3])
      (G.edge (zorg G x0 pl))))
    hleaf hpopfan hpoph

theorem false_of_redZPartStep_pcons8_fan1_hat_branch
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 f2 f3 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail)))
    (hshiftLeft :
      (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left =
        Pcons8 h f1 f2 f3 pl)
    (hnofit :
      QuizTree.Hypermap.quizTreeFit G
        (((G.face : G.Dart → G.Dart)^[3])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan2l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zhatl pl (Pcons8 h f1 f2 f3 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons8 h f1 f2 f3 tail) = true) :
    False := by
  let pr := Pcons8 h f1 f2 f3 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[3]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons8 h f1 f2 f3 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalidOriginal (loc) : zpvalid ctx (mkZ loc pl pr) := by
    simpa [pr] using (zpvalid_mkZ_loc (loc' := loc) hvalid)
  have hvalid1 := hvalidShift Zfan2l
  have hvalid2 := hvalidOriginal Zhatl
  have hvalid3 := hvalidShift Znil
  have hvalidHat := hvalidOriginal Zhat
  have hvalidFanR := hvalidShift Zfan1r
  have ⟨hqSpoke, hqHat, hqFan⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := h) (r3 := f1)
      (by simpa [zp, zpR, pr] using hleaf)
  have hrootSpoke :
      G.arity (zdart G x0 (mkZ Zhubr pl pr)) =
        (topQa (Part.getSpoke pr)).toNat :=
    hroot (zp := mkZ Zhubr pl pr)
      (qa := topQa (Part.getSpoke pr))
      (by simpa [zpvalid, mkZ, pr] using hvalid)
      hqSpoke
      (by simp [mkZ, redPop, redPoprSpoke, pr])
  have hspoke : G.arity (G.edge x) = 8 := by
    have hspokeTop :
        G.arity (G.edge x) = (topQa (Part.getSpoke pr)).toNat := by
      simpa [x] using
        arity_edge_zorg_eq_of_hubr (G := G) hCubic hrootSpoke
    have htop : (topQa (Part.getSpoke pr)).toNat = 8 := by
      change (topQa (Part.getSpoke (Pcons8 h f1 f2 f3 tail))).toNat = 8
      rfl
    exact hspokeTop.trans htop
  have hrootHat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) =
        (topQa h).toNat :=
    hroot (zp := mkZ Zhat pl pr) (qa := topQa h)
      hvalidHat
      (by simpa [pr, mkZ, zrange, Part.getHat] using hqHat)
      (by simpa [mkZ, redPop, pr] using hpoph)
  have hrootFan :
      G.arity (zdart G x0 (mkZ Zfan1r zpR.left zpR.right)) =
        (topQa f1).toNat :=
    hroot (zp := mkZ Zfan1r zpR.left zpR.right) (qa := topQa f1)
      hvalidFanR
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan1r] using hqFan)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan)
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    simpa [x, zp, zpR] using hshiftFacts.2
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zfan2l zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan2l zpR.left zpR.right)
          = zmove G Zfan2l (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face3_edge_eq_zfan2l_face_of_spoke8
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
      G.arity (G.node (G.node y)) = (topQa f1).toNat := by
    have hgeom := arity_node_node_face3_edge_eq_zfan1r_face
      (G := G) hPlain hCubic x
    have hrootFan' :
        G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) =
          (topQa f1).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan
    exact hgeom.trans hrootFan'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zfan2l zpR.left zpR.right)
    (zp2 := mkZ Zhatl pl pr)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := h)
    (r3 := f1) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons8_fan1_hat_branch_of_tail_ne_nil
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl tail : Part} {h f1 f2 f3 : PRange}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hvalidStep : ZippedStepValid ctx)
    (hroot : ZippedRootSound G ctx x0)
    (hstep : ZippedStepSound G ctx x0)
    (hsound : ZippedQuestionSound G ctx x0)
    (hnofit : NoQuizTreeFit G ctx.qt)
    (hvalid : zpvalid ctx (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail)))
    (htail : tail ≠ Pnil)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan2l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zhatl pl (Pcons8 h f1 f2 f3 tail))
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr f1
          (qztGetr h
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpoph : redPoprHat ctx (Pcons8 h f1 f2 f3 tail) = true) :
    False := by
  exact false_of_redZPartStep_pcons8_fan1_hat_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1) (f2 := f2) (f3 := f3)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (zshiftR_left_pcons8_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) (f2 := f2)
      (f3 := f3) htail)
    (hnofit (((G.face : G.Dart → G.Dart)^[3])
      (G.edge (zorg G x0 pl))))
    hleaf hpopfan hpoph


end Schematic.Math.GraphTheory.FourColor.RedPart
