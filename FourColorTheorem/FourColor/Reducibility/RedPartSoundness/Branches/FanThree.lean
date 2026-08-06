import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Questions

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem false_of_redZPartStep_pcons8_fan3_fan2_branch
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
        (((G.face : G.Dart → G.Dart)^[5])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zfan0l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zfan1r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr f3
          (qztGetr f2
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan3 :
      redPoplFan3r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpopfan2 :
      redPoplFan2r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true) :
    False := by
  let pr := Pcons8 h f1 f2 f3 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[5]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons8 h f1 f2 f3 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalid1 := hvalidShift Zfan0l
  have hvalid2 := hvalidShift Zfan1r
  have hvalid3 := hvalidShift Znil
  have hvalidFan2R := hvalidShift Zfan2r
  have hvalidFan3R := hvalidShift Zfan3r
  have ⟨hqSpoke, hqFan2, hqFan3⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := f2) (r3 := f3)
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
  have hrootFan2 :
      G.arity (zdart G x0 (mkZ Zfan2r zpR.left zpR.right)) =
        (topQa f2).toNat :=
    hroot (zp := mkZ Zfan2r zpR.left zpR.right) (qa := topQa f2)
      hvalidFan2R
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan2r] using hqFan2)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan2)
  have hrootFan3 :
      G.arity (zdart G x0 (mkZ Zfan3r zpR.left zpR.right)) =
        (topQa f3).toNat :=
    hroot (zp := mkZ Zfan3r zpR.left zpR.right) (qa := topQa f3)
      hvalidFan3R
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan3r] using hqFan3)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan3)
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
              (qstepR_face5_edge_eq_zfan0l_face_of_spoke8
                (G := G) hPlain hCubic (x := x) hspoke).symm
  have hzp2 :
      zpfit G x0 (qstepR G (G.node y))
        (mkZ Zfan1r zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan1r zpR.left zpR.right)
          = zmove G Zfan1r (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G (G.node y) := by
            simpa [y] using
              (qstepR_node_face5_edge_eq_zfan1r_face
                (G := G) hPlain x).symm
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node y)))
        (mkZ Znil zpR.left zpR.right) :=
    zpfit_mkZ_nil
  have harity1 :
      G.arity y = (topQa (Part.getSpoke pr)).toNat := by
    simpa [x, y] using
      arity_face_iter_edge_zorg_eq_of_hubr
        (G := G) hCubic 5 hrootSpoke
  have harity2 :
      G.arity (G.node y) = (topQa f2).toNat := by
    have hgeom := arity_node_face5_edge_eq_zfan2r_face
      (G := G) hPlain x
    have hrootFan2' :
        G.arity (zmove G ZPartLoc.Zfan2r (G.face x)) =
          (topQa f2).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan2
    exact hgeom.trans hrootFan2'
  have harity3 :
      G.arity (G.node (G.node y)) = (topQa f3).toNat := by
    have hgeom := arity_node_node_face5_edge_eq_zfan3r_face
      (G := G) hPlain hCubic x
    have hrootFan3' :
        G.arity (zmove G ZPartLoc.Zfan3r (G.face x)) =
          (topQa f3).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan3
    exact hgeom.trans hrootFan3'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zfan0l zpR.left zpR.right)
    (zp2 := mkZ Zfan1r zpR.left zpR.right)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := f2)
    (r3 := f3) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons8_fan3_fan2_branch_of_tail_ne_nil
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
        (mkZ Zfan0l
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zfan1r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr f3
          (qztGetr f2
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpopfan3 :
      redPoplFan3r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpopfan2 :
      redPoplFan2r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true) :
    False := by
  exact false_of_redZPartStep_pcons8_fan3_fan2_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1) (f2 := f2) (f3 := f3)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (zshiftR_left_pcons8_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) (f2 := f2)
      (f3 := f3) htail)
    (hnofit (((G.face : G.Dart → G.Dart)^[5])
      (G.edge (zorg G x0 pl))))
    hleaf hpopfan3 hpopfan2

theorem false_of_redZPartStep_pcons8_hat_fan3_branch
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
        (((G.face : G.Dart → G.Dart)^[6])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zfan2r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
          (qztGetr f3
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpopfan3 :
      redPoplFan3r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true) :
    False := by
  let pr := Pcons8 h f1 f2 f3 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[6]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons8 h f1 f2 f3 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalid1 := hvalidShift Zhatr
  have hvalid2 := hvalidShift Zfan2r
  have hvalid3 := hvalidShift Znil
  have hvalidFan3R := hvalidShift Zfan3r
  have hvalidHatR := hvalidShift Zhat
  have ⟨hqSpoke, hqFan3, hqHatR⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := f3)
      (r3 := Part.getHat zpR.right)
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
  have hrootFan3 :
      G.arity (zdart G x0 (mkZ Zfan3r zpR.left zpR.right)) =
        (topQa f3).toNat :=
    hroot (zp := mkZ Zfan3r zpR.left zpR.right) (qa := topQa f3)
      hvalidFan3R
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan3r] using hqFan3)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan3)
  have hrootHatR :
      G.arity (zdart G x0 (mkZ Zhat zpR.left zpR.right)) =
        (topQa (Part.getHat zpR.right)).toNat :=
    hroot (zp := mkZ Zhat zpR.left zpR.right)
      (qa := topQa (Part.getHat zpR.right))
      hvalidHatR hqHatR
      (by simpa [mkZ, redPop, zp, zpR] using hpophR)
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    simpa [x, zp, zpR] using hshiftFacts.2
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zhatr zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zhatr zpR.left zpR.right)
          = zmove G Zhatr (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face6_edge_eq_zhatr_face_of_spoke8
                (G := G) hPlain hCubic (x := x) hspoke).symm
  have hzp2 :
      zpfit G x0 (qstepR G (G.node y))
        (mkZ Zfan2r zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan2r zpR.left zpR.right)
          = zmove G Zfan2r (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G (G.node y) := by
            simpa [y] using
              (qstepR_node_face6_edge_eq_zfan2r_face
                (G := G) hPlain x).symm
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node y)))
        (mkZ Znil zpR.left zpR.right) :=
    zpfit_mkZ_nil
  have harity1 :
      G.arity y = (topQa (Part.getSpoke pr)).toNat := by
    simpa [x, y] using
      arity_face_iter_edge_zorg_eq_of_hubr
        (G := G) hCubic 6 hrootSpoke
  have harity2 :
      G.arity (G.node y) = (topQa f3).toNat := by
    have hgeom := arity_node_face6_edge_eq_zfan3r_face
      (G := G) hPlain x
    have hrootFan3' :
        G.arity (zmove G ZPartLoc.Zfan3r (G.face x)) =
          (topQa f3).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan3
    exact hgeom.trans hrootFan3'
  have harity3 :
      G.arity (G.node (G.node y)) =
        (topQa (Part.getHat zpR.right)).toNat := by
    have hgeom := arity_node_node_face6_edge_eq_zhat_face_of_spoke8
      (G := G) hPlain hCubic (x := x) hspoke
    have hrootHatR' :
        G.arity (zmove G ZPartLoc.Zhat (G.face x)) =
          (topQa (Part.getHat zpR.right)).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootHatR
    exact hgeom.trans hrootHatR'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zhatr zpR.left zpR.right)
    (zp2 := mkZ Zfan2r zpR.left zpR.right)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := f3)
    (r3 := Part.getHat zpR.right) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons8_hat_fan3_branch_of_tail_ne_nil
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
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Zfan2r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right)
          (qztGetr f3
            (qztGetr (Part.getSpoke (Pcons8 h f1 f2 f3 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true)
    (hpopfan3 :
      redPoplFan3r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).right = true) :
    False := by
  exact false_of_redZPartStep_pcons8_hat_fan3_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1) (f2 := f2) (f3 := f3)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (zshiftR_left_pcons8_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) (f2 := f2)
      (f3 := f3) htail)
    (hnofit (((G.face : G.Dart → G.Dart)^[6])
      (G.edge (zorg G x0 pl))))
    hleaf hpophR hpopfan3

theorem false_of_redZPartStep_pcons6_hat_fan1_branch
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
        (((G.face : G.Dart → G.Dart)^[4])
          (G.edge (zorg G x0 pl))) ctx.qt = false)
    (hleaf :
      redQztLeaf ctx
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Zfan0r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
          (qztGetr f1
            (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true) :
    False := by
  let pr := Pcons6 h f1 tail
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  let x := zorg G x0 pl
  let y := ((G.face : G.Dart → G.Dart)^[4]) (G.edge x)
  have hshiftLeft' : zpR.left = Pcons6 h f1 pl := by
    simpa [zp, pr, zpR] using hshiftLeft
  have hshiftFacts := valid_hubRightShift_locations_and_zorg_left_eq_face
    (G := G) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep (by simpa [pr] using hvalid)
  have hvalidShift (loc) : zpvalid ctx (mkZ loc zpR.left zpR.right) := by
    simpa [zp, zpR] using hshiftFacts.1 loc
  have hvalid1 := hvalidShift Zhatr
  have hvalid2 := hvalidShift Zfan0r
  have hvalid3 := hvalidShift Znil
  have hvalidFanR := hvalidShift Zfan1r
  have hvalidHatR := hvalidShift Zhat
  have ⟨hqSpoke, hqFan, hqHatR⟩ :=
    fitQa_getr_three_of_redQztLeaf
      (r1 := Part.getSpoke pr) (r2 := f1)
      (r3 := Part.getHat zpR.right)
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
  have hrootFan :
      G.arity (zdart G x0 (mkZ Zfan1r zpR.left zpR.right)) =
        (topQa f1).toNat :=
    hroot (zp := mkZ Zfan1r zpR.left zpR.right) (qa := topQa f1)
      hvalidFanR
      (by simpa [mkZ, zrange, hshiftLeft', Part.getFan1r] using hqFan)
      (by simpa [mkZ, redPop, zp, zpR] using hpopfan)
  have hrootHatR :
      G.arity (zdart G x0 (mkZ Zhat zpR.left zpR.right)) =
        (topQa (Part.getHat zpR.right)).toNat :=
    hroot (zp := mkZ Zhat zpR.left zpR.right)
      (qa := topQa (Part.getHat zpR.right))
      hvalidHatR hqHatR
      (by simpa [mkZ, redPop, zp, zpR] using hpophR)
  have hzorgR : zorg G x0 zpR.left = G.face x := by
    simpa [x, zp, zpR] using hshiftFacts.2
  have hzp1 :
      zpfit G x0 (qstepR G y) (mkZ Zhatr zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zhatr zpR.left zpR.right)
          = zmove G Zhatr (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G y := by
            simpa [y] using
              (qstepR_face4_edge_eq_zhatr_face_of_spoke6
                (G := G) hPlain hCubic (x := x) hspoke).symm
  have hzp2 :
      zpfit G x0 (qstepR G (G.node y))
        (mkZ Zfan0r zpR.left zpR.right) := by
    intro _hproper
    calc
      zdart G x0 (mkZ Zfan0r zpR.left zpR.right)
          = zmove G Zfan0r (G.face x) := by
            simp [mkZ, zdart, zporg, hzorgR]
      _ = qstepR G (G.node y) := by
            simpa [y] using
              (qstepR_node_face4_edge_eq_zfan0r_face
                (G := G) hPlain x).symm
  have hzp3 :
      zpfit G x0 (qstepR G (G.node (G.node y)))
        (mkZ Znil zpR.left zpR.right) :=
    zpfit_mkZ_nil
  have harity1 :
      G.arity y = (topQa (Part.getSpoke pr)).toNat := by
    simpa [x, y] using
      arity_face_iter_edge_zorg_eq_of_hubr
        (G := G) hCubic 4 hrootSpoke
  have harity2 :
      G.arity (G.node y) = (topQa f1).toNat := by
    have hgeom := arity_node_face4_edge_eq_zfan1r_face
      (G := G) hPlain x
    have hrootFan' :
        G.arity (zmove G ZPartLoc.Zfan1r (G.face x)) =
          (topQa f1).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootFan
    exact hgeom.trans hrootFan'
  have harity3 :
      G.arity (G.node (G.node y)) =
        (topQa (Part.getHat zpR.right)).toNat := by
    have hgeom := arity_node_node_face4_edge_eq_zhat_face_of_spoke6
      (G := G) hPlain hCubic (x := x) hspoke
    have hrootHatR' :
        G.arity (zmove G ZPartLoc.Zhat (G.face x)) =
          (topQa (Part.getHat zpR.right)).toNat := by
      simpa [x, mkZ, zdart, zporg, hzorgR] using hrootHatR
    exact hgeom.trans hrootHatR'
  exact false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := mkZ Zhatr zpR.left zpR.right)
    (zp2 := mkZ Zfan0r zpR.left zpR.right)
    (zp3 := mkZ Znil zpR.left zpR.right)
    (r1 := Part.getSpoke pr) (r2 := f1)
    (r3 := Part.getHat zpR.right) (qt := ctx.qt) (x := y)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3
    (by simpa [zp, zpR, pr] using hleaf)
    (by simpa [x, y] using hnofit)
    harity1 harity2 harity3

theorem false_of_redZPartStep_pcons6_hat_fan1_branch_of_tail_ne_nil
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
        (mkZ Zhatr
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Zfan0r
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (mkZ Znil
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
          (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
        (qztGetr
          (Part.getHat
            (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right)
          (qztGetr f1
            (qztGetr (Part.getSpoke (Pcons6 h f1 tail))
              (QuizTree.truncate ctx.qt)))) = true)
    (hpophR :
      redPoprHat ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true)
    (hpopfan :
      redPoplFan1r ctx
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).left
        (zshiftR ctx Zhub (mkZ Zhub pl (Pcons6 h f1 tail))).right = true) :
    False := by
  exact false_of_redZPartStep_pcons6_hat_fan1_branch
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
    (tail := tail) (h := h) (f1 := f1)
    hPlain hCubic hvalidStep hroot hstep hsound hvalid
    (zshiftR_left_pcons6_of_tail_ne_nil (ctx := ctx) (loc := Zhub)
      (pl := pl) (tail := tail) (h := h) (f1 := f1) htail)
    (hnofit (((G.face : G.Dart → G.Dart)^[4])
      (G.edge (zorg G x0 pl))))
    hleaf hpophR hpopfan


end Schematic.Math.GraphTheory.FourColor.RedPart
