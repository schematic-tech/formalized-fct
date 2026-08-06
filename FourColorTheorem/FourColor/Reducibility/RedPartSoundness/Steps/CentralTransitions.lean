import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Steps.LeftTransitions

/-! Central and right transition cases. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem zstepL_zhatr_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhatr pl pr)))
      (zstepL ctx (mkZ Zhatr pl pr)) := by
  intro _hproper
  exact (qstepL_zmove_zhatr_eq_zmove_zhub_of_cubic
    (G := G) hCubic (zorg G x0 pl)).symm

theorem zstepR_zhatr_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhatr pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhatr pl pr)))
      (zstepR ctx (mkZ Zhatr pl pr)) := by
  intro hproper
  have hvalidZhat : zpvalid ctx (mkZ Zhat pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  have hproperZhat : (zstepL ctx (mkZ Zhat pl pr)).proper = true := by
    simpa [zstepL, zstepR, mkZ] using hproper
  have hstep :=
    zstepL_zhat_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hCubic hleft hfit0 hvalidZhat hproperZhat
  have hmove :
      qstepL G (zdart G x0 (mkZ Zhat pl pr)) =
        qstepR G (zdart G x0 (mkZ Zhatr pl pr)) := by
    simpa [zdart, zporg] using
      (qstepR_zhatr_eq_qstepL_zhat_of_plain_cubic
        (G := G) hPlain hCubic (zorg G x0 pl)).symm
  rw [hmove] at hstep
  simpa [zstepL, zstepR, mkZ, zdart, zporg] using hstep

theorem zstepL_zhubr_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhubr pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhubr pl pr)))
      (zstepL ctx (mkZ Zhubr pl pr)) := by
  intro _hproper
  have hvalid' : zvalid ctx pl pr := by
    simpa [zpvalid, mkZ] using hvalid
  change
    zdart G x0 (zshiftR ctx Zhubr (mkZ Zhubr pl pr)) =
      qstepL G (G.node (G.node (zorg G x0 pl)))
  rw [zdart_zshiftR_eq_zmove_face_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0 hvalid']
  simpa [zmove] using
    (Hypermap.qstepL_node_node_eq_node_node_face_of_plain_cubic
      (G := G) hPlain hCubic (zorg G x0 pl)).symm

theorem zstepL_zfan0l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan0l pl pr)))
      (zstepL ctx (mkZ Zfan0l pl pr)) := by
  intro _hproper
  exact (qstepL_zfan0l_eq_zhatr_of_plain_cubic
    (G := G) hPlain hCubic (zorg G x0 pl)).symm

theorem zstepL_zfan1l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan1l pl pr)))
      (zstepL ctx (mkZ Zfan1l pl pr)) := by
  intro _hproper
  exact (qstepL_leftFan_succ_of_plain_cubic
    (G := G) hPlain hCubic 2 (zorg G x0 pl)).symm

theorem zstepL_zfan2l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan2l pl pr)))
      (zstepL ctx (mkZ Zfan2l pl pr)) := by
  intro _hproper
  exact (qstepL_leftFan_succ_of_plain_cubic
    (G := G) hPlain hCubic 3 (zorg G x0 pl)).symm

theorem zstepL_zfan3l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan3l pl pr)))
      (zstepL ctx (mkZ Zfan3l pl pr)) := by
  intro _hproper
  exact (qstepL_leftFan_succ_of_plain_cubic
    (G := G) hPlain hCubic 4 (zorg G x0 pl)).symm

theorem zstepR_zhat_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhat pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhat pl pr)))
      (zstepR ctx (mkZ Zhat pl pr)) := by
  have hvalidZ : zvalid ctx pl pr := by
    simpa [zpvalid, mkZ] using hvalid
  cases pl with
  | Pnil =>
      exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
  | Pcons s h tail =>
      cases s with
      | Pr55 =>
          intro _hproper
          have hvalid' : zvalid ctx tail (Pcons PRange.Pr55 h pr) := by
            simpa [zvalid, Part.reverseAppend] using hvalidZ
          have hfitRight :
              Part.fitp G (zorg G x0 tail)
                (Pcons PRange.Pr55 h pr) = true :=
            fitp_right_of_zvalid
              (G := G) (ctx := ctx) (x0 := x0)
              (pl := tail) (pr := Pcons PRange.Pr55 h pr)
              hvalid' hfit0
          have hspoke :
              G.arity
                (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) =
                  5 := by
            have hparts := hfitRight
            simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
            exact hparts.1.1
          have hnode :
              G.arity (G.node (zorg G x0 (Pcons PRange.Pr55 h tail))) =
                5 := by
            have hspoke' : G.arity (G.edge (zorg G x0 tail)) = 5 := by
              simpa [SubpartLoc.move] using hspoke
            have hnf :
                G.node (zorg G x0 (Pcons PRange.Pr55 h tail)) =
                  G.edge (zorg G x0 tail) := by
              simp [zorg, Part.size, Function.iterate_succ_apply',
                Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
            rw [hnf]
            exact hspoke'
          simpa [zstepR, zfanR, mkZ, zdart, zporg] using
            (qstepR_zhat_eq_zfan0r_of_node_arity_five
              (G := G) hPlain (x := zorg G x0 (Pcons PRange.Pr55 h tail))
              hnode).symm
      | Pr66 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr77 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr88 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr99 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr56 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr67 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr78 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr89 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr57 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr68 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr79 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr58 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr69 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
      | Pr59 =>
          exact zpfit_of_proper_false (by simp [zstepR, zfanR, mkZ, ZPart.proper])
  | Pcons6 h f1 tail =>
      intro _hproper
      have hvalid' : zvalid ctx tail (Pcons6 h f1 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalidZ
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons6 h f1 pr) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons6 h f1 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) =
              6 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1
      have hnode :
          G.arity (G.node (zorg G x0 (Pcons6 h f1 tail))) = 6 := by
        have hspoke' : G.arity (G.edge (zorg G x0 tail)) = 6 := by
          simpa [SubpartLoc.move] using hspoke
        have hnf :
            G.node (zorg G x0 (Pcons6 h f1 tail)) =
              G.edge (zorg G x0 tail) := by
          simp [zorg, Part.size, Function.iterate_succ_apply',
            Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
        rw [hnf]
        exact hspoke'
      simpa [zstepR, zfanR, mkZ, zdart, zporg] using
        (qstepR_zhat_eq_zfan1r_of_node_arity_six
          (G := G) hPlain (x := zorg G x0 (Pcons6 h f1 tail))
          hnode).symm
  | Pcons7 h f1 f2 tail =>
      intro _hproper
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalidZ
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons7 h f1 f2 pr) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons7 h f1 f2 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) =
              7 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1.1
      have hnode :
          G.arity (G.node (zorg G x0 (Pcons7 h f1 f2 tail))) = 7 := by
        have hspoke' : G.arity (G.edge (zorg G x0 tail)) = 7 := by
          simpa [SubpartLoc.move] using hspoke
        have hnf :
            G.node (zorg G x0 (Pcons7 h f1 f2 tail)) =
              G.edge (zorg G x0 tail) := by
          simp [zorg, Part.size, Function.iterate_succ_apply',
            Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
        rw [hnf]
        exact hspoke'
      simpa [zstepR, zfanR, mkZ, zdart, zporg] using
        (qstepR_zhat_eq_zfan2r_of_node_arity_seven
          (G := G) hPlain (x := zorg G x0 (Pcons7 h f1 f2 tail))
          hnode).symm
  | Pcons8 h f1 f2 f3 tail =>
      intro _hproper
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalidZ
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons8 h f1 f2 f3 pr) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons8 h f1 f2 f3 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) =
              8 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1.1.1
      have hnode :
          G.arity (G.node (zorg G x0 (Pcons8 h f1 f2 f3 tail))) =
            8 := by
        have hspoke' : G.arity (G.edge (zorg G x0 tail)) = 8 := by
          simpa [SubpartLoc.move] using hspoke
        have hnf :
            G.node (zorg G x0 (Pcons8 h f1 f2 f3 tail)) =
              G.edge (zorg G x0 tail) := by
          simp [zorg, Part.size, Function.iterate_succ_apply',
            Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
        rw [hnf]
        exact hspoke'
      simpa [zstepR, zfanR, mkZ, zdart, zporg] using
        (qstepR_zhat_eq_zfan3r_of_node_arity_eight
          (G := G) hPlain
          (x := zorg G x0 (Pcons8 h f1 f2 f3 tail)) hnode).symm

theorem zstepL_zhatl_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhatl pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhatl pl pr)))
      (zstepL ctx (mkZ Zhatl pl pr)) := by
  have hvalidZhat : zpvalid ctx (mkZ Zhat pl pr) := by
    simpa [zpvalid, mkZ] using hvalid
  simpa [zstepL, zstepR, mkZ, zdart, zporg, zmove, qstepL, qstepR]
    using
      zstepR_zhat_fit_of_reverse_exact
        (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
        hPlain hfit0 hvalidZhat

theorem zstepLt_zhatl_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhatl pl pr))
    (htop : zpfitTop G ctx x0 (mkZ Zhatl pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhatl pl pr)))
      (zstepLt ctx (mkZ Zhatl pl pr)) := by
  cases pl with
  | Pnil =>
      simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using
        zstepL_zhatl_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0) (pl := Pnil) (pr := pr)
          hPlain hfit0 hvalid
  | Pcons s h tail =>
      have hbase :
          zpfit G x0
            (qstepL G (zdart G x0 (mkZ Zhatl (Pcons s h tail) pr)))
            (zstepL ctx (mkZ Zhatl (Pcons s h tail) pr)) :=
        zstepL_zhatl_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := Pcons s h tail) (pr := pr) hPlain hfit0 hvalid
      cases s with
      | Pr55 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr66 =>
          intro _hproper
          have hnode :
              G.arity
                (G.node (zorg G x0 (Pcons PRange.Pr66 h tail))) = 6 := by
            simpa [zpfitTop, mkZ, zdart, zporg, zrange, Part.getSpoke,
              topQa, QArity.toNat, arity_zmove_zhatl_eq_node] using htop
          simpa [zstepLt, zfanRt, mkZ, zdart, zporg, zmove, qstepL, qstepR]
            using
              (qstepR_zhat_eq_zfan1r_of_node_arity_six
                (G := G) hPlain
                (x := zorg G x0 (Pcons PRange.Pr66 h tail)) hnode).symm
      | Pr77 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr88 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr99 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr56 =>
          intro _hproper
          have hnode :
              G.arity
                (G.node (zorg G x0 (Pcons PRange.Pr56 h tail))) = 6 := by
            simpa [zpfitTop, mkZ, zdart, zporg, zrange, Part.getSpoke,
              topQa, QArity.toNat, arity_zmove_zhatl_eq_node] using htop
          simpa [zstepLt, zfanRt, mkZ, zdart, zporg, zmove, qstepL, qstepR]
            using
              (qstepR_zhat_eq_zfan1r_of_node_arity_six
                (G := G) hPlain
                (x := zorg G x0 (Pcons PRange.Pr56 h tail)) hnode).symm
      | Pr67 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr78 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr89 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr57 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr68 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr79 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr58 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr69 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
      | Pr59 =>
          simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using hbase
  | Pcons6 h f1 tail =>
      simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using
        zstepL_zhatl_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := Pcons6 h f1 tail) (pr := pr) hPlain hfit0 hvalid
  | Pcons7 h f1 f2 tail =>
      simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using
        zstepL_zhatl_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := Pcons7 h f1 f2 tail) (pr := pr) hPlain hfit0 hvalid
  | Pcons8 h f1 f2 f3 tail =>
      simpa [zstepL, zstepLt, zfanR, zfanRt, mkZ] using
        zstepL_zhatl_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := Pcons8 h f1 f2 f3 tail) (pr := pr) hPlain hfit0 hvalid

theorem zstepR_zhatl_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhatl pl pr)))
      (zstepR ctx (mkZ Zhatl pl pr)) := by
  intro _hproper
  exact (qstepR_zmove_zhatl_eq_zmove_zhub_of_plain_cubic
    (G := G) hPlain hCubic (zorg G x0 pl)).symm

theorem zstepR_zhubl_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhubl pl pr)))
      (zstepR ctx (mkZ Zhubl pl pr)) := by
  intro _hproper
  change
    zdart G x0 (zshiftL ctx Zhubl (mkZ Zhubl pl pr)) =
      qstepR G (G.node (zorg G x0 pl))
  rw [zdart_zshiftL_eq_zmove_face_symm_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0]
  simpa [zmove] using
    (Hypermap.qstepR_node_face_eq_node_of_plain
      (G := G) hPlain (G.face.symm (zorg G x0 pl))).symm

end Schematic.Math.GraphTheory.FourColor.RedPart
