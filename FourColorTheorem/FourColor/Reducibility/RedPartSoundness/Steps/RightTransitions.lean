import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Steps.CentralTransitions

/-! Right-fan and truncated transition cases. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem zstepR_zfan0r_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan0r pl pr)))
      (zstepR ctx (mkZ Zfan0r pl pr)) := by
  intro _hproper
  change
    zdart G x0 (zshiftL ctx Zhatl (mkZ Zfan0r pl pr)) =
      qstepR G (zmove G Zfan0r (zorg G x0 pl))
  rw [zdart_zshiftL_eq_zmove_face_symm_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0]
  simpa [zmove] using
    (qstepR_zfan0r_face_eq_zhatl_of_plain_cubic
      (G := G) hPlain hCubic
      (G.face.symm (zorg G x0 pl))).symm

theorem zstepR_zfan1r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan1r pl pr)))
      (zstepR ctx (mkZ Zfan1r pl pr)) := by
  intro _hproper
  exact (qstepR_rightFan_succ_of_plain
    (G := G) hPlain 2 (zorg G x0 pl)).symm

theorem zstepR_zfan2r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan2r pl pr)))
      (zstepR ctx (mkZ Zfan2r pl pr)) := by
  intro _hproper
  exact (qstepR_rightFan_succ_of_plain
    (G := G) hPlain 3 (zorg G x0 pl)).symm

theorem zstepR_zfan3r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan3r pl pr)))
      (zstepR ctx (mkZ Zfan3r pl pr)) := by
  intro _hproper
  exact (qstepR_rightFan_succ_of_plain
    (G := G) hPlain 4 (zorg G x0 pl)).symm

theorem zstepLt_zhubl_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part} :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhubl pl pr)))
      (zstepLt ctx (mkZ Zhubl pl pr)) := by
  intro _hproper
  rfl

theorem zstepLt_zhub_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhub pl pr)))
      (zstepLt ctx (mkZ Zhub pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zhub_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hleft hfit0

theorem zstepLt_zhat_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhat pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhat pl pr)))
      (zstepLt ctx (mkZ Zhat pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zhat_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hCubic hleft hfit0 hvalid

theorem zstepLt_zhubr_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhubr pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhubr pl pr)))
      (zstepLt ctx (mkZ Zhubr pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zhubr_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hCubic hleft hfit0 hvalid

theorem zstepLt_zfan0l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan0l pl pr)))
      (zstepLt ctx (mkZ Zfan0l pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zfan0l_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain hCubic

theorem zstepRt_zhubr_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part} :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhubr pl pr)))
      (zstepRt ctx (mkZ Zhubr pl pr)) := by
  intro _hproper
  rfl

theorem zstepRt_zhub_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhub pl pr)))
      (zstepRt ctx (mkZ Zhub pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zhub_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hleft hfit0 hvalid

theorem zstepRt_zhat_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhat pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhat pl pr)))
      (zstepRt ctx (mkZ Zhat pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zhat_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hfit0 hvalid

theorem zstepLt_zhatr_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhatr pl pr)))
      (zstepLt ctx (mkZ Zhatr pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zhatr_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hCubic

theorem zstepRt_zhatl_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhatl pl pr)))
      (zstepRt ctx (mkZ Zhatl pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zhatl_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain hCubic

theorem zstepRt_zhubl_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhubl pl pr)))
      (zstepRt ctx (mkZ Zhubl pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zhubl_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hleft hfit0

theorem zstepRt_zfan0r_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan0r pl pr)))
      (zstepRt ctx (mkZ Zfan0r pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zfan0r_fit_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      hPlain hCubic hleft hfit0

theorem zstepRt_zhatr_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhatr pl pr))
    (htop : zpfitTop G ctx x0 (mkZ Zhatr pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhatr pl pr)))
      (zstepRt ctx (mkZ Zhatr pl pr)) := by
  cases pr with
  | Pnil =>
      simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using
        zstepR_zhatr_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := Pnil)
          hPlain hCubic hleft hfit0 hvalid
  | Pcons s h tail =>
      have hbase :
          zpfit G x0
            (qstepR G (zdart G x0 (mkZ Zhatr pl (Pcons s h tail))))
            (zstepR ctx (mkZ Zhatr pl (Pcons s h tail))) :=
        zstepR_zhatr_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons s h tail)
          hPlain hCubic hleft hfit0 hvalid
      cases s with
      | Pr55 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr66 =>
          have hvalidZhat : zpvalid ctx (mkZ Zhat pl (Pcons PRange.Pr66 h tail)) := by
            simpa [zpvalid, mkZ] using hvalid
          have hspoke :
              G.arity (G.edge (zorg G x0 pl)) = 6 := by
            simpa [zpfitTop, mkZ, zdart, zporg, zrange, Part.getSpoke,
              topQa, QArity.toNat,
              arity_zmove_zhatr_eq_edge_of_cubic (G := G) hCubic] using htop
          have hgeom :
              qstepL G (zmove G Zhat (zorg G x0 pl)) =
                zmove G Zfan1l (G.face (zorg G x0 pl)) := by
            simpa [zmove] using
              qstepL_zhat_eq_leftFan_of_edge_arity
                (G := G) hPlain hCubic 3
                (x := zorg G x0 pl) (by simpa using hspoke)
          have hstep :=
            zstepL_zhat_zshiftR_fit_of_face
              (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
              (pr := Pcons PRange.Pr66 h tail) (loc := Zfan1l)
              hleft hfit0 hvalidZhat hgeom
          have hmove :
              qstepL G (zdart G x0 (mkZ Zhat pl (Pcons PRange.Pr66 h tail))) =
                qstepR G (zdart G x0 (mkZ Zhatr pl (Pcons PRange.Pr66 h tail))) := by
            simpa [zdart, zporg] using
              (qstepR_zhatr_eq_qstepL_zhat_of_plain_cubic
                (G := G) hPlain hCubic (zorg G x0 pl)).symm
          rw [hmove] at hstep
          simpa [zstepRt, zfanLt, mkZ] using hstep
      | Pr77 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr88 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr99 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr56 =>
          have hvalidZhat : zpvalid ctx (mkZ Zhat pl (Pcons PRange.Pr56 h tail)) := by
            simpa [zpvalid, mkZ] using hvalid
          have hspoke :
              G.arity (G.edge (zorg G x0 pl)) = 6 := by
            simpa [zpfitTop, mkZ, zdart, zporg, zrange, Part.getSpoke,
              topQa, QArity.toNat,
              arity_zmove_zhatr_eq_edge_of_cubic (G := G) hCubic] using htop
          have hgeom :
              qstepL G (zmove G Zhat (zorg G x0 pl)) =
                zmove G Zfan1l (G.face (zorg G x0 pl)) := by
            simpa [zmove] using
              qstepL_zhat_eq_leftFan_of_edge_arity
                (G := G) hPlain hCubic 3
                (x := zorg G x0 pl) (by simpa using hspoke)
          have hstep :=
            zstepL_zhat_zshiftR_fit_of_face
              (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
              (pr := Pcons PRange.Pr56 h tail) (loc := Zfan1l)
              hleft hfit0 hvalidZhat hgeom
          have hmove :
              qstepL G (zdart G x0 (mkZ Zhat pl (Pcons PRange.Pr56 h tail))) =
                qstepR G (zdart G x0 (mkZ Zhatr pl (Pcons PRange.Pr56 h tail))) := by
            simpa [zdart, zporg] using
              (qstepR_zhatr_eq_qstepL_zhat_of_plain_cubic
                (G := G) hPlain hCubic (zorg G x0 pl)).symm
          rw [hmove] at hstep
          simpa [zstepRt, zfanLt, mkZ] using hstep
      | Pr67 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr78 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr89 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr57 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr68 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr79 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr58 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr69 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
      | Pr59 =>
          simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using hbase
  | Pcons6 h f1 tail =>
      simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using
        zstepR_zhatr_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons6 h f1 tail)
          hPlain hCubic hleft hfit0 hvalid
  | Pcons7 h f1 f2 tail =>
      simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using
        zstepR_zhatr_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons7 h f1 f2 tail)
          hPlain hCubic hleft hfit0 hvalid
  | Pcons8 h f1 f2 f3 tail =>
      simpa [zstepR, zstepRt, zfanL, zfanLt, mkZ] using
        zstepR_zhatr_fit_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons8 h f1 f2 f3 tail)
          hPlain hCubic hleft hfit0 hvalid

theorem zstepLt_zfan1l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan1l pl pr)))
      (zstepLt ctx (mkZ Zfan1l pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zfan1l_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain hCubic

theorem zstepLt_zfan2l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan2l pl pr)))
      (zstepLt ctx (mkZ Zfan2l pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zfan2l_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain hCubic

theorem zstepLt_zfan3l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zfan3l pl pr)))
      (zstepLt ctx (mkZ Zfan3l pl pr)) := by
  simpa [zstepL, zstepLt, mkZ] using
    zstepL_zfan3l_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain hCubic

theorem zstepRt_zfan1r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan1r pl pr)))
      (zstepRt ctx (mkZ Zfan1r pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zfan1r_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain

theorem zstepRt_zfan2r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan2r pl pr)))
      (zstepRt ctx (mkZ Zfan2r pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zfan2r_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain

theorem zstepRt_zfan3r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zfan3r pl pr)))
      (zstepRt ctx (mkZ Zfan3r pl pr)) := by
  simpa [zstepR, zstepRt, mkZ] using
    zstepR_zfan3r_fit (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pr) hPlain


end Schematic.Math.GraphTheory.FourColor.RedPart
