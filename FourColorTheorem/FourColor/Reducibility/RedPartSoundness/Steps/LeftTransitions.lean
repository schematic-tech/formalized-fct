import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.SoundnessInternal

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem zstepL_zhubl_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part} :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhubl pl pr)))
      (zstepL ctx (mkZ Zhubl pl pr)) := by
  intro _hproper
  rfl

theorem zstepL_zhub_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhub pl pr)))
      (zstepL ctx (mkZ Zhub pl pr)) := by
  intro _hproper
  change
    zdart G x0 (zshiftL ctx Zhubl (mkZ Zhub pl pr)) =
      qstepL G (zorg G x0 pl)
  rw [zdart_zshiftL_eq_zmove_face_symm_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0]
  simpa [zmove] using
    (Hypermap.qstepL_face_eq_node_of_plain
      (G := G) hPlain (G.face.symm (zorg G x0 pl))).symm

theorem zstepR_zhubr_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part} :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhubr pl pr)))
      (zstepR ctx (mkZ Zhubr pl pr)) := by
  intro _hproper
  rfl

theorem zstepR_zhub_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr)) :
    zpfit G x0
      (qstepR G (zdart G x0 (mkZ Zhub pl pr)))
      (zstepR ctx (mkZ Zhub pl pr)) := by
  intro _hproper
  have hvalid' : zvalid ctx pl pr := by
    simpa [zpvalid, mkZ] using hvalid
  change
    zdart G x0 (zshiftR ctx Zhubr (mkZ Zhub pl pr)) =
      qstepR G (zorg G x0 pl)
  rw [zdart_zshiftR_eq_zmove_face_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0 hvalid']
  simpa [zmove] using
    (Hypermap.qstepR_eq_node_node_face_of_plain
      (G := G) hPlain (zorg G x0 pl)).symm

theorem zstepL_zhat_zshiftR_fit_of_face
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {loc : ZPartLoc}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhat pl pr))
    (hgeom :
      qstepL G (zmove G Zhat (zorg G x0 pl)) =
        zmove G loc (G.face (zorg G x0 pl))) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhat pl pr)))
      (zshiftR ctx loc (mkZ Zhat pl pr)) := by
  intro _hproper
  have hvalid' : zvalid ctx pl pr := by
    simpa [zpvalid, mkZ] using hvalid
  change
    zdart G x0 (zshiftR ctx loc (mkZ Zhat pl pr)) =
      qstepL G (zmove G Zhat (zorg G x0 pl))
  rw [zdart_zshiftR_eq_zmove_face_zorg_of_reverse_exact
    (G := G) (ctx := ctx) (x0 := x0) hleft hfit0 hvalid']
  exact hgeom.symm

theorem zstepL_zhat_fit_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zpvalid ctx (mkZ Zhat pl pr)) :
    zpfit G x0
      (qstepL G (zdart G x0 (mkZ Zhat pl pr)))
      (zstepL ctx (mkZ Zhat pl pr)) := by
  have hvalidZ : zvalid ctx pl pr := by
    simpa [zpvalid, mkZ] using hvalid
  cases pr with
  | Pnil =>
      exact zpfit_of_proper_false
        (by simp [zstepL, zshiftR, zfanL, mkZ, ZPart.proper])
  | Pcons s h tail =>
      cases s with
      | Pr55 =>
          have hfitRight :
              Part.fitp G (zorg G x0 pl) (Pcons PRange.Pr55 h tail) =
                true :=
            fitp_right_of_zvalid
              (G := G) (ctx := ctx) (x0 := x0)
              (pl := pl) (pr := Pcons PRange.Pr55 h tail)
              hvalidZ hfit0
          have hspoke : G.arity (G.edge (zorg G x0 pl)) = 5 := by
            have hparts := hfitRight
            simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
            exact hparts.1.1
          have hgeom :
              qstepL G (zmove G Zhat (zorg G x0 pl)) =
                zmove G Zfan0l (G.face (zorg G x0 pl)) := by
            simpa [zmove] using
              qstepL_zhat_eq_leftFan_of_edge_arity
                (G := G) hPlain hCubic 2
                (x := zorg G x0 pl) (by simpa using hspoke)
          simpa [zstepL, zshiftR, zfanL, mkZ] using
            zstepL_zhat_zshiftR_fit_of_face
              (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
              (pr := Pcons PRange.Pr55 h tail) (loc := Zfan0l)
              hleft hfit0 hvalid hgeom
      | Pr66 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr66 h tail)))
      | Pr77 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr77 h tail)))
      | Pr88 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr88 h tail)))
      | Pr99 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr99 h tail)))
      | Pr56 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr56 h tail)))
      | Pr67 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr67 h tail)))
      | Pr78 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr78 h tail)))
      | Pr89 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr89 h tail)))
      | Pr57 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr57 h tail)))
      | Pr68 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr68 h tail)))
      | Pr79 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr79 h tail)))
      | Pr58 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr58 h tail)))
      | Pr69 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr69 h tail)))
      | Pr59 =>
          exact zpfit_of_proper_false
            (by
              simpa [zstepL, zfanL, mkZ] using
                zshiftR_znil_proper_false ctx
                  (mkZ Zhat pl (Pcons PRange.Pr59 h tail)))
  | Pcons6 h f1 tail =>
      have hfitRight :
          Part.fitp G (zorg G x0 pl) (Pcons6 h f1 tail) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons6 h f1 tail) hvalidZ hfit0
      have hspoke : G.arity (G.edge (zorg G x0 pl)) = 6 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1
      have hgeom :
          qstepL G (zmove G Zhat (zorg G x0 pl)) =
            zmove G Zfan1l (G.face (zorg G x0 pl)) := by
        simpa [zmove] using
          qstepL_zhat_eq_leftFan_of_edge_arity
            (G := G) hPlain hCubic 3
            (x := zorg G x0 pl) (by simpa using hspoke)
      simpa [zstepL, zshiftR, zfanL, mkZ] using
        zstepL_zhat_zshiftR_fit_of_face
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
          (pr := Pcons6 h f1 tail) (loc := Zfan1l)
          hleft hfit0 hvalid hgeom
  | Pcons7 h f1 f2 tail =>
      have hfitRight :
          Part.fitp G (zorg G x0 pl) (Pcons7 h f1 f2 tail) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons7 h f1 f2 tail) hvalidZ hfit0
      have hspoke : G.arity (G.edge (zorg G x0 pl)) = 7 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1.1
      have hgeom :
          qstepL G (zmove G Zhat (zorg G x0 pl)) =
            zmove G Zfan2l (G.face (zorg G x0 pl)) := by
        simpa [zmove] using
          qstepL_zhat_eq_leftFan_of_edge_arity
            (G := G) hPlain hCubic 4
            (x := zorg G x0 pl) (by simpa using hspoke)
      simpa [zstepL, zshiftR, zfanL, mkZ] using
        zstepL_zhat_zshiftR_fit_of_face
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
          (pr := Pcons7 h f1 f2 tail) (loc := Zfan2l)
          hleft hfit0 hvalid hgeom
  | Pcons8 h f1 f2 f3 tail =>
      have hfitRight :
          Part.fitp G (zorg G x0 pl) (Pcons8 h f1 f2 f3 tail) = true :=
        fitp_right_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons8 h f1 f2 f3 tail) hvalidZ hfit0
      have hspoke : G.arity (G.edge (zorg G x0 pl)) = 8 := by
        have hparts := hfitRight
        simp [Part.fitp, PRange.contains, SubpartLoc.move] at hparts
        exact hparts.1.1.1.1.1
      have hgeom :
          qstepL G (zmove G Zhat (zorg G x0 pl)) =
            zmove G Zfan3l (G.face (zorg G x0 pl)) := by
        simpa [zmove] using
          qstepL_zhat_eq_leftFan_of_edge_arity
            (G := G) hPlain hCubic 5
            (x := zorg G x0 pl) (by simpa using hspoke)
      simpa [zstepL, zshiftR, zfanL, mkZ] using
        zstepL_zhat_zshiftR_fit_of_face
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl)
          (pr := Pcons8 h f1 f2 f3 tail) (loc := Zfan3l)
          hleft hfit0 hvalid hgeom


end Schematic.Math.GraphTheory.FourColor.RedPart
