import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Fit.Locations

/-! Root-soundness assembly for redpart fitting. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

open SoundnessInternal

universe u
theorem redPop_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    {zp : ZPart} {qa : QArity}
    (hvalid : zpvalid ctx zp)
    (hfit : fitQa (zrange ctx zp) qa = true)
    (hred : redPop ctx zp = true) :
    G.arity (zdart G x0 zp) = qa.toNat := by
  rcases zp with ⟨loc, pl, pr⟩
  have hvalid' : zvalid ctx pl pr := by
    simpa [zpvalid] using hvalid
  cases loc with
  | Znil =>
      exact False.elim
        (false_of_fitQa_zrange_znil
          (ctx := ctx) (pl := pl) (pr := pr) (qa := qa)
          (by simpa [mkZ] using hfit))
  | Zhub =>
      simpa [mkZ] using
        redPop_fit_zhub
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hx0 (by simpa [mkZ] using hfit)
  | Zhubl =>
      simpa [mkZ] using
        redPop_fit_zhubl
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zhubr =>
      simpa [mkZ] using
        redPop_fit_zhubr
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hCubic hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zhat =>
      simpa [mkZ] using
        redPop_fit_zhat
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hCubic hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zhatl =>
      simpa [mkZ] using
        redPop_fit_zhatl
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zhatr =>
      simpa [mkZ] using
        redPop_fit_zhatr
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hCubic hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan0l =>
      simpa [mkZ] using
        redPop_fit_zfan0l
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hCubic hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan1l =>
      simpa [mkZ] using
        redPop_fit_zfan1l
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan2l =>
      simpa [mkZ] using
        redPop_fit_zfan2l
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan3l =>
      simpa [mkZ] using
        redPop_fit_zfan3l
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan0r =>
      simpa [mkZ] using
        redPop_fit_zfan0r
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan1r =>
      simpa [mkZ] using
        redPop_fit_zfan1r
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan2r =>
      simpa [mkZ] using
        redPop_fit_zfan2r
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)
  | Zfan3r =>
      simpa [mkZ] using
        redPop_fit_zfan3r
          (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
          (qa := qa) hPlain hNoRedRec hx0 hvalid' hfit0
          (by simpa [mkZ] using hfit)
          (by simpa [mkZ] using hred)

theorem zippedRootSound_of_noRedRec
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    ZippedRootSound G ctx x0 := by
  intro zp qa hvalid hfit hred
  exact redPop_fit
    (G := G) (ctx := ctx) (x0 := x0)
    hPlain hCubic hNoRedRec hx0 hfit0 hvalid hfit hred


end Schematic.Math.GraphTheory.FourColor.RedPart
