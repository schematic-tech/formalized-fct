import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Steps.RightTransitions

/-! Assembly of all zipped-step transition cases. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
theorem zippedStepSound_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    ZippedStepSound G ctx x0 where
  stepL := by
    intro zp hvalid
    rcases zp with ⟨loc, pl, pr⟩
    cases loc with
    | Znil =>
        exact zpfit_of_proper_false (by simp [zstepL, mkZ, ZPart.proper])
    | Zhub =>
        simpa [mkZ] using
          zstepL_zhub_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0
    | Zhubl =>
        simpa [mkZ] using
          zstepL_zhubl_fit (G := G) (ctx := ctx) (x0 := x0)
            (pl := pl) (pr := pr)
    | Zhubr =>
        simpa [mkZ] using
          zstepL_zhubr_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhat =>
        simpa [mkZ] using
          zstepL_zhat_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhatl =>
        simpa [mkZ] using
          zstepL_zhatl_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hfit0 (by simpa [mkZ] using hvalid)
    | Zhatr =>
        simpa [mkZ] using
          zstepL_zhatr_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hCubic
    | Zfan0l =>
        simpa [mkZ] using
          zstepL_zfan0l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan1l =>
        simpa [mkZ] using
          zstepL_zfan1l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan2l =>
        simpa [mkZ] using
          zstepL_zfan2l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan3l =>
        simpa [mkZ] using
          zstepL_zfan3l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan0r =>
        exact zpfit_of_proper_false (by simp [zstepL, mkZ, ZPart.proper])
    | Zfan1r =>
        exact zpfit_of_proper_false (by simp [zstepL, mkZ, ZPart.proper])
    | Zfan2r =>
        exact zpfit_of_proper_false (by simp [zstepL, mkZ, ZPart.proper])
    | Zfan3r =>
        exact zpfit_of_proper_false (by simp [zstepL, mkZ, ZPart.proper])
  stepR := by
    intro zp hvalid
    rcases zp with ⟨loc, pl, pr⟩
    cases loc with
    | Znil =>
        exact zpfit_of_proper_false (by simp [zstepR, mkZ, ZPart.proper])
    | Zhub =>
        simpa [mkZ] using
          zstepR_zhub_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhubl =>
        simpa [mkZ] using
          zstepR_zhubl_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0
    | Zhubr =>
        simpa [mkZ] using
          zstepR_zhubr_fit (G := G) (ctx := ctx) (x0 := x0)
            (pl := pl) (pr := pr)
    | Zhat =>
        simpa [mkZ] using
          zstepR_zhat_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hfit0 (by simpa [mkZ] using hvalid)
    | Zhatl =>
        simpa [mkZ] using
          zstepR_zhatl_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zhatr =>
        simpa [mkZ] using
          zstepR_zhatr_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zfan0l =>
        exact zpfit_of_proper_false (by simp [zstepR, mkZ, ZPart.proper])
    | Zfan1l =>
        exact zpfit_of_proper_false (by simp [zstepR, mkZ, ZPart.proper])
    | Zfan2l =>
        exact zpfit_of_proper_false (by simp [zstepR, mkZ, ZPart.proper])
    | Zfan3l =>
        exact zpfit_of_proper_false (by simp [zstepR, mkZ, ZPart.proper])
    | Zfan0r =>
        simpa [mkZ] using
          zstepR_zfan0r_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0
    | Zfan1r =>
        simpa [mkZ] using
          zstepR_zfan1r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain
    | Zfan2r =>
        simpa [mkZ] using
          zstepR_zfan2r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain
    | Zfan3r =>
        simpa [mkZ] using
          zstepR_zfan3r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain
  stepLt := by
    intro zp hvalid htop
    rcases zp with ⟨loc, pl, pr⟩
    cases loc with
    | Znil =>
        exact zpfit_of_proper_false (by simp [zstepLt, mkZ, ZPart.proper])
    | Zhub =>
        simpa [mkZ] using
          zstepLt_zhub_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0
    | Zhubl =>
        simpa [mkZ] using
          zstepLt_zhubl_fit (G := G) (ctx := ctx) (x0 := x0)
            (pl := pl) (pr := pr)
    | Zhubr =>
        simpa [mkZ] using
          zstepLt_zhubr_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhat =>
        simpa [mkZ] using
          zstepLt_zhat_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhatl =>
        simpa [mkZ] using
          zstepLt_zhatl_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hfit0 (by simpa [mkZ] using hvalid)
            (by simpa [mkZ] using htop)
    | Zhatr =>
        simpa [mkZ] using
          zstepLt_zhatr_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hCubic
    | Zfan0l =>
        simpa [mkZ] using
          zstepLt_zfan0l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan1l =>
        simpa [mkZ] using
          zstepLt_zfan1l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan2l =>
        simpa [mkZ] using
          zstepLt_zfan2l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan3l =>
        simpa [mkZ] using
          zstepLt_zfan3l_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zfan0r =>
        exact zpfit_of_proper_false (by simp [zstepLt, mkZ, ZPart.proper])
    | Zfan1r =>
        exact zpfit_of_proper_false (by simp [zstepLt, mkZ, ZPart.proper])
    | Zfan2r =>
        exact zpfit_of_proper_false (by simp [zstepLt, mkZ, ZPart.proper])
    | Zfan3r =>
        exact zpfit_of_proper_false (by simp [zstepLt, mkZ, ZPart.proper])
  stepRt := by
    intro zp hvalid htop
    rcases zp with ⟨loc, pl, pr⟩
    cases loc with
    | Znil =>
        exact zpfit_of_proper_false (by simp [zstepRt, mkZ, ZPart.proper])
    | Zhub =>
        simpa [mkZ] using
          zstepRt_zhub_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0 (by simpa [mkZ] using hvalid)
    | Zhubl =>
        simpa [mkZ] using
          zstepRt_zhubl_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hleft hfit0
    | Zhubr =>
        simpa [mkZ] using
          zstepRt_zhubr_fit (G := G) (ctx := ctx) (x0 := x0)
            (pl := pl) (pr := pr)
    | Zhat =>
        simpa [mkZ] using
          zstepRt_zhat_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hfit0 (by simpa [mkZ] using hvalid)
    | Zhatl =>
        simpa [mkZ] using
          zstepRt_zhatl_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic
    | Zhatr =>
        simpa [mkZ] using
          zstepRt_zhatr_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0 (by simpa [mkZ] using hvalid)
            (by simpa [mkZ] using htop)
    | Zfan0l =>
        exact zpfit_of_proper_false (by simp [zstepRt, mkZ, ZPart.proper])
    | Zfan1l =>
        exact zpfit_of_proper_false (by simp [zstepRt, mkZ, ZPart.proper])
    | Zfan2l =>
        exact zpfit_of_proper_false (by simp [zstepRt, mkZ, ZPart.proper])
    | Zfan3l =>
        exact zpfit_of_proper_false (by simp [zstepRt, mkZ, ZPart.proper])
    | Zfan0r =>
        simpa [mkZ] using
          zstepRt_zfan0r_fit_of_reverse_exact
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain hCubic hleft hfit0
    | Zfan1r =>
        simpa [mkZ] using
          zstepRt_zfan1r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain
    | Zfan2r =>
        simpa [mkZ] using
          zstepRt_zfan2r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain
    | Zfan3r =>
        simpa [mkZ] using
          zstepRt_zfan3r_fit
            (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
            hPlain


end Schematic.Math.GraphTheory.FourColor.RedPart
