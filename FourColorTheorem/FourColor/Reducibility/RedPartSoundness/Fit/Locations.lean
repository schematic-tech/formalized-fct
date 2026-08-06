import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Fit.Fans

/-! Fit semantics for zipped-part locations. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

open SoundnessInternal

universe u
theorem redPop_fit_zhubl
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zhubl pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zhubl pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zhubl pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg, zmove] using
    redPoplSpoke_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zhub
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit : fitQa (zrange ctx (mkZ Zhub pl pr)) qa = true) :
    G.arity (zdart G x0 (mkZ Zhub pl pr)) = qa.toNat := by
  have hhub : ctx.ahub.toNat = qa.toNat :=
    hubRange_fitQa_eq (ahub := ctx.ahub) (qa := qa)
      (by simpa [mkZ, zrange] using hfit)
  have hzorg : G.arity (zorg G x0 pl) = ctx.nhub := by
    rw [zorg, Hypermap.arity_face_iter]
    exact hx0
  simpa [mkZ, zdart, zporg, zmove, Context.nhub, hhub] using hzorg

theorem false_of_fitQa_zrange_znil
    {ctx : Context} {pl pr : Part} {qa : QArity}
    (hfit : fitQa (zrange ctx (mkZ Znil pl pr)) qa = true) :
    False := by
  simp [mkZ, zrange, fitQa_Pr59_false qa] at hfit

theorem SoundnessInternal.arity_zmove_zhatl_eq_node
    {G : Hypermap.{u}} (x : G.Dart) :
    G.arity (zmove G Zhatl x) = G.arity (G.node x) := by
  simp [zmove]
  rw [← Hypermap.arity_face (G := G) (G.edge (G.node (G.node x)))]
  rw [G.face_edge_node]

theorem SoundnessInternal.arity_zmove_zhatr_eq_edge_of_cubic
    {G : Hypermap.{u}} (hCubic : G.Cubic) (x : G.Dart) :
    G.arity (zmove G Zhatr x) = G.arity (G.edge x) := by
  simp [zmove]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
  rw [Hypermap.arity_face]
  rw [Hypermap.arity_face]

private theorem arity_zmove_zhat_eq_phat
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (zmove G Zhat x) =
      G.arity (SubpartLoc.move SubpartLoc.Phat G x) := by
  simp [zmove]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
  rw [show G.edge (G.face (G.edge x)) =
      G.node (G.face (G.face (G.edge x))) by
    exact (Hypermap.Plain.node_face_eq_edge (G := G) hPlain
      (G.face (G.edge x))).symm]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic
    (G.face (G.face (G.edge x)))]
  rw [Hypermap.arity_face]
  rfl

private theorem arity_zmove_zfan0l_eq_zhat
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.arity (zmove G Zfan0l x) = G.arity (zmove G Zhat x) := by
  simp [zmove, Function.iterate_succ_apply,
    Hypermap.Plain.edge_edge (G := G) hPlain, Hypermap.arity_face]

theorem redPop_fit_zhatl
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zhatl pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zhatl pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zhatl pl pr)) = qa.toNat := by
  have hcore : G.arity (G.node (zorg G x0 pl)) = qa.toNat :=
    redPoplSpoke_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0
      (by simpa [mkZ, zrange] using hfit)
      (by simpa [mkZ, redPop] using hred)
  simpa [mkZ, zdart, zporg, arity_zmove_zhatl_eq_node] using hcore

theorem redPop_fit_zhat
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zhat pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zhat pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zhat pl pr)) = qa.toNat := by
  have hcore :
      G.arity (SubpartLoc.move SubpartLoc.Phat G (zorg G x0 pl)) =
        qa.toNat :=
    redPoprHat_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hNoRedRec hx0 hvalid hfit0
      (by simpa [mkZ, zrange] using hfit)
      (by simpa [mkZ, redPop] using hred)
  rw [mkZ, zdart, zporg]
  rw [arity_zmove_zhat_eq_phat (G := G) hPlain hCubic]
  exact hcore

theorem redPop_fit_zhubr
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zhubr pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zhubr pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zhubr pl pr)) = qa.toNat := by
  have hcore :
      G.arity (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 pl)) =
        qa.toNat :=
    redPoprSpoke_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hNoRedRec hx0 hvalid hfit0
      (by simpa [mkZ, zrange] using hfit)
      (by simpa [mkZ, redPop] using hred)
  simp [mkZ, zdart, zporg, zmove]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic]
  rw [Hypermap.arity_face]
  simpa [SubpartLoc.move] using hcore

theorem redPop_fit_zhatr
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zhatr pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zhatr pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zhatr pl pr)) = qa.toNat := by
  have hcore :
      G.arity (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 pl)) =
        qa.toNat :=
    redPoprSpoke_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hNoRedRec hx0 hvalid hfit0
      (by simpa [mkZ, zrange] using hfit)
      (by simpa [mkZ, redPop] using hred)
  simp [mkZ, zdart, zporg, zmove]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic]
  rw [Hypermap.arity_face]
  rw [Hypermap.arity_face]
  simpa [SubpartLoc.move] using hcore

theorem redPop_fit_zfan0r
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan0r pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan0r pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan0r pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
      redPoplHat_fit_zfan0r
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan0l
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan0l pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan0l pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan0l pl pr)) = qa.toNat := by
  have hhat :
      G.arity (zdart G x0 (mkZ Zhat pl pr)) = qa.toNat :=
    redPop_fit_zhat
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hCubic hNoRedRec hx0 hvalid hfit0
      (by simpa [mkZ, zrange] using hfit)
      (by simpa [mkZ, redPop] using hred)
  have hloc :
      G.arity (zdart G x0 (mkZ Zfan0l pl pr)) =
        G.arity (zdart G x0 (mkZ Zhat pl pr)) := by
    simpa [mkZ, zdart, zporg] using
      arity_zmove_zfan0l_eq_zhat
        (G := G) hPlain (zorg G x0 pl)
  exact hloc.trans hhat

theorem redPop_fit_zfan1l
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan1l pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan1l pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan1l pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan1l_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan2l
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan2l pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan2l pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan2l pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan2l_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan3l
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan3l pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan3l pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan3l pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan3l_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan1r
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan1r pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan1r pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan1r pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan1r_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan2r
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan2r pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan2r pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan2r pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan2r_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred

theorem redPop_fit_zfan3r
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (zrange ctx (mkZ Zfan3r pl pr)) qa = true)
    (hred : redPop ctx (mkZ Zfan3r pl pr) = true) :
    G.arity (zdart G x0 (mkZ Zfan3r pl pr)) = qa.toNat := by
  simpa [mkZ, zrange, redPop, zdart, zporg] using
    redPoplFan3r_fit
      (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
      (qa := qa) hPlain hNoRedRec hx0 hvalid hfit0 hfit hred


end Schematic.Math.GraphTheory.FourColor.RedPart
