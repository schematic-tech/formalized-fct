import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.SoundnessInternal.FanCoordinates

/-! Coordinate identities for zipped-part transitions. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

namespace SoundnessInternal
theorem qstepL_zhat_eq_leftFan_of_edge_arity
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (n : Nat) {x : G.Dart}
    (hspoke : G.arity (G.edge x) = n + 3) :
    qstepL G (zmove G Zhat x) =
      G.face
        (G.edge
          (((fun y : G.Dart => G.edge (G.node y))^[n])
            (G.node (G.face x)))) := by
  have hsymm :
      ((G.face.symm : G.Dart → G.Dart)^[n]) (G.edge x) =
        ((G.face : G.Dart → G.Dart)^[3]) (G.edge x) := by
    have h := Hypermap.face_symm_iter_eq_face_iter_sub_arity
      (G := G) (x := G.edge x) (n := n) (by omega)
    have hsub : G.arity (G.edge x) - n = 3 := by omega
    rw [h, hsub]
  calc
    qstepL G (zmove G Zhat x)
        = G.node
            (G.edge (((G.face : G.Dart → G.Dart)^[2]) (G.edge x))) := by
          change
            G.node
                (G.edge
                  (G.node (G.node (G.edge (G.node (G.node x)))))) =
              G.node (G.edge (G.face (G.face (G.edge x))))
          rw [Hypermap.Cubic.node_node_eq_face_edge
            (G := G) hCubic (G.edge (G.node (G.node x)))]
          rw [Hypermap.Plain.edge_edge (G := G) hPlain]
          rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic x]
    _ = G.face
            (G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.edge x))) := by
          simpa [Function.iterate_succ_apply] using
            node_edge_eq_face_edge_face_of_plain_cubic
              (G := G) hPlain hCubic
              (((G.face : G.Dart → G.Dart)^[2]) (G.edge x))
    _ = G.face
            (G.edge (((G.face.symm : G.Dart → G.Dart)^[n]) (G.edge x))) := by
          rw [hsymm]
    _ = G.face
          (G.edge
            (((fun y : G.Dart => G.edge (G.node y))^[n])
              (G.node (G.face x)))) := by
          rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
          rw [edgeNode_iter_eq_face_symm_iter (G := G) n (G.edge x)]

theorem qstepR_zhatr_eq_qstepL_zhat_of_plain_cubic
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    qstepR G (zmove G Zhatr x) = qstepL G (zmove G Zhat x) := by
  change
    G.node (G.edge (G.face (G.node (G.node x)))) =
      G.node
        (G.edge
          (G.node (G.node (G.edge (G.node (G.node x))))))
  rw [Hypermap.Cubic.node_node_eq_face_edge
    (G := G) hCubic (G.edge (G.node (G.node x)))]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]

theorem zpfit_of_proper_false
    {G : Hypermap.{u}} {x0 x : G.Dart} {zp : ZPart}
    (hproper : zp.proper = false) :
    zpfit G x0 x zp := by
  intro hz
  rw [hz] at hproper
  cases hproper

theorem zshiftR_znil_proper_false
    (ctx : Context) (zp : ZPart) :
    (zshiftR ctx Znil zp).proper = false := by
  simpa [locProper] using zshiftR_proper ctx Znil zp

theorem mkZ_zshiftR_left_right_eq
    (ctx : Context) (loc loc' : ZPartLoc) (zp : ZPart) :
    mkZ loc (zshiftR ctx loc' zp).left (zshiftR ctx loc' zp).right =
      zshiftR ctx loc zp := by
  rcases zp with ⟨loc0, pl, pr⟩
  cases pr with
  | Pnil => rfl
  | Pcons s h tail => cases tail <;> rfl
  | Pcons6 h f1 tail => cases tail <;> rfl
  | Pcons7 h f1 f2 tail => cases tail <;> rfl
  | Pcons8 h f1 f2 f3 tail => cases tail <;> rfl

theorem zshiftR_mkZ_loc_eq
    (ctx : Context) (loc loc₁ loc₂ : ZPartLoc) (pl pr : Part) :
    zshiftR ctx loc (mkZ loc₁ pl pr) =
      zshiftR ctx loc (mkZ loc₂ pl pr) := by
  cases pr with
  | Pnil => rfl
  | Pcons s h tail => cases tail <;> rfl
  | Pcons6 h f1 tail => cases tail <;> rfl
  | Pcons7 h f1 f2 tail => cases tail <;> rfl
  | Pcons8 h f1 f2 f3 tail => cases tail <;> rfl

theorem zshiftR_left_pcons6_of_tail_ne_nil
    {ctx : Context} {loc : ZPartLoc} {pl tail : Part} {h f1 : PRange}
    (htail : tail ≠ Pnil) :
    (zshiftR ctx loc (mkZ Zhub pl (Pcons6 h f1 tail))).left =
      Pcons6 h f1 pl := by
  cases tail <;> simp [zshiftR, mkZ] at htail ⊢

theorem zshiftR_left_pcons7_of_tail_ne_nil
    {ctx : Context} {loc : ZPartLoc} {pl tail : Part}
    {h f1 f2 : PRange}
    (htail : tail ≠ Pnil) :
    (zshiftR ctx loc (mkZ Zhub pl (Pcons7 h f1 f2 tail))).left =
      Pcons7 h f1 f2 pl := by
  cases tail <;> simp [zshiftR, mkZ] at htail ⊢

theorem zshiftR_left_pcons8_of_tail_ne_nil
    {ctx : Context} {loc : ZPartLoc} {pl tail : Part}
    {h f1 f2 f3 : PRange}
    (htail : tail ≠ Pnil) :
    (zshiftR ctx loc (mkZ Zhub pl (Pcons8 h f1 f2 f3 tail))).left =
      Pcons8 h f1 f2 f3 pl := by
  cases tail <;> simp [zshiftR, mkZ] at htail ⊢

theorem zshiftR_zhub_eq_shiftPart_drop_of_size_gt_one
    {ctx : Context} {pl pr : Part}
    (hsize : 1 < Part.size pr) :
    zshiftR ctx Zhub (mkZ Zhub pl pr) =
      mkZ Zhub (shiftPart pr pl) (Part.drop 1 pr) := by
  cases pr with
  | Pnil =>
      simp [Part.size] at hsize
  | Pcons s h tail =>
      cases tail <;> simp [Part.size, zshiftR, mkZ, shiftPart, Part.take,
        Part.drop, Part.append] at hsize ⊢
  | Pcons6 h f1 tail =>
      cases tail <;> simp [Part.size, zshiftR, mkZ, shiftPart, Part.take,
        Part.drop, Part.append] at hsize ⊢
  | Pcons7 h f1 f2 tail =>
      cases tail <;> simp [Part.size, zshiftR, mkZ, shiftPart, Part.take,
        Part.drop, Part.append] at hsize ⊢
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;> simp [Part.size, zshiftR, mkZ, shiftPart, Part.take,
        Part.drop, Part.append] at hsize ⊢

theorem mkZ_zshiftL_left_right_eq
    (ctx : Context) (loc loc' : ZPartLoc) (zp : ZPart) :
    mkZ loc (zshiftL ctx loc' zp).left (zshiftL ctx loc' zp).right =
      zshiftL ctx loc zp := by
  rcases zp with ⟨loc0, pl, pr⟩
  cases pl with
  | Pnil => rfl
  | Pcons s h tail => cases tail <;> rfl
  | Pcons6 h f1 tail => cases tail <;> rfl
  | Pcons7 h f1 f2 tail => cases tail <;> rfl
  | Pcons8 h f1 f2 f3 tail => cases tail <;> rfl

theorem zorg_p0l_eq_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zorg G x0 ctx.p0l = x0 := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hsize : Part.size ctx.p0l = G.arity x0 := by
    rw [hleft, Part.size_reverse]
    exact hparts.1.symm
  simpa [zorg, hsize] using G.face_iterate_arity x0

theorem zorg_drop_one_p0l_eq_face_symm_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zorg G x0 (Part.drop 1 ctx.p0l) = G.face.symm x0 := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hsize : Part.size ctx.p0l = G.arity x0 := by
    rw [hleft, Part.size_reverse]
    exact hparts.1.symm
  have hsucc :
      G.arity x0 = Part.size (Part.drop 1 ctx.p0l) + 1 := by
    rw [Part.size_drop, hsize]
    have hpos := Hypermap.arity_pos (G := G) x0
    omega
  simpa [zorg] using
    Part.face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x0) (n := Part.size (Part.drop 1 ctx.p0l))
      hsucc

theorem face_iterate_two_arity_eq_self
    {G : Hypermap.{u}} (x : G.Dart) :
    ((G.face : G.Dart → G.Dart)^[2 * G.arity x]) x = x := by
  rw [show 2 * G.arity x = G.arity x + G.arity x by omega]
  rw [Function.iterate_add_apply, G.face_iterate_arity, G.face_iterate_arity]

theorem face_iterate_two_arity_pred_eq_face_symm
    {G : Hypermap.{u}} (x : G.Dart) :
    ((G.face : G.Dart → G.Dart)^[2 * G.arity x - 1]) x =
      G.face.symm x := by
  have hpos := Hypermap.arity_pos (G := G) x
  have hsplit : 2 * G.arity x - 1 = (G.arity x - 1) + G.arity x := by
    omega
  have hsucc : G.arity x = (G.arity x - 1) + 1 := by
    omega
  rw [hsplit, Function.iterate_add_apply, G.face_iterate_arity]
  exact Part.face_iterate_pred_eq_face_symm_of_arity_succ
    (G := G) (x := x) (n := G.arity x - 1) hsucc

theorem zorg_shiftPart_p0r_p0l_eq_face_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zorg G x0 (shiftPart ctx.p0r ctx.p0l) = G.face x0 := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hp0size : Part.size ctx.p0r = G.arity x0 := hparts.1.symm
  have hleftSize : Part.size ctx.p0l = G.arity x0 := by
    rw [hleft, Part.size_reverse, hp0size]
  have htake : Part.size (Part.take 1 ctx.p0r) = 1 := by
    exact Part.size_take_of_le (p := ctx.p0r)
      (by simpa [hp0size] using Hypermap.arity_pos (G := G) x0)
  have hsize :
      Part.size (shiftPart ctx.p0r ctx.p0l) = G.arity x0 + 1 := by
    simp [shiftPart, Part.size_append, htake, hleftSize]
    omega
  rw [zorg, hsize]
  rw [show G.arity x0 + 1 = 1 + G.arity x0 by omega]
  rw [Function.iterate_add_apply, G.face_iterate_arity]
  rfl

theorem zorg_of_zvalid_nil_right_eq_self
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl : Part}
    (hvalid : zvalid ctx pl Part.Pnil)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zorg G x0 pl = x0 := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hp0size : Part.size ctx.p0r = G.arity x0 := hparts.1.symm
  have hvalidSize := zvalid_size (ctx := ctx) (pl := pl)
    (pr := Part.Pnil) hvalid
  have hpl : Part.size pl = 2 * G.arity x0 := by
    simp [Part.size] at hvalidSize
    omega
  simpa [zorg, hpl] using face_iterate_two_arity_eq_self (G := G) x0

theorem zorg_of_zvalid_singleton_right_eq_face_symm
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hpr : Part.size pr = 1)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true) :
    zorg G x0 pl = G.face.symm x0 := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hp0size : Part.size ctx.p0r = G.arity x0 := hparts.1.symm
  have hvalidSize := zvalid_size (ctx := ctx) (pl := pl)
    (pr := pr) hvalid
  have hpl : Part.size pl = 2 * G.arity x0 - 1 := by
    omega
  simpa [zorg, hpl] using
    face_iterate_two_arity_pred_eq_face_symm (G := G) x0

private theorem zdart_zshiftR_of_right_ne_nil
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (loc loc' : ZPartLoc) (hne : pr ≠ Part.Pnil) :
    zdart G x0 (zshiftR ctx loc (mkZ loc' pl pr)) =
      if pr.size = 1 then
        zmove G loc (zorg G x0 ctx.p0l)
      else
        zmove G loc (G.face (zorg G x0 pl)) := by
  cases pr with
  | Pnil => exact False.elim (hne rfl)
  | Pcons s h tail =>
      cases tail <;>
        simp [zshiftR, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons6 h f1 tail =>
      cases tail <;>
        simp [zshiftR, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons7 h f1 f2 tail =>
      cases tail <;>
        simp [zshiftR, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;>
        simp [zshiftR, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']

/-- Moving the zipper one sector to the right advances its geometric origin
by one face step.  The wrap and singleton cases are discharged from the
reference part; every other constructor is the same sequence operation. -/
theorem zdart_zshiftR_eq_zmove_face_zorg_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalid : zvalid ctx pl pr)
    (loc loc' : ZPartLoc) :
    zdart G x0 (zshiftR ctx loc (mkZ loc' pl pr)) =
      zmove G loc (G.face (zorg G x0 pl)) := by
  by_cases hnil : pr = Part.Pnil
  · subst pr
    have hsource : zorg G x0 pl = x0 :=
      zorg_of_zvalid_nil_right_eq_self
        (G := G) (ctx := ctx) (x0 := x0) (pl := pl) hvalid hfit0
    have htarget :
        zorg G x0 (shiftPart ctx.p0r ctx.p0l) = G.face x0 :=
      zorg_shiftPart_p0r_p0l_eq_face_of_reverse_exact
        (G := G) (ctx := ctx) (x0 := x0) hleft hfit0
    simpa [zshiftR, mkZ, zdart, zporg, hsource] using
      congrArg (zmove G loc) htarget
  · rw [zdart_zshiftR_of_right_ne_nil loc loc' hnil]
    split
    next hsize =>
      have hsource : zorg G x0 pl = G.face.symm x0 :=
        zorg_of_zvalid_singleton_right_eq_face_symm
          (G := G) (ctx := ctx) (x0 := x0) hsize hvalid hfit0
      have hroot : zorg G x0 ctx.p0l = x0 :=
        zorg_p0l_eq_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0) hleft hfit0
      simp [hsource, hroot]
    next _ => rfl

private theorem zdart_zshiftL_of_left_ne_nil
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (loc loc' : ZPartLoc) (hne : pl ≠ Part.Pnil) :
    zdart G x0 (zshiftL ctx loc (mkZ loc' pl pr)) =
      if pl.size = 1 then
        zmove G loc (zorg G x0 ctx.p0l)
      else
        zmove G loc (G.face.symm (zorg G x0 pl)) := by
  cases pl with
  | Pnil => exact False.elim (hne rfl)
  | Pcons s h tail =>
      cases tail <;>
        simp [zshiftL, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons6 h f1 tail =>
      cases tail <;>
        simp [zshiftL, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons7 h f1 f2 tail =>
      cases tail <;>
        simp [zshiftL, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;>
        simp [zshiftL, mkZ, zdart, zporg, zorg, Part.size,
          Function.iterate_succ_apply']

/-- Moving the zipper one sector to the left moves its geometric origin one
face step backwards. -/
theorem zdart_zshiftL_eq_zmove_face_symm_zorg_of_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (loc loc' : ZPartLoc) :
    zdart G x0 (zshiftL ctx loc (mkZ loc' pl pr)) =
      zmove G loc (G.face.symm (zorg G x0 pl)) := by
  by_cases hnil : pl = Part.Pnil
  · subst pl
    have hprev :
        zorg G x0 (Part.drop 1 ctx.p0l) = G.face.symm x0 :=
      zorg_drop_one_p0l_eq_face_symm_of_reverse_exact
        (G := G) (ctx := ctx) (x0 := x0) hleft hfit0
    simpa [zshiftL, mkZ, zdart, zporg, zorg] using
      congrArg (zmove G loc) hprev
  · rw [zdart_zshiftL_of_left_ne_nil loc loc' hnil]
    split
    next hsize =>
      have hsource : zorg G x0 pl = G.face x0 := by
        simp [zorg, hsize]
      have hroot : zorg G x0 ctx.p0l = x0 :=
        zorg_p0l_eq_of_reverse_exact
          (G := G) (ctx := ctx) (x0 := x0) hleft hfit0
      simp [hsource, hroot]
    next _ => rfl


end SoundnessInternal

end Schematic.Math.GraphTheory.FourColor.RedPart
