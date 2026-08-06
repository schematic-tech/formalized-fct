import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Fit.Basic

/-! Fit semantics for fan operations. -/

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

open SoundnessInternal

universe u
theorem SoundnessInternal.edgeNode_iter_eq_face_symm_iter
    {G : Hypermap.{u}} (n : Nat) (x : G.Dart) :
    ((fun y : G.Dart => G.edge (G.node y))^[n]) x =
      ((G.face.symm : G.Dart → G.Dart)^[n]) x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [Function.iterate_succ_apply']
      exact Hypermap.edge_node_eq_face_symm (G := G) _

private theorem arity_zmove_leftFan_eq
    {G : Hypermap.{u}} (hPlain : G.Plain) {n m : Nat} {x : G.Dart}
    (hspoke : G.arity (SubpartLoc.move SubpartLoc.Pspoke G x) = m)
    (hn : n ≤ m) :
    G.arity
        (G.face
          (G.edge
            (((fun y : G.Dart => G.edge (G.node y))^[n])
              (G.node (G.face x))))) =
      G.arity
        (G.edge (((G.face : G.Dart → G.Dart)^[m - n]) (G.edge x))) := by
  have hspoke' : G.arity (G.edge x) = m := by
    simpa [SubpartLoc.move] using hspoke
  have hn' : n ≤ G.arity (G.edge x) := by
    rw [hspoke']
    exact hn
  rw [Hypermap.arity_face]
  rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain x]
  rw [edgeNode_iter_eq_face_symm_iter (G := G) n (G.edge x)]
  rw [Hypermap.face_symm_iter_eq_face_iter_sub_arity (G := G)
    (x := G.edge x) (n := n) hn']
  rw [hspoke']

theorem redPoplFan1l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan1l pl) qa = true)
    (hred : redPoplFan1l ctx pl pr = true) :
    G.arity (zmove G Zfan1l (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan1l, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan1l, fitQa] at hfit
  | Pcons6 h f1 tail =>
      have hvalid' : zvalid ctx tail (Pcons6 h f1 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons6 h f1 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons6 h f1 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 6 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons6 h r p') (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP6f1 h) hfit
          (by simpa [redPoplFan1l] using hred)
      have hzorg :
          zorg G x0 (Pcons6 h f1 tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[3])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 3) (m := 6)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons7 h f1 f2 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons7 h f1 f2 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 7 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons7 h f1 r p') (j := SubpartLoc.Pfan2)
          (r := f2) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP7f2 h f1) hfit
          (by simpa [redPoplFan1l] using hred)
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[3])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 3) (m := 7)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons8 h f1 f2 f3 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons8 h f1 f2 f3 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 8 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan3 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h f1 f2 r p')
          (j := SubpartLoc.Pfan3)
          (r := f3) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f3 h f1 f2) hfit
          (by simpa [redPoplFan1l] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[3])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 3) (m := 8)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore

theorem redPoplFan2l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan2l pl) qa = true)
    (hred : redPoplFan2l ctx pl pr = true) :
    G.arity (zmove G Zfan2l (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan2l, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan2l, fitQa] at hfit
  | Pcons6 h f1 tail =>
      simp [Part.getFan2l, fitQa] at hfit
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons7 h f1 f2 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons7 h f1 f2 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 7 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons7 h r f2 p') (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP7f1 h f2) hfit
          (by simpa [redPoplFan2l] using hred)
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[4])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 4) (m := 7)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons8 h f1 f2 f3 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons8 h f1 f2 f3 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 8 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h f1 r f3 p')
          (j := SubpartLoc.Pfan2)
          (r := f2) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f2 h f1 f3) hfit
          (by simpa [redPoplFan2l] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[4])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 4) (m := 8)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore

theorem redPoplFan3l_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan3l pl) qa = true)
    (hred : redPoplFan3l ctx pl pr = true) :
    G.arity (zmove G Zfan3l (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan3l, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan3l, fitQa] at hfit
  | Pcons6 h f1 tail =>
      simp [Part.getFan3l, fitQa] at hfit
  | Pcons7 h f1 f2 tail =>
      simp [Part.getFan3l, fitQa] at hfit
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons8 h f1 f2 f3 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons8 h f1 f2 f3 pr) hvalid' hfit0
      have hspoke :
          G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 tail)) = 8 := by
          have hparts := hfitRight
          simp [Part.fitp, PRange.contains] at hparts
          exact hparts.1.1.1.1.1
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h r f2 f3 p')
          (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f1 h f2 f3) hfit
          (by simpa [redPoplFan3l] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      change
        G.arity
            (G.face
              (G.edge
                (((fun y : G.Dart => G.edge (G.node y))^[5])
                  (G.node (G.face (zorg G x0 tail)))))) = qa.toNat
      rw [arity_zmove_leftFan_eq (G := G) hPlain (n := 5) (m := 8)
        (x := zorg G x0 tail) hspoke (by omega)]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore

theorem redPoplFan1r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan1r pl) qa = true)
    (hred : redPoplFan1r ctx pl pr = true) :
    G.arity (zmove G Zfan1r (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan1r, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan1r, fitQa] at hfit
  | Pcons6 h f1 tail =>
      have hvalid' : zvalid ctx tail (Pcons6 h f1 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons6 h r p') (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP6f1 h) hfit
          (by simpa [redPoplFan1r] using hred)
      have hzorg :
          zorg G x0 (Pcons6 h f1 tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan1r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons7 h r f2 p') (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP7f1 h f2) hfit
          (by simpa [redPoplFan1r] using hred)
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan1r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h r f2 f3 p')
          (j := SubpartLoc.Pfan1)
          (r := f1) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f1 h f2 f3) hfit
          (by simpa [redPoplFan1r] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan1r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore

theorem redPoplFan2r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan2r pl) qa = true)
    (hred : redPoplFan2r ctx pl pr = true) :
    G.arity (zmove G Zfan2r (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan2r, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan2r, fitQa] at hfit
  | Pcons6 h f1 tail =>
      simp [Part.getFan2r, fitQa] at hfit
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons7 h f1 r p') (j := SubpartLoc.Pfan2)
          (r := f2) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP7f2 h f1) hfit
          (by simpa [redPoplFan2r] using hred)
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan2r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h f1 r f3 p')
          (j := SubpartLoc.Pfan2)
          (r := f2) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f2 h f1 f3) hfit
          (by simpa [redPoplFan2r] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan2r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore

theorem redPoplFan3r_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getFan3r pl) qa = true)
    (hred : redPoplFan3r ctx pl pr = true) :
    G.arity (zmove G Zfan3r (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getFan3r, fitQa] at hfit
  | Pcons s h tail =>
      simp [Part.getFan3r, fitQa] at hfit
  | Pcons6 h f1 tail =>
      simp [Part.getFan3r, fitQa] at hfit
  | Pcons7 h f1 f2 tail =>
      simp [Part.getFan3r, fitQa] at hfit
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pfan3 G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 h f1 f2 r p')
          (j := SubpartLoc.Pfan3)
          (r := f3) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8f3 h f1 f2) hfit
          (by simpa [redPoplFan3r] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, zmove_zfan3r,
        Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore


end Schematic.Math.GraphTheory.FourColor.RedPart
