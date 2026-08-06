import FourColorTheorem.FourColor.Reducibility.RedPart
import FourColorTheorem.FourColor.Discharging.PartGeometry

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

namespace SoundnessInternal
end SoundnessInternal

open SoundnessInternal

universe u
theorem fitp_append_self_of_exactFitp
    {G : Hypermap} {x : G.Dart} {p : Part}
    (hfit : Part.exactFitp G x p = true) :
    Part.fitp G x (Part.append p p) = true := by
  have hparts := hfit
  simp [Part.exactFitp] at hparts
  have harity : G.arity x = Part.size p := hparts.1
  have hfitp : Part.fitp G x p = true := hparts.2
  rw [Part.fitp_append]
  rw [Bool.and_eq_true]
  constructor
  · exact hfitp
  · have hcycle :
        Part.fitp G ((G.face : G.Dart → G.Dart)^[Part.size p] x) p =
          Part.fitp G x p :=
      Part.fitp_face_iterate_arity_eq
        (G := G) (p := p) (x := x) (n := Part.size p) harity
    rw [hcycle]
    exact hfitp

theorem exactFitp_take_of_fitp_of_arity_eq_of_size_le
    {G : Hypermap} {x : G.Dart} {p : Part} {n : Nat}
    (hfit : Part.fitp G x p = true)
    (harity : G.arity x = n)
    (hle : n ≤ Part.size p) :
    Part.exactFitp G x (Part.take n p) = true := by
  have htakefit : Part.fitp G x (Part.take n p) = true :=
    Part.fitp_take_of_eq_true (G := G) n p x hfit
  have hsizetake : Part.size (Part.take n p) = n :=
    Part.size_take_of_le hle
  simp [Part.exactFitp, harity, hsizetake, htakefit]

theorem exactFitp_redPcons_residual_of_fitp_append
    {G : Hypermap} {ctx : Context} {pc : PRange → Part → Part}
    {r : PRange} {pr : Part} {y : G.Dart}
    (hfit :
      Part.fitp G y
        (Part.append (pc (popQa r) pr) ctx.p0r) = true)
    (hy : G.arity y = ctx.nhub)
    (hp0size : Part.size ctx.p0r = ctx.nhub) :
    Part.exactFitp G y
      (Part.take ctx.nhub
        (Part.append (pc (popQa r) pr) ctx.p0r)) = true := by
  have hle :
      ctx.nhub ≤ Part.size (Part.append (pc (popQa r) pr) ctx.p0r) := by
    simp [Part.size_append, hp0size]
  exact exactFitp_take_of_fitp_of_arity_eq_of_size_le
    (G := G) (x := y)
    (p := Part.append (pc (popQa r) pr) ctx.p0r)
    (n := ctx.nhub) hfit hy hle

theorem redPcons_not_rec_of_fitp_append
    {G : Hypermap} {ctx : Context} {pc : PRange → Part → Part}
    {r : PRange} {pr : Part} {y : G.Dart} {n : Nat}
    (hNoRedRec : NoRedRec G ctx)
    (hy : G.arity y = ctx.nhub)
    (hp0size : Part.size ctx.p0r = ctx.nhub)
    (hfit :
      PRange.contains (popQa r) n = true →
        Part.fitp G y
          (Part.append (pc (popQa r) pr) ctx.p0r) = true) :
    PRange.contains (popQa r) n = true →
      ctx.redRec
        (Part.take ctx.nhub
          (Part.append (pc (popQa r) pr) ctx.p0r)) = false :=
  redPcons_not_rec_of_exactFit
    (G := G) (ctx := ctx) (pc := pc) (r := r) (pr := pr)
    (y := y) (n := n) hNoRedRec hy
    (fun hcontains =>
      exactFitp_redPcons_residual_of_fitp_append
        (G := G) (ctx := ctx) (pc := pc) (r := r) (pr := pr)
        (y := y) (hfit hcontains) hy hp0size)

theorem fitp_append_popped_of_update_tail
    {G : Hypermap.{u}} {ctx : Context} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {y : G.Dart}
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G y (pc r pr) = true)
    (hcontains :
      PRange.contains (popQa r)
        (G.arity (SubpartLoc.move j G y)) = true)
    (htail :
      Part.fitp G
        ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)] y)
        ctx.p0r = true) :
    Part.fitp G y (Part.append (pc (popQa r) pr) ctx.p0r) = true := by
  have hhead : Part.fitp G y (pc (popQa r) pr) = true :=
    fitp_popped_of_update
      (G := G) (pc := pc) (j := j) (r := r) (pr := pr) (x := y)
      hupdate hfitpc hcontains
  rw [Part.fitp_append]
  simp [hhead, htail]

theorem redPcons_not_rec_of_update_tail
    {G : Hypermap.{u}} {ctx : Context} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {y : G.Dart}
    (hNoRedRec : NoRedRec G ctx)
    (hy : G.arity y = ctx.nhub)
    (hp0size : Part.size ctx.p0r = ctx.nhub)
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G y (pc r pr) = true)
    (htail :
      PRange.contains (popQa r)
          (G.arity (SubpartLoc.move j G y)) = true →
        Part.fitp G
          ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)] y)
          ctx.p0r = true) :
    PRange.contains (popQa r)
        (G.arity (SubpartLoc.move j G y)) = true →
      ctx.redRec
        (Part.take ctx.nhub
          (Part.append (pc (popQa r) pr) ctx.p0r)) = false :=
  redPcons_not_rec_of_fitp_append
    (G := G) (ctx := ctx) (pc := pc) (r := r) (pr := pr) (y := y)
    (n := G.arity (SubpartLoc.move j G y)) hNoRedRec hy hp0size
    (fun hcontains =>
      fitp_append_popped_of_update_tail
        (G := G) (ctx := ctx) (pc := pc) (j := j) (r := r) (pr := pr)
        (y := y) hupdate hfitpc hcontains (htail hcontains))

theorem redPcons_fit_of_update_tail
    {G : Hypermap.{u}} {ctx : Context} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {qa : QArity}
    {y : G.Dart}
    (hNoRedRec : NoRedRec G ctx)
    (hy : G.arity y = ctx.nhub)
    (hp0size : Part.size ctx.p0r = ctx.nhub)
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G y (pc r pr) = true)
    (hfit : fitQa r qa = true)
    (hred : redPcons ctx pc r pr = true)
    (htail :
      PRange.contains (popQa r)
          (G.arity (SubpartLoc.move j G y)) = true →
        Part.fitp G
          ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)] y)
          ctx.p0r = true) :
    G.arity (SubpartLoc.move j G y) = qa.toNat := by
  exact redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := pc) (j := j) (r := r) (pr := pr)
    (qa := qa) (x := y) hupdate hfitpc hfit hred
    (redPcons_not_rec_of_update_tail
      (G := G) (ctx := ctx) (pc := pc) (j := j) (r := r) (pr := pr)
      (y := y) hNoRedRec hy hp0size hupdate hfitpc htail)

theorem fitp_right_of_zvalid
    {G : Hypermap} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hvalid : zvalid ctx pl pr)
    (hfit : Part.exactFitp G x0 ctx.p0r = true) :
    Part.fitp G (zorg G x0 pl) pr = true := by
  have hdoubled : Part.fitp G x0 (Part.append ctx.p0r ctx.p0r) = true :=
    fitp_append_self_of_exactFitp (G := G) (x := x0) (p := ctx.p0r) hfit
  have hz : Part.fitp G x0 (Part.reverseAppend pl pr) = true := by
    rw [hvalid]
    exact hdoubled
  rw [Part.reverseAppend_eq_append_reverse, Part.fitp_append] at hz
  simp [Part.size_reverse] at hz
  exact hz.2

theorem fitp_tail_p0r_of_zvalid_update
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pc : PRange → Part → Part} {j : SubpartLoc}
    {r : PRange} {pr pl : Part}
    (hvalid : zvalid ctx pl (pc r pr))
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hupdate : Part.PartUpdate.{u} pc j) :
    Part.fitp G
      ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)]
        (zorg G x0 pl))
      ctx.p0r = true := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have harity : G.arity x0 = Part.size ctx.p0r := hparts.1
  have hfitp0 : Part.fitp G x0 ctx.p0r = true := hparts.2
  have hvalidSize : Part.size pl + Part.size (pc r pr) =
      2 * Part.size ctx.p0r :=
    zvalid_size (ctx := ctx) (pl := pl) (pr := pc r pr) hvalid
  have hsizePop : Part.size (pc (popQa r) pr) = Part.size (pc r pr) := by
    have hpop := (hupdate (popQa r) pr).1
    have hcur := (hupdate r pr).1
    omega
  have htotal :
      Part.size (pc (popQa r) pr) + Part.size pl =
        2 * Part.size ctx.p0r := by
    omega
  have hcycle :
      (G.face : G.Dart → G.Dart)^[Part.size ctx.p0r] x0 = x0 := by
    simpa [harity] using G.face_iterate_arity x0
  have hpos :
      ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)]
          (zorg G x0 pl)) = x0 := by
    calc
      ((G.face : G.Dart → G.Dart)^[Part.size (pc (popQa r) pr)]
          (zorg G x0 pl))
          =
          ((G.face : G.Dart → G.Dart)^[
            Part.size (pc (popQa r) pr) + Part.size pl] x0) := by
            rw [zorg, ← Function.iterate_add_apply]
      _ = ((G.face : G.Dart → G.Dart)^[2 * Part.size ctx.p0r] x0) := by
            rw [htotal]
      _ = x0 := by
            have htwo : 2 * Part.size ctx.p0r =
                Part.size ctx.p0r + Part.size ctx.p0r := by omega
            rw [htwo, Function.iterate_add_apply, hcycle, hcycle]
  simpa [hpos] using hfitp0

theorem redPcons_fit_of_zvalid
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pc : PRange → Part → Part} {j : SubpartLoc}
    {r : PRange} {pr pl : Part} {qa : QArity}
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl (pc r pr))
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfit : fitQa r qa = true)
    (hred : redPcons ctx pc r pr = true) :
    G.arity (SubpartLoc.move j G (zorg G x0 pl)) = qa.toNat := by
  have hparts := hfit0
  simp [Part.exactFitp] at hparts
  have hp0size : Part.size ctx.p0r = ctx.nhub := by
    omega
  have hy : G.arity (zorg G x0 pl) = ctx.nhub := by
    rw [zorg]
    rw [Hypermap.arity_face_iter]
    exact hx0
  have hfitpc : Part.fitp G (zorg G x0 pl) (pc r pr) = true :=
    fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
      (pl := pl) (pr := pc r pr) hvalid hfit0
  exact redPcons_fit_of_update_tail
    (G := G) (ctx := ctx) (pc := pc) (j := j) (r := r) (pr := pr)
    (qa := qa) (y := zorg G x0 pl) hNoRedRec hy hp0size hupdate
    hfitpc hfit hred
    (fun _hcontains =>
      fitp_tail_p0r_of_zvalid_update
        (G := G) (ctx := ctx) (x0 := x0) (pc := pc) (j := j)
        (r := r) (pr := pr) (pl := pl) hvalid hfit0 hupdate)

theorem redPoprSpoke_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getSpoke pr) qa = true)
    (hred : redPoprSpoke ctx pr = true) :
    G.arity (SubpartLoc.move SubpartLoc.Pspoke G (zorg G x0 pl)) =
      qa.toNat := by
  cases pr with
  | Pcons s h p =>
      exact redPcons_fit_of_zvalid
        (G := G) (ctx := ctx) (x0 := x0)
        (pc := fun r p' => Pcons r h p') (j := SubpartLoc.Pspoke)
        (r := s) (pr := p) (pl := pl) (qa := qa)
        hNoRedRec hx0 hvalid hfit0 (Part.updatePs h) hfit
        (by simpa [redPoprSpoke] using hred)
  | Pnil =>
      simp [Part.getSpoke, fitQa] at hfit
  | Pcons6 h f1 p =>
      have hfitpr :
          Part.fitp G (zorg G x0 pl) (Pcons6 h f1 p) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons6 h f1 p) hvalid hfit0
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega
  | Pcons7 h f1 f2 p =>
      have hfitpr :
          Part.fitp G (zorg G x0 pl) (Pcons7 h f1 f2 p) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons7 h f1 f2 p) hvalid hfit0
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega
  | Pcons8 h f1 f2 f3 p =>
      have hfitpr :
          Part.fitp G (zorg G x0 pl) (Pcons8 h f1 f2 f3 p) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := pl) (pr := Pcons8 h f1 f2 f3 p) hvalid hfit0
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega

theorem redPoprHat_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getHat pr) qa = true)
    (hred : redPoprHat ctx pr = true) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G (zorg G x0 pl)) =
      qa.toNat := by
  cases pr with
  | Pnil =>
      simp [Part.getHat, Part.nextHat, fitQa] at hfit
  | Pcons s h p =>
      exact redPcons_fit_of_zvalid
        (G := G) (ctx := ctx) (x0 := x0)
        (pc := fun r p' => Pcons s r p') (j := SubpartLoc.Phat)
        (r := h) (pr := p) (pl := pl) (qa := qa)
        hNoRedRec hx0 hvalid hfit0 (Part.updatePh s) hfit
        (by simpa [redPoprHat] using hred)
  | Pcons6 h f1 p =>
      exact redPcons_fit_of_zvalid
        (G := G) (ctx := ctx) (x0 := x0)
        (pc := fun r p' => Pcons6 r f1 p') (j := SubpartLoc.Phat)
        (r := h) (pr := p) (pl := pl) (qa := qa)
        hNoRedRec hx0 hvalid hfit0 (Part.updateP6h f1) hfit
        (by simpa [redPoprHat] using hred)
  | Pcons7 h f1 f2 p =>
      exact redPcons_fit_of_zvalid
        (G := G) (ctx := ctx) (x0 := x0)
        (pc := fun r p' => Pcons7 r f1 f2 p') (j := SubpartLoc.Phat)
        (r := h) (pr := p) (pl := pl) (qa := qa)
        hNoRedRec hx0 hvalid hfit0 (Part.updateP7h f1 f2) hfit
        (by simpa [redPoprHat] using hred)
  | Pcons8 h f1 f2 f3 p =>
      exact redPcons_fit_of_zvalid
        (G := G) (ctx := ctx) (x0 := x0)
        (pc := fun r p' => Pcons8 r f1 f2 f3 p') (j := SubpartLoc.Phat)
        (r := h) (pr := p) (pl := pl) (qa := qa)
        hNoRedRec hx0 hvalid hfit0 (Part.updateP8h f1 f2 f3) hfit
        (by simpa [redPoprHat] using hred)

theorem redPoplSpoke_fit
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getSpoke pl) qa = true)
    (hred : redPoplSpoke ctx pl pr = true) :
    G.arity (G.node (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getSpoke, fitQa] at hfit
  | Pcons s h tail =>
      have hvalid' : zvalid ctx tail (Pcons s h pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pspoke G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons r h p') (j := SubpartLoc.Pspoke)
          (r := s) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updatePs h) hfit
          (by simpa [redPoplSpoke] using hred)
      have hzorg :
          zorg G x0 (Pcons s h tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move] using hcore
  | Pcons6 h f1 tail =>
      have hvalid' : zvalid ctx tail (Pcons6 h f1 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons6 h f1 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons6 h f1 pr) hvalid' hfit0
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pspoke G
            (zorg G x0 tail)) = qa.toNat := by
        cases qa <;>
          simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
            QArity.toNat] at hfit hfitRight ⊢
        omega
      have hzorg :
          zorg G x0 (Pcons6 h f1 tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move] using hcore
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons7 h f1 f2 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons7 h f1 f2 pr) hvalid' hfit0
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pspoke G
            (zorg G x0 tail)) = qa.toNat := by
        cases qa <;>
          simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
            QArity.toNat] at hfit hfitRight ⊢
        omega
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hfitRight :
          Part.fitp G (zorg G x0 tail) (Pcons8 h f1 f2 f3 pr) = true :=
        fitp_right_of_zvalid (G := G) (ctx := ctx) (x0 := x0)
          (pl := tail) (pr := Pcons8 h f1 f2 f3 pr) hvalid' hfit0
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Pspoke G
            (zorg G x0 tail)) = qa.toNat := by
        cases qa <;>
          simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
            QArity.toNat] at hfit hfitRight ⊢
        omega
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg, Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move] using hcore

theorem redPoplHat_fit_zfan0r
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {pl pr : Part} {qa : QArity}
    (hPlain : G.Plain)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hvalid : zvalid ctx pl pr)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hfit : fitQa (Part.getHat pl) qa = true)
    (hred : redPoplHat ctx pl pr = true) :
    G.arity (zmove G Zfan0r (zorg G x0 pl)) = qa.toNat := by
  cases pl with
  | Pnil =>
      simp [Part.getHat, Part.nextHat, fitQa] at hfit
  | Pcons s h tail =>
      have hvalid' : zvalid ctx tail (Pcons s h pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Phat G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons s r p') (j := SubpartLoc.Phat)
          (r := h) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updatePh s) hfit
          (by simpa [redPoplHat] using hred)
      have hzorg :
          zorg G x0 (Pcons s h tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      rw [zmove_zfan0r]
      rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons6 h f1 tail =>
      have hvalid' : zvalid ctx tail (Pcons6 h f1 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Phat G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons6 r f1 p') (j := SubpartLoc.Phat)
          (r := h) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP6h f1) hfit
          (by simpa [redPoplHat] using hred)
      have hzorg :
          zorg G x0 (Pcons6 h f1 tail) = G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      rw [zmove_zfan0r]
      rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons7 h f1 f2 tail =>
      have hvalid' : zvalid ctx tail (Pcons7 h f1 f2 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Phat G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons7 r f1 f2 p') (j := SubpartLoc.Phat)
          (r := h) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP7h f1 f2) hfit
          (by simpa [redPoplHat] using hred)
      have hzorg :
          zorg G x0 (Pcons7 h f1 f2 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      rw [zmove_zfan0r]
      rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore
  | Pcons8 h f1 f2 f3 tail =>
      have hvalid' : zvalid ctx tail (Pcons8 h f1 f2 f3 pr) := by
        simpa [zvalid, Part.reverseAppend] using hvalid
      have hcore :
          G.arity (SubpartLoc.move SubpartLoc.Phat G
            (zorg G x0 tail)) = qa.toNat :=
        redPcons_fit_of_zvalid
          (G := G) (ctx := ctx) (x0 := x0)
          (pc := fun r p' => Pcons8 r f1 f2 f3 p') (j := SubpartLoc.Phat)
          (r := h) (pr := pr) (pl := tail) (qa := qa)
          hNoRedRec hx0 hvalid' hfit0 (Part.updateP8h f1 f2 f3) hfit
          (by simpa [redPoplHat] using hred)
      have hzorg :
          zorg G x0 (Pcons8 h f1 f2 f3 tail) =
            G.face (zorg G x0 tail) := by
        simp [zorg, Part.size, Function.iterate_succ_apply']
      rw [hzorg]
      rw [zmove_zfan0r]
      rw [Hypermap.Plain.node_face_eq_edge (G := G) hPlain]
      simpa [SubpartLoc.move, Function.iterate_succ_apply] using hcore


end Schematic.Math.GraphTheory.FourColor.RedPart
