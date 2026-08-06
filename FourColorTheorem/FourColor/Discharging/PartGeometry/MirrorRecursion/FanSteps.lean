import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorRecursion.PConsSteps
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem fitp_mirrorRec_step_pcons6_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (h f1 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hboundary :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true)
    (hfitq :
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
        true)
    (hfitp : fitp G.mirror x (Pcons6 h f1 p) = true) :
    fitp G (G.face.symm x) (Pcons6 (nextHat h0 p) f1 q) = true ∧
      fitp G.mirror (G.face.symm x) p = true := by
  have hfitq0 : fitp G x q = true := by
    have htmp :
        fitp G ((G.face : G.Dart → G.Dart)^[G.arity x] x) q = true := by
      simpa [hsize] using hfitq
    simpa [G.face_iterate_arity x] using htmp
  have hstep :
      ((fitp G x q && fitp G.mirror x (Pcons6 h f1 p)) && true) =
        ((fitp G (G.face.symm x) (Pcons6 (nextHat h0 p) f1 q) &&
            fitp G.mirror (G.face.symm x) p) && true) := by
    by_cases hp : p = Pnil
    · subst p
      by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons6_q_pnil
          (G := G) hPlain hCubic h0 (p := Pnil) (x := x)
          h f1 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · have hspoke :
            (G.face : G.Dart → G.Dart)^[q.size] x =
              G.face.symm x :=
          face_iterate_pred_eq_face_symm_of_arity_succ
            (G := G) (x := x) (n := q.size)
            (by simpa [size] using hsize)
        have hb :
            h0 (G.arity
              (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
              true := by
          simpa [hspoke] using hboundary
        have hstep0 := fitp_mirrorRec_step_pcons6_tail_pnil
          (G := G) hPlain hCubic h0 (q := q) (x := x)
          h f1 (by simpa [size] using hsize) hnext hq
        simpa [hb] using hstep0
    · by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons6_q_pnil
          (G := G) hPlain hCubic h0 (p := p) (x := x)
          h f1 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · exact fitp_mirrorRec_step_pcons6_nonempty
          (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
          (h0x := true) h f1 hsize hnext hp hq
  have hcomb :
      ((fitp G x q && fitp G.mirror x (Pcons6 h f1 p)) && true) = true := by
    simp [hfitq0, hfitp]
  rw [hstep] at hcomb
  simpa [Bool.and_eq_true] using hcomb

theorem fitp_mirrorRec_step_pcons7_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (h f1 f2 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hboundary :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true)
    (hfitq :
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
        true)
    (hfitp : fitp G.mirror x (Pcons7 h f1 f2 p) = true) :
    fitp G (G.face.symm x) (Pcons7 (nextHat h0 p) f2 f1 q) = true ∧
      fitp G.mirror (G.face.symm x) p = true := by
  have hfitq0 : fitp G x q = true := by
    have htmp :
        fitp G ((G.face : G.Dart → G.Dart)^[G.arity x] x) q = true := by
      simpa [hsize] using hfitq
    simpa [G.face_iterate_arity x] using htmp
  have hstep :
      ((fitp G x q && fitp G.mirror x (Pcons7 h f1 f2 p)) && true) =
        ((fitp G (G.face.symm x) (Pcons7 (nextHat h0 p) f2 f1 q) &&
            fitp G.mirror (G.face.symm x) p) && true) := by
    by_cases hp : p = Pnil
    · subst p
      by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons7_q_pnil
          (G := G) hPlain hCubic h0 (p := Pnil) (x := x)
          h f1 f2 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · have hspoke :
            (G.face : G.Dart → G.Dart)^[q.size] x =
              G.face.symm x :=
          face_iterate_pred_eq_face_symm_of_arity_succ
            (G := G) (x := x) (n := q.size)
            (by simpa [size] using hsize)
        have hb :
            h0 (G.arity
              (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
              true := by
          simpa [hspoke] using hboundary
        have hstep0 := fitp_mirrorRec_step_pcons7_tail_pnil
          (G := G) hPlain hCubic h0 (q := q) (x := x)
          h f1 f2 (by simpa [size] using hsize) hnext hq
        simpa [hb] using hstep0
    · by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons7_q_pnil
          (G := G) hPlain hCubic h0 (p := p) (x := x)
          h f1 f2 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · exact fitp_mirrorRec_step_pcons7_nonempty
          (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
          (h0x := true) h f1 f2 hsize hnext hp hq
  have hcomb :
      ((fitp G x q && fitp G.mirror x (Pcons7 h f1 f2 p)) && true) = true := by
    simp [hfitq0, hfitp]
  rw [hstep] at hcomb
  simpa [Bool.and_eq_true] using hcomb

theorem fitp_mirrorRec_step_pcons8_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (h f1 f2 f3 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hboundary :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true)
    (hfitq :
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
        true)
    (hfitp : fitp G.mirror x (Pcons8 h f1 f2 f3 p) = true) :
    fitp G (G.face.symm x) (Pcons8 (nextHat h0 p) f3 f2 f1 q) = true ∧
      fitp G.mirror (G.face.symm x) p = true := by
  have hfitq0 : fitp G x q = true := by
    have htmp :
        fitp G ((G.face : G.Dart → G.Dart)^[G.arity x] x) q = true := by
      simpa [hsize] using hfitq
    simpa [G.face_iterate_arity x] using htmp
  have hstep :
      ((fitp G x q && fitp G.mirror x (Pcons8 h f1 f2 f3 p)) && true) =
        ((fitp G (G.face.symm x) (Pcons8 (nextHat h0 p) f3 f2 f1 q) &&
            fitp G.mirror (G.face.symm x) p) && true) := by
    by_cases hp : p = Pnil
    · subst p
      by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons8_q_pnil
          (G := G) hPlain hCubic h0 (p := Pnil) (x := x)
          h f1 f2 f3 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · have hspoke :
            (G.face : G.Dart → G.Dart)^[q.size] x =
              G.face.symm x :=
          face_iterate_pred_eq_face_symm_of_arity_succ
            (G := G) (x := x) (n := q.size)
            (by simpa [size] using hsize)
        have hb :
            h0 (G.arity
              (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
              true := by
          simpa [hspoke] using hboundary
        have hstep0 := fitp_mirrorRec_step_pcons8_tail_pnil
          (G := G) hPlain hCubic h0 (q := q) (x := x)
          h f1 f2 f3 (by simpa [size] using hsize) hnext hq
        simpa [hb] using hstep0
    · by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons8_q_pnil
          (G := G) hPlain hCubic h0 (p := p) (x := x)
          h f1 f2 f3 (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · exact fitp_mirrorRec_step_pcons8_nonempty
          (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
          (h0x := true) h f1 f2 f3 hsize hnext hp hq
  have hcomb :
      ((fitp G x q && fitp G.mirror x (Pcons8 h f1 f2 f3 p)) && true) =
        true := by
    simp [hfitq0, hfitp]
  rw [hstep] at hcomb
  simpa [Bool.and_eq_true] using hcomb

end

end Part

end FourColor

end Schematic.Math.GraphTheory
