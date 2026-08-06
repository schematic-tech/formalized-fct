import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorRecursion.BaseSteps
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem fitp_mirrorRec_step_pcons_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (s h : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hboundary :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true)
    (hfitq :
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
        true)
    (hfitp : fitp G.mirror x (Pcons s h p) = true) :
    fitp G (G.face.symm x) (Pcons s (nextHat h0 p) q) = true ∧
      fitp G.mirror (G.face.symm x) p = true := by
  have hfitq0 : fitp G x q = true := by
    have htmp :
        fitp G ((G.face : G.Dart → G.Dart)^[G.arity x] x) q = true := by
      simpa [hsize] using hfitq
    simpa [G.face_iterate_arity x] using htmp
  have hstep :
      ((fitp G x q && fitp G.mirror x (Pcons s h p)) && true) =
        ((fitp G (G.face.symm x) (Pcons s (nextHat h0 p) q) &&
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
        have hstep0 := fitp_mirrorRec_step_pcons_q_pnil
          (G := G) hPlain hCubic h0 (p := Pnil) (x := x)
          s h (by simpa [size] using hsize) hnext'
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
        have hstep0 := fitp_mirrorRec_step_pcons_tail_pnil
          (G := G) hPlain hCubic h0 (q := q) (x := x)
          s h (by simpa [size] using hsize) hnext hq
        simpa [hb] using hstep0
    · by_cases hq : q = Pnil
      · subst q
        have hb :
            h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [size] using hboundary
        have hnext' : h0 = h := by
          simpa [nextHat] using hnext
        have hstep0 := fitp_mirrorRec_step_pcons_q_pnil
          (G := G) hPlain hCubic h0 (p := p) (x := x)
          s h (by simpa [size] using hsize) hnext'
        simpa [hb] using hstep0
      · exact fitp_mirrorRec_step_pcons_nonempty
          (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
          (h0x := true) s h hsize hnext hp hq
  have hcomb :
      ((fitp G x q && fitp G.mirror x (Pcons s h p)) && true) = true := by
    simp [hfitq0, hfitp]
  rw [hstep] at hcomb
  simpa [Bool.and_eq_true] using hcomb

theorem fitp_mirrorRec_step_pcons6_nonempty
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart} {h0x : Bool}
    (h f1 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hp : p ≠ Pnil) (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons6 h f1 p)) && h0x) =
      ((fitp G (G.face.symm x) (Pcons6 (nextHat h0 p) f1 q) &&
          fitp G.mirror (G.face.symm x) p) && h0x) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size + q.size] x =
        G.face.symm x :=
    face_iterate_add_eq_face_symm_of_arity_add_succ
      (G := G) (a := p.size) (b := q.size) (x := x) hsize
  rw [fitp_mirror_pcons6_of_arity_succ
    (G := G) hPlain hCubic (n := p.size + q.size)
    (x := x) hsize h f1 p]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat : h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp [hqhat]
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_ne_pnil hPlain hCubic h0 hp hfitp
      simp [hqhat, hphat, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons7_nonempty
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart} {h0x : Bool}
    (h f1 f2 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hp : p ≠ Pnil) (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons7 h f1 f2 p)) && h0x) =
      ((fitp G (G.face.symm x) (Pcons7 (nextHat h0 p) f2 f1 q) &&
          fitp G.mirror (G.face.symm x) p) && h0x) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size + q.size] x =
        G.face.symm x :=
    face_iterate_add_eq_face_symm_of_arity_add_succ
      (G := G) (a := p.size) (b := q.size) (x := x) hsize
  rw [fitp_mirror_pcons7_of_arity_succ
    (G := G) hPlain hCubic (n := p.size + q.size)
    (x := x) hsize h f1 f2 p]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat : h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp [hqhat]
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_ne_pnil hPlain hCubic h0 hp hfitp
      simp [hqhat, hphat, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons8_nonempty
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart} {h0x : Bool}
    (h f1 f2 f3 : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hp : p ≠ Pnil) (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons8 h f1 f2 f3 p)) && h0x) =
      ((fitp G (G.face.symm x) (Pcons8 (nextHat h0 p) f3 f2 f1 q) &&
          fitp G.mirror (G.face.symm x) p) && h0x) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size + q.size] x =
        G.face.symm x :=
    face_iterate_add_eq_face_symm_of_arity_add_succ
      (G := G) (a := p.size) (b := q.size) (x := x) hsize
  rw [fitp_mirror_pcons8_of_arity_succ
    (G := G) hPlain hCubic (n := p.size + q.size)
    (x := x) hsize h f1 f2 f3 p]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat : h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp [hqhat]
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_ne_pnil hPlain hCubic h0 hp hfitp
      simp [hqhat, hphat, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

end

end Part

end FourColor

end Schematic.Math.GraphTheory
