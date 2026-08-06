import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorEvaluation
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem nextHat_fitp_of_ne_pnil
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hp : p ≠ Pnil) (hfit : fitp G x p = true) :
    nextHat h0 p (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
  rcases fitp_nextHat_or_pnil (G := G) h0 hfit with hnil | hhat
  · exact (hp hnil).elim
  · exact hhat

theorem nextHat_fitp_mirror_of_ne_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hp : p ≠ Pnil)
    (hfit : fitp G.mirror (G.face.symm x) p = true) :
    nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
      true := by
  rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with hnil | hhat
  · exact (hp hnil).elim
  · simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic
      (G.face.symm x)] using hhat

theorem nextHat_fitp_mirror_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hsize : G.arity x = p.size + 1)
    (h0x : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    (hfit : fitp G.mirror (G.face.symm x) p = true) :
    nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
      true := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size] x = G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ (G := G) hsize
  rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with hnil | hhat
  · subst p
    simpa [hspoke.symm] using h0x
  · simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic
      (G.face.symm x)] using hhat

theorem fitp_mirrorRec_step_pcons_nonempty
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart} {h0x : Bool}
    (s h : PRange)
    (hsize : G.arity x = p.size + q.size + 1)
    (hnext : nextHat h0 q = h)
    (hp : p ≠ Pnil) (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons s h p)) && h0x) =
      ((fitp G (G.face.symm x) (Pcons s (nextHat h0 p) q) &&
          fitp G.mirror (G.face.symm x) p) && h0x) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size + q.size] x =
        G.face.symm x :=
    face_iterate_add_eq_face_symm_of_arity_add_succ
      (G := G) (a := p.size) (b := q.size) (x := x) hsize
  rw [fitp_mirror_pcons_of_arity_succ
    (G := G) hPlain hCubic (n := p.size + q.size)
    (x := x) hsize s h p]
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
      simp [hqhat, hphat, Bool.and_left_comm, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons_q_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (s h : PRange)
    (hsize : G.arity x = p.size + 1)
    (hnext : h0 = h) :
    ((fitp G x Pnil && fitp G.mirror x (Pcons s h p)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((fitp G (G.face.symm x) (Pcons s (nextHat h0 p) Pnil) &&
          fitp G.mirror (G.face.symm x) p) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := p.size) hsize
  rw [fitp_mirror_pcons_of_arity_succ
    (G := G) hPlain hCubic (n := p.size)
    (x := x) hsize s h p]
  rw [← hnext]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_arity_succ
          hPlain hCubic h0 hsize hb hfitp
      simp [hphat]

theorem fitp_mirrorRec_step_pcons6_q_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (h f1 : PRange)
    (hsize : G.arity x = p.size + 1)
    (hnext : h0 = h) :
    ((fitp G x Pnil && fitp G.mirror x (Pcons6 h f1 p)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((fitp G (G.face.symm x) (Pcons6 (nextHat h0 p) f1 Pnil) &&
          fitp G.mirror (G.face.symm x) p) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := p.size) hsize
  rw [fitp_mirror_pcons6_of_arity_succ
    (G := G) hPlain hCubic (n := p.size)
    (x := x) hsize h f1 p]
  rw [← hnext]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_arity_succ
          hPlain hCubic h0 hsize hb hfitp
      simp [hphat]

theorem fitp_mirrorRec_step_pcons7_q_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (h f1 f2 : PRange)
    (hsize : G.arity x = p.size + 1)
    (hnext : h0 = h) :
    ((fitp G x Pnil && fitp G.mirror x (Pcons7 h f1 f2 p)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((fitp G (G.face.symm x) (Pcons7 (nextHat h0 p) f2 f1 Pnil) &&
          fitp G.mirror (G.face.symm x) p) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := p.size) hsize
  rw [fitp_mirror_pcons7_of_arity_succ
    (G := G) hPlain hCubic (n := p.size)
    (x := x) hsize h f1 f2 p]
  rw [← hnext]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_arity_succ
          hPlain hCubic h0 hsize hb hfitp
      simp [hphat, Bool.and_assoc, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons8_q_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart}
    (h f1 f2 f3 : PRange)
    (hsize : G.arity x = p.size + 1)
    (hnext : h0 = h) :
    ((fitp G x Pnil && fitp G.mirror x (Pcons8 h f1 f2 f3 p)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((fitp G (G.face.symm x) (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) &&
          fitp G.mirror (G.face.symm x) p) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[p.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := p.size) hsize
  rw [fitp_mirror_pcons8_of_arity_succ
    (G := G) hPlain hCubic (n := p.size)
    (x := x) hsize h f1 f2 f3 p]
  rw [← hnext]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · cases hfitp : fitp G.mirror (G.face.symm x) p
    · simp
    · have hphat :
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x))) =
            true :=
        nextHat_fitp_mirror_of_arity_succ
          hPlain hCubic h0 hsize hb hfitp
      simp [hphat, Bool.and_assoc, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons_tail_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {q : Part} {x : G.Dart}
    (s h : PRange)
    (hsize : G.arity x = q.size + 1)
    (hnext : nextHat h0 q = h)
    (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons s h Pnil)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) =
      ((fitp G (G.face.symm x) (Pcons s h0 q) &&
          fitp G.mirror (G.face.symm x) Pnil) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[q.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := q.size) hsize
  rw [fitp_mirror_pcons_of_arity_succ
    (G := G) hPlain hCubic (n := q.size)
    (x := x) hsize s h Pnil]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat :
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))
    · simp [hqhat]
    · simp [hqhat]

theorem fitp_mirrorRec_step_pcons6_tail_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {q : Part} {x : G.Dart}
    (h f1 : PRange)
    (hsize : G.arity x = q.size + 1)
    (hnext : nextHat h0 q = h)
    (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons6 h f1 Pnil)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) =
      ((fitp G (G.face.symm x) (Pcons6 h0 f1 q) &&
          fitp G.mirror (G.face.symm x) Pnil) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[q.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := q.size) hsize
  rw [fitp_mirror_pcons6_of_arity_succ
    (G := G) hPlain hCubic (n := q.size)
    (x := x) hsize h f1 Pnil]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat :
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))
    · simp [hqhat]
    · simp [hqhat]

theorem fitp_mirrorRec_step_pcons7_tail_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {q : Part} {x : G.Dart}
    (h f1 f2 : PRange)
    (hsize : G.arity x = q.size + 1)
    (hnext : nextHat h0 q = h)
    (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons7 h f1 f2 Pnil)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) =
      ((fitp G (G.face.symm x) (Pcons7 h0 f2 f1 q) &&
          fitp G.mirror (G.face.symm x) Pnil) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[q.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := q.size) hsize
  rw [fitp_mirror_pcons7_of_arity_succ
    (G := G) hPlain hCubic (n := q.size)
    (x := x) hsize h f1 f2 Pnil]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat :
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))
    · simp [hqhat]
    · simp [hqhat, Bool.and_assoc, Bool.and_comm]

theorem fitp_mirrorRec_step_pcons8_tail_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {q : Part} {x : G.Dart}
    (h f1 f2 f3 : PRange)
    (hsize : G.arity x = q.size + 1)
    (hnext : nextHat h0 q = h)
    (hq : q ≠ Pnil) :
    ((fitp G x q && fitp G.mirror x (Pcons8 h f1 f2 f3 Pnil)) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) =
      ((fitp G (G.face.symm x) (Pcons8 h0 f3 f2 f1 q) &&
          fitp G.mirror (G.face.symm x) Pnil) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))) := by
  have hspoke :
      (G.face : G.Dart → G.Dart)^[q.size] x =
        G.face.symm x :=
    face_iterate_pred_eq_face_symm_of_arity_succ
      (G := G) (x := x) (n := q.size) hsize
  rw [fitp_mirror_pcons8_of_arity_succ
    (G := G) hPlain hCubic (n := q.size)
    (x := x) hsize h f1 f2 f3 Pnil]
  simp [fitp, hspoke, Bool.and_assoc]
  cases hfitq : fitp G x q
  · simp
  · have hqhat :
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rw [← hnext]
      exact nextHat_fitp_of_ne_pnil h0 hq hfitq
    cases hb : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face.symm x)))
    · simp [hqhat]
    · simp [hqhat, Bool.and_assoc, Bool.and_comm]

end

end Part

end FourColor

end Schematic.Math.GraphTheory
