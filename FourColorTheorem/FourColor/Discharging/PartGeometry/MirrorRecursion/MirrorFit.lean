import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorRecursion.FanSteps
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

/-- Common recursive finish for all four `Part` constructors.  The
constructor-specific step only has to produce the next accumulator and its
two fit facts; orbit normalization and the induction call live here. -/
private theorem fitp_mirrorRec_induction_step
    (h0 : PRange) {p q q' : Part} {x : G.Dart}
    (ih : ∀ {q : Part} {x : G.Dart},
      G.arity x = p.size + q.size →
      nextHat h0 q = nextHat h0 p →
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true →
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size] x) q = true →
      fitp G.mirror x p = true →
      fitp G ((G.face : G.Dart → G.Dart)^[q.size] x)
        (mirrorRec h0 q p) = true)
    (hsize : G.arity x = p.size + q.size + 1)
    (hqsize : q'.size = q.size + 1)
    (hnext : nextHat h0 q' = nextHat h0 p)
    (hboundary :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true)
    (hfitq : fitp G (G.face.symm x) q' = true)
    (hfitp : fitp G.mirror (G.face.symm x) p = true) :
    fitp G ((G.face : G.Dart → G.Dart)^[q'.size] (G.face.symm x))
      (mirrorRec h0 q' p) = true := by
  have hsize' : G.arity (G.face.symm x) = p.size + q'.size := by
    rw [Hypermap.arity_face_symm, hqsize]
    omega
  have hboundary' :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q'.size] (G.face.symm x)))) = true := by
    simpa [hqsize, face_iterate_succ_face_symm] using hboundary
  have hfitqFull :
      fitp G
        ((G.face : G.Dart → G.Dart)^[p.size + q'.size]
          (G.face.symm x)) q' = true := by
    have htmp :
        fitp G
          ((G.face : G.Dart → G.Dart)^[G.arity (G.face.symm x)]
            (G.face.symm x)) q' = true := by
      simpa [G.face_iterate_arity (G.face.symm x)] using hfitq
    simpa [hsize'] using htmp
  exact ih hsize' hnext hboundary' hfitqFull hfitp

theorem fitp_mirrorRec_true_of_fitp_mirror_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) :
    ∀ {p q : Part} {x : G.Dart},
      G.arity x = p.size + q.size →
      nextHat h0 q = nextHat h0 p →
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[q.size] x))) = true →
      fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size] x) q = true →
      fitp G.mirror x p = true →
        fitp G ((G.face : G.Dart → G.Dart)^[q.size] x)
          (mirrorRec h0 q p) = true := by
  intro p
  induction p with
  | Pnil =>
      intro q x _hsize _hnext _hboundary hfitq _hfitp
      simpa [mirrorRec, size] using hfitq
  | Pcons s h p ih =>
      intro q x hsize hnext hboundary hfitq hfitp
      let q' : Part := Pcons s (nextHat h0 p) q
      have hsizeStep : G.arity x = p.size + q.size + 1 := by
        simp [size] at hsize
        omega
      have hnextStep : nextHat h0 q = h := by
        simpa [nextHat] using hnext
      have hfitqStep :
          fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
            true := by
        simpa [size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfitq
      have hstep := fitp_mirrorRec_step_pcons_true
        (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
        s h hsizeStep hnextStep hboundary hfitqStep hfitp
      rcases hstep with ⟨hfitq', hfitp'⟩
      have hrec := fitp_mirrorRec_induction_step
        (G := G) (h0 := h0) (p := p) (q := q) (q' := q') (x := x)
        (ih := ih) hsizeStep
        (by simp [q', size]) rfl hboundary hfitq' hfitp'
      simpa [q', mirrorRec, size, face_iterate_succ_face_symm] using hrec
  | Pcons6 h f1 p ih =>
      intro q x hsize hnext hboundary hfitq hfitp
      let q' : Part := Pcons6 (nextHat h0 p) f1 q
      have hsizeStep : G.arity x = p.size + q.size + 1 := by
        simp [size] at hsize
        omega
      have hnextStep : nextHat h0 q = h := by
        simpa [nextHat] using hnext
      have hfitqStep :
          fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
            true := by
        simpa [size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfitq
      have hstep := fitp_mirrorRec_step_pcons6_true
        (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
        h f1 hsizeStep hnextStep hboundary hfitqStep hfitp
      rcases hstep with ⟨hfitq', hfitp'⟩
      have hrec := fitp_mirrorRec_induction_step
        (G := G) (h0 := h0) (p := p) (q := q) (q' := q') (x := x)
        (ih := ih) hsizeStep
        (by simp [q', size]) rfl hboundary hfitq' hfitp'
      simpa [q', mirrorRec, size, face_iterate_succ_face_symm] using hrec
  | Pcons7 h f1 f2 p ih =>
      intro q x hsize hnext hboundary hfitq hfitp
      let q' : Part := Pcons7 (nextHat h0 p) f2 f1 q
      have hsizeStep : G.arity x = p.size + q.size + 1 := by
        simp [size] at hsize
        omega
      have hnextStep : nextHat h0 q = h := by
        simpa [nextHat] using hnext
      have hfitqStep :
          fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
            true := by
        simpa [size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfitq
      have hstep := fitp_mirrorRec_step_pcons7_true
        (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
        h f1 f2 hsizeStep hnextStep hboundary hfitqStep hfitp
      rcases hstep with ⟨hfitq', hfitp'⟩
      have hrec := fitp_mirrorRec_induction_step
        (G := G) (h0 := h0) (p := p) (q := q) (q' := q') (x := x)
        (ih := ih) hsizeStep
        (by simp [q', size]) rfl hboundary hfitq' hfitp'
      simpa [q', mirrorRec, size, face_iterate_succ_face_symm] using hrec
  | Pcons8 h f1 f2 f3 p ih =>
      intro q x hsize hnext hboundary hfitq hfitp
      let q' : Part := Pcons8 (nextHat h0 p) f3 f2 f1 q
      have hsizeStep : G.arity x = p.size + q.size + 1 := by
        simp [size] at hsize
        omega
      have hnextStep : nextHat h0 q = h := by
        simpa [nextHat] using hnext
      have hfitqStep :
          fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size + 1] x) q =
            true := by
        simpa [size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfitq
      have hstep := fitp_mirrorRec_step_pcons8_true
        (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x)
        h f1 f2 f3 hsizeStep hnextStep hboundary hfitqStep hfitp
      rcases hstep with ⟨hfitq', hfitp'⟩
      have hrec := fitp_mirrorRec_induction_step
        (G := G) (h0 := h0) (p := p) (q := q) (q' := q') (x := x)
        (ih := ih) hsizeStep
        (by simp [q', size]) rfl hboundary hfitq' hfitp'
      simpa [q', mirrorRec, size, face_iterate_succ_face_symm] using hrec

end

end Part

end FourColor

end Schematic.Math.GraphTheory
