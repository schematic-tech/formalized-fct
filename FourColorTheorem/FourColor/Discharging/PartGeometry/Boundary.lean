import FourColorTheorem.FourColor.Discharging.PartGeometry.HatGeometry

namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem face_iterate_succ_face_symm (n : Nat) (x : G.Dart) :
    (G.face : G.Dart → G.Dart)^[n + 1] (G.face.symm x) =
      (G.face : G.Dart → G.Dart)^[n] x := by
  rw [Function.iterate_succ_apply]
  simp

theorem face_iterate_pred_eq_face_symm_of_arity_succ
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1) :
    (G.face : G.Dart → G.Dart)^[n] x = G.face.symm x := by
  apply G.face.injective
  rw [Equiv.apply_symm_apply]
  rw [← Function.iterate_succ_apply' (f := (G.face : G.Dart → G.Dart)) n x]
  simpa [hsize] using G.face_iterate_arity x

theorem face_iterate_add_eq_face_symm_of_arity_add_succ
    {a b : Nat} {x : G.Dart}
    (hsize : G.arity x = a + b + 1) :
    (G.face : G.Dart → G.Dart)^[a + b] x = G.face.symm x :=
  face_iterate_pred_eq_face_symm_of_arity_succ
    (G := G) (x := x) (n := a + b) hsize

theorem face_iterate_add_succ_eq_self_of_arity_add_succ
    {a b : Nat} {x : G.Dart}
    (hsize : G.arity x = a + b + 1) :
    (G.face : G.Dart → G.Dart)^[a + 1 + b] x = x := by
  have hcycle :
      (G.face : G.Dart → G.Dart)^[G.arity x] x = x :=
    G.face_iterate_arity x
  have hexp : a + 1 + b = G.arity x := by omega
  simpa [hexp] using hcycle

theorem fitp_face_iterate_succ_face_symm
    (n : Nat) (p : Part) (x : G.Dart) :
    fitp G ((G.face : G.Dart → G.Dart)^[n + 1] (G.face.symm x)) p =
      fitp G ((G.face : G.Dart → G.Dart)^[n] x) p := by
  rw [face_iterate_succ_face_symm]

theorem fitp_face_iterate_arity_eq
    {n : Nat} {x : G.Dart} (p : Part)
    (hsize : G.arity x = n) :
    fitp G ((G.face : G.Dart → G.Dart)^[n] x) p =
      fitp G x p := by
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  rw [hcycle]

theorem fitp_face_iterate_add_succ_eq_self_of_arity_add_succ
    {a b : Nat} {x : G.Dart} (p : Part)
    (hsize : G.arity x = a + b + 1) :
    fitp G ((G.face : G.Dart → G.Dart)^[a + 1 + b] x) p =
      fitp G x p := by
  rw [face_iterate_add_succ_eq_self_of_arity_add_succ
    (G := G) (x := x) hsize]

theorem face_iterate_face (p : Part) (x : G.Dart) :
    (G.face : G.Dart → G.Dart)^[p.size] (G.face x) =
      G.face ((G.face : G.Dart → G.Dart)^[p.size] x) := by
  calc
    (G.face : G.Dart → G.Dart)^[p.size] (G.face x) =
        (G.face : G.Dart → G.Dart)^[p.size.succ] x := by
      exact (Function.iterate_succ_apply
        (f := (G.face : G.Dart → G.Dart)) p.size x).symm
    _ = G.face ((G.face : G.Dart → G.Dart)^[p.size] x) := by
      exact Function.iterate_succ_apply'
        (f := (G.face : G.Dart → G.Dart)) p.size x

theorem fitp_append (p q : Part) (x : G.Dart) :
    fitp G x (append p q) =
      (fitp G x p &&
        fitp G ((G.face : G.Dart → G.Dart)^[p.size] x) q) := by
  induction p generalizing x with
  | Pnil =>
      simp [append, fitp, size]
  | Pcons s h p ih =>
      simp [append, fitp, size, ih, face_iterate_face (G := G) p x,
        Bool.and_assoc]
  | Pcons6 h f1 p ih =>
      simp [append, fitp, size, ih, face_iterate_face (G := G) p x,
        Bool.and_assoc]
  | Pcons7 h f1 f2 p ih =>
      simp [append, fitp, size, ih, face_iterate_face (G := G) p x,
        Bool.and_assoc]
  | Pcons8 h f1 f2 f3 p ih =>
      simp [append, fitp, size, ih, face_iterate_face (G := G) p x,
        Bool.and_assoc]

theorem fitp_nextHat_or_pnil
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hfit : fitp G x p = true) :
    p = Pnil ∨
      nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
  cases p with
  | Pnil =>
      exact Or.inl rfl
  | Pcons s h p =>
      simp [fitp] at hfit
      exact Or.inr hfit.1.2
  | Pcons6 h f1 p =>
      simp [fitp] at hfit
      exact Or.inr hfit.1.1.2
  | Pcons7 h f1 f2 p =>
      simp [fitp] at hfit
      exact Or.inr hfit.1.1.1.2
  | Pcons8 h f1 f2 f3 p =>
      simp [fitp] at hfit
      exact Or.inr hfit.1.1.1.1.2

theorem nextHat_eq_true_of_fitp_or_pnil
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hfit : fitp G x p = true)
    (hpnil :
      p = Pnil →
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
  rcases fitp_nextHat_or_pnil (G := G) h0 hfit with hnil | hhat
  · subst p
    exact hpnil rfl
  · exact hhat

theorem nextHat_and_boundary_eq_boundary_of_fitp_or_pnil
    (h0 h : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = b)
    (hnext : nextHat h0 p = h) :
    (h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) && b) = b := by
  rw [← hnext]
  rcases fitp_nextHat_or_pnil (G := G) h0 hfit with hnil | hhat
  · subst p
    have hb := hpnil rfl
    simp [hb]
  · simp [hhat]

theorem fitp_and_nextHat_boundary_eq_fitp_and_boundary
    (h0 h : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = b)
    (hnext : nextHat h0 p = h) :
    ((fitp G x p &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) && b) =
      (fitp G x p && b) := by
  cases hfit : fitp G x p
  · simp
  · have hdrop := nextHat_and_boundary_eq_boundary_of_fitp_or_pnil
      (G := G) h0 h (p := p) (x := x) (b := b) hfit hpnil hnext
    simp [hdrop]

theorem nextHat_and_boundary_eq_boundary_of_fitp_ne_pnil
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G x p = true)
    (hp : p ≠ Pnil) :
    (nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) && b) = b := by
  rcases fitp_nextHat_or_pnil (G := G) h0 hfit with hnil | hhat
  · exact (hp hnil).elim
  · simp [hhat]

theorem fitp_and_nextHat_boundary_eq_fitp_and_boundary_of_ne_pnil
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hp : p ≠ Pnil) :
    ((fitp G x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) && b) =
      (fitp G x p && b) := by
  cases hfit : fitp G x p
  · simp
  · have hdrop := nextHat_and_boundary_eq_boundary_of_fitp_ne_pnil
      (G := G) h0 (p := p) (x := x) (b := b) hfit hp
    simp [hdrop]

theorem nextHat_and_size_eq_zero_or_boundary_eq
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
      ((p.size == 0) || b)) =
      ((p.size == 0) || b) := by
  rcases fitp_nextHat_or_pnil (G := G) h0 hfit with hnil | hhat
  · subst p
    simp [size, hpnil rfl]
  · simp [hhat]

theorem boundary_and_nextHat_and_size_eq_zero_or_boundary_eq
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (((p.size == 0) || b) &&
      nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((p.size == 0) || b) := by
  rw [Bool.and_comm]
  exact nextHat_and_size_eq_zero_or_boundary_eq
    (G := G) h0 hfit hpnil

theorem fitp_and_nextHat_and_size_boundary_eq_fitp_and_size_boundary
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    ((fitp G x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) &&
        ((p.size == 0) || b)) =
      (fitp G x p && ((p.size == 0) || b)) := by
  cases hfit : fitp G x p
  · simp
  · have hdrop := nextHat_and_size_eq_zero_or_boundary_eq
      (G := G) h0 (p := p) (x := x) (b := b) hfit hpnil
    simp [hdrop]

theorem fitp_and_nextHat_eq_fitp_of_pnil_boundary
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hpnil :
      p = Pnil →
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (fitp G x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      fitp G x p := by
  cases hfit : fitp G x p
  · rfl
  · have hhat := nextHat_eq_true_of_fitp_or_pnil
      (G := G) h0 hfit hpnil
    simp [hhat]

theorem fitp_and_nextHat_eq_fitp_of_h0_boundary
    (h0 : PRange) {p : Part} {x : G.Dart}
    (hh0 : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (fitp G x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      fitp G x p :=
  fitp_and_nextHat_eq_fitp_of_pnil_boundary
    (G := G) h0 (by intro _; exact hh0)

theorem fitp_and_nextHat_and_h0_boundary_eq
    (h0 : PRange) {p : Part} {x : G.Dart} :
    ((fitp G x p &&
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      (fitp G x p &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  cases hh0 :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · have hdrop := fitp_and_nextHat_eq_fitp_of_h0_boundary
      (G := G) (h0 := h0) (p := p) (x := x) hh0
    rw [hdrop]

theorem fitp_face_iter_arity_and_nextHat_eq_fitp_of_pnil_boundary
    (h0 : PRange) {p : Part} {x : G.Dart} {n : Nat}
    (hsize : G.arity x = n)
    (hpnil :
      p = Pnil →
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
        nextHat h0 p
          (G.arity
            (SubpartLoc.move SubpartLoc.Phat G
              ((G.face : G.Dart → G.Dart)^[n] x)))) =
      fitp G ((G.face : G.Dart → G.Dart)^[n] x) p := by
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  rw [hcycle]
  exact fitp_and_nextHat_eq_fitp_of_pnil_boundary
    (G := G) h0 hpnil

theorem fitp_face_iter_arity_and_nextHat_eq_fitp_of_h0_boundary
    (h0 : PRange) {p : Part} {x : G.Dart} {n : Nat}
    (hsize : G.arity x = n)
    (hh0 : h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
        nextHat h0 p
          (G.arity
            (SubpartLoc.move SubpartLoc.Phat G
              ((G.face : G.Dart → G.Dart)^[n] x)))) =
      fitp G ((G.face : G.Dart → G.Dart)^[n] x) p :=
  fitp_face_iter_arity_and_nextHat_eq_fitp_of_pnil_boundary
    (G := G) h0 hsize (by intro _; exact hh0)

theorem fitp_face_iter_arity_and_nextHat_and_boundary_eq
    (h0 : PRange) {p : Part} {x : G.Dart} {n : Nat}
    (hsize : G.arity x = n) :
    ((fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
          nextHat h0 p
            (G.arity
              (SubpartLoc.move SubpartLoc.Phat G
                ((G.face : G.Dart → G.Dart)^[n] x)))) &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      (fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  cases hboundary :
      nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · have hdrop :=
      fitp_face_iter_arity_and_nextHat_eq_fitp_of_pnil_boundary
        (G := G) (h0 := h0) (p := p) (x := x) (n := n) hsize
        (by
          intro hp
          subst p
          simpa using hboundary)
    rw [hdrop]

theorem fitp_face_iter_arity_and_nextHat_and_h0_boundary_eq
    (h0 : PRange) {p : Part} {x : G.Dart} {n : Nat}
    (hsize : G.arity x = n) :
    ((fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
          nextHat h0 p
            (G.arity
              (SubpartLoc.move SubpartLoc.Phat G
                ((G.face : G.Dart → G.Dart)^[n] x)))) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      (fitp G ((G.face : G.Dart → G.Dart)^[n] x) p &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  cases hh0 :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · have hdrop :=
      fitp_face_iter_arity_and_nextHat_eq_fitp_of_h0_boundary
        (G := G) (h0 := h0) (p := p) (x := x) (n := n) hsize hh0
    rw [hdrop]

theorem fitp_mirror_and_getHat_boundary_eq_fitp
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (p : Part) (x : G.Dart) :
    (fitp G.mirror x p &&
        ((p.size == 0) ||
          getHat p (G.arity (SubpartLoc.move SubpartLoc.Phat G x)))) =
      fitp G.mirror x p := by
  cases hfit : fitp G.mirror x p
  · rfl
  · rcases fitp_nextHat_or_pnil (G := G.mirror) (getHat p) hfit with
      hnil | hhat
    · subst p
      simp [size]
    · have hhat' :
          getHat p
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
        simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
          using hhat
      simp [hhat']

theorem fitp_mirror_and_nextHat_boundary_eq_fitp
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (hnext : nextHat h0 q = nextHat h0 p) :
    (fitp G.mirror x p &&
        ((p.size == 0) ||
          nextHat h0 q
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x)))) =
      fitp G.mirror x p := by
  cases hfit : fitp G.mirror x p
  · rfl
  · rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with
      hnil | hhat
    · subst p
      simp [size]
    · have hhat' :
          nextHat h0 q
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
        rw [hnext]
        simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
          using hhat
      simp [hhat']

theorem fitp_mirror_and_nextHat_and_h0_boundary_eq
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} :
    ((fitp G.mirror x p &&
          nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      (fitp G.mirror x p &&
        h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  cases hh0 :
      h0 (G.arity (SubpartLoc.move SubpartLoc.Phat G x))
  · simp
  · cases hfit : fitp G.mirror x p
    · simp
    · rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with
        hnil | hhat
      · subst p
        simpa [nextHat] using hh0
      · have hhat' :
            nextHat h0 p
                (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
          simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
            using hhat
        simp [hhat']

theorem nextHat_and_boundary_eq_boundary_of_fitp_mirror_or_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 h : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G.mirror x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = b)
    (hnext : nextHat h0 p = h) :
    (h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) && b) = b := by
  rw [← hnext]
  rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with hnil | hhat
  · subst p
    have hb := hpnil rfl
    simp [hb]
  · have hhat' :
        nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
        using hhat
    simp [hhat']

theorem fitp_mirror_and_nextHat_boundary_eq_fitp_mirror_and_boundary
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 h : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = b)
    (hnext : nextHat h0 p = h) :
    ((fitp G.mirror x p &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) && b) =
      (fitp G.mirror x p && b) := by
  cases hfit : fitp G.mirror x p
  · simp
  · have hdrop := nextHat_and_boundary_eq_boundary_of_fitp_mirror_or_pnil
      (G := G) hPlain hCubic h0 h (p := p) (x := x) (b := b)
      hfit hpnil hnext
    simp [hdrop]

theorem nextHat_and_boundary_eq_boundary_of_fitp_mirror_ne_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G.mirror x p = true)
    (hp : p ≠ Pnil) :
    (nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) && b) = b := by
  rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with hnil | hhat
  · exact (hp hnil).elim
  · have hhat' :
        nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
        using hhat
    simp [hhat']

theorem fitp_mirror_and_nextHat_boundary_eq_fitp_mirror_and_boundary_of_ne_pnil
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hp : p ≠ Pnil) :
    ((fitp G.mirror x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) && b) =
      (fitp G.mirror x p && b) := by
  cases hfit : fitp G.mirror x p
  · simp
  · have hdrop := nextHat_and_boundary_eq_boundary_of_fitp_mirror_ne_pnil
      (G := G) hPlain hCubic h0 (p := p) (x := x) (b := b) hfit hp
    simp [hdrop]

theorem nextHat_and_size_eq_zero_or_boundary_eq_of_fitp_mirror
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G.mirror x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
      ((p.size == 0) || b)) =
      ((p.size == 0) || b) := by
  rcases fitp_nextHat_or_pnil (G := G.mirror) h0 hfit with hnil | hhat
  · subst p
    simp [size, hpnil rfl]
  · have hhat' :
        nextHat h0 p
            (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x]
        using hhat
    simp [hhat']

theorem boundary_and_nextHat_and_size_eq_zero_or_boundary_eq_of_fitp_mirror
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hfit : fitp G.mirror x p = true)
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    (((p.size == 0) || b) &&
      nextHat h0 p
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) =
      ((p.size == 0) || b) := by
  rw [Bool.and_comm]
  exact nextHat_and_size_eq_zero_or_boundary_eq_of_fitp_mirror
    (G := G) hPlain hCubic h0 hfit hpnil

theorem fitp_mirror_and_nextHat_and_size_boundary_eq_fitp_and_size_boundary
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p : Part} {x : G.Dart} {b : Bool}
    (hpnil :
      p = Pnil →
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true) :
    ((fitp G.mirror x p &&
        nextHat h0 p
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) &&
        ((p.size == 0) || b)) =
      (fitp G.mirror x p && ((p.size == 0) || b)) := by
  cases hfit : fitp G.mirror x p
  · simp
  · have hdrop := nextHat_and_size_eq_zero_or_boundary_eq_of_fitp_mirror
      (G := G) hPlain hCubic h0 (p := p) (x := x) (b := b)
      hfit hpnil
    simp [hdrop]

theorem fitp_mirrorRec_pnil_eq_fitp_of_arity_eq_size
    (h0 : PRange) (q : Part) {x : G.Dart}
    (hsize : G.arity x = q.size) :
    fitp G ((G.face : G.Dart → G.Dart)^[q.size] x)
        (mirrorRec h0 q Pnil) =
      fitp G x q := by
  have hcycle :
      (G.face : G.Dart → G.Dart)^[q.size] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  simp [mirrorRec, hcycle]

theorem fitp_mirrorRec_eq_fitp_mirrorRec_pnil_and_fitp
    (h0 : PRange) (q p : Part) (x : G.Dart) :
    fitp G x (mirrorRec h0 q p) =
      (fitp G x (mirrorRec h0 Pnil p) &&
        fitp G ((G.face : G.Dart → G.Dart)^[p.size] x) q) := by
  rw [mirrorRec_eq_append]
  rw [fitp_append]
  simp [size_mirrorRec, size]

theorem fitp_mirrorRec_aux_simplify_tail_boundary
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h0 : PRange) {p q : Part} {x : G.Dart}
    (hrec :
      ((fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size] x) q &&
          fitp G.mirror x p) &&
          (((p.size == 0) ||
            nextHat h0 q
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x))))) =
        fitp G ((G.face : G.Dart → G.Dart)^[q.size] x)
          (mirrorRec h0 q p))
    (hnext : nextHat h0 q = nextHat h0 p) :
    (fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size] x) q &&
        fitp G.mirror x p) =
      fitp G ((G.face : G.Dart → G.Dart)^[q.size] x)
        (mirrorRec h0 q p) := by
  have htailBoundary := fitp_mirror_and_nextHat_boundary_eq_fitp
    (G := G) hPlain hCubic h0 (p := p) (q := q) (x := x) hnext
  rw [← hrec]
  cases ha : fitp G ((G.face : G.Dart → G.Dart)^[p.size + q.size] x) q
  · simp
  · cases hb : fitp G.mirror x p
    · simp
    · have hc :
          ((p.size == 0) ||
            nextHat h0 q
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) = true := by
        simpa [hb] using htailBoundary
      simp [hc]


end

end Part

end FourColor

end Schematic.Math.GraphTheory
