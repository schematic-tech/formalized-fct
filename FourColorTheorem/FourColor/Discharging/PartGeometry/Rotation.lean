import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadComplements
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem fitp_drop
    (n : Nat) (p : Part) (x : G.Dart) :
    fitp G x p = true →
      fitp G ((G.face : G.Dart → G.Dart)^[n] x) (drop n p) = true := by
  induction n generalizing p x with
  | zero =>
      intro hfit
      simpa [drop] using hfit
  | succ n ih =>
      intro hfit
      cases p <;> simp [drop, fitp] at hfit ⊢
      all_goals exact ih _ _ hfit.2

theorem fitp_drop_of_eq_true
    {p : Part} {x : G.Dart}
    (n : Nat)
    (hfit : fitp G x p = true) :
    fitp G ((G.face : G.Dart → G.Dart)^[n] x) (drop n p) = true :=
  fitp_drop (G := G) n p x hfit

theorem fitp_take_of_eq_true
    (n : Nat) (p : Part) (x : G.Dart)
    (hfit : fitp G x p = true) :
    fitp G x (take n p) = true := by
  have hcat : fitp G x (append (take n p) (drop n p)) = true := by
    simpa [append_take_drop] using hfit
  rw [fitp_append] at hcat
  rw [Bool.and_eq_true] at hcat
  exact hcat.1

/-- Rotation of a fitting part follows the face orbit.  The face-period
equality is split out because it is an orbit-cardinality fact, while this
lemma is only about the executable `Part` operations. -/
theorem fitp_rotate_of_fitp_of_le_of_face_iter_size_eq_self
    {n : Nat} {p : Part} {x : G.Dart}
    (hle : n ≤ p.size)
    (hcycle : (G.face : G.Dart → G.Dart)^[p.size] x = x)
    (hfit : fitp G x p = true) :
    fitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) = true := by
  have hdrop :
      fitp G ((G.face : G.Dart → G.Dart)^[n] x) (drop n p) = true :=
    fitp_drop (G := G) n p x hfit
  have htake : fitp G x (take n p) = true :=
    fitp_take_of_eq_true (G := G) n p x hfit
  rw [rotate, fitp_append]
  rw [Bool.and_eq_true]
  constructor
  · exact hdrop
  · have hiter :
        (G.face : G.Dart → G.Dart)^[p.size - n]
            ((G.face : G.Dart → G.Dart)^[n] x) = x := by
      calc
        (G.face : G.Dart → G.Dart)^[p.size - n]
            ((G.face : G.Dart → G.Dart)^[n] x) =
            (G.face : G.Dart → G.Dart)^[p.size - n + n] x := by
              exact (Function.iterate_add_apply
                (f := (G.face : G.Dart → G.Dart)) (p.size - n) n x).symm
        _ = (G.face : G.Dart → G.Dart)^[p.size] x := by
          rw [Nat.sub_add_cancel hle]
        _ = x := hcycle
    simpa [size_drop, hiter] using htake

theorem exactFitp_rotate_of_le_of_face_iter_size_eq_self
    {n : Nat} {p : Part} {x : G.Dart}
    (hle : n ≤ p.size)
    (hcycle : (G.face : G.Dart → G.Dart)^[p.size] x = x)
    (hfit : exactFitp G x p = true) :
    exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) = true := by
  have hfits := hfit
  simp [exactFitp] at hfits ⊢
  exact ⟨by
      rw [Hypermap.arity_face_iter]
      exact hfits.1,
    fitp_rotate_of_fitp_of_le_of_face_iter_size_eq_self
      (G := G) hle hcycle hfits.2⟩

/-- Exact-fit rotation specialized with the proved face-period theorem. -/
theorem exactFitp_rotate_of_le
    {n : Nat} {p : Part} {x : G.Dart}
    (hle : n ≤ p.size)
    (hfit : exactFitp G x p = true) :
    exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) = true := by
  have hfits := hfit
  simp [exactFitp] at hfits
  have hcycle :
      (G.face : G.Dart → G.Dart)^[p.size] x = x := by
    simpa [hfits.1] using G.face_iterate_arity x
  exact exactFitp_rotate_of_le_of_face_iter_size_eq_self
    (G := G) hle hcycle hfit

theorem exactFitp_face_iter_rotate_of_arity_eq
    {n nhub : Nat} {p : Part} {x : G.Dart}
    (hn : n ≤ nhub) (hx : G.arity x = nhub)
    (hfit : exactFitp G x p = true) :
    exactFitp G ((G.face : G.Dart → G.Dart)^[n] x)
      (rotate n p) = true := by
  have hs := hfit
  simp [exactFitp] at hs
  have hle : n ≤ p.size := by
    simpa [← hs.1, hx] using hn
  exact exactFitp_rotate_of_le (G := G) hle hfit

theorem exactFitp_face_iter_reverse_rotate_of_arity_eq
    {n nhub : Nat} {p : Part} {x : G.Dart}
    (hn : n ≤ nhub) (hx : G.arity x = nhub)
    (hfit : exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) p = true) :
    exactFitp G x (rotate (nhub - n) p) = true := by
  have hs := hfit
  simp [exactFitp] at hs
  have hsize : p.size = nhub := by
    have harity :
        G.arity ((G.face : G.Dart → G.Dart)^[n] x) = nhub := by
      simpa [hx] using Hypermap.arity_face_iter (G := G) n x
    exact hs.1.symm.trans harity
  have hle : nhub - n ≤ p.size := by
    rw [hsize]
    omega
  have hrot := exactFitp_rotate_of_le (G := G) hle hfit
  have hpoint :
      (G.face : G.Dart → G.Dart)^[nhub - n]
          ((G.face : G.Dart → G.Dart)^[n] x) = x := by
    calc
      (G.face : G.Dart → G.Dart)^[nhub - n]
          ((G.face : G.Dart → G.Dart)^[n] x) =
          (G.face : G.Dart → G.Dart)^[nhub - n + n] x := by
            exact (Function.iterate_add_apply
              (f := (G.face : G.Dart → G.Dart)) (nhub - n) n x).symm
      _ = (G.face : G.Dart → G.Dart)^[nhub] x := by
        rw [Nat.sub_add_cancel hn]
      _ = x := by
        simpa [hx] using G.face_iterate_arity x
  simpa [hpoint] using hrot

/-- Exact fitting is invariant under rotating the part and advancing the
pointed dart by the same number of face steps.  This is the Boolean equality
form of Coq `fitp_rot`. -/
theorem exactFitp_rotate_eq_of_le
    {n : Nat} {p : Part} {x : G.Dart}
    (hle : n ≤ p.size) :
    exactFitp G x p =
      exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) := by
  by_cases hfit : exactFitp G x p = true
  · have hrot := exactFitp_rotate_of_le (G := G) hle hfit
    simp [hfit, hrot]
  · have hfalse : exactFitp G x p = false := by
      cases h : exactFitp G x p with
      | false => rfl
      | true => exact False.elim (hfit h)
    by_cases hrot :
        exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) = true
    · have hs := hrot
      simp [exactFitp] at hs
      have hx : G.arity x = p.size := by
        have harity :
            G.arity ((G.face : G.Dart → G.Dart)^[n] x) = p.size := by
          simpa [size_rotate] using hs.1
        simpa [Hypermap.arity_face_iter] using harity
      have hback := exactFitp_face_iter_reverse_rotate_of_arity_eq
        (G := G) (n := n) (nhub := p.size) (p := rotate n p)
        (x := x) hle hx hrot
      have htrue : exactFitp G x p = true := by
        simpa [rotate_size_sub_rotate] using hback
      exact False.elim (hfit htrue)
    · have hrotFalse :
        exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) (rotate n p) =
          false := by
        cases h : exactFitp G ((G.face : G.Dart → G.Dart)^[n] x)
            (rotate n p) with
        | false => rfl
        | true => exact False.elim (hrot h)
      simp [hfalse, hrotFalse]

/-- Rotating backward by `size - n` is the same as advancing the pointed dart
by `n` face steps. -/
theorem exactFitp_reverse_rotate_eq_face_iter
    {n : Nat} {p : Part} {x : G.Dart}
    (hle : n ≤ p.size) :
    exactFitp G x (rotate (p.size - n) p) =
      exactFitp G ((G.face : G.Dart → G.Dart)^[n] x) p := by
  have hrot := exactFitp_rotate_eq_of_le
    (G := G) (n := n) (p := rotate (p.size - n) p) (x := x)
    (by simpa [size_rotate] using hle)
  have hcombine :
      rotate n (rotate (p.size - n) p) = p := by
    have h := rotate_size_sub_rotate (p.size - n) p
    have hsub : p.size - (p.size - n) = n := by omega
    simpa [hsub] using h
  simpa [hcombine] using hrot

/-- The one-step form used in the discharge-rule mirror pairing. -/
theorem exactFitp_rotate_pred_eq_face
    {p : Part} {x : G.Dart}
    (hpos : 1 ≤ p.size) :
    exactFitp G x (rotate (p.size - 1) p) =
      exactFitp G (G.face x) p := by
  simpa [Function.iterate_one] using
    exactFitp_reverse_rotate_eq_face_iter
      (G := G) (n := 1) (p := p) (x := x) hpos

theorem size_iterate_rotate (n i : Nat) :
    ∀ p : Part,
    (((rotate n)^[i]) p).size = p.size := by
  induction i with
  | zero =>
      intro p
      rfl
  | succ i ih =>
      intro p
      calc
        (((rotate n)^[i + 1]) p).size =
            (((rotate n)^[i]) (rotate n p)).size := by
              rw [Function.iterate_succ_apply]
        _ = (rotate n p).size := ih (rotate n p)
        _ = p.size := by simp

/-- Iterating the predecessor rotation advances the pointed dart by the same
number of face steps.  This is the reusable Lean form of the `fit_rp`
calculation in Coq's `dscore_mirror` proof. -/
theorem exactFitp_iterate_rotate_pred_eq_face_iter
    {p : Part} {x : G.Dart}
    (hpos : 1 ≤ p.size) (i : Nat) :
    exactFitp G x (((rotate (p.size - 1))^[i]) p) =
      exactFitp G ((G.face : G.Dart → G.Dart)^[i] x) p := by
  induction i generalizing p x with
  | zero =>
      simp
  | succ i ih =>
      let q : Part := rotate (p.size - 1) p
      have hqsize : q.size = p.size := by
        simp [q]
      have hqpos : 1 ≤ q.size := by
        simpa [hqsize] using hpos
      have hih := ih (p := q) (x := x) hqpos
      have hstep :
          exactFitp G ((G.face : G.Dart → G.Dart)^[i] x) q =
            exactFitp G
              (G.face (((G.face : G.Dart → G.Dart)^[i] x))) p := by
        simpa [q] using
          exactFitp_rotate_pred_eq_face
            (G := G) (p := p)
            (x := ((G.face : G.Dart → G.Dart)^[i] x)) hpos
      calc
        exactFitp G x (((rotate (p.size - 1))^[i + 1]) p) =
            exactFitp G x (((rotate (p.size - 1))^[i]) q) := by
              rw [Function.iterate_succ_apply]
        _ = exactFitp G ((G.face : G.Dart → G.Dart)^[i] x) q := by
              simpa [q, hqsize] using hih
        _ = exactFitp G
              (G.face (((G.face : G.Dart → G.Dart)^[i] x))) p := hstep
        _ = exactFitp G ((G.face : G.Dart → G.Dart)^[i + 1] x) p := by
              rw [Function.iterate_succ_apply']

end

end Part

end FourColor

end Schematic.Math.GraphTheory
