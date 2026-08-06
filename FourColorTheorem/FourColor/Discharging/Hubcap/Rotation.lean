import FourColorTheorem.FourColor.Discharging.Hubcap.Coverage

/-! Rotations and modular indices for hubcap bounds. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open Part PartRel

namespace Discharge

namespace Hubcap

/-- Rotation aligning a part with the hubcap index `j`. -/
def rotIndex (nhub j : Nat) : Nat :=
  if 2 ≤ j then j - 2 else nhub + j - 2

theorem rotIndex_le {nhub j : Nat}
    (hj : j < nhub) :
    rotIndex nhub j ≤ nhub := by
  unfold rotIndex
  by_cases h : 2 ≤ j
  · simp [h]
    omega
  · simp [h]
    omega

theorem face_iter_rotIndex_eq_face_iter_invFace2
    {G : Hypermap} {nhub j : Nat}
    (hj : j < nhub) (h2 : 2 ≤ nhub)
    (x : G.Dart) (hx : G.arity x = nhub) :
    (G.face : G.Dart → G.Dart)^[rotIndex nhub j] x =
      (G.face : G.Dart → G.Dart)^[j] (G.invFace2 x) := by
  have harityInv : G.arity (G.invFace2 x) = nhub := by
    simpa [hx] using G.arity_invFace2 x
  have hcycleInv :
      (G.face : G.Dart → G.Dart)^[nhub] (G.invFace2 x) =
        G.invFace2 x := by
    simpa [harityInv] using G.face_iterate_arity (G.invFace2 x)
  rcases j with _ | _ | j
  · simp [rotIndex]
    calc
      (G.face : G.Dart → G.Dart)^[nhub - 2] x =
          (G.face : G.Dart → G.Dart)^[nhub - 2]
            ((G.face : G.Dart → G.Dart)^[2] (G.invFace2 x)) := by
            simp
      _ = (G.face : G.Dart → G.Dart)^[nhub - 2 + 2] (G.invFace2 x) := by
        exact (Function.iterate_add_apply
          (f := (G.face : G.Dart → G.Dart)) (nhub - 2) 2
          (G.invFace2 x)).symm
      _ = (G.face : G.Dart → G.Dart)^[nhub] (G.invFace2 x) := by
        rw [Nat.sub_add_cancel h2]
      _ = G.invFace2 x := hcycleInv
  · have h1 : 1 ≤ nhub := by omega
    simp [rotIndex]
    calc
      (G.face : G.Dart → G.Dart)^[nhub - 1] x =
          (G.face : G.Dart → G.Dart)^[nhub - 1]
            ((G.face : G.Dart → G.Dart)^[2] (G.invFace2 x)) := by
            simp
      _ = (G.face : G.Dart → G.Dart)^[nhub - 1 + 2] (G.invFace2 x) := by
        exact (Function.iterate_add_apply
          (f := (G.face : G.Dart → G.Dart)) (nhub - 1) 2
          (G.invFace2 x)).symm
      _ = (G.face : G.Dart → G.Dart)^[nhub + 1] (G.invFace2 x) := by
        have hsum : nhub - 1 + 2 = nhub + 1 := by omega
        rw [hsum]
      _ = (G.face : G.Dart → G.Dart)^[1 + nhub] (G.invFace2 x) := by
        rw [Nat.add_comm]
      _ = (G.face : G.Dart → G.Dart)^[1]
            ((G.face : G.Dart → G.Dart)^[nhub] (G.invFace2 x)) := by
        rw [Function.iterate_add_apply]
      _ = G.face (G.invFace2 x) := by
        rw [hcycleInv]
        rfl
  · simp [rotIndex]

/-- Rotation aligning a part with the hubcap index `j`. -/
def rot (nhub j : Nat) (p : Part) : Part :=
  Part.rotate (rotIndex nhub j) p

theorem size_rot (nhub j : Nat) (p : Part) :
    (rot nhub j p).size = p.size := by
  simp [rot, Part.size_rotate]

theorem exactFitp_rot_of_exactFitp
    {G : Hypermap} {nhub j : Nat} {p : Part} {x : G.Dart}
    (hj : j < nhub) (h2 : 2 ≤ nhub)
    (hsize : p.size = nhub)
    (hfit : Part.exactFitp G x p = true) :
    Part.exactFitp G
      ((G.face : G.Dart → G.Dart)^[j] (G.invFace2 x))
      (rot nhub j p) = true := by
  have hle : rotIndex nhub j ≤ p.size := by
    simpa [hsize] using rotIndex_le (nhub := nhub) (j := j) hj
  have hs := hfit
  simp [Part.exactFitp] at hs
  have hx : G.arity x = nhub := hs.1.trans hsize
  have hrot :=
    Part.exactFitp_rotate_of_le (G := G) hle hfit
  simpa [rot, face_iter_rotIndex_eq_face_iter_invFace2
    (G := G) (nhub := nhub) (j := j) hj h2 x hx] using hrot

/-- Subtraction modulo the hub size, in the concrete arithmetic form used by
the Coq checker. -/
def hubSubn (nhub i j : Nat) : Nat :=
  (if j ≤ i then i else i + nhub) - j

theorem hubSubn_le {nhub i j : Nat}
    (hi : i < nhub) :
    hubSubn nhub i j ≤ nhub := by
  unfold hubSubn
  by_cases hji : j ≤ i
  · simp [hji]
    omega
  · simp [hji]
    omega

theorem face_iter_hubSubn {G : Hypermap} {nhub i j : Nat}
    (hj : j < nhub) (x : G.Dart) (hx : G.arity x = nhub) :
    (G.face : G.Dart → G.Dart)^[hubSubn nhub i j]
        ((G.face : G.Dart → G.Dart)^[j] x) =
      (G.face : G.Dart → G.Dart)^[i] x := by
  unfold hubSubn
  by_cases hji : j ≤ i
  · simp [hji]
    calc
      (G.face : G.Dart → G.Dart)^[i - j]
          ((G.face : G.Dart → G.Dart)^[j] x) =
          (G.face : G.Dart → G.Dart)^[i - j + j] x := by
            exact (Function.iterate_add_apply
              (f := (G.face : G.Dart → G.Dart)) (i - j) j x).symm
      _ = (G.face : G.Dart → G.Dart)^[i] x := by
        rw [Nat.sub_add_cancel hji]
  · simp [hji]
    have hle : j ≤ i + nhub := by omega
    calc
      (G.face : G.Dart → G.Dart)^[i + nhub - j]
          ((G.face : G.Dart → G.Dart)^[j] x) =
          (G.face : G.Dart → G.Dart)^[i + nhub - j + j] x := by
            exact (Function.iterate_add_apply
              (f := (G.face : G.Dart → G.Dart)) (i + nhub - j) j x).symm
      _ = (G.face : G.Dart → G.Dart)^[i + nhub] x := by
        rw [Nat.sub_add_cancel hle]
      _ = (G.face : G.Dart → G.Dart)^[i] x := by
        rw [Nat.add_comm i nhub, Function.iterate_add_apply]
        have hcycle :
            (G.face : G.Dart → G.Dart)^[nhub]
                ((G.face : G.Dart → G.Dart)^[i] x) =
              (G.face : G.Dart → G.Dart)^[i] x := by
          simpa [Hypermap.arity_face_iter, hx] using
            G.face_iterate_arity ((G.face : G.Dart → G.Dart)^[i] x)
        exact hcycle

end Hubcap

end Discharge

end FourColor

end Schematic.Math.GraphTheory
