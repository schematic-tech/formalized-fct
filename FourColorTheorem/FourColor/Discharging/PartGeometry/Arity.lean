
import FourColorTheorem.FourColor.PermutationIteration
import FourColorTheorem.FourColor.Discharging.Part
import Schematic.Math.GraphTheory.Embedding.Counts

/-!
Semantic facts connecting geometric face-size hypotheses to executable parts.

The presentation files use `Part.pconsN n` for a completely unconstrained
`n`-hub sector.  Its ranges are all `[5,∞)`, so it fits whenever every face
arity is at least five.  This file keeps that soundness layer separate from
the executable certificate files so normal development builds do not run the
0--633 reducibility checks.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

universe u

namespace Hypermap

variable {G : Hypermap.{u}}

theorem arity_face_iter (n : Nat) (x : G.Dart) :
    G.arity ((G.face : G.Dart → G.Dart)^[n] x) = G.arity x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (G.face x)).trans (G.arity_face x)

theorem arity_face_symm (x : G.Dart) :
    G.arity (G.face.symm x) = G.arity x :=
  (G.arity_eq_of_faceReachable (PermReachable.backward G.face x)).symm

theorem arity_face_symm_iter (n : Nat) (x : G.Dart) :
    G.arity ((G.face.symm : G.Dart → G.Dart)^[n] x) = G.arity x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (G.face.symm x)).trans (arity_face_symm (G := G) x)

theorem arity_edge_node_edge_node (x : G.Dart) :
    G.arity (G.edge (G.node (G.edge (G.node x)))) = G.arity x := by
  rw [Hypermap.edge_node_edge_node_eq_face_symm_face_symm]
  exact arity_face_symm_iter (G := G) 2 x

theorem node_edge_node_edge_node_eq_edge_face_symm3
    (hPlain : G.Plain) (x : G.Dart) :
    G.node (G.edge (G.node (G.edge (G.node x)))) =
      G.edge ((G.face.symm : G.Dart → G.Dart)^[3] x) := by
  calc
    G.node (G.edge (G.node (G.edge (G.node x)))) =
        G.node (G.edge (G.node (G.face.symm x))) := by
          rw [Hypermap.edge_node_eq_face_symm (G := G) x]
    _ = G.node (G.face.symm (G.face.symm x)) := by
          rw [Hypermap.edge_node_eq_face_symm (G := G) (G.face.symm x)]
    _ = G.edge ((G.face.symm : G.Dart → G.Dart)^[3] x) := by
          change G.node (G.face.symm (G.face.symm x)) =
            G.edge (G.face.symm (G.face.symm (G.face.symm x)))
          rw [← Hypermap.Plain.node_face_eq_edge (G := G) hPlain
            (G.face.symm (G.face.symm (G.face.symm x)))]
          simp

theorem face_iter_sub_arity {n : Nat} {x : G.Dart}
    (hn : n ≤ G.arity x) :
    (G.face : G.Dart → G.Dart)^[G.arity x - n]
        ((G.face : G.Dart → G.Dart)^[n] x) = x := by
  calc
    (G.face : G.Dart → G.Dart)^[G.arity x - n]
        ((G.face : G.Dart → G.Dart)^[n] x) =
        (G.face : G.Dart → G.Dart)^[G.arity x - n + n] x := by
          exact (Function.iterate_add_apply
            (f := (G.face : G.Dart → G.Dart)) (G.arity x - n) n x).symm
    _ = (G.face : G.Dart → G.Dart)^[G.arity x] x := by
      rw [Nat.sub_add_cancel hn]
    _ = x := G.face_iterate_arity x

theorem face_symm_iter_eq_face_iter_sub_arity {n : Nat} {x : G.Dart}
    (hn : n ≤ G.arity x) :
    (G.face.symm : G.Dart → G.Dart)^[n] x =
      (G.face : G.Dart → G.Dart)^[G.arity x - n] x :=
  Equiv.symm_iterate_eq_iterate_sub_of_period G.face hn
    (G.face_iterate_arity x)

theorem mirror_face_iter_eq_face_symm_iter
    (n : Nat) (x : G.Dart) :
    ((G.mirror.face : G.Dart → G.Dart)^[n] x) =
      ((G.face.symm : G.Dart → G.Dart)^[n] x) := by
  rfl

theorem mirror_face_iter_eq_face_iter_sub_arity
    {n : Nat} {x : G.Dart}
    (hn : n ≤ G.arity x) :
    ((G.mirror.face : G.Dart → G.Dart)^[n] x) =
      ((G.face : G.Dart → G.Dart)^[G.arity x - n] x) :=
  face_symm_iter_eq_face_iter_sub_arity (G := G) (x := x) (n := n) hn

theorem face_face_eq_self_of_arity_two {x : G.Dart}
    (hx : G.arity x = 2) :
    G.face (G.face x) = x := by
  have h := G.face_iterate_arity x
  simpa [hx, Function.iterate_succ_apply] using h

theorem face_symm_eq_face_of_arity_two {x : G.Dart}
    (hx : G.arity x = 2) :
    G.face.symm x = G.face x := by
  apply G.face.injective
  simp [face_face_eq_self_of_arity_two (G := G) hx]

theorem face_iter_mod_eq_of_period {m n : Nat} {x : G.Dart}
    (hperiod : (G.face : G.Dart → G.Dart)^[n] x = x) :
    (G.face : G.Dart → G.Dart)^[m % n] x =
      (G.face : G.Dart → G.Dart)^[m] x := by
  have hmul : ∀ k : Nat,
      (G.face : G.Dart → G.Dart)^[n * k] x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          (G.face : G.Dart → G.Dart)^[n * (k + 1)] x =
              (G.face : G.Dart → G.Dart)^[n * k + n] x := by
                rw [Nat.mul_succ]
          _ = (G.face : G.Dart → G.Dart)^[n * k]
                ((G.face : G.Dart → G.Dart)^[n] x) := by
                rw [Function.iterate_add_apply]
          _ = (G.face : G.Dart → G.Dart)^[n * k] x := by
                rw [hperiod]
          _ = x := ih
  have hmain :
      (G.face : G.Dart → G.Dart)^[m] x =
        (G.face : G.Dart → G.Dart)^[m % n] x := by
    calc
      (G.face : G.Dart → G.Dart)^[m] x =
          (G.face : G.Dart → G.Dart)^[m % n + n * (m / n)] x := by
            rw [Nat.mod_add_div]
      _ = (G.face : G.Dart → G.Dart)^[m % n]
            ((G.face : G.Dart → G.Dart)^[n * (m / n)] x) := by
            rw [Function.iterate_add_apply]
      _ = (G.face : G.Dart → G.Dart)^[m % n] x := by
            rw [hmul]
  exact hmain.symm

theorem face_iter_mod_arity {m : Nat} {x : G.Dart} :
    (G.face : G.Dart → G.Dart)^[m % G.arity x] x =
      (G.face : G.Dart → G.Dart)^[m] x :=
  face_iter_mod_eq_of_period (G := G) (G.face_iterate_arity x)

theorem Pentagonal.ne_face_iterate_of_pos_le_four
    (hG : G.Pentagonal) (x : G.Dart) {n : Nat}
    (hpos : 0 < n) (hle : n ≤ 4) :
    x ≠ (G.face : G.Dart → G.Dart)^[n] x := by
  rcases n with _ | n
  · cases hpos
  rcases n with _ | n
  · simpa using (hG x).1
  rcases n with _ | n
  · simpa [Function.iterate_succ_apply] using (hG x).2.1
  rcases n with _ | n
  · simpa [Function.iterate_succ_apply] using (hG x).2.2.1
  rcases n with _ | n
  · simpa [Function.iterate_succ_apply] using (hG x).2.2.2
  · have : ¬ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) ≤ 4 := by
      omega
    exact False.elim (this hle)

/-- Pentagonality gives the executable lower arity bound used by free parts:
the first five face iterates embed in the face class. -/
theorem arity_ge_five_of_pentagonal
    (hG : G.Pentagonal) (x : G.Dart) :
    5 ≤ G.arity x := by
  letI : Finite (G.FaceClass x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let f : Fin 5 → G.FaceClass x := fun i =>
    ⟨(G.face : G.Dart → G.Dart)^[i.val] x,
      permReachable_of_iterate_eq G.face rfl⟩
  have hdistinct :
      ∀ {n : Nat}, 0 < n → n ≤ 4 →
        x ≠ (G.face : G.Dart → G.Dart)^[n] x :=
    Pentagonal.ne_face_iterate_of_pos_le_four hG x
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    by_cases hij : i.val ≤ j.val
    · have hself :=
        Equiv.iterate_eq_self_of_iterate_eq G.face hij (Subtype.ext_iff.mp h)
      by_cases heq : i.val = j.val
      · exact heq
      · have hpos : 0 < j.val - i.val :=
          Nat.sub_pos_of_lt (lt_of_le_of_ne hij heq)
        have hle : j.val - i.val ≤ 4 := by omega
        exact False.elim ((hdistinct hpos hle) hself)
    · have hji : j.val ≤ i.val := le_of_lt (Nat.lt_of_not_ge hij)
      have hself :=
        Equiv.iterate_eq_self_of_iterate_eq G.face hji
          (Subtype.ext_iff.mp h).symm
      have hne : j.val ≠ i.val := by omega
      have hpos : 0 < i.val - j.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hji hne)
      have hle : i.val - j.val ≤ 4 := by omega
      exact False.elim ((hdistinct hpos hle) hself)
  have hle := Nat.card_le_card_of_injective f hinj
  simpa [Hypermap.arity] using hle

theorem ne_face_iterate_of_arity_ge_five
    (hG : ∀ x : G.Dart, 5 ≤ G.arity x) (x : G.Dart) {n : Nat}
    (hpos : 0 < n) (hle : n ≤ 4) :
    x ≠ (G.face : G.Dart → G.Dart)^[n] x := by
  intro hreturn
  have hperiod :
      (G.face : G.Dart → G.Dart)^[n] x = x := hreturn.symm
  have hdvd : G.arity x ∣ n :=
    G.arity_dvd_of_face_iterate_eq_self hperiod
  have harity_le : G.arity x ≤ n :=
    Nat.le_of_dvd hpos hdvd
  have hfive : 5 ≤ G.arity x := hG x
  omega

theorem pentagonal_of_arity_ge_five
    (hG : ∀ x : G.Dart, 5 ≤ G.arity x) :
    G.Pentagonal := by
  intro x
  constructor
  · simpa using
      ne_face_iterate_of_arity_ge_five (G := G) hG x
        (n := 1) (by omega) (by omega)
  · constructor
    · simpa [Function.iterate_succ_apply] using
        ne_face_iterate_of_arity_ge_five (G := G) hG x
          (n := 2) (by omega) (by omega)
    · constructor
      · simpa [Function.iterate_succ_apply] using
          ne_face_iterate_of_arity_ge_five (G := G) hG x
            (n := 3) (by omega) (by omega)
      · simpa [Function.iterate_succ_apply] using
          ne_face_iterate_of_arity_ge_five (G := G) hG x
            (n := 4) (by omega) (by omega)

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
