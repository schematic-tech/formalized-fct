
import FourColorTheorem.FourColor.Discharging.Part

/-!
Preembedding vocabulary for configuration embeddings.

This ports the statement-level infrastructure around Coq `edge_central`,
`preembedding`, `good_ring_arity`, and `radius2` from `coloring.v`.  The large
extension theorem from `embed.v` will build on these definitions.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Ring-face arities accepted by the configuration embedding check.  This is
Coq `good_ring_arity`, expressed propositionally. -/
def GoodRingArity (x : G.Dart) : Prop :=
  G.arity x = 3 ∨ G.arity x = 4 ∨ G.arity x = 5 ∨ G.arity x = 6

/-- The bounded forward face-iterate index from `x` to a face-reachable dart
`y`, matching Coq's `findex face` use in the embedding construction. -/
noncomputable def faceIndex {x y : G.Dart}
    (hxy : PermReachable G.face x y) : Nat :=
  Nat.find (permReachable_exists_iterate_lt_minimalPeriod G.face hxy)

theorem faceIndex_lt_arity
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.faceIndex hxy < G.arity x := by
  let H := permReachable_exists_iterate_lt_minimalPeriod G.face hxy
  have hfind :
      Nat.find H < Function.minimalPeriod (G.face : G.Dart → G.Dart) x :=
    (Nat.find_spec H).1
  unfold faceIndex
  simpa [Hypermap.arity_eq_minimalPeriod] using hfind

theorem face_iter_faceIndex
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    ((G.face : G.Dart → G.Dart)^[G.faceIndex hxy]) x = y := by
  let H := permReachable_exists_iterate_lt_minimalPeriod G.face hxy
  have hspec :
      ((G.face : G.Dart → G.Dart)^[Nat.find H]) x = y :=
    (Nat.find_spec H).2
  unfold faceIndex
  exact hspec

theorem faceIndex_eq_of_iterate_eq_lt_arity
    {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    {n : Nat}
    (hnlt : n < G.arity x)
    (hn : ((G.face : G.Dart → G.Dart)^[n]) x = y) :
    G.faceIndex hxy = n := by
  have hidxlt : G.faceIndex hxy < G.arity x :=
    G.faceIndex_lt_arity hxy
  have hidxlt' :
      G.faceIndex hxy <
        Function.minimalPeriod (G.face : G.Dart → G.Dart) x := by
    simpa [Hypermap.arity_eq_minimalPeriod] using hidxlt
  have hnlt' :
      n < Function.minimalPeriod (G.face : G.Dart → G.Dart) x := by
    simpa [Hypermap.arity_eq_minimalPeriod] using hnlt
  exact
    (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := (G.face : G.Dart → G.Dart)) (x := x) hidxlt' hnlt').mp
      ((G.face_iter_faceIndex hxy).trans hn.symm)

theorem face_iterate_succ_mod_arity_eq
    (x : G.Dart) (n : Nat) :
    ((G.face : G.Dart → G.Dart)^[(n + 1) % G.arity x]) x =
      G.face (((G.face : G.Dart → G.Dart)^[n]) x) := by
  calc
    ((G.face : G.Dart → G.Dart)^[(n + 1) % G.arity x]) x =
        ((G.face : G.Dart → G.Dart)^[n + 1]) x := by
          rw [G.arity_eq_minimalPeriod x]
          exact Function.iterate_mod_minimalPeriod_eq
    _ = G.face (((G.face : G.Dart → G.Dart)^[n]) x) := by
          rw [Function.iterate_succ_apply']

theorem faceIndex_forward_eq_succ_mod_arity
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.faceIndex
        (PermReachable.trans G.face hxy
          (PermReachable.forward G.face y)) =
      (G.faceIndex hxy + 1) % G.arity x := by
  apply G.faceIndex_eq_of_iterate_eq_lt_arity
  · exact Nat.mod_lt _ (G.arity_pos x)
  · calc
      ((G.face : G.Dart → G.Dart)^[
          (G.faceIndex hxy + 1) % G.arity x]) x =
          G.face (((G.face : G.Dart → G.Dart)^[G.faceIndex hxy]) x) := by
            exact G.face_iterate_succ_mod_arity_eq x (G.faceIndex hxy)
      _ = G.face y := by
            exact congrArg G.face (G.face_iter_faceIndex hxy)

theorem faceIndex_eq_zero_of_eq
    {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (h : x = y) :
    G.faceIndex hxy = 0 := by
  subst y
  let H := permReachable_exists_iterate_lt_minimalPeriod G.face hxy
  unfold faceIndex
  rw [Nat.find_eq_zero]
  constructor
  · simpa [← G.arity_eq_minimalPeriod x] using G.arity_pos x
  · rfl

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
