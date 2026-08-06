
import FourColorTheorem.FourColor.Hypermap.Patch

/-!
The special Euler formula for a connected plain map which is cubic away from
one listed node cycle.  This is Coq `geometry.v::quasicubic_Euler` and is the
cardinality engine in `Birkhoff_valid`.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

private theorem nodeComplementInvariant
    (r : List G.Dart) (hcycle : FunctionCycle G.node r) (x : G.Dart) :
    (G.node x ∉ r) ↔ x ∉ r :=
  not_congr (hcycle.image_mem_iff G.node.injective x)

/-- The hypermap used only to count node orbits outside a cyclic perimeter.
Its node permutation is the restriction of the original node permutation;
the other two permutations are chosen canonically so the hypermap law holds. -/
private noncomputable def nodeComplementMap
    (G : Hypermap.{u}) (r : List G.Dart)
    (hcycle : FunctionCycle G.node r) : Hypermap.{u} where
  Dart := {x : G.Dart // x ∉ r}
  edge := Equiv.refl _
  node := G.node.subtypePerm (nodeComplementInvariant r hcycle)
  face := (G.node.subtypePerm (nodeComplementInvariant r hcycle)).symm
  node_face_edge := by
    intro x
    simp

private theorem nodeComplementMap_cubic
    {r : List G.Dart} (hcycle : FunctionCycle G.node r)
    (hquasi : G.Quasicubic r) :
    (nodeComplementMap G r hcycle).Cubic := by
  intro x
  constructor
  · apply Subtype.ext
    change G.node (G.node (G.node x.1)) = x.1
    exact (hquasi x.1 x.2).1
  · intro hfixed
    apply (hquasi x.1 x.2).2
    exact congrArg Subtype.val hfixed

private theorem card_nodeComplementMap
    {r : List G.Dart} (hcycle : FunctionCycle G.node r)
    (hquasi : G.Quasicubic r) :
    Fintype.card {x : G.Dart // x ∉ r} =
      3 * Nat.card
        (PermOrbit
          (G.node.subtypePerm (p := fun x => x ∉ r)
            (nodeComplementInvariant r hcycle))) := by
  simpa [nodeComplementMap, Hypermap.nodeOrbitCount] using
    (nodeComplementMap_cubic hcycle hquasi).card_dart_eq_three_mul_nodeOrbitCount

private theorem card_cycleSubtype
    (r : List G.Dart) (hnodup : r.Nodup) :
    Fintype.card {x : G.Dart // x ∈ r} = r.length := by
  classical
  rw [Fintype.card_subtype]
  have hfin : ({x : G.Dart | x ∈ r} : Finset G.Dart) = r.toFinset := by
    ext x
    simp
  rw [hfin]
  exact List.toFinset_card_of_nodup hnodup

/-- Node-orbit and dart-count decomposition behind Coq
`quasicubic_Euler`. -/
theorem quasicubicNodeCounts
    {r : List G.Dart}
    (hcycle : FunctionCycle G.node r) (hnodup : r.Nodup)
    (hquasi : G.Quasicubic r) :
    let nOutside := Nat.card
      (PermOrbit
        (G.node.subtypePerm (p := fun x => x ∉ r)
          (nodeComplementInvariant r hcycle)))
    G.nodeOrbitCount = (if r = [] then 0 else 1) + nOutside ∧
      Fintype.card G.Dart = r.length + 3 * nOutside := by
  classical
  let hinv : ∀ x : G.Dart, G.node x ∈ r ↔ x ∈ r :=
    fun x => hcycle.image_mem_iff G.node.injective x
  let nOutside := Nat.card
    (PermOrbit (G.node.subtypePerm
      (p := fun x => x ∉ r) (fun x => not_congr (hinv x))))
  have horbits := PermOrbit.card_eq_restricted_add_compl
    G.node (fun x : G.Dart => x ∈ r) hinv
  have hboundary := FunctionCycle.restrictedOrbitCount G.node r hcycle
  have houtside :
      Nat.card
          (PermOrbit
            (G.node.subtypePerm
              (p := fun x => x ∉ r) (fun x => not_congr (hinv x)))) =
        nOutside := rfl
  have hnodes :
      G.nodeOrbitCount = (if r = [] then 0 else 1) + nOutside := by
    unfold Hypermap.nodeOrbitCount
    rw [horbits, hboundary]
  have hinsideCard := card_cycleSubtype (G := G) r hnodup
  have hcomplementCard :=
    Fintype.card_subtype_compl (fun x : G.Dart => x ∈ r)
  have hinsideLe := Fintype.card_subtype_le (fun x : G.Dart => x ∈ r)
  have houtsideCard :
      Fintype.card {x : G.Dart // x ∉ r} = 3 * nOutside := by
    simpa [nOutside, hinv, nodeComplementInvariant] using
      card_nodeComplementMap (G := G) hcycle hquasi
  have hdarts : Fintype.card G.Dart = r.length + 3 * nOutside := by
    rw [hinsideCard] at hcomplementCard hinsideLe
    rw [houtsideCard] at hcomplementCard
    omega
  exact ⟨hnodes, hdarts⟩

/-- Coq `quasicubic_Euler`, in equality form.  The extra face in the left
factor is present exactly when the listed node cycle is nonempty. -/
theorem quasicubicEuler
    {r : List G.Dart}
    (hcycle : FunctionCycle G.node r) (hnodup : r.Nodup)
    (hplain : G.Plain) (hquasi : G.Quasicubic r)
    (hconnected : G.Connected) :
    G.EulerPlanar ↔
      6 * ((if r = [] then 0 else 1) + G.faceOrbitCount) =
        Fintype.card G.Dart + (2 * r.length + 12) := by
  let nOutside := Nat.card
    (PermOrbit
      (G.node.subtypePerm (p := fun x => x ∉ r)
        (nodeComplementInvariant r hcycle)))
  have hcounts := quasicubicNodeCounts hcycle hnodup hquasi
  change G.nodeOrbitCount = _ ∧ _ at hcounts
  have hcomp := hconnected.componentCount_eq_one
  have hedge := hplain.card_dart_eq_two_mul_edgeOrbitCount
  constructor
  · intro hplanar
    have heuler := euler_eq_of_evenGenus_planar (Hypermap.evenGenus G) hplanar
    unfold Hypermap.eulerLeft Hypermap.eulerRight at heuler
    omega
  · intro hformula
    apply eulerPlanar_of_eulerLeft_le_eulerRight
    unfold Hypermap.eulerLeft Hypermap.eulerRight
    omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
