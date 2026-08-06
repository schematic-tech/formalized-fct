
import FourColorTheorem.FourColor.Hypermap.EulerInequality
import FourColorTheorem.FourColor.Hypermap.Patch

/-!
The Euler-tree selector used by the Kempe reduction.

Coq proves a stronger Jordan-only theorem (`Euler_tree`) for an arbitrary
edge orbit.  `Kempe_map` applies it to the perimeter node orbit of a plain
Euler-planar map.  In that specialized setting the required conclusion has a
shorter count proof: if every perimeter dart is sent by `face` to a distinct
perimeter dart, the perimeter is a whole component.  That component would
have one node orbit, two darts per edge orbit, and at most one face orbit per
two darts, contradicting Euler equality.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

private theorem mem_apply_iff_of_maps_to
    {alpha : Type u} [DecidableEq alpha]
    {f : alpha -> alpha} (hf : Function.Injective f)
    {r : List alpha}
    (hclosed : forall x, x ∈ r -> f x ∈ r)
    (x : alpha) :
    f x ∈ r ↔ x ∈ r := by
  classical
  let s : Finset alpha := r.toFinset
  have hsub : s.image f ⊆ s := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact List.mem_toFinset.mpr
      (hclosed z (List.mem_toFinset.mp hz))
  have hcard : (s.image f).card = s.card :=
    Finset.card_image_of_injective s hf
  have heq : s.image f = s :=
    Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcard.symm)
  constructor
  · intro hfx
    have hmem : f x ∈ s.image f := by
      rw [heq]
      exact List.mem_toFinset.mpr hfx
    rcases Finset.mem_image.mp hmem with ⟨y, hy, hyx⟩
    have : y = x := hf hyx
    simpa [this] using List.mem_toFinset.mp hy
  · exact hclosed x

/-- A fixed-point-free finite permutation has at most half as many orbits as
points. -/
theorem two_mul_permOrbitCount_le_card_of_no_fixed
    {alpha : Type u} [Fintype alpha]
    (sigma : Equiv.Perm alpha)
    (hfixed : forall x, sigma x ≠ x) :
    2 * Nat.card (PermOrbit sigma) ≤ Fintype.card alpha := by
  classical
  rw [← sum_permClass_card_eq_card sigma]
  calc
    2 * Nat.card (PermOrbit sigma) =
        ∑ o : PermOrbit sigma, 2 := by
      simp [Nat.card_eq_fintype_card, Nat.mul_comm]
    _ ≤ ∑ o : PermOrbit sigma,
          Nat.card (PermClass sigma (Quotient.out o)) := by
      apply Finset.sum_le_sum
      intro o _
      let x := Quotient.out o
      let a : PermClass sigma x :=
        ⟨x, PermReachable.refl sigma x⟩
      let b : PermClass sigma x :=
        ⟨sigma x, PermReachable.forward sigma x⟩
      have hab : a ≠ b := by
        intro h
        exact hfixed x (Subtype.ext_iff.mp h).symm
      letI : Nontrivial (PermClass sigma x) := ⟨⟨a, b, hab⟩⟩
      exact Finite.one_lt_card

/-- The exact selector extracted from Coq `Euler_tree` in its `Kempe_map`
application.  A nonempty duplicate-free node cycle in a plain Euler-planar
hypermap contains a dart whose face is degenerate or leaves the cycle. -/
theorem exists_face_fixed_or_face_not_mem_nodeCycle
    (G : Hypermap.{u})
    (hplanar : G.EulerPlanar)
    (hplain : G.Plain)
    {r : List G.Dart}
    (hcycle : FunctionCycle G.node r)
    {x : G.Dart} (hx : x ∈ r) :
    ∃ z : G.Dart, z ∈ r ∧
      (G.face z = z ∨ G.face z ∉ r) := by
  classical
  by_contra hnone
  have hbad : forall z, z ∈ r ->
      G.face z ≠ z ∧ G.face z ∈ r := by
    intro z hz
    have hzbad : ¬ (G.face z = z ∨ G.face z ∉ r) := by
      intro h
      exact hnone ⟨z, hz, h⟩
    exact ⟨fun h => hzbad (Or.inl h),
      not_not.mp (fun h => hzbad (Or.inr h))⟩
  have hfaceMem (z : G.Dart) :
      G.face z ∈ r ↔ z ∈ r :=
    mem_apply_iff_of_maps_to G.face.injective
      (fun y hy => (hbad y hy).2) z
  have hnodeMem (z : G.Dart) :
      G.node z ∈ r ↔ z ∈ r :=
    hcycle.image_mem_iff G.node.injective z
  have hfaceSymmMem (z : G.Dart) :
      G.face.symm z ∈ r ↔ z ∈ r := by
    have h := hfaceMem (G.face.symm z)
    simpa using h.symm
  have hnodeSymmMem (z : G.Dart) :
      G.node.symm z ∈ r ↔ z ∈ r := by
    have h := hnodeMem (G.node.symm z)
    simpa using h.symm
  have hedgeMem (z : G.Dart) :
      G.edge z ∈ r ↔ z ∈ r := by
    rw [← G.mirror_edge_original z]
    exact (hfaceSymmMem (G.node.symm z)).trans (hnodeSymmMem z)
  have hlinkMem {a b : G.Dart}
      (ha : a ∈ r) (hab : G.Link a b) :
      b ∈ r := by
    rcases hab with rfl | rfl | rfl
    · exact (hedgeMem a).2 ha
    · exact (hnodeMem a).2 ha
    · exact (hfaceMem a).2 ha
  let c : G.Component := G.componentOf x
  let H : Hypermap.{u} := G.componentHypermap c
  have hreachesMem {y : G.Dart}
      (hreach : G.Reachable x y) : y ∈ r := by
    induction hreach with
    | refl => exact hx
    | tail _ hab ih => exact hlinkMem ih hab
  have hcomponentMem (y : H.Dart) : y.1 ∈ r := by
    have hcomp : G.componentOf x = G.componentOf y.1 := by
      simpa [c] using y.2.symm
    have hreach : G.Reachable x y.1 :=
      G.reachable_of_componentOf_eq hcomp
    exact hreachesMem hreach
  have hplainH : H.Plain :=
    componentHypermap.plain (G := G) (c := c) hplain
  have hplanarH : H.EulerPlanar :=
    Unavoidability.componentEulerPlanarInherited_proved G c hplanar
  have hcompCount : H.componentCount = 1 :=
    componentHypermap.componentCount_eq_one (G := G) (c := c)
  have hnodeReach : forall a b : H.Dart,
      PermReachable H.node a b := by
    intro a b
    apply componentHypermap.nodeReachable_lift (G := G) (c := c)
    exact hcycle.permReachable_of_mem_mem
      (hcomponentMem a) (hcomponentMem b)
  let xH : H.Dart := ⟨x, rfl⟩
  have hnodeCount : H.nodeOrbitCount = 1 := by
    change Nat.card (PermOrbit H.node) = 1
    exact permOrbit_count_eq_one_of_forall_reachable H.node xH hnodeReach
  have hfaceFixed : forall y : H.Dart, H.face y ≠ y := by
    intro y hy
    exact (hbad y.1 (hcomponentMem y)).1
      (Subtype.ext_iff.mp hy)
  have hfaceBound : 2 * H.faceOrbitCount ≤ Fintype.card H.Dart := by
    exact two_mul_permOrbitCount_le_card_of_no_fixed H.face hfaceFixed
  have hdart : Fintype.card H.Dart = 2 * H.edgeOrbitCount :=
    hplainH.card_dart_eq_two_mul_edgeOrbitCount
  have heuler : H.eulerLeft = H.eulerRight :=
    euler_eq_of_evenGenus_planar (Hypermap.evenGenus H) hplanarH
  unfold Hypermap.eulerLeft Hypermap.eulerRight at heuler
  omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
