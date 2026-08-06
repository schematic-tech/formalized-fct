import FourColorTheorem.FourColor.Hypermap.FunctionCycles

namespace Schematic.Math.GraphTheory

namespace FourColor

/-! ### Orbit restriction bookkeeping

MathComp's `n_compC`/`adjunction_n_comp` API counts the orbits in a closed
predicate and its complement.  The patch proof uses that API repeatedly.  We
package the corresponding finite-permutation fact here: restricting a
permutation to an invariant predicate gives exactly the ambient orbits that
satisfy that predicate.
-/

theorem permInvariant_iff_of_reachable
    {α : Type _} [Fintype α] {σ : Equiv.Perm α} {p : α → Prop}
    (hp : ∀ x, p (σ x) ↔ p x) {x y : α}
    (hxy : PermReachable σ x y) :
    p x ↔ p y := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, rfl⟩
  have hiter : ∀ n : Nat, ∀ z : α,
      p (((σ : α → α)^[n]) z) ↔ p z := by
    intro m z
    induction m generalizing z with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact (hp _).trans (ih z)
  exact (hiter n x).symm

/-- The predicate induced on permutation orbits by an invariant predicate on
points. -/
def PermOrbit.OrbitPred
    {α : Type _} [Fintype α] (σ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ x, p (σ x) ↔ p x) :
    PermOrbit σ → Prop :=
  Quotient.lift p (by
    intro x y hxy
    exact propext (permInvariant_iff_of_reachable hp hxy))

@[simp]
theorem PermOrbit.orbitPred_of
    {α : Type _} [Fintype α] (σ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ x, p (σ x) ↔ p x) (x : α) :
    PermOrbit.OrbitPred σ p hp (PermOrbit.of σ x) = p x :=
  rfl

theorem subtypePerm_iterate_val
    {α : Type _} {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm α)
    (hp : ∀ x, p (σ x) ↔ p x)
    (x : {x : α // p x}) :
    ∀ n : Nat,
      (((σ.subtypePerm hp : {x : α // p x} → {x : α // p x})^[n]) x).1 =
        ((σ : α → α)^[n]) x.1
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Equiv.Perm.subtypePerm_apply]
      simpa using subtypePerm_iterate_val σ hp ((σ.subtypePerm hp) x) n

theorem subtypePerm_permReachable_iff
    {α : Type _} [Fintype α]
    {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm α)
    (hp : ∀ x, p (σ x) ↔ p x)
    (x y : {x : α // p x}) :
    PermReachable (σ.subtypePerm hp) x y ↔
      PermReachable σ x.1 y.1 := by
  constructor
  · intro hxy
    rcases permReachable_exists_iterate (σ.subtypePerm hp) hxy with ⟨n, hn⟩
    apply permReachable_of_iterate_eq σ
    rw [← subtypePerm_iterate_val σ hp x]
    exact congrArg Subtype.val hn
  · intro hxy
    rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
    apply permReachable_of_iterate_eq (σ.subtypePerm hp)
    apply Subtype.ext
    rw [subtypePerm_iterate_val σ hp x]
    exact hn

/-- Restricting a finite permutation to an invariant predicate identifies its
orbits with the ambient orbits satisfying that predicate. -/
noncomputable def PermOrbit.restrictedOrbitMap
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    PermOrbit (σ.subtypePerm hp) →
      {o : PermOrbit σ // PermOrbit.OrbitPred σ p hp o} :=
  Quotient.lift
    (fun x => ⟨PermOrbit.of σ x.1, x.2⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      exact PermOrbit.of_eq_of σ
        ((subtypePerm_permReachable_iff σ hp x y).1 hxy))

@[simp]
theorem PermOrbit.restrictedOrbitMap_of
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) (x : {x : α // p x}) :
    PermOrbit.restrictedOrbitMap σ p hp
        (PermOrbit.of (σ.subtypePerm hp) x) =
      ⟨PermOrbit.of σ x.1, x.2⟩ :=
  rfl

theorem PermOrbit.restrictedOrbitMap_injective
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    Function.Injective (PermOrbit.restrictedOrbitMap σ p hp) := by
  intro o q hoq
  refine Quotient.inductionOn₂ o q ?_ hoq
  intro x y hxy
  have hambient : PermOrbit.of σ x.1 = PermOrbit.of σ y.1 :=
    congrArg Subtype.val hxy
  exact Quot.sound
    ((subtypePerm_permReachable_iff σ hp x y).2
      (Quotient.exact hambient))

theorem PermOrbit.restrictedOrbitMap_surjective
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    Function.Surjective (PermOrbit.restrictedOrbitMap σ p hp) := by
  rintro ⟨o, ho⟩
  refine Quotient.inductionOn o ?_ ho
  intro x hx
  exact ⟨PermOrbit.of (σ.subtypePerm hp) ⟨x, hx⟩, rfl⟩

noncomputable def PermOrbit.restrictedOrbitEquiv
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    PermOrbit (σ.subtypePerm hp) ≃
      {o : PermOrbit σ // PermOrbit.OrbitPred σ p hp o} :=
  Equiv.ofBijective (PermOrbit.restrictedOrbitMap σ p hp)
    ⟨PermOrbit.restrictedOrbitMap_injective σ p hp,
      PermOrbit.restrictedOrbitMap_surjective σ p hp⟩

/-- The orbit-subtype presentation of an invariant face predicate agrees with
the existential `FaceOrbitMeeting` presentation used for Coq `fcard`. -/
noncomputable def Hypermap.faceOrbitPredEquivMeeting
    (G : Hypermap) (p : G.Dart → Prop)
    (hp : ∀ x, p (G.face x) ↔ p x) :
    {o : G.FaceOrbit // PermOrbit.OrbitPred G.face p hp o} ≃
      G.FaceOrbitMeeting p := by
  classical
  exact Equiv.subtypeEquivRight (fun o => by
    refine Quotient.inductionOn o ?_
    intro x
    constructor
    · intro hx
      exact ⟨x, rfl, hx⟩
    · rintro ⟨y, hyx, hy⟩
      have hryx : PermReachable G.face y x := Quotient.exact hyx
      exact (permInvariant_iff_of_reachable hp hryx).1 hy)

/-- Restricting the face permutation to an invariant predicate counts exactly
the ambient face orbits meeting that predicate. -/
theorem Hypermap.restrictedFaceOrbitCount_eq_faceOrbitCountOf
    (G : Hypermap) (p : G.Dart → Prop) [DecidablePred p]
    (hp : ∀ x, p (G.face x) ↔ p x) :
    Nat.card (PermOrbit (G.face.subtypePerm hp)) =
      G.FaceOrbitCountOf p := by
  rw [Hypermap.FaceOrbitCountOf]
  exact Nat.card_congr
    ((PermOrbit.restrictedOrbitEquiv G.face p hp).trans
      (G.faceOrbitPredEquivMeeting p hp))

theorem PermOrbit.orbitPred_not_iff
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ x, p (σ x) ↔ p x)
    (o : PermOrbit σ) :
    PermOrbit.OrbitPred σ (fun x => ¬ p x)
        (fun x => not_congr (hp x)) o ↔
      ¬ PermOrbit.OrbitPred σ p hp o := by
  refine Quotient.inductionOn o ?_
  intro x
  rfl

/-- Orbit-count partition into an invariant predicate and its complement. -/
theorem PermOrbit.card_eq_restricted_add_compl
    {α : Type _} [Fintype α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    Nat.card (PermOrbit σ) =
      Nat.card (PermOrbit (σ.subtypePerm hp)) +
      Nat.card (PermOrbit
        (σ.subtypePerm (p := fun x => ¬ p x)
          (fun x => not_congr (hp x)))) := by
  classical
  let pred : PermOrbit σ → Prop := PermOrbit.OrbitPred σ p hp
  let hpNot : ∀ x, (¬ p (σ x)) ↔ ¬ p x :=
    fun x => not_congr (hp x)
  let ePos := PermOrbit.restrictedOrbitEquiv σ p hp
  let eNeg0 := PermOrbit.restrictedOrbitEquiv σ (fun x => ¬ p x) hpNot
  let eNeg :
      PermOrbit (σ.subtypePerm hpNot) ≃ {o : PermOrbit σ // ¬ pred o} :=
    eNeg0.trans (Equiv.subtypeEquivRight fun o =>
      PermOrbit.orbitPred_not_iff σ p hp o)
  calc
    Nat.card (PermOrbit σ) =
        Nat.card ({o : PermOrbit σ // pred o} ⊕
          {o : PermOrbit σ // ¬ pred o}) :=
      (Nat.card_congr (Equiv.sumCompl pred)).symm
    _ = Nat.card {o : PermOrbit σ // pred o} +
          Nat.card {o : PermOrbit σ // ¬ pred o} := Nat.card_sum
    _ = Nat.card (PermOrbit (σ.subtypePerm hp)) +
          Nat.card (PermOrbit (σ.subtypePerm hpNot)) := by
      rw [Nat.card_congr ePos.symm, Nat.card_congr eNeg.symm]

/-- A listed cycle contributes no restricted orbit when empty and one orbit
otherwise. -/
theorem FunctionCycle.restrictedOrbitCount
    {α : Type _} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (r : List α) (hc : FunctionCycle σ r) :
    Nat.card (PermOrbit
      (σ.subtypePerm (p := fun x => x ∈ r)
        (fun x => hc.image_mem_iff σ.injective x))) =
      if r = [] then 0 else 1 := by
  classical
  cases r with
  | nil =>
      rw [if_pos rfl]
      apply Nat.card_eq_zero.mpr
      left
      constructor
      intro o
      refine Quotient.inductionOn o ?_
      intro x
      have hx := x.property
      simp at hx
  | cons z zs =>
      simp only [List.cons_ne_nil, if_false]
      apply Nat.card_eq_one_iff_unique.mpr
      constructor
      · constructor
        intro o q
        refine Quotient.inductionOn₂ o q ?_
        intro x y
        apply Quot.sound
        apply (subtypePerm_permReachable_iff σ
          (fun x => hc.image_mem_iff σ.injective x) x y).2
        exact hc.permReachable_of_mem_mem x.2 y.2
      · exact ⟨PermOrbit.of
          (σ.subtypePerm (p := fun x => x ∈ z :: zs)
            (fun x => hc.image_mem_iff σ.injective x))
          ⟨z, by simp⟩⟩
end FourColor

end Schematic.Math.GraphTheory
