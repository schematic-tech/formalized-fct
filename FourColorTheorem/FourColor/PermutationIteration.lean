import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Function.Iterate

/-!
Iteration lemmas for permutations.
-/

namespace Schematic.Math.GraphTheory.FourColor

universe u

namespace Equiv

theorem iterate_eq_self_of_iterate_eq
    {α : Type u} (σ : Equiv.Perm α) {x : α} {i j : Nat}
    (hij : i ≤ j)
    (h : (σ : α → α)^[i] x = (σ : α → α)^[j] x) :
    x = (σ : α → α)^[j - i] x := by
  have h' : (σ : α → α)^[i] x =
      (σ : α → α)^[i] ((σ : α → α)^[j - i] x) := by
    calc
      (σ : α → α)^[i] x = (σ : α → α)^[j] x := h
      _ = (σ : α → α)^[i + (j - i)] x := by
        rw [Nat.add_sub_of_le hij]
      _ = (σ : α → α)^[i] ((σ : α → α)^[j - i] x) := by
        rw [Function.iterate_add_apply]
  exact (σ.injective.iterate i) h'

theorem iterate_apply_symm_iterate_self
    {α : Type u} (σ : Equiv.Perm α) (n : Nat) (x : α) :
    (σ : α → α)^[n] ((σ.symm : α → α)^[n] x) = x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply'
        (f := (σ : α → α)) n ((σ.symm : α → α)^[n + 1] x)]
      rw [Function.iterate_succ_apply
        (f := (σ.symm : α → α)) n x]
      rw [ih (σ.symm x)]
      simp

theorem symm_iterate_apply_self
    {α : Type u} (σ : Equiv.Perm α) (n : Nat) (x : α) :
    (σ.symm : α → α)^[n] (σ x) =
      σ ((σ.symm : α → α)^[n] x) := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply
        (f := (σ.symm : α → α)) n (σ x)]
      rw [Function.iterate_succ_apply
        (f := (σ.symm : α → α)) n x]
      simpa using ih (σ.symm x)

theorem symm_iterate_eq_iterate_sub_of_period
    {α : Type u} (σ : Equiv.Perm α) {x : α} {m n : Nat}
    (hn : n ≤ m)
    (hperiod : (σ : α → α)^[m] x = x) :
    (σ.symm : α → α)^[n] x =
      (σ : α → α)^[m - n] x := by
  apply (σ.injective.iterate n)
  calc
    (σ : α → α)^[n] ((σ.symm : α → α)^[n] x) = x :=
      iterate_apply_symm_iterate_self σ n x
    _ = (σ : α → α)^[m] x := hperiod.symm
    _ = (σ : α → α)^[n + (m - n)] x := by
      rw [Nat.add_sub_of_le hn]
    _ = (σ : α → α)^[n] ((σ : α → α)^[m - n] x) := by
      rw [Function.iterate_add_apply]

end Equiv

end Schematic.Math.GraphTheory.FourColor
