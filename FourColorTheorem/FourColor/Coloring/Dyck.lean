import Mathlib.Data.Nat.Bits

/-!
Dyck/Raney number recurrence.

This ports the arithmetic front of Gonthier's `dyck.v`, used by the initial
trace-tree and chromogram-tree constructions.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- Generalized Dyck/Raney numbers.  `genDyck m n` counts fragments of length
`n` with `m - 1` extra closing brackets. -/
def genDyck (m : Nat) : Nat → Nat
  | 0 => if m = 1 then 1 else 0
  | n + 1 =>
      match m with
      | 0 => 0
      | m' + 1 => genDyck (m + 1) n + genDyck m' n

/-- Ordinary Dyck numbers. -/
def dyck (n : Nat) : Nat :=
  genDyck 1 n

@[simp]
theorem genDyck_zero_left (n : Nat) :
    genDyck 0 n = 0 := by
  cases n <;> rfl

theorem genDyck_succ_succ (m n : Nat) :
    genDyck (m + 1) (n + 1) = genDyck (m + 2) n + genDyck m n := by
  rfl

theorem ite_genDyck_succ_succ
    (p : Prop) [Decidable p] (m n : Nat) :
    (if p then genDyck (m + 1) (n + 1) else 0) =
      (if p then genDyck (m + 2) n else 0) +
        (if p then genDyck m n else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp, if_pos hp, genDyck_succ_succ]
  · rw [if_neg hp, if_neg hp, if_neg hp]

theorem ite_genDyck_succ_one_add
    (p : Prop) [Decidable p] (m n : Nat) :
    (if p then genDyck (m + 1) (1 + n) else 0) =
      (if p then genDyck (m + 2) n else 0) +
        (if p then genDyck m n else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp, if_pos hp, Nat.one_add,
      genDyck_succ_succ]
  · rw [if_neg hp, if_neg hp, if_neg hp]

@[simp]
theorem dyck_zero :
    dyck 0 = 1 := rfl

@[simp]
theorem dyck_two :
    dyck 2 = 1 := rfl

@[simp]
theorem dyck_four :
    dyck 4 = 2 := rfl

theorem genDyck_max :
    ∀ (m n : Nat), n + 1 < m → genDyck m n = 0
  | 0, n, _ => by
      cases n <;> rfl
  | 1, n, h => by
      omega
  | m + 2, 0, _ => by
      simp [genDyck]
  | m + 2, n + 1, h => by
      have h₁ : n + 1 < (m + 2) + 1 := by omega
      have h₂ : n + 1 < m + 1 := by omega
      simp [genDyck, genDyck_max ((m + 2) + 1) n h₁,
        genDyck_max (m + 1) n h₂]

theorem genDyck_all_close :
    ∀ m : Nat, genDyck (m + 1) m = 1
  | 0 => by
      simp [genDyck]
  | m + 1 => by
      have hmax : genDyck ((m + 2) + 1) m = 0 := by
        exact genDyck_max ((m + 2) + 1) m (by omega)
      simp [genDyck, hmax, genDyck_all_close m]

theorem dyck_add_two (n : Nat) :
    dyck (n + 2) = genDyck 3 n + dyck n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

theorem dyck_pos_of_bodd_false :
    ∀ n : Nat, n.bodd = false → 0 < dyck n
  | 0, _ => by simp
  | 1, h => by simp at h
  | Nat.succ (Nat.succ n), h => by
      have hstep : (Nat.succ (Nat.succ n)).bodd = n.bodd := by
        rw [Nat.bodd_succ, Nat.bodd_succ]
        cases n.bodd <;> rfl
      have hprev : n.bodd = false := by
        rwa [hstep] at h
      change 0 < dyck (n + 2)
      rw [dyck_add_two]
      have ih := dyck_pos_of_bodd_false n hprev
      omega

end FourColor

end Schematic.Math.GraphTheory
