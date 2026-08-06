
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import FourColorTheorem.FourColor.Discharging.PartGeometry

/-!
Discharging rule data.

This starts the port of Coq `discharge.v`.  The concrete Robertson--Sanders--
Seymour--Thomas discharge rules are represented as `Part`s; subsequent files
use the selector and sorting functions here to bound score transfers during
the unavoidability presentations.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

open PRange
open Part
open PartRel

/-- Lists of discharging parts. -/
abbrev Drules := List Part

namespace Discharge

namespace RuleSyntax

def nil : Part := Pnil

/-- Coq notation `$ s p`: free hat, specified spoke. -/
def spoke (s : PRange) (p : Part) : Part :=
  Pcons s Pr59 p

/-- Coq notation `$[h] s p`. -/
def hat (h s : PRange) (p : Part) : Part :=
  Pcons s h p

/-- Coq notation `$[h f1] 6 p`. -/
def fan6 (h f1 : PRange) (p : Part) : Part :=
  Pcons6 h f1 p

/-- Coq notation `$[h f1 f2] 7 p`. -/
def fan7 (h f1 f2 : PRange) (p : Part) : Part :=
  Pcons7 h f1 f2 p

/-- Coq notation `$[h f1 f2 f3] 8 p`. -/
def fan8 (h f1 f2 f3 : PRange) (p : Part) : Part :=
  Pcons8 h f1 f2 f3 p

end RuleSyntax

open RuleSyntax

def drule1 : Part :=
  spoke Pr59 (spoke Pr59 (spoke Pr69 (spoke Pr59 (spoke Pr59 nil))))

def drule2 : Part :=
  spoke Pr59 (spoke Pr55 (spoke Pr79 (spoke Pr59 (spoke Pr59 nil))))

def drule2' : Part :=
  spoke Pr59 (spoke Pr55 (spoke Pr79
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule3 : Part :=
  spoke Pr55 (spoke Pr56 (spoke Pr69 (spoke Pr59 (spoke Pr59 nil))))

def drule3' : Part :=
  spoke Pr55 (spoke Pr56 (spoke Pr69
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule4 : Part :=
  spoke Pr56 (hat Pr55 Pr55 (spoke Pr69
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule4' : Part :=
  spoke Pr56 (hat Pr55 Pr66 (spoke Pr69
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule5 : Part :=
  spoke Pr66 (fan6 Pr56 Pr55 (spoke Pr69
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule6 : Part :=
  spoke Pr66 (hat Pr56 Pr55 (hat Pr55 Pr79
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule7 : Part :=
  spoke Pr66 (fan6 Pr66 Pr56 (hat Pr55 Pr79
    (spoke Pr59 (spoke Pr59 (spoke Pr59 nil)))))

def drule8 : Part :=
  spoke Pr55 (spoke Pr56 (spoke Pr79
    (spoke Pr59 (spoke Pr59 (spoke Pr59 (spoke Pr59 nil))))))

def drule9 : Part :=
  spoke Pr56 (spoke Pr56 (spoke Pr79
    (spoke Pr59 (spoke Pr59 (spoke Pr59 (spoke Pr55 nil))))))

def drule10 : Part :=
  spoke Pr55 (spoke Pr55 (spoke Pr79
    (spoke Pr55 (spoke Pr69 (spoke Pr59 (spoke Pr59 nil))))))

def drule10' : Part :=
  spoke Pr55 (spoke Pr55 (spoke Pr79
    (spoke Pr55 (spoke Pr55 (spoke Pr59 (spoke Pr59 nil))))))

def drule11 : Part :=
  spoke Pr66 (hat Pr55 Pr55 (spoke Pr79
    (spoke Pr55 (spoke Pr69 (spoke Pr59 (spoke Pr59 nil))))))

def drule12 : Part :=
  spoke Pr55 (hat Pr55 Pr55 (spoke Pr79
    (spoke Pr55 (hat Pr55 Pr55 (spoke Pr59 (spoke Pr59 nil))))))

def drule13 : Part :=
  spoke Pr66 (hat Pr55 Pr55 (hat Pr55 Pr89
    (spoke Pr55 (spoke Pr55 (spoke Pr59 (spoke Pr59 nil))))))

def drule14 : Part :=
  spoke Pr55 (hat Pr55 Pr66 (spoke Pr79
    (spoke Pr55 (spoke Pr59 (spoke Pr59 (spoke Pr59 nil))))))

def drule15 : Part :=
  spoke Pr55 (spoke Pr66 (spoke Pr79
    (spoke Pr55 (spoke Pr79 (spoke Pr55 (spoke Pr66 nil))))))

def drule16 : Part :=
  spoke Pr66 (spoke Pr66 (spoke Pr79
    (spoke Pr55 (spoke Pr55 (spoke Pr55 (spoke Pr66 nil))))))

def drule17 : Part :=
  spoke Pr55 (hat Pr66 Pr66 (spoke Pr79
    (spoke Pr55 (spoke Pr55 (spoke Pr79 (spoke Pr55 nil))))))

def drule18 : Part :=
  spoke Pr66 (hat Pr55 Pr55 (hat Pr55 Pr77
    (spoke Pr69 (spoke Pr59 (spoke Pr59 (spoke Pr55 nil))))))

def drule19 : Part :=
  spoke Pr66 (spoke Pr69 (spoke Pr89
    (hat Pr55 Pr55 (hat Pr55 Pr66 (spoke Pr55 (spoke Pr66 nil))))))

def drule20 : Part :=
  spoke Pr55 (spoke Pr66 (spoke Pr79
    (spoke Pr66 (spoke Pr66 (spoke Pr55 (spoke Pr55 nil))))))

def drule21 : Part :=
  spoke Pr56 (spoke Pr66 (hat Pr55 Pr77
    (spoke Pr69 (spoke Pr59 (spoke Pr55 (spoke Pr55 nil))))))

def drule22 : Part :=
  spoke Pr55 (spoke Pr66 (hat Pr55 Pr77
    (spoke Pr69 (spoke Pr59 (spoke Pr55 (spoke Pr66 nil))))))

def drule23 : Part :=
  spoke Pr55 (hat Pr55 Pr77 (spoke Pr79
    (spoke Pr55 (spoke Pr59 (spoke Pr59 (spoke Pr59 nil))))))

def drule24 : Part :=
  spoke Pr55 (spoke Pr55 (hat Pr55 Pr77
    (spoke Pr79 (spoke Pr66 (spoke Pr66 (spoke Pr55 nil))))))

def drule25 : Part :=
  spoke Pr55 (spoke Pr55 (spoke Pr79
    (fan7 Pr59 Pr59 Pr55
      (hat Pr66 Pr55 (spoke Pr55 (spoke Pr59 nil))))))

def drule26 : Part :=
  spoke Pr66 (spoke Pr66 (hat Pr55 Pr77
    (spoke Pr79 (spoke Pr55 (spoke Pr55 (spoke Pr66 nil))))))

def drule27 : Part :=
  spoke Pr79 (spoke Pr66 (fan7 Pr66 Pr55 Pr69
    (spoke Pr77 (hat Pr55 Pr56 (spoke Pr59 (spoke Pr59 nil))))))

def drule28 : Part :=
  spoke Pr55 (spoke Pr55 (spoke Pr79
    (spoke Pr55 (spoke Pr55 (spoke Pr59 (spoke Pr59 (spoke Pr55 nil)))))))

def drule29 : Part :=
  spoke Pr55 (hat Pr55 Pr55 (spoke Pr79
    (spoke Pr55 (spoke Pr59 (spoke Pr59 (spoke Pr55 (spoke Pr55 nil)))))))

def drule30 : Part :=
  spoke Pr55 (spoke Pr55 (spoke Pr79
    (spoke Pr55 (hat Pr55 Pr66 (spoke Pr55 (spoke Pr59 (spoke Pr59 nil)))))))

def drule31 : Part :=
  spoke Pr55 (hat Pr55 Pr55 (spoke Pr79
    (spoke Pr55 (hat Pr69 Pr55 (spoke Pr69 (spoke Pr59 (spoke Pr69 nil)))))))

def drule31' : Part :=
  spoke Pr55 (hat Pr55 Pr55 (spoke Pr79
    (spoke Pr55 (hat Pr55 Pr55 (spoke Pr69 (spoke Pr59 (spoke Pr69 nil)))))))

def drule32 : Part :=
  spoke Pr55 (spoke Pr66 (hat Pr55 Pr77
    (spoke Pr79 (spoke Pr66 (spoke Pr55 (spoke Pr55 (spoke Pr55 nil)))))))

/-- The 38 base discharge rules, with the same multiplicities as Coq. -/
def baseDrules : Drules :=
  [drule1, drule1, drule2, drule2', drule3, drule3', drule4, drule4',
    drule5, drule6, drule7, drule8, drule9, drule10, drule10',
    drule11, drule12, drule13, drule14, drule15, drule16, drule17,
    drule18, drule19, drule20, drule21, drule22, drule23, drule24,
    drule25, drule26, drule27, drule28, drule29, drule30, drule31,
    drule31', drule32]

theorem length_baseDrules :
    baseDrules.length = 38 := by
  rfl

theorem baseDrules_all_size_pos :
    (baseDrules.all (fun p => decide (1 ≤ p.size))) = true := by
  fct_decide

theorem one_le_size_of_mem_baseDrules {p : Part}
    (hp : p ∈ baseDrules) :
    1 ≤ p.size := by
  have h := List.all_eq_true.mp baseDrules_all_size_pos p hp
  exact of_decide_eq_true h

/-- The third-spoke symmetric variant added for non-symmetric rules. -/
def symmetricRule (p : Part) : Part :=
  ((Part.rotate (p.size - 1))^[5]) p.mirror

@[simp]
theorem size_symmetricRule (p : Part) :
    (symmetricRule p).size = p.size := by
  simp [symmetricRule, Part.size_mirror]

/-- Coq `dscore_mirror` introduces
`rp i = iter i (rot_part (size_part p).-1) (mirror_part p)` and proves that
fitting `rp i` at `x` is the same as fitting `mirror_part p` at the `i`th
face successor of `x`.  This is the specialized `i = 5` form used by the
symmetrized discharge-rule list. -/
theorem exactFitp_symmetricRule_eq_face_iter_mirror
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hpos : 1 ≤ p.size) :
    Part.exactFitp G x (symmetricRule p) =
      Part.exactFitp G ((G.face : G.Dart → G.Dart)^[5] x) p.mirror := by
  have hposMirror : 1 ≤ p.mirror.size := by
    simpa [Part.size_mirror] using hpos
  have h := Part.exactFitp_iterate_rotate_pred_eq_face_iter
    (G := G) (p := p.mirror) (x := x) hposMirror 5
  simpa [symmetricRule, Part.size_mirror] using h

/-- Complete a discharge-rule list by adding symmetric variants when needed. -/
def symmetrizeDrules : Drules → Drules
  | [] => []
  | p :: ps =>
      let p' := symmetricRule p
      let psr := p :: symmetrizeDrules ps
      match Part.cmp p p' with
      | Psubset => psr
      | _ => p' :: psr

/-- The exact discharge-rule list used for score transfer. -/
def theDrules : Drules :=
  symmetrizeDrules baseDrules

theorem length_theDrules :
    theDrules.length = 71 := by
  fct_decide

/-- Select source rules of a fixed hub size. -/
def pickSourceDrules (nhub : Nat) (rs : Drules) : Drules :=
  rs.filter (fun p => p.size == nhub)

/-- Select target rules whose converse part admits a fixed hub size. -/
def pickTargetDrules (nhub : Nat) : Drules → Drules
  | [] => []
  | p :: ps =>
      let (u, p') := p.converse
      let tr := pickTargetDrules nhub ps
      if u nhub then p' :: tr else tr

/-- Result of sorting rules against a part: forced rule count and straddlers. -/
structure SortDrulesResult where
  nbForcedDrules : Nat
  straddlingDrules : Drules
  deriving Repr

/-- Sort rules by comparison against a part. -/
def sortDrulesRec (p : Part) (n : Nat) (rs : Drules) : Drules →
    SortDrulesResult
  | [] => ⟨n, rs⟩
  | p' :: ps =>
      match Part.cmp p p' with
      | Psubset => sortDrulesRec p (n + 1) rs ps
      | Pstraddle => sortDrulesRec p n (p' :: rs) ps
      | Pdisjoint => sortDrulesRec p n rs ps

def sortDrules (p : Part) (rs : Drules) : SortDrulesResult :=
  sortDrulesRec p 0 [] rs

theorem sortDrulesRec_nbForced_add_length_le (p : Part) :
    ∀ (todo acc : Drules) (n : Nat),
      (sortDrulesRec p n acc todo).nbForcedDrules +
          (sortDrulesRec p n acc todo).straddlingDrules.length ≤
        n + acc.length + todo.length := by
  intro todo
  induction todo with
  | nil =>
      intro acc n
      simp [sortDrulesRec]
  | cons r todo ih =>
      intro acc n
      simp [sortDrulesRec]
      cases Part.cmp p r <;> simp
      · have h := ih acc n
        omega
      · have h := ih (r :: acc) n
        simp at h
        omega
      · have h := ih acc (n + 1)
        omega

theorem sortDrules_nbForced_add_length_le (p : Part) (rs : Drules) :
    (sortDrules p rs).nbForcedDrules +
        (sortDrules p rs).straddlingDrules.length ≤ rs.length := by
  have h := sortDrulesRec_nbForced_add_length_le p rs [] 0
  simpa [sortDrules] using h

/-- Predicate recording the intended computed source/target specializations
for a hub size. -/
inductive DruleForkValues (nhub : Nat) : Drules → Drules → Prop
  | mk :
      DruleForkValues nhub
        (pickSourceDrules nhub theDrules)
        (pickTargetDrules nhub theDrules)

/-- Specialized source and target rule lists for a fixed hub size. -/
structure DruleFork (nhub : Nat) where
  sourceDrules : Drules
  targetDrules : Drules
  values : DruleForkValues nhub sourceDrules targetDrules

/-- Canonical computed fork for a hub size. -/
def theDruleFork (nhub : Nat) : DruleFork nhub where
  sourceDrules := pickSourceDrules nhub theDrules
  targetDrules := pickTargetDrules nhub theDrules
  values := DruleForkValues.mk

/-- Count true values produced by a Boolean predicate. -/
def countBy {α : Type _} (f : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + countBy f xs

theorem countBy_le_length {α : Type _} (f : α → Bool) :
    ∀ xs : List α, countBy f xs ≤ xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : f x = true
      · simp [countBy, hx]
        omega
      · have hx' : f x = false := by
          cases hfx : f x with
          | false => rfl
          | true => exact (False.elim (hx hfx))
        simp [countBy, hx']
        omega

theorem countBy_filter {α : Type _} (f keep : α → Bool) :
    ∀ xs : List α,
      countBy f (xs.filter keep) = countBy (fun x => keep x && f x) xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hk : keep x = true
      · by_cases hf : f x = true
        · simp [List.filter, countBy, hk, hf, ih]
        · have hf' : f x = false := by
            cases hfx : f x with
            | false => rfl
            | true => exact False.elim (hf hfx)
          simp [List.filter, countBy, hk, hf', ih]
      · have hk' : keep x = false := by
          cases hkx : keep x with
          | false => rfl
          | true => exact False.elim (hk hkx)
        simp [List.filter, countBy, hk', ih]

theorem theDrules_all_size_Pr58 :
    (theDrules.all (fun p => PRange.Pr58 p.size)) = true := by
  fct_decide

theorem size_Pr58_of_mem_theDrules {p : Part}
    (hp : p ∈ theDrules) :
    PRange.Pr58 p.size = true :=
  List.all_eq_true.mp theDrules_all_size_Pr58 p hp

theorem pickSourceDrules_eq_nil_of_not_Pr58 {nhub : Nat}
    (h : PRange.Pr58 nhub = false) :
    pickSourceDrules nhub theDrules = [] := by
  rw [pickSourceDrules]
  apply List.filter_eq_nil_iff.mpr
  intro p hp hkeep
  have hp58 : PRange.Pr58 p.size = true :=
    size_Pr58_of_mem_theDrules hp
  simp at hkeep
  rw [hkeep, h] at hp58
  cases hp58

end Discharge

end FourColor

end Schematic.Math.GraphTheory
