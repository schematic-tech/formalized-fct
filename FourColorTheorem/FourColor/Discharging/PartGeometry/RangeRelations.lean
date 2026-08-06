import FourColorTheorem.FourColor.Discharging.PartGeometry.Arity

/-! Boolean range and part-relation semantics used by part geometry. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PRange

theorem contains_cmpRange (r q : PRange) {n : Nat}
    (hr : r n = true) :
    q n = (cmpRange r q) (q n) := by
  cases r <;> cases q <;>
    simp [cmpRange, contains, PartRel.apply] at hr ⊢ <;> omega

theorem contains_of_cmpRange_eq_subset (r q : PRange) {n : Nat}
    (hcmp : cmpRange r q = PartRel.Psubset)
    (hr : r n = true) :
    q n = true := by
  have h := contains_cmpRange r q hr
  rw [hcmp] at h
  simpa [PartRel.apply] using h

theorem contains_false_of_cmpRange_eq_disjoint (r q : PRange) {n : Nat}
    (hcmp : cmpRange r q = PartRel.Pdisjoint)
    (hr : r n = true) :
    q n = false := by
  cases r <;> cases q <;>
    simp [cmpRange, contains] at hcmp hr ⊢ <;> omega

theorem contains_Pr66_false_of_Pr77 {n : Nat}
    (h : Pr77 n = true) :
    Pr66 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_Pr66_false_of_Pr88 {n : Nat}
    (h : Pr88 n = true) :
    Pr66 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_Pr77_false_of_Pr66 {n : Nat}
    (h : Pr66 n = true) :
    Pr77 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_Pr77_false_of_Pr88 {n : Nat}
    (h : Pr88 n = true) :
    Pr77 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_Pr88_false_of_Pr66 {n : Nat}
    (h : Pr66 n = true) :
    Pr88 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_Pr88_false_of_Pr77 {n : Nat}
    (h : Pr77 n = true) :
    Pr88 n = false := by
  simp [contains] at h ⊢
  omega

theorem contains_notPsubset_cmpRange (r q : PRange) {n : Nat}
    (hr : r n = true) :
    q n = (notPsubset (cmpRange r q)) (q n) := by
  cases r <;> cases q <;>
    simp [cmpRange, contains, PartRel.apply, notPsubset] at hr ⊢ <;>
      omega

theorem contains_meetRange_of_contains (r q : PRange) {n : Nat}
    (hr : r n = true) (hq : q n = true) :
    meetRange r q n = true := by
  cases r <;> cases q <;>
    simp [meetRange, contains] at hr hq ⊢ <;> omega

end PRange

namespace PartRel

theorem meetPRel_eq_subset {c d : PartRel} :
    meetPRel c d = Psubset → c = Psubset ∧ d = Psubset := by
  cases c <;> cases d <;> simp [meetPRel, notPsubset]

theorem meetPRel_eq_disjoint {c d : PartRel} :
    meetPRel c d = Pdisjoint → c = Pdisjoint ∨ d = Pdisjoint := by
  cases c <;> cases d <;> simp [meetPRel, notPsubset]

theorem notPsubset_ne_subset (c : PartRel) :
    notPsubset c ≠ Psubset := by
  cases c <;> simp [notPsubset]

theorem and_eq_meetPRel_apply {a b : Bool} {c d : PartRel}
    (ha : a = c a) (hb : b = d b) :
    (a && b) = (meetPRel c d) (a && b) := by
  cases c <;> cases d <;> cases a <;> cases b <;>
    simp [PartRel.apply, meetPRel, notPsubset] at ha hb ⊢

end PartRel

end FourColor

end Schematic.Math.GraphTheory
