import Mathlib.Data.Bool.Basic

/-! A tree-independent Boolean predicate partition invariant. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Bool

/-- `left` and `right` are disjoint Boolean predicates whose union is
`whole`. -/
def SpecPartition {α : Type*}
    (whole left right : α → Bool) : Prop :=
  (∀ x, whole x = (left x || right x)) ∧
    ∀ x, left x = true → right x = false

theorem specPartition_symm
    {α : Type*} {whole left right : α → Bool}
    (h : SpecPartition whole left right) :
    SpecPartition whole right left := by
  constructor
  · intro x
    rw [h.1 x, Bool.or_comm]
  · intro x hr
    cases hl : left x <;> simp
    have := h.2 x hl
    simp [hr] at this

end Bool

end FourColor

end Schematic.Math.GraphTheory
