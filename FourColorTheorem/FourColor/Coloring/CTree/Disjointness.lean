import FourColorTheorem.FourColor.Coloring.CTree.TraceOperations

/-! Disjointness semantics for trace-coloring trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem mem_disjoint :
    ∀ (tl tr : CTree) (et : ColSeq),
      disjoint tl tr = true → mem tr et = true → mem tl et = false
  | empty, tr, et, _, _ => by
      simp [mem_empty]
  | leaf lf, empty, et, _, hmem => by
      simp [mem_empty] at hmem
  | leaf lf, leaf rf, et, hdis, _ => by
      simp [disjoint] at hdis
  | leaf lf, node r1 r2 r3, et, _, hmem => by
      cases et <;> simp [mem, sub] at hmem ⊢
  | node l1 l2 l3, empty, et, _, hmem => by
      simp [mem_empty] at hmem
  | node l1 l2 l3, leaf rf, et, _, hmem => by
      cases et <;> simp [mem, sub] at hmem ⊢
  | node l1 l2 l3, node r1 r2 r3, [], _, _ => by
      simp [mem, sub]
  | node l1 l2 l3, node r1 r2 r3, Color.zero :: et, _, _ => by
      simp [mem, sub]
  | node l1 l2 l3, node r1 r2 r3, Color.one :: et, hdis, hmem => by
      simp [disjoint] at hdis
      have hr : mem r1 et = true := by
        simpa [mem, sub] using hmem
      change mem l1 et = false
      exact mem_disjoint l1 r1 et hdis.1.1 hr
  | node l1 l2 l3, node r1 r2 r3, Color.two :: et, hdis, hmem => by
      simp [disjoint] at hdis
      have hr : mem r2 et = true := by
        simpa [mem, sub] using hmem
      change mem l2 et = false
      exact mem_disjoint l2 r2 et hdis.1.2 hr
  | node l1 l2 l3, node r1 r2 r3, Color.three :: et, hdis, hmem => by
      simp [disjoint] at hdis
      have hr : mem r3 et = true := by
        simpa [mem, sub] using hmem
      change mem l3 et = false
      exact mem_disjoint l3 r3 et hdis.2 hr

theorem exists_mem_of_disjoint_false :
    ∀ (tl tr : CTree),
      disjoint tl tr = false →
        ∃ et : ColSeq, mem tl et = true ∧ mem tr et = true
  | empty, tr, h => by
      cases tr <;> simp [disjoint] at h
  | leaf lf, empty, h => by
      simp [disjoint] at h
  | leaf lf, leaf rf, _ => by
      refine ⟨[], ?_, ?_⟩ <;> simp [mem, sub]
  | leaf lf, node r1 r2 r3, h => by
      simp [disjoint] at h
  | node l1 l2 l3, empty, h => by
      simp [disjoint] at h
  | node l1 l2 l3, leaf rf, h => by
      simp [disjoint] at h
  | node l1 l2 l3, node r1 r2 r3, h => by
      cases h1 : disjoint l1 r1 with
      | false =>
          rcases exists_mem_of_disjoint_false l1 r1 h1 with ⟨et, hl, hr⟩
          refine ⟨Color.one :: et, ?_, ?_⟩
          · simpa [mem, sub] using hl
          · simpa [mem, sub] using hr
      | true =>
          cases h2 : disjoint l2 r2 with
          | false =>
              rcases exists_mem_of_disjoint_false l2 r2 h2 with ⟨et, hl, hr⟩
              refine ⟨Color.two :: et, ?_, ?_⟩
              · simpa [mem, sub] using hl
              · simpa [mem, sub] using hr
          | true =>
              have h3 : disjoint l3 r3 = false := by
                cases h3 : disjoint l3 r3 with
                | false => rfl
                | true =>
                    simp [disjoint, h1, h2, h3] at h
              rcases exists_mem_of_disjoint_false l3 r3 h3 with ⟨et, hl, hr⟩
              refine ⟨Color.three :: et, ?_, ?_⟩
              · simpa [mem, sub] using hl
              · simpa [mem, sub] using hr

theorem disjoint_false_iff_exists_mem (tl tr : CTree) :
    disjoint tl tr = false ↔
      ∃ et : ColSeq, mem tl et = true ∧ mem tr et = true := by
  constructor
  · exact exists_mem_of_disjoint_false tl tr
  · rintro ⟨et, htl, htr⟩
    cases h : disjoint tl tr with
    | false => rfl
    | true =>
        have htl_false := mem_disjoint tl tr et h htr
        simp [htl] at htl_false

theorem disjoint_comm :
    ∀ (tl tr : CTree), disjoint tl tr = disjoint tr tl
  | empty, tr => by
      cases tr <;> rfl
  | leaf lf, tr => by
      cases tr <;> rfl
  | node l1 l2 l3, empty => rfl
  | node l1 l2 l3, leaf rf => rfl
  | node l1 l2 l3, node r1 r2 r3 => by
      simp [disjoint, disjoint_comm l1 r1,
        disjoint_comm l2 r2, disjoint_comm l3 r3]

theorem mem_disjoint_left
    (tl tr : CTree) (et : ColSeq)
    (hdis : disjoint tl tr = true)
    (hmem : mem tl et = true) :
    mem tr et = false := by
  rw [disjoint_comm] at hdis
  exact mem_disjoint tr tl et hdis hmem

theorem disjoint_true_iff_forall_no_common (tl tr : CTree) :
    disjoint tl tr = true ↔
      ∀ et : ColSeq, mem tl et = true → mem tr et = false := by
  constructor
  · intro hdis et hmem
    exact mem_disjoint_left tl tr et hdis hmem
  · intro hno
    cases hdis : disjoint tl tr with
    | false =>
        rcases exists_mem_of_disjoint_false tl tr hdis with ⟨et, htl, htr⟩
        have hfalse := hno et htl
        simp [htr] at hfalse
    | true =>
        rfl

theorem disjoint_true_iff_forall_no_common_right (tl tr : CTree) :
    disjoint tl tr = true ↔
      ∀ et : ColSeq, mem tr et = true → mem tl et = false := by
  rw [disjoint_comm]
  exact disjoint_true_iff_forall_no_common tr tl

end CTree

end FourColor

end Schematic.Math.GraphTheory
