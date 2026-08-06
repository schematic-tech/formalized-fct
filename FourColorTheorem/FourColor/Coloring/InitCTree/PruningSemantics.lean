import FourColorTheorem.FourColor.Coloring.InitCTree.TableSemantics

/-! Pruning semantics for normalized initial trace trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree
@[simp]
theorem initTree_zero :
    initTree 0 = empty := by
  rfl

@[simp]
theorem initTree_one :
    initTree 1 = cons simpleLeaf simpleLeaf simpleLeaf := by
  rfl

@[simp]
theorem initTree_two :
    initTree 2 =
      cons (cons empty simpleLeaf empty)
        (cons empty empty simpleLeaf)
        (cons simpleLeaf empty empty) := by
  rfl

theorem proper_initTree_one :
    Proper 1 (initTree 1) := by
  rw [initTree_one]
  exact proper_cons proper_simpleLeaf proper_simpleLeaf proper_simpleLeaf

theorem sub_initTree_zero (et : ColSeq) :
    sub (initTree 0) et = initSubSpec 0 et := by
  cases et with
  | nil =>
      simp [initSubSpec, ColSeq.ctrace]
  | cons e et =>
      simp [initSubSpec]

theorem sub_initTree_one (et : ColSeq) :
    sub (initTree 1) et = initSubSpec 1 et := by
  cases et with
  | nil =>
      rw [initTree_one, sub_cons]
      rfl
  | cons e et =>
      cases et with
      | nil =>
          cases e <;> rfl
      | cons e' et =>
          rw [initTree_one, sub_cons]
          cases e <;> rfl

theorem sub_initTree_two (et : ColSeq) :
    sub (initTree 2) et = initSubSpec 2 et := by
  cases et with
  | nil =>
      rw [initTree_two, sub_cons]
      rfl
  | cons e et =>
      cases et with
      | nil =>
          rw [initTree_two, sub_cons]
          cases e <;> rfl
      | cons e' et =>
          cases et with
          | nil =>
              cases e <;> cases e' <;> rfl
          | cons e'' et =>
              rw [initTree_two, sub_cons]
              cases e with
              | zero =>
                  rfl
              | one =>
                  change sub (cons empty simpleLeaf empty) (e' :: e'' :: et) =
                    initSubSpec 2 (Color.one :: e' :: e'' :: et)
                  rw [sub_cons]
                  cases e' <;> rfl
              | two =>
                  change sub (cons empty empty simpleLeaf) (e' :: e'' :: et) =
                    initSubSpec 2 (Color.two :: e' :: e'' :: et)
                  rw [sub_cons]
                  cases e' <;> rfl
              | three =>
                  change sub (cons simpleLeaf empty empty) (e' :: e'' :: et) =
                    initSubSpec 2 (Color.three :: e' :: e'' :: et)
                  rw [sub_cons]
                  cases e' <;> rfl

@[simp]
theorem sub_prune1_nil :
    ∀ t : CTree, sub (prune1 t) [] = sub t []
  | empty => rfl
  | leaf lf => rfl
  | node t1 t2 t3 => by
      change sub (cons (prune1 t1) t2 empty) [] =
        sub (node t1 t2 t3) []
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune1_one :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune1 t) (Color.one :: et) =
      match t with
      | node t1 _ _ => sub (prune1 t1) et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons (prune1 t1) t2 empty) (Color.one :: et) =
        sub (prune1 t1) et
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune1_two :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune1 t) (Color.two :: et) =
      match t with
      | node _ t2 _ => sub t2 et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons (prune1 t1) t2 empty) (Color.two :: et) =
        sub t2 et
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune1_three :
    ∀ (t : CTree) (et : ColSeq), sub (prune1 t) (Color.three :: et) = 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons (prune1 t1) t2 empty) (Color.three :: et) = 0
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune2_nil :
    ∀ t : CTree, sub (prune2 t) [] = sub t []
  | empty => rfl
  | leaf lf => rfl
  | node t1 t2 t3 => by
      change sub (cons empty (prune2 t2) t3) [] =
        sub (node t1 t2 t3) []
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune2_one :
    ∀ (t : CTree) (et : ColSeq), sub (prune2 t) (Color.one :: et) = 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons empty (prune2 t2) t3) (Color.one :: et) = 0
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune2_two :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune2 t) (Color.two :: et) =
      match t with
      | node _ t2 _ => sub (prune2 t2) et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons empty (prune2 t2) t3) (Color.two :: et) =
        sub (prune2 t2) et
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune2_three :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune2 t) (Color.three :: et) =
      match t with
      | node _ _ t3 => sub t3 et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons empty (prune2 t2) t3) (Color.three :: et) =
        sub t3 et
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune3_nil :
    ∀ t : CTree, sub (prune3 t) [] = sub t []
  | empty => rfl
  | leaf lf => rfl
  | node t1 t2 t3 => by
      change sub (cons t1 empty (prune3 t3)) [] =
        sub (node t1 t2 t3) []
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune3_one :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune3 t) (Color.one :: et) =
      match t with
      | node t1 _ _ => sub t1 et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons t1 empty (prune3 t3)) (Color.one :: et) =
        sub t1 et
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune3_two :
    ∀ (t : CTree) (et : ColSeq), sub (prune3 t) (Color.two :: et) = 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons t1 empty (prune3 t3)) (Color.two :: et) = 0
      rw [sub_cons]
      rfl

@[simp]
theorem sub_prune3_three :
    ∀ (t : CTree) (et : ColSeq),
    sub (prune3 t) (Color.three :: et) =
      match t with
      | node _ _ t3 => sub (prune3 t3) et
      | _ => 0
  | empty, et => rfl
  | leaf lf, et => rfl
  | node t1 t2 t3, et => by
      change sub (cons t1 empty (prune3 t3)) (Color.three :: et) =
        sub (prune3 t3) et
      rw [sub_cons]
      rfl

@[simp]
theorem evenTrace_one_one (et : ColSeq) :
    ColSeq.evenTrace (Color.one :: Color.one :: et) =
      ColSeq.evenTrace (Color.one :: et) := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_one_two (et : ColSeq) :
    ColSeq.evenTrace (Color.one :: Color.two :: et) = true := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_one_three (et : ColSeq) :
    ColSeq.evenTrace (Color.one :: Color.three :: et) = false := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_two_one (et : ColSeq) :
    ColSeq.evenTrace (Color.two :: Color.one :: et) = false := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_two_two (et : ColSeq) :
    ColSeq.evenTrace (Color.two :: Color.two :: et) =
      ColSeq.evenTrace (Color.two :: et) := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_two_three (et : ColSeq) :
    ColSeq.evenTrace (Color.two :: Color.three :: et) = true := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_three_one (et : ColSeq) :
    ColSeq.evenTrace (Color.three :: Color.one :: et) = true := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_three_two (et : ColSeq) :
    ColSeq.evenTrace (Color.three :: Color.two :: et) = false := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

@[simp]
theorem evenTrace_three_three (et : ColSeq) :
    ColSeq.evenTrace (Color.three :: Color.three :: et) =
      ColSeq.evenTrace (Color.three :: et) := by
  simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
    ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot, EdgePerm.apply]

theorem sub_prune1_eq_if_evenTrace_one :
    ∀ (et : ColSeq) (t : CTree),
      sub (prune1 t) et =
        if ColSeq.evenTrace (Color.one :: et) then sub t et else 0
  | [], t => by
      rw [sub_prune1_nil]
      simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
        ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot]
  | e :: et, t => by
      cases t with
      | empty =>
          cases e <;> simp [sub]
      | leaf lf =>
          cases e <;> simp [sub]
      | node t1 t2 t3 =>
          cases e with
          | zero =>
              simp [sub]
          | one =>
              simpa [sub_prune1_one, sub] using
                sub_prune1_eq_if_evenTrace_one et t1
          | two =>
              simp [sub_prune1_two, sub]
          | three =>
              simp [sub_prune1_three]

theorem sub_prune2_eq_if_evenTrace_two :
    ∀ (et : ColSeq) (t : CTree),
      sub (prune2 t) et =
        if ColSeq.evenTrace (Color.two :: et) then sub t et else 0
  | [], t => by
      rw [sub_prune2_nil]
      simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
        ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot]
  | e :: et, t => by
      cases t with
      | empty =>
          cases e <;> simp [sub]
      | leaf lf =>
          cases e <;> simp [sub]
      | node t1 t2 t3 =>
          cases e with
          | zero =>
              simp [sub]
          | one =>
              simp [sub_prune2_one]
          | two =>
              simpa [sub_prune2_two, sub] using
                sub_prune2_eq_if_evenTrace_two et t2
          | three =>
              simp [sub_prune2_three, sub]

theorem sub_prune3_eq_if_evenTrace_three :
    ∀ (et : ColSeq) (t : CTree),
      sub (prune3 t) et =
        if ColSeq.evenTrace (Color.three :: et) then sub t et else 0
  | [], t => by
      rw [sub_prune3_nil]
      simp [ColSeq.evenTrace, ColSeq.ttail, ColSeq.ProperTrace,
        ColSeq.headColor, ColSeq.perm, EdgePerm.edgeRot]
  | e :: et, t => by
      cases t with
      | empty =>
          cases e <;> simp [sub]
      | leaf lf =>
          cases e <;> simp [sub]
      | node t1 t2 t3 =>
          cases e with
          | zero =>
              simp [sub]
          | one =>
              simp [sub_prune3_one, sub]
          | two =>
              simp [sub_prune3_two]
          | three =>
              simpa [sub_prune3_three, sub] using
                sub_prune3_eq_if_evenTrace_three et t3

theorem tableSubSpec_init_one (h : Nat) (et : ColSeq) :
    (if ColSeq.evenTrace (Color.one :: et) then
        tableSubSpec h 0 true et
      else 0) =
      initSubSpec (h + 1) (Color.one :: et) := by
  cases he : ColSeq.evenTrace (Color.one :: et) <;>
    simp [initSubSpec, tableSubSpec, ColSeq.ctrace, ColSeq.sum,
      ColSeq.countBit1, he, Color.cons, Color.bit1]

theorem tableSubSpec_init_two (h : Nat) (et : ColSeq) :
    (if ColSeq.evenTrace (Color.two :: et) then
        tableSubSpec h 1 false et
      else 0) =
      initSubSpec (h + 1) (Color.two :: et) := by
  cases he : ColSeq.evenTrace (Color.two :: et) <;>
    simp [initSubSpec, tableSubSpec, ColSeq.ctrace, ColSeq.sum,
      ColSeq.countBit1, he, Color.cons, Color.bit1, Nat.add_comm]

theorem tableSubSpec_init_three (h : Nat) (et : ColSeq) :
    (if ColSeq.evenTrace (Color.three :: et) then
        tableSubSpec h 1 true et
      else 0) =
      initSubSpec (h + 1) (Color.three :: et) := by
  cases he : ColSeq.evenTrace (Color.three :: et) <;>
    simp [initSubSpec, tableSubSpec, ColSeq.ctrace, ColSeq.sum,
      ColSeq.countBit1, he, Color.cons, Color.bit1, Nat.add_comm]


end CTree

end FourColor

end Schematic.Math.GraphTheory
