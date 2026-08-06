import FourColorTheorem.FourColor.Coloring.CTree.Definitions

/-! Elementary semantics of trace-coloring tree operations. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem isEmpty_eq {t : CTree} :
    isEmpty t = true → t = empty := by
  cases t <;> simp [isEmpty]

theorem emptyNode_eq {t1 t2 t3 : CTree} :
    emptyNode (node t1 t2 t3) = true →
      t1 = empty ∧ t2 = empty ∧ t3 = empty := by
  cases t1 <;> cases t2 <;> cases t3 <;> simp [emptyNode]

theorem select_empty (c : Color) :
    select empty c = empty := by
  cases c <;> rfl

@[simp]
theorem select_zero (t : CTree) :
    select t Color.zero = empty := by
  cases t <;> rfl

theorem proper_select
    {h : Nat} {t : CTree} (e : Color)
    (ht : Proper h t) :
    Proper (h - 1) (select t e) := by
  cases h with
  | zero =>
      cases t <;> cases e <;> simp [Proper, select] at ht ⊢
  | succ h =>
      cases t with
      | empty =>
          cases h <;> trivial
      | leaf lf =>
          simp [Proper] at ht
      | node t1 t2 t3 =>
          rcases ht with ⟨_, h1, h2, h3⟩
          cases e with
          | zero =>
              cases h <;> trivial
          | one =>
              exact h1
          | two =>
              exact h2
          | three =>
              exact h3

@[simp]
theorem sub_empty (et : ColSeq) :
    sub empty et = 0 := by
  cases et <;> rfl

@[simp]
theorem sub_nil_of_proper_succ
    {h : Nat} {t : CTree} (ht : Proper (h + 1) t) :
    sub t [] = 0 := by
  cases t <;> simp [Proper, sub] at ht ⊢

theorem sub_cons_of_proper_zero
    {t : CTree} (ht : Proper 0 t) (e : Color) (et : ColSeq) :
    sub t (e :: et) = 0 := by
  cases t with
  | empty =>
      cases e <;> rfl
  | leaf lf =>
      cases e <;> rfl
  | node t1 t2 t3 =>
      simp [Proper] at ht

@[simp]
theorem mem_empty (et : ColSeq) :
    mem empty et = false := by
  simp [mem]

theorem sub_zero_of_mem
    (t : CTree) :
    ∀ {et : ColSeq}, Color.zero ∈ et → sub t et = 0
  | [], h => by simp at h
  | e :: et, h => by
      cases t with
      | empty =>
          cases e <;> rfl
      | leaf lf =>
          cases e <;> rfl
      | node t1 t2 t3 =>
          cases e with
          | zero => rfl
          | one =>
              simp at h
              exact sub_zero_of_mem t1 h
          | two =>
              simp at h
              exact sub_zero_of_mem t2 h
          | three =>
              simp at h
              exact sub_zero_of_mem t3 h

theorem mem_zero_of_mem
    (t : CTree) {et : ColSeq}
    (h : Color.zero ∈ et) :
    mem t et = false := by
  simp [mem, sub_zero_of_mem t h]

theorem mem_nil (t : CTree) :
    mem t [] = isLeaf t := by
  cases t <;> simp [mem, isLeaf, sub]

theorem mem_leaf (lf : CTree) (et : ColSeq) :
    mem (leaf lf) et = decide (et = []) := by
  cases et <;> simp [mem, sub]

theorem sub_select (t : CTree) (e : Color) (et : ColSeq) :
    sub t (e :: et) = sub (select t e) et := by
  cases t <;> cases e <;> rfl

theorem mem_select (t : CTree) (e : Color) (et : ColSeq) :
    mem t (e :: et) = mem (select t e) et := by
  simp [mem, sub_select]

theorem sub_leafOf (n : Nat) (et : ColSeq) :
    sub (leafOf n) et = if et.length = 0 then n else 0 := by
  cases et with
  | nil =>
      induction n with
      | zero => rfl
      | succ n ih =>
          simp [leafOf, sub, ih]
  | cons e et =>
      cases n <;> rfl

@[simp]
theorem sub_leafOf_nil (n : Nat) :
    sub (leafOf n) [] = n := by
  simpa using sub_leafOf n []

@[simp]
theorem sub_leafOf_cons (n : Nat) (e : Color) (et : ColSeq) :
    sub (leafOf n) (e :: et) = 0 := by
  simpa using sub_leafOf n (e :: et)

theorem mem_leafOf_nil (n : Nat) :
    mem (leafOf n) [] = (n != 0) := by
  simp [mem]

@[simp]
theorem mem_leafOf_cons (n : Nat) (e : Color) (et : ColSeq) :
    mem (leafOf n) (e :: et) = false := by
  simp [mem]

theorem isEmpty_leafOf (n : Nat) :
    isEmpty (leafOf n) = decide (n = 0) := by
  cases n <;> rfl

theorem size_leafOf_le (n : Nat) :
    size (leafOf n) ≤ n := by
  cases n <;> simp [leafOf]

theorem size_leafOf_le_one (n : Nat) :
    size (leafOf n) ≤ 1 := by
  cases n <;> simp [leafOf]

theorem size_leafOf_sub_le (n k : Nat) :
    size (leafOf (n - k)) ≤ size (leafOf n) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      simp [leafOf]
      exact size_leafOf_le_one (Nat.succ n - k)

theorem isLeaf_cons (t1 t2 t3 : CTree) :
    isLeaf (cons t1 t2 t3) = false := by
  cases t1 <;> cases t2 <;> cases t3 <;> rfl

theorem cons_spec (t1 t2 t3 : CTree) :
    cons t1 t2 t3 =
      if emptyNode (node t1 t2 t3) then empty else node t1 t2 t3 := by
  cases t1 <;> cases t2 <;> cases t3 <;> rfl

theorem select_cons (t1 t2 t3 : CTree) (e : Color) :
    select (cons t1 t2 t3) e = select (node t1 t2 t3) e := by
  cases t1 <;> cases t2 <;> cases t3 <;> cases e <;> rfl

theorem sub_cons (t1 t2 t3 : CTree) (et : ColSeq) :
    sub (cons t1 t2 t3) et = sub (node t1 t2 t3) et := by
  cases t1 <;> cases t2 <;> cases t3 <;> cases et with
  | nil => rfl
  | cons e et => cases e <;> rfl

theorem mem_cons (t1 t2 t3 : CTree) (et : ColSeq) :
    mem (cons t1 t2 t3) et = mem (node t1 t2 t3) et := by
  simp [mem, sub_cons]

theorem size_cons (t1 t2 t3 : CTree) :
    size (cons t1 t2 t3) = size (node t1 t2 t3) := by
  cases t1 <;> cases t2 <;> cases t3 <;> rfl

@[simp]
theorem union_empty_left (t : CTree) :
    union empty t = t := by
  cases t <;> rfl

@[simp]
theorem union_empty_right (t : CTree) :
    union t empty = t := by
  cases t <;> rfl

theorem union_comm :
    ∀ (t u : CTree), union t u = union u t
  | node t1 t2 t3, node u1 u2 u3 => by
      simp [union, union_comm t1 u1, union_comm t2 u2, union_comm t3 u3]
  | empty, u => by
      cases u <;> rfl
  | t, empty => by
      cases t <;> rfl
  | leaf _, leaf _ => rfl
  | leaf _, node _ _ _ => rfl
  | node _ _ _, leaf _ => rfl

theorem union_cons_cons
    (t1 t2 t3 u1 u2 u3 : CTree) :
    union (cons t1 t2 t3) (cons u1 u2 u3) =
      cons (union t1 u1) (union t2 u2) (union t3 u3) := by
  cases t1 <;> cases t2 <;> cases t3 <;>
    cases u1 <;> cases u2 <;> cases u3 <;> rfl

theorem size_union_le_add :
    ∀ (t u : CTree), size (union t u) ≤ size t + size u
  | node t1 t2 t3, node u1 u2 u3 => by
      rw [union, size_cons]
      simp only [size_node]
      have h1 := size_union_le_add t1 u1
      have h2 := size_union_le_add t2 u2
      have h3 := size_union_le_add t3 u3
      omega
  | empty, u => by
      simp
  | t, empty => by
      simp
  | leaf _, leaf _ => by
      simp [union, simpleLeaf]
  | leaf _, node _ _ _ => by
      simp [union, simpleLeaf]
  | node _ _ _, leaf _ => by
      simp [union, simpleLeaf]

end CTree

end FourColor

end Schematic.Math.GraphTheory
