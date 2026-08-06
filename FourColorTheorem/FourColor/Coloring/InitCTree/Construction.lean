import Mathlib.Data.Nat.Bits
import FourColorTheorem.FourColor.Coloring.CTree
import FourColorTheorem.FourColor.Coloring.Dyck

/-!
Initial trace-colouring trees.

This ports the executable construction layer from Gonthier's `initctree.v`:
tables of `CTree.Pair`s, Dyck leaf-stack expansion, adjacent-pair merging,
odd-permutation pruning, and the final initial trace tree.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CTree

/-- Tables used to build full trace-colouring trees. -/
abbrev Table := List Pair

/-- Iterate a function `n` times. -/
def iterate {α : Type _} (n : Nat) (f : α → α) (x : α) : α :=
  Nat.rec x (fun _ acc => f acc) n

/-- Add the leaf stack counted by the generalized Dyck recurrence.  This is
the executable shape of Coq's `ctree_add_dyck`; the arithmetic identification
with `genDyck` is a later proof layer. -/
def addDyck (m : Nat) : Nat → CTree → CTree
  | 0, lf => leaf lf
  | n + 1, lf =>
      (List.range (m + 1)).foldl
        (fun acc i => addDyck (i + 1) n acc) lf

@[simp]
theorem addDyck_zero (m : Nat) (lf : CTree) :
    addDyck m 0 lf = leaf lf := rfl

theorem addDyck_zero_succ (n : Nat) (lf : CTree) :
    addDyck 0 (n + 1) lf = addDyck 1 n lf := rfl

theorem addDyck_succ_succ (m n : Nat) (lf : CTree) :
    addDyck (m + 1) (n + 1) lf =
      addDyck (m + 2) n (addDyck m (n + 1) lf) := by
  change
    (List.range (m + 2)).foldl
        (fun acc i => addDyck (i + 1) n acc) lf =
      addDyck (m + 2) n
        ((List.range (m + 1)).foldl
          (fun acc i => addDyck (i + 1) n acc) lf)
  rw [show List.range (m + 2) = List.range (m + 1) ++ [m + 1] by
    simpa [Nat.add_assoc] using (List.range_succ (n := m + 1))]
  simp [List.foldl_append]

theorem addDyck_leafOf :
    ∀ (n m d : Nat),
      addDyck m n (leafOf d) =
        leafOf (genDyck (m + 1) (m + 2 * n) + d)
  | 0, m, d => by
      change leafOf (d + 1) =
        leafOf (genDyck (m + 1) (m + 2 * 0) + d)
      rw [show m + 2 * 0 = m by omega, genDyck_all_close]
      apply congrArg leafOf
      omega
  | n + 1, m, d => by
      induction m generalizing d with
      | zero =>
          rw [addDyck_zero_succ, addDyck_leafOf n 1 d]
          apply congrArg leafOf
          rw [show 0 + 2 * (n + 1) = (1 + 2 * n) + 1 by omega]
          rw [show 1 + 2 * n = 2 * n + 1 by omega]
          simp [genDyck]
      | succ m ihm =>
          rw [addDyck_succ_succ]
          rw [ihm d]
          rw [addDyck_leafOf n (m + 2)
            (genDyck (m + 1) (m + 2 * (n + 1)) + d)]
          apply congrArg leafOf
          let k := m + 2 * n + 2
          rw [show (m + 1) + 2 * (n + 1) = k + 1 by
            dsimp [k]
            omega]
          rw [show (m + 2) + 2 * n = k by
            dsimp [k]
            omega]
          rw [show m + 2 * (n + 1) = k by
            dsimp [k]
            omega]
          simp [genDyck, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem addDyck_leafOf_dyck_step (n : Nat) :
    addDyck 2 n (leafOf (dyck (2 * n + 2))) =
      leafOf (dyck (2 * (n + 1) + 2)) := by
  rw [addDyck_leafOf]
  apply congrArg leafOf
  rw [show 2 + 2 * n = 2 * n + 2 by omega]
  rw [← dyck_add_two (2 * n + 2)]
  apply congrArg dyck
  omega

/-- Leaf table suffix. -/
def leafTableFrom : CTree → Nat → Nat → Table
  | _, _, 0 => []
  | lf, _, 1 => [⟨lf, lf⟩]
  | lf, n, h + 2 =>
      ⟨lf, lf⟩ :: ⟨empty, lf⟩ ::
        leafTableFrom (addDyck 2 n lf) (n + 1) h

/-- Initial leaf table for ring size `h`. -/
def leafTable (h : Nat) : Table :=
  ⟨empty, simpleLeaf⟩ :: leafTableFrom simpleLeaf 0 h

/-- Select a table entry and then one component of the pair. -/
def tableSub (tab : Table) (i : Nat) (b : Bool) : CTree :=
  pairSub (tab.getD i emptyPair) b

@[simp]
theorem tableSub_nil (i : Nat) (b : Bool) :
    tableSub [] i b = empty := by
  cases i <;> cases b <;> rfl

@[simp]
theorem tableSub_zero (pt : Pair) (tab : Table) (b : Bool) :
    tableSub (pt :: tab) 0 b = pairSub pt b := rfl

@[simp]
theorem tableSub_succ (pt : Pair) (tab : Table) (i : Nat) (b : Bool) :
    tableSub (pt :: tab) (i + 1) b = tableSub tab i b := rfl

/-- Merge two adjacent table entries. -/
def mergePair (tu tu' : Pair) : Pair where
  left := cons tu.right tu'.left tu'.right
  right := cons tu.left tu'.right tu'.left

/-- Adjacent-pair map used by table merging. -/
def mergeTableAux (prev : Pair) : Table → Table
  | [] => []
  | pt :: tab => mergePair prev pt :: mergeTableAux pt tab

@[simp]
theorem mergePair_left (tu tu' : Pair) :
    (mergePair tu tu').left = cons tu.right tu'.left tu'.right := rfl

@[simp]
theorem mergePair_right (tu tu' : Pair) :
    (mergePair tu tu').right = cons tu.left tu'.right tu'.left := rfl

theorem mergePair_proper
    {h : Nat} {tu tu' : Pair}
    (htu_left : Proper h tu.left)
    (htu_right : Proper h tu.right)
    (htu'_left : Proper h tu'.left)
    (htu'_right : Proper h tu'.right) :
    Proper (h + 1) (mergePair tu tu').left ∧
      Proper (h + 1) (mergePair tu tu').right := by
  constructor
  · exact proper_cons htu_right htu'_left htu'_right
  · exact proper_cons htu_left htu'_right htu'_left

@[simp]
theorem sub_mergePair_left_one
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').left (Color.one :: et) = sub tu.right et := by
  rw [mergePair_left, sub_cons]
  rfl

@[simp]
theorem sub_mergePair_left_two
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').left (Color.two :: et) = sub tu'.left et := by
  rw [mergePair_left, sub_cons]
  rfl

@[simp]
theorem sub_mergePair_left_three
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').left (Color.three :: et) =
      sub tu'.right et := by
  rw [mergePair_left, sub_cons]
  rfl

@[simp]
theorem sub_mergePair_right_one
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').right (Color.one :: et) = sub tu.left et := by
  rw [mergePair_right, sub_cons]
  rfl

@[simp]
theorem sub_mergePair_right_two
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').right (Color.two :: et) =
      sub tu'.right et := by
  rw [mergePair_right, sub_cons]
  rfl

@[simp]
theorem sub_mergePair_right_three
    (tu tu' : Pair) (et : ColSeq) :
    sub (mergePair tu tu').right (Color.three :: et) =
      sub tu'.left et := by
  rw [mergePair_right, sub_cons]
  rfl

/-- Compute the next-height trace table. -/
def mergeTable : Table → Table
  | [] => []
  | line :: tab => mergeTableAux line tab

/-- Prune branches where colour two appears before colour one. -/
def prune1 : CTree → CTree
  | node t1 t2 _ => cons (prune1 t1) t2 empty
  | t => t

/-- Prune branches where colour three appears before colour two. -/
def prune2 : CTree → CTree
  | node _ t2 t3 => cons empty (prune2 t2) t3
  | t => t

/-- Prune branches where colour one appears before colour three. -/
def prune3 : CTree → CTree
  | node t1 _ t3 => cons t1 empty (prune3 t3)
  | t => t

/-- Full initial trace-colouring tree for ring size `h`. -/
def initTree (h : Nat) : CTree :=
  match iterate (h - 1) mergeTable (leafTable h) with
  | ⟨_, t1⟩ :: ⟨t2, t3⟩ :: _ =>
      cons (prune1 t1) (prune2 t2) (prune3 t3)
  | _ => empty


end CTree

end FourColor

end Schematic.Math.GraphTheory
