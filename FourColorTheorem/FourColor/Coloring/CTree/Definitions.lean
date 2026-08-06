import Schematic.Math.GraphTheory.Embedding.Trace

/-!
Trace-colouring trees.

This ports the executable front of Gonthier's `ctree.v`: ternary trees indexed
by non-zero edge colours, canonical leaves, union/rotation operations, and the
basic uniform-depth well-formedness predicate.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

/-- Ternary trees of edge-colour traces, with leaf stacks recording
multiplicity. -/
inductive CTree
  | node (t1 t2 t3 : CTree)
  | leaf (lf : CTree)
  | empty
  deriving DecidableEq

namespace CTree

/-- Classifier for the empty tree. -/
def isEmpty : CTree → Bool
  | empty => true
  | _ => false

/-- Classifier for leaf nodes. -/
def isLeaf : CTree → Bool
  | leaf _ => true
  | _ => false

/-- Test for the redundant empty node, which is contracted by `cons`. -/
def emptyNode : CTree → Bool
  | node empty empty empty => true
  | _ => false

/-- Immediate subtree selected by an edge colour.  `Color.zero` and non-nodes
select the empty tree. -/
def select : CTree → Color → CTree
  | node t1 _ _, Color.one => t1
  | node _ t2 _, Color.two => t2
  | node _ _ t3, Color.three => t3
  | _, _ => empty

/-- Proper trees of height `h`: all leaves occur at uniform depth and no
explicit empty node remains. -/
def Proper : Nat → CTree → Prop
  | _, empty => True
  | 0, leaf lf => Proper 0 lf
  | h + 1, node t1 t2 t3 =>
      emptyNode (node t1 t2 t3) = false ∧
        Proper h t1 ∧ Proper h t2 ∧ Proper h t3
  | _, _ => False

/-- Multiplicity of a trace in a tree. -/
def sub : CTree → ColSeq → Nat
  | node t1 _ _, Color.one :: et => sub t1 et
  | node _ t2 _, Color.two :: et => sub t2 et
  | node _ _ t3, Color.three :: et => sub t3 et
  | leaf lf, [] => sub lf [] + 1
  | _, _ => 0

/-- Boolean membership, obtained by forgetting multiplicity. -/
def mem (t : CTree) (et : ColSeq) : Bool :=
  t.sub et != 0

/-- Pair type used by restriction algorithms. -/
structure Pair where
  left : CTree
  right : CTree
  deriving DecidableEq

/-- The empty pair. -/
def emptyPair : Pair where
  left := empty
  right := empty

/-- Select one component of a pair. -/
def pairSub (tp : Pair) (b : Bool) : CTree :=
  if b then tp.right else tp.left

/-- A stack of `n` leaves over the empty tree. -/
def leafOf : Nat → CTree
  | 0 => empty
  | n + 1 => leaf (leafOf n)

/-- Contracting node constructor. -/
def cons (t1 t2 t3 : CTree) : CTree :=
  match t1, t2, t3 with
  | empty, empty, empty => empty
  | _, _, _ => node t1 t2 t3

/-- Empty one-branch constructor. -/
def cons0 (_ : CTree) : CTree :=
  empty

/-- One-colour one-branch constructor. -/
def cons1 (t : CTree) : CTree :=
  cons t empty empty

/-- Two-colour one-branch constructor. -/
def cons2 (t : CTree) : CTree :=
  cons empty t empty

/-- Three-colour one-branch constructor. -/
def cons3 (t : CTree) : CTree :=
  cons empty empty t

/-- Shared proper leaf used for reachable trace sets. -/
def simpleLeaf : CTree :=
  leaf empty

/-- Constructor indexed by an edge colour. -/
def consE : Color → CTree → CTree
  | Color.zero => cons0
  | Color.one => cons1
  | Color.two => cons2
  | Color.three => cons3

/-- Tree containing a single normalised trace tail. -/
def ofTtail : ColSeq → CTree :=
  List.foldr consE simpleLeaf

@[simp]
theorem ofTtail_nil :
    ofTtail [] = simpleLeaf := rfl

@[simp]
theorem ofTtail_cons_zero (et : ColSeq) :
    ofTtail (Color.zero :: et) = empty := rfl

@[simp]
theorem ofTtail_cons_one (et : ColSeq) :
    ofTtail (Color.one :: et) = cons1 (ofTtail et) := rfl

@[simp]
theorem ofTtail_cons_two (et : ColSeq) :
    ofTtail (Color.two :: et) = cons2 (ofTtail et) := rfl

@[simp]
theorem ofTtail_cons_three (et : ColSeq) :
    ofTtail (Color.three :: et) = cons3 (ofTtail et) := rfl

/-- Union of trace trees.  Colliding leaves are collapsed to `simpleLeaf`,
matching the reachable-set use of this operation. -/
def union : CTree → CTree → CTree
  | node tl1 tl2 tl3, node tr1 tr2 tr3 =>
      cons (union tl1 tr1) (union tl2 tr2) (union tl3 tr3)
  | empty, tr => tr
  | tl, empty => tl
  | _, _ => simpleLeaf

/-- Left colour rotation `one ↦ two ↦ three ↦ one` on tree indices. -/
def rotL : CTree → CTree
  | node t1 t2 t3 => cons (rotL t3) (rotL t1) (rotL t2)
  | t => t

/-- Right colour rotation `one ↦ three ↦ two ↦ one` on tree indices. -/
def rotR : CTree → CTree
  | node t1 t2 t3 => cons (rotR t2) (rotR t3) (rotR t1)
  | t => t

/-- Add all three colour rotations of a tree at the root. -/
def consRot (t : CTree) : CTree :=
  cons t t.rotL t.rotR

/-- Optimised union of left and right rotations. -/
def unionRotLR : CTree → CTree → CTree
  | node tl1 tl2 tl3, node tr1 tr2 tr3 =>
      cons (unionRotLR tl3 tr2) (unionRotLR tl1 tr3) (unionRotLR tl2 tr1)
  | leaf _, leaf _ => simpleLeaf
  | tl, tr => union tl.rotL tr.rotR

/-- Union of the two nontrivial colour rotations. -/
def rotLR (t : CTree) : CTree :=
  unionRotLR t t

@[simp]
theorem rotL_empty :
    rotL empty = empty := rfl

@[simp]
theorem rotR_empty :
    rotR empty = empty := rfl

@[simp]
theorem rotLR_empty :
    rotLR empty = empty := rfl

/-- Disjointness test for trace trees. -/
def disjoint : CTree → CTree → Bool
  | leaf _, leaf _ => false
  | node tl1 tl2 tl3, node tr1 tr2 tr3 =>
      disjoint tl1 tr1 && disjoint tl2 tr2 && disjoint tl3 tr3
  | _, _ => true

/-- Number of represented trace leaves.  This is Coq's `ctree_size`; it is
used by the Kempe-closure convergence argument. -/
def size : CTree → Nat
  | node t1 t2 t3 => size t1 + (size t2 + size t3)
  | leaf _ => 1
  | empty => 0

@[simp]
theorem size_empty :
    size empty = 0 := rfl

@[simp]
theorem size_leaf (lf : CTree) :
    size (leaf lf) = 1 := rfl

@[simp]
theorem size_node (t1 t2 t3 : CTree) :
    size (node t1 t2 t3) = size t1 + (size t2 + size t3) := rfl

end CTree

end FourColor

end Schematic.Math.GraphTheory
