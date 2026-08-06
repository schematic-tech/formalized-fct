import FourColorTheorem.FourColor.Coloring.KempeTree.Initialization

/-!
Executable program-independent and program-indexed Kempe trees.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

/-- Program-independent Kempe closure tree for a fixed height and deleted
trace tree. -/
def treeOfHeight (h : Nat) (ctr : CTree) : CTree :=
  (closure h (h + 2) (initialCTree h) ctr (initialGTree h)).ctu

/-- Build a program-indexed Kempe tree from a choice of colouring tree. -/
def treeWith (colorTree : CProg → CTree) (cp : CProg) : CTree :=
  match CProg.ringSize cp with
  | 0 => CTree.empty
  | 1 => CTree.empty
  | Nat.succ (Nat.succ h) => treeOfHeight h (colorTree cp)

/-- Program-indexed Kempe tree using the specification colouring tree. -/
def tree (cp : CProg) : CTree :=
  treeWith CProg.cpColor cp

/-- Program-indexed Kempe tree using the optimized colouring tree. -/
def treeFast (cp : CProg) : CTree :=
  treeWith CProg.cpColorFast cp

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
