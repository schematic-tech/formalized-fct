import Schematic.Math.GraphTheory.Embedding.FaceOrbit
import FourColorTheorem.Tactic.Decide

/-!
Parts for the discharging and unavoidability proof.

This ports the data representation and executable operations from the first
half of Gonthier's `part.v`.  A `Part` records arity constraints in the second
neighbourhood of a hub face.  The later discharging, hubcap, and presentation
layers use these operations to refine local sectors and to test compatibility
with reducible configurations.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

/-- Ranges of face arities used in parts.  Constructors follow Coq names:
`PrMN` represents `[M,N]`, with upper endpoint `9` denoting an unbounded
range. -/
inductive PRange
  | Pr55 | Pr66 | Pr77 | Pr88 | Pr99
  | Pr56 | Pr67 | Pr78 | Pr89
  | Pr57 | Pr68 | Pr79
  | Pr58 | Pr69
  | Pr59
  deriving DecidableEq, Repr, Inhabited

namespace PRange

/-- Boolean membership in an arity range. -/
def contains : PRange → Nat → Bool
  | Pr55, n => n == 5
  | Pr66, n => n == 6
  | Pr77, n => n == 7
  | Pr88, n => n == 8
  | Pr99, n => decide (9 ≤ n)
  | Pr56, n => n == 5 || n == 6
  | Pr67, n => n == 6 || n == 7
  | Pr78, n => n == 7 || n == 8
  | Pr89, n => decide (8 ≤ n)
  | Pr57, n => n == 5 || n == 6 || n == 7
  | Pr68, n => n == 6 || n == 7 || n == 8
  | Pr79, n => decide (7 ≤ n)
  | Pr58, n => n == 5 || n == 6 || n == 7 || n == 8
  | Pr69, n => decide (6 ≤ n)
  | Pr59, n => decide (5 ≤ n)

instance : CoeFun PRange (fun _ => Nat → Bool) :=
  ⟨contains⟩

theorem contains_Pr59_of_ge_five {n : Nat}
    (hn : 5 ≤ n) :
    contains Pr59 n = true := by
  simp [contains, hn]

end PRange

/-- Local part patterns around a hub, represented as an optimized list of
subparts. -/
inductive Part
  | Pnil
  | Pcons (spoke hat : PRange) (tail : Part)
  | Pcons6 (hat fan1 : PRange) (tail : Part)
  | Pcons7 (hat fan1 fan2 : PRange) (tail : Part)
  | Pcons8 (hat fan1 fan2 fan3 : PRange) (tail : Part)
  deriving DecidableEq, Repr, Inhabited

/-- Locations inside a subpart. -/
inductive SubpartLoc
  | Pspoke | Phat | Pfan1 | Pfan2 | Pfan3
  deriving DecidableEq, Repr, Inhabited

open PRange
open Part
open SubpartLoc

namespace Part

/-- Add a subpart with a specified spoke range and free hat range. -/
def pconsS (s : PRange) (p : Part) : Part :=
  Pcons s Pr59 p

/-- A part consisting of `n` completely free subparts. -/
def pconsN : Nat → Part
  | 0 => Pnil
  | n + 1 => Pcons Pr59 Pr59 (pconsN n)

end Part

/-- Outcomes for comparing part/range denotations. -/
inductive PartRel
  | Pdisjoint | Pstraddle | Psubset
  deriving DecidableEq, Repr, Inhabited

namespace PartRel

/-- Apply a comparison result to a Boolean membership test. -/
def apply : PartRel → Bool → Bool
  | Pdisjoint, _ => false
  | Psubset, _ => true
  | Pstraddle, b => b

instance : CoeFun PartRel (fun _ => Bool → Bool) :=
  ⟨apply⟩

end PartRel

open PartRel

/-- Downgrade strict subset information when taking a product comparison. -/
def notPsubset : PartRel → PartRel
  | Psubset => Pstraddle
  | c => c

/-- Product comparison of two independent part/range comparisons. -/
def meetPRel : PartRel → PartRel → PartRel
  | Pdisjoint, _ => Pdisjoint
  | Psubset, c' => c'
  | Pstraddle, c' => notPsubset c'

/-- Compare two arity ranges as sets.  `cmpRange r r'` compares the first
range against the second. -/
def cmpRange (r r' : PRange) : PartRel :=
  match r', r with
  | Pr59, _    => Psubset
  | _ ,   Pr59 => Pstraddle
  | Pr69, Pr55 => Pdisjoint
  | Pr69, Pr56 => Pstraddle
  | Pr69, Pr57 => Pstraddle
  | Pr69, Pr58 => Pstraddle
  | Pr69, _    => Psubset
  | Pr55, Pr69 => Pdisjoint
  | _,    Pr69 => Pstraddle
  | Pr58, Pr99 => Pdisjoint
  | Pr58, Pr89 => Pstraddle
  | Pr58, Pr79 => Pstraddle
  | Pr58, _    => Psubset
  | Pr99, Pr58 => Pdisjoint
  | _,    Pr58 => Pstraddle
  | Pr55, Pr55 => Psubset
  | Pr55, Pr56 => Pstraddle
  | Pr55, Pr57 => Pstraddle
  | Pr55, _    => Pdisjoint
  | Pr56, Pr55 => Psubset
  | Pr57, Pr55 => Psubset
  | _,    Pr55 => Pdisjoint
  | Pr99, Pr99 => Psubset
  | Pr99, Pr89 => Pstraddle
  | Pr99, Pr79 => Pstraddle
  | Pr99, _    => Pdisjoint
  | Pr89, Pr99 => Psubset
  | Pr79, Pr99 => Psubset
  | _,    Pr99 => Pdisjoint
  | Pr66, Pr66 => Psubset
  | Pr66, Pr56 => Pstraddle
  | Pr66, Pr57 => Pstraddle
  | Pr66, Pr67 => Pstraddle
  | Pr66, Pr68 => Pstraddle
  | Pr66, _    => Pdisjoint
  | Pr56, Pr66 => Psubset
  | Pr57, Pr66 => Psubset
  | Pr67, Pr66 => Psubset
  | Pr68, Pr66 => Psubset
  | _,    Pr66 => Pdisjoint
  | Pr88, Pr88 => Psubset
  | Pr88, Pr89 => Pstraddle
  | Pr88, Pr79 => Pstraddle
  | Pr88, Pr78 => Pstraddle
  | Pr88, Pr68 => Pstraddle
  | Pr88, _    => Pdisjoint
  | Pr89, Pr88 => Psubset
  | Pr79, Pr88 => Psubset
  | Pr78, Pr88 => Psubset
  | Pr68, Pr88 => Psubset
  | _,    Pr88 => Pdisjoint
  | Pr77, Pr77 => Psubset
  | Pr77, Pr56 => Pdisjoint
  | Pr77, Pr89 => Pdisjoint
  | Pr77, _    => Pstraddle
  | Pr56, Pr77 => Pdisjoint
  | Pr89, Pr77 => Pdisjoint
  | _,    Pr77 => Psubset
  | Pr68, Pr68 => Psubset
  | Pr68, Pr67 => Psubset
  | Pr68, Pr78 => Psubset
  | Pr68, _    => Pstraddle
  | _,    Pr68 => Pstraddle
  | Pr67, Pr67 => Psubset
  | Pr67, Pr89 => Pdisjoint
  | Pr67, _    => Pstraddle
  | Pr57, Pr67 => Psubset
  | Pr89, Pr67 => Pdisjoint
  | _,    Pr67 => Pstraddle
  | Pr78, Pr78 => Psubset
  | Pr78, Pr56 => Pdisjoint
  | Pr78, _    => Pstraddle
  | Pr79, Pr78 => Psubset
  | Pr56, Pr78 => Pdisjoint
  | _,    Pr78 => Pstraddle
  | Pr89, Pr56 => Pdisjoint
  | Pr79, Pr56 => Pdisjoint
  | _,    Pr56 => Psubset
  | Pr56, Pr57 => Pstraddle
  | Pr56, _    => Pdisjoint
  | Pr57, Pr89 => Pdisjoint
  | _,    Pr89 => Psubset
  | Pr89, Pr79 => Pstraddle
  | Pr89, _    => Pdisjoint
  | Pr57, Pr57 => Psubset
  | Pr79, Pr79 => Psubset
  | _,    _    => Pstraddle

/-- Intersection of two non-disjoint ranges.  In disjoint cases this still
returns a deterministic range, matching Coq's executable code. -/
def meetRange (r r' : PRange) : PRange :=
  match r', r with
  | Pr56, Pr67 => Pr66
  | Pr56, Pr68 => Pr66
  | Pr56, Pr69 => Pr66
  | Pr67, Pr56 => Pr66
  | Pr68, Pr56 => Pr66
  | Pr69, Pr56 => Pr66
  | Pr57, Pr78 => Pr77
  | Pr57, Pr79 => Pr77
  | Pr67, Pr78 => Pr77
  | Pr67, Pr79 => Pr77
  | Pr78, Pr57 => Pr77
  | Pr79, Pr57 => Pr77
  | Pr78, Pr67 => Pr77
  | Pr79, Pr67 => Pr77
  | Pr89, Pr58 => Pr88
  | Pr89, Pr68 => Pr88
  | Pr89, Pr78 => Pr88
  | Pr58, Pr89 => Pr88
  | Pr68, Pr89 => Pr88
  | Pr78, Pr89 => Pr88
  | Pr57, Pr68 => Pr67
  | Pr57, Pr69 => Pr67
  | Pr68, Pr57 => Pr67
  | Pr69, Pr57 => Pr67
  | Pr79, Pr58 => Pr78
  | Pr79, Pr68 => Pr78
  | Pr58, Pr79 => Pr78
  | Pr68, Pr79 => Pr78
  | Pr58, Pr69 => Pr68
  | Pr69, Pr58 => Pr68
  | Pr59, _    => r
  | _,    Pr59 => r'
  | Pr58, _    => r
  | Pr69, _    => r
  | _,    Pr58 => r'
  | _,    Pr69 => r'
  | Pr57, _    => r
  | Pr68, _    => r
  | Pr79, _    => r
  | _,    Pr57 => r'
  | _,    Pr68 => r'
  | _,    Pr79 => r'
  | Pr56, _    => r
  | Pr67, _    => r
  | Pr78, _    => r
  | Pr89, _    => r
  | _,    Pr56 => r'
  | _,    Pr67 => r'
  | _,    Pr78 => r'
  | _,    _    => r'

end FourColor

end Schematic.Math.GraphTheory
