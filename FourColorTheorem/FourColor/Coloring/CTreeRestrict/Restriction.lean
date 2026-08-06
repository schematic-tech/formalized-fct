import FourColorTheorem.FourColor.Coloring.CTree
import FourColorTheorem.FourColor.Coloring.GTree

/-!
Trace-tree restriction.

This ports the executable front of Gonthier's `ctreerestrict.v`: restrictions
as lists of open-stack chromogram-tree matches, match-count subtraction,
restriction splitting by the next colour, leaf-stack decrementing, pair
constructors, and the recursive trace-tree partition function.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CTree

/-- A trace-tree restriction is a list of open-stack chromogram-tree matches to
subtract from trace multiplicities. -/
inductive Restriction
  | nil
  | cons (bs : Chromogram.BitStack) (t : GTree) (r : Restriction)
  deriving DecidableEq

namespace Restriction

/-- Smart constructor that omits empty chromogram trees. -/
def consSmart
    (bs : Chromogram.BitStack) (t : GTree) (r : Restriction) :
    Restriction :=
  if GTree.isEmpty t then r else cons bs t r

/-- Match count represented by a restriction for a partial trace. -/
def sub : Restriction → ColSeq → Nat
  | nil, _ => 0
  | cons bs t r, et => GTree.sub t bs et + sub r et

theorem sub_nil (et : ColSeq) :
    sub nil et = 0 := rfl

theorem sub_consSmart
    (bs : Chromogram.BitStack) (t : GTree) (r : Restriction)
    (et : ColSeq) :
    sub (consSmart bs t r) et = GTree.sub t bs et + sub r et := by
  unfold consSmart
  cases h : GTree.isEmpty t with
  | false =>
      simp [sub]
  | true =>
      have ht : t = GTree.empty := GTree.isEmpty_eq h
      subst t
      simp [GTree.sub_empty]

theorem sub_add
    (bs : Chromogram.BitStack) (t : GTree) (r : Restriction)
    (et : ColSeq) :
    sub (if GTree.isEmpty t then r else cons bs t r) et =
      GTree.sub t bs et + sub r et := by
  cases h : GTree.isEmpty t with
  | false =>
      simp [sub]
  | true =>
      have ht : t = GTree.empty := GTree.isEmpty_eq h
      subst t
      simp [GTree.sub_empty]

theorem sub_zero_cons :
    ∀ (r : Restriction) (et : ColSeq),
      sub r (Color.zero :: et) = 0
  | nil, et => rfl
  | cons bs t r, et => by
      simp [sub, GTree.sub, GTree.matchCount, sub_zero_cons r et]

@[simp]
theorem sub_nil_trace :
    ∀ (r : Restriction), sub r [] = 0
  | nil => rfl
  | cons bs t r => by
      simp [sub, sub_nil_trace r]

/-- CPS split of a restriction by the next trace colour. -/
def split {α : Type _}
    (cont : Restriction → Restriction → Restriction → α) :
    Restriction → Restriction → Restriction → Restriction → α
  | r1, r2, r3, nil => cont r1 r2 r3
  | r1, r2, r3, cons bs (GTree.node t0 t1 t2 t3) r =>
      let add bs t r' := if GTree.isEmpty t then r' else cons bs t r'
      let run r2' r3' :=
        if GTree.isEmpty t0 then
          split cont (add bs t1 r1) r2' r3' r
        else
          split cont (add bs t1 r1)
            (cons (Chromogram.BitStack.push0 bs) t0 r2')
            (cons (Chromogram.BitStack.push1 bs) t0 r3') r
      match bs with
      | Chromogram.BitStack.empty => run r2 r3
      | Chromogram.BitStack.push0 bs' => run (add bs' t2 r2) (add bs' t3 r3)
      | Chromogram.BitStack.push1 bs' => run (add bs' t3 r2) (add bs' t2 r3)
  | r1, r2, r3, cons _ _ r => split cont r1 r2 r3 r

/-- View a restriction as the subtree corresponding to a next colour. -/
def splitColor (r : Restriction) : Color → Restriction
  | Color.zero => nil
  | Color.one => split (fun r1 _ _ => r1) nil nil nil r
  | Color.two => split (fun _ r2 _ => r2) nil nil nil r
  | Color.three => split (fun _ _ r3 => r3) nil nil nil r

@[simp]
theorem splitColor_zero (r : Restriction) :
    splitColor r Color.zero = nil := rfl

private inductive SplitBranch
  | one | two | three

private def SplitBranch.color : SplitBranch → Color
  | .one => Color.one
  | .two => Color.two
  | .three => Color.three

private def SplitBranch.project : SplitBranch →
    Restriction → Restriction → Restriction → Restriction
  | .one => fun r1 _ _ => r1
  | .two => fun _ r2 _ => r2
  | .three => fun _ _ r3 => r3

private theorem split_branch_sub_cons :
    ∀ (b : SplitBranch) (r1 r2 r3 r : Restriction)
      (e : Color) (et : ColSeq),
      sub (split b.project r1 r2 r3 r) (e :: et) =
        sub (b.project r1 r2 r3) (e :: et) +
          sub r (b.color :: e :: et) := by
  intro b r1 r2 r3 r
  induction r generalizing b r1 r2 r3 with
  | nil =>
      intro e et
      cases b <;> simp [split, SplitBranch.project, sub]
  | cons bs t r ih =>
      intro e et
      have ihb := ih b
      cases b <;>
        simp [SplitBranch.project, SplitBranch.color] at ihb <;>
        cases t with
      | node t0 t1 t2 t3 =>
          cases bs <;> by_cases h0 : GTree.isEmpty t0
          all_goals
            first
            | have ht0 : t0 = GTree.empty := GTree.isEmpty_eq h0
              subst t0
              simp [split, SplitBranch.project, SplitBranch.color, h0, ihb,
                sub, sub_add, GTree.sub_empty, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm]
            | simp [split, SplitBranch.project, SplitBranch.color, h0, ihb,
                sub, sub_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | leaf0 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf1 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf2 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf3 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf01 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf12 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf13 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | leaf23 =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub]
      | empty =>
          simp [split, SplitBranch.project, SplitBranch.color, ihb, sub,
            GTree.sub_empty]

theorem split_one_sub_cons :
    ∀ (r1 r2 r3 r : Restriction) (e : Color) (et : ColSeq),
      sub (split (fun r1 _ _ => r1) r1 r2 r3 r) (e :: et) =
        sub r1 (e :: et) + sub r (Color.one :: e :: et) := by
  intro r1 r2 r3 r e et
  simpa [SplitBranch.project, SplitBranch.color] using
    split_branch_sub_cons SplitBranch.one r1 r2 r3 r e et

theorem split_two_sub_cons :
    ∀ (r1 r2 r3 r : Restriction) (e : Color) (et : ColSeq),
      sub (split (fun _ r2 _ => r2) r1 r2 r3 r) (e :: et) =
        sub r2 (e :: et) + sub r (Color.two :: e :: et) := by
  intro r1 r2 r3 r e et
  simpa [SplitBranch.project, SplitBranch.color] using
    split_branch_sub_cons SplitBranch.two r1 r2 r3 r e et

theorem split_three_sub_cons :
    ∀ (r1 r2 r3 r : Restriction) (e : Color) (et : ColSeq),
      sub (split (fun _ _ r3 => r3) r1 r2 r3 r) (e :: et) =
        sub r3 (e :: et) + sub r (Color.three :: e :: et) := by
  intro r1 r2 r3 r e et
  simpa [SplitBranch.project, SplitBranch.color] using
    split_branch_sub_cons SplitBranch.three r1 r2 r3 r e et

@[simp]
theorem splitColor_one_sub_cons
    (r : Restriction) (e : Color) (et : ColSeq) :
    sub (splitColor r Color.one) (e :: et) =
      sub r (Color.one :: e :: et) := by
  simpa [splitColor, sub] using
    (split_one_sub_cons Restriction.nil Restriction.nil Restriction.nil r e et)

@[simp]
theorem splitColor_two_sub_cons
    (r : Restriction) (e : Color) (et : ColSeq) :
    sub (splitColor r Color.two) (e :: et) =
      sub r (Color.two :: e :: et) := by
  simpa [splitColor, sub] using
    (split_two_sub_cons Restriction.nil Restriction.nil Restriction.nil r e et)

@[simp]
theorem splitColor_three_sub_cons
    (r : Restriction) (e : Color) (et : ColSeq) :
    sub (splitColor r Color.three) (e :: et) =
      sub r (Color.three :: e :: et) := by
  simpa [splitColor, sub] using
    (split_three_sub_cons Restriction.nil Restriction.nil Restriction.nil r e et)

theorem splitColor_sub_cons
    (r : Restriction) (c e : Color) (et : ColSeq) :
    sub (splitColor r c) (e :: et) =
      sub r (c :: e :: et) := by
  cases c with
  | zero =>
      simp [splitColor, sub, sub_zero_cons]
  | one =>
      exact splitColor_one_sub_cons r e et
  | two =>
      exact splitColor_two_sub_cons r e et
  | three =>
      exact splitColor_three_sub_cons r e et

@[simp]
theorem splitColor_sub_nil (r : Restriction) (c : Color) :
    sub (splitColor r c) [] = 0 := by
  simp

theorem split_eq_acc {α : Type _}
    (cont : Restriction → Restriction → Restriction → α) :
    ∀ r1 r2 r3 r,
      split cont r1 r2 r3 r =
        cont
          (split (fun r1 _ _ => r1) r1 r2 r3 r)
          (split (fun _ r2 _ => r2) r1 r2 r3 r)
          (split (fun _ _ r3 => r3) r1 r2 r3 r) := by
  intro r1 r2 r3 r
  induction r generalizing r1 r2 r3 with
  | nil =>
      rfl
  | cons bs t r ih =>
      cases t with
      | node t0 t1 t2 t3 =>
          cases bs <;> cases t0 <;>
            simp [split, ih, GTree.isEmpty]
      | leaf0 =>
          simpa [split] using ih r1 r2 r3
      | leaf1 =>
          simpa [split] using ih r1 r2 r3
      | leaf2 =>
          simpa [split] using ih r1 r2 r3
      | leaf3 =>
          simpa [split] using ih r1 r2 r3
      | leaf01 =>
          simpa [split] using ih r1 r2 r3
      | leaf12 =>
          simpa [split] using ih r1 r2 r3
      | leaf13 =>
          simpa [split] using ih r1 r2 r3
      | leaf23 =>
          simpa [split] using ih r1 r2 r3
      | empty =>
          simpa [split] using ih r1 r2 r3

theorem split_eq {α : Type _}
    (cont : Restriction → Restriction → Restriction → α)
    (r : Restriction) :
    split cont nil nil nil r =
      cont
        (splitColor r Color.one)
        (splitColor r Color.two)
        (splitColor r Color.three) := by
  simpa [splitColor] using
    (split_eq_acc cont nil nil nil r)

end Restriction

end CTree

end FourColor

end Schematic.Math.GraphTheory
