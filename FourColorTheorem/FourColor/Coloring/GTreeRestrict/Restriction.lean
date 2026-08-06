import FourColorTheorem.FourColor.Coloring.CTree
import FourColorTheorem.FourColor.Coloring.GTree

/-!
Chromogram-tree restriction.

This ports the executable front of Gonthier's `gtreerestrict.v`: restrictions
as lists of open-stack trace-tree matches, splitting restrictions by the next
chromogram symbol, the size-one match tests, and the tree partition function.
The semantic partition theorems are the next proof layer.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace GTree

/-- A restriction is a list of open-stack trace-tree matches to delete from a
chromogram tree. -/
inductive Restriction
  | nil
  | cons (bs : Chromogram.BitStack) (t : CTree) (r : Restriction)
  deriving DecidableEq

namespace Restriction

/-- Membership in a restriction: some stored trace tree matches the
chromogram under its open stack. -/
def mem : Restriction → Chromogram → Bool
  | nil, _ => false
  | cons bs t r, w =>
      hasMatch bs (CTree.mem t) w || mem r w

/-- Smart constructor that omits empty trace trees. -/
def consSmart
    (bs : Chromogram.BitStack) (t : CTree) (r : Restriction) :
    Restriction :=
  if CTree.isEmpty t then r else cons bs t r

theorem mem_consSmart
    (bs : Chromogram.BitStack) (t : CTree) (r : Restriction)
    (w : Chromogram) :
    mem (consSmart bs t r) w =
      (hasMatch bs (CTree.mem t) w || mem r w) := by
  unfold consSmart
  cases h : CTree.isEmpty t with
  | false =>
      simp [mem]
  | true =>
      have ht : t = CTree.empty := CTree.isEmpty_eq h
      subst t
      simp [GTree.hasMatch_eq_false_of_false (ct := CTree.mem CTree.empty)
        (by simp)]

/-- CPS split of restrictions by the next chromogram symbol. -/
def split {α : Type _}
    (cont : Restriction → Restriction → Restriction → Restriction → α) :
    Restriction → Restriction → Restriction → Restriction → Restriction → α
  | rPush, rSkip, rPop0, rPop1, nil =>
      cont rPush rSkip rPop0 rPop1
  | rPush, rSkip, rPop0, rPop1,
      cons bs (CTree.node t1 t2 t3) r =>
      let r02 := cons (Chromogram.BitStack.push0 bs) t2 rPush
      let r03 := cons (Chromogram.BitStack.push1 bs) t3 rPush
      let r023 := cons (Chromogram.BitStack.push0 bs) t2 r03
      let rSkip' := if CTree.isEmpty t1 then rSkip else cons bs t1 rSkip
      let addPop0 bs' t := cons bs' t rPop0
      let addPop1 bs' t := cons bs' t rPop1
      match t2, t3, bs with
      | CTree.empty, CTree.empty, _ =>
          split cont rPush rSkip' rPop0 rPop1 r
      | CTree.empty, _, Chromogram.BitStack.empty =>
          split cont r03 rSkip' rPop0 rPop1 r
      | CTree.empty, _, Chromogram.BitStack.push0 bs' =>
          split cont r03 rSkip' rPop0 (addPop1 bs' t3) r
      | CTree.empty, _, Chromogram.BitStack.push1 bs' =>
          split cont r03 rSkip' (addPop0 bs' t3) rPop1 r
      | _, CTree.empty, Chromogram.BitStack.empty =>
          split cont r02 rSkip' rPop0 rPop1 r
      | _, CTree.empty, Chromogram.BitStack.push0 bs' =>
          split cont r02 rSkip' (addPop0 bs' t2) rPop1 r
      | _, CTree.empty, Chromogram.BitStack.push1 bs' =>
          split cont r02 rSkip' rPop0 (addPop1 bs' t2) r
      | _, _, Chromogram.BitStack.empty =>
          split cont r023 rSkip' rPop0 rPop1 r
      | _, _, Chromogram.BitStack.push0 bs' =>
          split cont r023 rSkip' (addPop0 bs' t2) (addPop1 bs' t3) r
      | _, _, Chromogram.BitStack.push1 bs' =>
          split cont r023 rSkip' (addPop0 bs' t3) (addPop1 bs' t2) r
  | rPush, rSkip, rPop0, rPop1, cons _ _ r =>
      split cont rPush rSkip rPop0 rPop1 r

/-- View a restriction as the subtree corresponding to one chromogram symbol. -/
def splitSymbol (r : Restriction) : GramSymbol → Restriction
  | GramSymbol.push =>
      split (fun rPush _ _ _ => rPush) nil nil nil nil r
  | GramSymbol.skip =>
      split (fun _ rSkip _ _ => rSkip) nil nil nil nil r
  | GramSymbol.pop0 =>
      split (fun _ _ rPop0 _ => rPop0) nil nil nil nil r
  | GramSymbol.pop1 =>
      split (fun _ _ _ rPop1 => rPop1) nil nil nil nil r

theorem split_eq_acc {α : Type _}
    (cont : Restriction → Restriction → Restriction → Restriction → α) :
    ∀ rPush rSkip rPop0 rPop1 r,
      split cont rPush rSkip rPop0 rPop1 r =
        cont
          (split (fun rPush _ _ _ => rPush)
            rPush rSkip rPop0 rPop1 r)
          (split (fun _ rSkip _ _ => rSkip)
            rPush rSkip rPop0 rPop1 r)
          (split (fun _ _ rPop0 _ => rPop0)
            rPush rSkip rPop0 rPop1 r)
          (split (fun _ _ _ rPop1 => rPop1)
            rPush rSkip rPop0 rPop1 r) := by
  intro rPush rSkip rPop0 rPop1 r
  induction r generalizing rPush rSkip rPop0 rPop1 with
  | nil =>
      rfl
  | cons bs t r ih =>
      cases t with
      | empty =>
          simpa [split] using ih rPush rSkip rPop0 rPop1
      | leaf lf =>
          simpa [split] using ih rPush rSkip rPop0 rPop1
      | node t1 t2 t3 =>
          cases t2 <;> cases t3 <;> cases bs <;>
            simp [split, ih]

theorem split_eq {α : Type _}
    (cont : Restriction → Restriction → Restriction → Restriction → α)
    (r : Restriction) :
    split cont nil nil nil nil r =
      cont
        (splitSymbol r GramSymbol.push)
        (splitSymbol r GramSymbol.skip)
        (splitSymbol r GramSymbol.pop0)
        (splitSymbol r GramSymbol.pop1) := by
  simpa [splitSymbol] using
    (split_eq_acc cont nil nil nil nil r)

local macro "prove_split_mem" : tactic =>
  `(tactic| exact by
    intro rPush rSkip rPop0 rPop1 r w
    induction r generalizing rPush rSkip rPop0 rPop1 with
    | nil =>
        simp [split, mem]
    | cons bs t r ih =>
        cases t with
        | empty =>
            cases bs <;>
              simp [split, mem, GTree.hasMatch, CTree.mem, CTree.sub, ih]
        | leaf lf =>
            cases bs <;>
              simp [split, mem, GTree.hasMatch, CTree.mem, CTree.sub, ih]
        | node t1 t2 t3 =>
            cases t1 <;> cases t2 <;> cases t3 <;> cases bs <;>
              simp [split, mem, GTree.hasMatch, CTree.mem, CTree.sub,
                CTree.isEmpty, ih, Bool.or_left_comm, Bool.or_comm] <;>
              ac_rfl)

theorem split_push_mem :
    ∀ (rPush rSkip rPop0 rPop1 r : Restriction) (w : Chromogram),
      mem (split (fun rPush _ _ _ => rPush)
        rPush rSkip rPop0 rPop1 r) w =
        (mem rPush w || mem r (GramSymbol.push :: w)) := by
  prove_split_mem

theorem split_skip_mem :
    ∀ (rPush rSkip rPop0 rPop1 r : Restriction) (w : Chromogram),
      mem (split (fun _ rSkip _ _ => rSkip)
        rPush rSkip rPop0 rPop1 r) w =
        (mem rSkip w || mem r (GramSymbol.skip :: w)) := by
  prove_split_mem

theorem split_pop0_mem :
    ∀ (rPush rSkip rPop0 rPop1 r : Restriction) (w : Chromogram),
      mem (split (fun _ _ rPop0 _ => rPop0)
        rPush rSkip rPop0 rPop1 r) w =
        (mem rPop0 w || mem r (GramSymbol.pop0 :: w)) := by
  prove_split_mem

theorem split_pop1_mem :
    ∀ (rPush rSkip rPop0 rPop1 r : Restriction) (w : Chromogram),
      mem (split (fun _ _ _ rPop1 => rPop1)
        rPush rSkip rPop0 rPop1 r) w =
        (mem rPop1 w || mem r (GramSymbol.pop1 :: w)) := by
  prove_split_mem

theorem splitSymbol_mem
    (r : Restriction) (s : GramSymbol) (w : Chromogram) :
    mem (splitSymbol r s) w = mem r (s :: w) := by
  cases s <;>
    simp [splitSymbol, split_push_mem, split_skip_mem, split_pop0_mem,
      split_pop1_mem, mem]

/-- Size-one `[push]` match test. -/
def match0 : Restriction → Bool
  | nil => false
  | cons _ (CTree.node _ (CTree.leaf _) _) _ => true
  | cons _ (CTree.node _ _ (CTree.leaf _)) _ => true
  | cons _ _ r => match0 r

/-- Size-one `[skip]` match test. -/
def match1 : Restriction → Bool
  | nil => false
  | cons _ (CTree.node (CTree.leaf _) _ _) _ => true
  | cons _ _ r => match1 r

/-- Size-one `[pop0]` match test. -/
def match2 : Restriction → Bool
  | nil => false
  | cons (Chromogram.BitStack.push0 _)
      (CTree.node _ (CTree.leaf _) _) _ => true
  | cons (Chromogram.BitStack.push1 _)
      (CTree.node _ _ (CTree.leaf _)) _ => true
  | cons _ _ r => match2 r

/-- Size-one `[pop1]` match test. -/
def match3 : Restriction → Bool
  | nil => false
  | cons (Chromogram.BitStack.push0 _)
      (CTree.node _ _ (CTree.leaf _)) _ => true
  | cons (Chromogram.BitStack.push1 _)
      (CTree.node _ (CTree.leaf _) _) _ => true
  | cons _ _ r => match3 r

theorem match0_eq_mem :
    ∀ r : Restriction, match0 r = mem r [GramSymbol.push]
  | nil => rfl
  | cons bs t r => by
      cases t with
      | empty =>
          simp [match0, mem, GTree.hasMatch, match0_eq_mem r]
      | leaf lf =>
          simp [match0, mem, GTree.hasMatch, CTree.mem, CTree.sub,
            match0_eq_mem r]
      | node t1 t2 t3 =>
          cases t2 <;> cases t3 <;> cases bs <;>
            simp [match0, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match0_eq_mem r]

theorem match1_eq_mem :
    ∀ r : Restriction, match1 r = mem r [GramSymbol.skip]
  | nil => rfl
  | cons bs t r => by
      cases t with
      | empty =>
          simp [match1, mem, GTree.hasMatch, match1_eq_mem r]
      | leaf lf =>
          simp [match1, mem, GTree.hasMatch, CTree.mem, CTree.sub,
            match1_eq_mem r]
      | node t1 t2 t3 =>
          cases t1 <;> cases bs <;>
            simp [match1, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match1_eq_mem r]

theorem match2_eq_mem :
    ∀ r : Restriction, match2 r = mem r [GramSymbol.pop0]
  | nil => rfl
  | cons bs t r => by
      cases t with
      | empty =>
          cases bs <;> simp [match2, mem, GTree.hasMatch, match2_eq_mem r]
      | leaf lf =>
          cases bs <;>
            simp [match2, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match2_eq_mem r]
      | node t1 t2 t3 =>
          cases bs <;> cases t2 <;> cases t3 <;>
            simp [match2, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match2_eq_mem r]

theorem match3_eq_mem :
    ∀ r : Restriction, match3 r = mem r [GramSymbol.pop1]
  | nil => rfl
  | cons bs t r => by
      cases t with
      | empty =>
          cases bs <;> simp [match3, mem, GTree.hasMatch, match3_eq_mem r]
      | leaf lf =>
          cases bs <;>
            simp [match3, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match3_eq_mem r]
      | node t1 t2 t3 =>
          cases bs <;> cases t2 <;> cases t3 <;>
            simp [match3, mem, GTree.hasMatch, CTree.mem, CTree.sub,
              match3_eq_mem r]

end Restriction

end GTree

end FourColor

end Schematic.Math.GraphTheory
