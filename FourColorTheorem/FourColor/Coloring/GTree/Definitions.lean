import FourColorTheorem.FourColor.Coloring.Chromogram

/-!
Chromogram trees.

This ports the executable front of Gonthier's `gtree.v`: four-way trees of
partial chromograms, membership, trace/chromogram matching counters, empty-node
tests, and the pair infrastructure used by restriction algorithms.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

/-- Four-way trees storing sets of partial chromograms. -/
inductive GTree
  | node (tPush tSkip tPop0 tPop1 : GTree)
  | leaf0
  | leaf1
  | leaf2
  | leaf3
  | leaf01
  | leaf12
  | leaf13
  | leaf23
  | empty
  deriving DecidableEq

namespace GTree

/-- Empty-tree classifier. -/
def isEmpty : GTree → Bool
  | empty => true
  | _ => false

/-- Select the subtree corresponding to the next chromogram symbol. -/
def select : GTree → GramSymbol → GTree
  | node tPush _ _ _, GramSymbol.push => tPush
  | node _ tSkip _ _, GramSymbol.skip => tSkip
  | node _ _ tPop0 _, GramSymbol.pop0 => tPop0
  | node _ _ _ tPop1, GramSymbol.pop1 => tPop1
  | _, _ => empty

/-- Membership test for a chromogram in a tree. -/
def mem : GTree → Chromogram → Bool
  | node tPush tSkip tPop0 tPop1, s :: w =>
      mem (select (node tPush tSkip tPop0 tPop1) s) w
  | leaf0, [GramSymbol.push] => true
  | leaf1, [GramSymbol.skip] => true
  | leaf2, [GramSymbol.pop0] => true
  | leaf3, [GramSymbol.pop1] => true
  | leaf01, [GramSymbol.push] => true
  | leaf01, [GramSymbol.skip] => true
  | leaf12, [GramSymbol.skip] => true
  | leaf12, [GramSymbol.pop0] => true
  | leaf13, [GramSymbol.skip] => true
  | leaf13, [GramSymbol.pop1] => true
  | leaf23, [GramSymbol.pop0] => true
  | leaf23, [GramSymbol.pop1] => true
  | _, _ => false

abbrev SpecCTree := ColSeq → Bool

abbrev SpecGTree := Chromogram → Bool

/-- Open-stack partial chromogram matcher, porting Coq's `matchpg`.
Unlike `Chromogram.matchPartial`, the empty trace/word succeeds with any
residual open stack. -/
def matchOpen : Chromogram.BitStack → ColSeq → Chromogram → Bool
  | _, [], [] => true
  | bs, e :: et, s :: w =>
      match e, s, bs with
      | Color.one, GramSymbol.skip, _ => matchOpen bs et w
      | Color.two, GramSymbol.push, _ =>
          matchOpen (Chromogram.BitStack.push0 bs) et w
      | Color.two, GramSymbol.pop0, Chromogram.BitStack.push0 bs' =>
          matchOpen bs' et w
      | Color.two, GramSymbol.pop1, Chromogram.BitStack.push1 bs' =>
          matchOpen bs' et w
      | Color.three, GramSymbol.push, _ =>
          matchOpen (Chromogram.BitStack.push1 bs) et w
      | Color.three, GramSymbol.pop0, Chromogram.BitStack.push1 bs' =>
          matchOpen bs' et w
      | Color.three, GramSymbol.pop1, Chromogram.BitStack.push0 bs' =>
          matchOpen bs' et w
      | _, _, _ => false
  | _, _, _ => false

theorem matchOpen_flip_perm132
    (bs : Chromogram.BitStack) :
    ∀ (et : ColSeq) (w : Chromogram),
      matchOpen bs.flip (ColSeq.perm EdgePerm.p132 et) w =
        matchOpen bs et w
  | et, w => by
      induction et generalizing bs w with
      | nil =>
          cases w <;> cases bs <;> rfl
      | cons e et ih =>
          cases w with
          | nil =>
              cases e <;> cases bs <;> rfl
          | cons s w =>
              cases e with
              | zero =>
                  cases s <;> cases bs <;> rfl
              | one =>
                  cases s with
                  | push => cases bs <;> rfl
                  | skip =>
                      simpa [ColSeq.perm, EdgePerm.apply] using ih bs w
                  | pop0 => cases bs <;> rfl
                  | pop1 => cases bs <;> rfl
              | two =>
                  cases s with
                  | push =>
                      simpa [ColSeq.perm, EdgePerm.apply,
                        Chromogram.BitStack.flip] using
                        ih (Chromogram.BitStack.push0 bs) w
                  | skip => cases bs <;> rfl
                  | pop0 =>
                      cases bs with
                      | empty => rfl
                      | push0 bs' =>
                          simpa [ColSeq.perm, EdgePerm.apply,
                            Chromogram.BitStack.flip] using ih bs' w
                      | push1 bs' => rfl
                  | pop1 =>
                      cases bs with
                      | empty => rfl
                      | push0 bs' => rfl
                      | push1 bs' =>
                          simpa [ColSeq.perm, EdgePerm.apply,
                            Chromogram.BitStack.flip] using ih bs' w
              | three =>
                  cases s with
                  | push =>
                      simpa [ColSeq.perm, EdgePerm.apply,
                        Chromogram.BitStack.flip] using
                        ih (Chromogram.BitStack.push1 bs) w
                  | skip => cases bs <;> rfl
                  | pop0 =>
                      cases bs with
                      | empty => rfl
                      | push0 bs' => rfl
                      | push1 bs' =>
                          simpa [ColSeq.perm, EdgePerm.apply,
                            Chromogram.BitStack.flip] using ih bs' w
                  | pop1 =>
                      cases bs with
                      | empty => rfl
                      | push0 bs' =>
                          simpa [ColSeq.perm, EdgePerm.apply,
                            Chromogram.BitStack.flip] using ih bs' w
                      | push1 bs' => rfl

theorem matchOpen_empty_perm132
    (et : ColSeq) (w : Chromogram) :
    matchOpen Chromogram.BitStack.empty
        (ColSeq.perm EdgePerm.p132 et) w =
      matchOpen Chromogram.BitStack.empty et w := by
  simpa using matchOpen_flip_perm132 Chromogram.BitStack.empty et w

theorem matchOpen_empty_etrace
    (et : ColSeq) (w : Chromogram) :
    matchOpen Chromogram.BitStack.empty (ColSeq.etrace et) w =
      matchOpen Chromogram.BitStack.empty et w := by
  by_cases heven : ColSeq.evenTrace et = true
  · rw [ColSeq.etrace_of_even heven]
  · have hfalse : ColSeq.evenTrace et = false := by
      cases h : ColSeq.evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    rw [ColSeq.etrace_of_not_even hfalse]
    exact matchOpen_empty_perm132 et w

theorem matchOpen_length
    {bs : Chromogram.BitStack} {et : ColSeq} {w : Chromogram}
    (hmatch : matchOpen bs et w = true) :
    w.length = et.length := by
  induction et generalizing bs w with
  | nil =>
      cases w with
      | nil => rfl
      | cons s w =>
          simp [matchOpen] at hmatch
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases e <;> cases s <;> cases bs <;>
            simp [matchOpen] at hmatch ⊢
          all_goals exact ih hmatch

theorem matchOpen_not_mem_zero
    {bs : Chromogram.BitStack} {et : ColSeq} {w : Chromogram}
    (hmatch : matchOpen bs et w = true) :
    Color.zero ∉ et := by
  induction et generalizing bs w with
  | nil =>
      simp
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases e <;> cases s <;> cases bs <;>
            simp [matchOpen] at hmatch ⊢
          all_goals simpa using ih hmatch

theorem matchOpen_dropLast_of_matchg_append
    {bs : Chromogram.BitStack} :
    ∀ {et : ColSeq} {e : Color} {w : Chromogram},
      Chromogram.matchg bs.toList (et ++ [e]) w = true →
        matchOpen bs et w.dropLast = true
  | [], e, w, hmatch => by
      cases w with
      | nil =>
          cases bs <;> cases e <;> simp [Chromogram.matchg] at hmatch
      | cons s w =>
          cases w with
          | nil =>
              simp [matchOpen]
          | cons t w =>
              have hlen := Chromogram.matchg_length hmatch
              simp at hlen
  | c :: et, e, w, hmatch => by
      cases w with
      | nil =>
          cases c <;> cases bs <;> simp [Chromogram.matchg] at hmatch
      | cons s wtail =>
          cases wtail with
          | nil =>
              have hlen := Chromogram.matchg_length hmatch
              simp at hlen
          | cons t wtail =>
              have hne : t :: wtail ≠ [] := by simp
              rw [Chromogram.dropLast_cons_of_ne_nil (s := s) hne]
              cases c <;> cases s <;> cases bs <;>
                simp [matchOpen, Chromogram.matchg] at hmatch ⊢
              all_goals
                exact matchOpen_dropLast_of_matchg_append hmatch

theorem matchOpen_dropLast_of_matchg_ctrace
    {et : ColSeq} {w : Chromogram}
    (hmatch : Chromogram.matchg [] (ColSeq.ctrace et) w = true) :
    matchOpen Chromogram.BitStack.empty et w.dropLast = true := by
  simpa [ColSeq.ctrace] using
    (matchOpen_dropLast_of_matchg_append
      (bs := Chromogram.BitStack.empty)
      (et := et) (e := ColSeq.sum et) (w := w) hmatch)

/-- Existence test for a partial trace matching a chromogram and satisfying a
Boolean trace specification. -/
def hasMatch :
    Chromogram.BitStack → SpecCTree → Chromogram → Bool
  | _, ct, [] => ct []
  | bs, ct, GramSymbol.push :: w =>
      hasMatch (Chromogram.BitStack.push0 bs)
          (fun et => ct (Color.two :: et)) w ||
        hasMatch (Chromogram.BitStack.push1 bs)
          (fun et => ct (Color.three :: et)) w
  | bs, ct, GramSymbol.skip :: w =>
      hasMatch bs (fun et => ct (Color.one :: et)) w
  | Chromogram.BitStack.empty, _, GramSymbol.pop0 :: _ => false
  | Chromogram.BitStack.push0 bs, ct, GramSymbol.pop0 :: w =>
      hasMatch bs (fun et => ct (Color.two :: et)) w
  | Chromogram.BitStack.push1 bs, ct, GramSymbol.pop0 :: w =>
      hasMatch bs (fun et => ct (Color.three :: et)) w
  | Chromogram.BitStack.empty, _, GramSymbol.pop1 :: _ => false
  | Chromogram.BitStack.push0 bs, ct, GramSymbol.pop1 :: w =>
      hasMatch bs (fun et => ct (Color.three :: et)) w
  | Chromogram.BitStack.push1 bs, ct, GramSymbol.pop1 :: w =>
      hasMatch bs (fun et => ct (Color.two :: et)) w

/-- Count chromograms satisfying `st` that match a partial trace under stack
`bs`. -/
def matchCount (st : SpecGTree) :
    Chromogram.BitStack → ColSeq → Nat
  | _, [] => if st [] then 1 else 0
  | _, Color.zero :: _ => 0
  | bs, Color.one :: et =>
      matchCount (fun w => st (GramSymbol.skip :: w)) bs et
  | bs, Color.two :: et =>
      matchCount (fun w => st (GramSymbol.push :: w))
          (Chromogram.BitStack.push0 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (fun w => st (GramSymbol.pop0 :: w)) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (fun w => st (GramSymbol.pop1 :: w)) bs' et
  | bs, Color.three :: et =>
      matchCount (fun w => st (GramSymbol.push :: w))
          (Chromogram.BitStack.push1 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (fun w => st (GramSymbol.pop1 :: w)) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (fun w => st (GramSymbol.pop0 :: w)) bs' et

/-- Number of stored chromograms matching a trace and stack. -/
def sub (t : GTree) : Chromogram.BitStack → ColSeq → Nat :=
  matchCount (mem t)

/-- Non-short-circuiting helper used by the empty-node test. -/
def emptyAnd (t : GTree) (b : Bool) : Bool :=
  match t, b with
  | empty, true => true
  | _, _ => false

/-- Classifier for nodes whose four children are empty. -/
def empty4 : GTree → Bool
  | node tPush tSkip tPop0 tPop1 =>
      emptyAnd tPush
        (emptyAnd tSkip (emptyAnd tPop0 (isEmpty tPop1)))
  | _ => false

/-- Pair type returned by chromogram-tree restriction algorithms. -/
structure Pair where
  left : GTree
  right : GTree
  deriving DecidableEq

/-- Empty chromogram-tree pair. -/
def emptyPair : Pair where
  left := empty
  right := empty

/-- Select one component of a tree pair. -/
def pairSub (pt : Pair) (b : Bool) : GTree :=
  if b then pt.right else pt.left

/-- Assemble a pair of nodes from four pairs of subtrees.  Coq
`gtree_cons_pairs` canonicalizes an all-empty side to the `empty` constructor;
the closure algorithm relies on that representation-level invariant. -/
def consPairs (pPush pSkip pPop0 pPop1 : Pair) : Pair :=
  let left := node pPush.left pSkip.left pPop0.left pPop1.left
  let right := node pPush.right pSkip.right pPop0.right pPop1.right
  if empty4 left then
    ⟨pPush.left, right⟩
  else if empty4 right then
    ⟨left, pPush.right⟩
  else
    ⟨left, right⟩

end GTree

end FourColor

end Schematic.Math.GraphTheory
