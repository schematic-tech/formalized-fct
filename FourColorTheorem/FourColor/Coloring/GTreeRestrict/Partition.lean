import FourColorTheorem.FourColor.Coloring.GTreeRestrict.Restriction
import FourColorTheorem.FourColor.Coloring.BoolPartition

/-! Canonical tree pairs and their partition semantics. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

def treePair (l r : GTree) : Pair := ⟨l, r⟩

def pair0Empty : Pair := treePair leaf0 empty
def pair1Empty : Pair := treePair leaf1 empty
def pair2Empty : Pair := treePair leaf2 empty
def pair3Empty : Pair := treePair leaf3 empty
def pair01Empty : Pair := treePair leaf01 empty
def pair12Empty : Pair := treePair leaf12 empty
def pair13Empty : Pair := treePair leaf13 empty
def pair23Empty : Pair := treePair leaf23 empty

def pairEmpty0 : Pair := treePair empty leaf0
def pairEmpty1 : Pair := treePair empty leaf1
def pairEmpty2 : Pair := treePair empty leaf2
def pairEmpty3 : Pair := treePair empty leaf3
def pairEmpty01 : Pair := treePair empty leaf01
def pairEmpty12 : Pair := treePair empty leaf12
def pairEmpty13 : Pair := treePair empty leaf13
def pairEmpty23 : Pair := treePair empty leaf23

def pair01 : Pair := treePair leaf0 leaf1
def pair10 : Pair := treePair leaf1 leaf0
def pair12 : Pair := treePair leaf1 leaf2
def pair21 : Pair := treePair leaf2 leaf1
def pair13 : Pair := treePair leaf1 leaf3
def pair31 : Pair := treePair leaf3 leaf1
def pair23 : Pair := treePair leaf2 leaf3
def pair32 : Pair := treePair leaf3 leaf2

/-- Partition a chromogram tree by deleting all matches in a restriction. -/
def restrict : GTree → Restriction → Pair
  | t, Restriction.nil => treePair empty t
  | node tPush tSkip tPop0 tPop1, r =>
      let cont rPush rSkip rPop0 rPop1 :=
        consPairs
          (restrict tPush rPush)
          (restrict tSkip rSkip)
          (restrict tPop0 rPop0)
          (restrict tPop1 rPop1)
      Restriction.split cont
        Restriction.nil Restriction.nil Restriction.nil Restriction.nil r
  | leaf0, r => if Restriction.match0 r then pair0Empty else pairEmpty0
  | leaf1, r => if Restriction.match1 r then pair1Empty else pairEmpty1
  | leaf2, r => if Restriction.match2 r then pair2Empty else pairEmpty2
  | leaf3, r => if Restriction.match3 r then pair3Empty else pairEmpty3
  | leaf01, r =>
      if Restriction.match0 r then
        if Restriction.match1 r then pair01Empty else pair01
      else
        if Restriction.match1 r then pair10 else pairEmpty01
  | leaf12, r =>
      if Restriction.match1 r then
        if Restriction.match2 r then pair12Empty else pair12
      else
        if Restriction.match2 r then pair21 else pairEmpty12
  | leaf13, r =>
      if Restriction.match1 r then
        if Restriction.match3 r then pair13Empty else pair13
      else
        if Restriction.match3 r then pair31 else pairEmpty13
  | leaf23, r =>
      if Restriction.match2 r then
        if Restriction.match3 r then pair23Empty else pair23
      else
        if Restriction.match3 r then pair32 else pairEmpty23
  | empty, _ => emptyPair

@[simp]
theorem restrict_nil (t : GTree) :
    restrict t Restriction.nil = treePair empty t := by
  cases t <;> rfl

@[simp]
theorem restriction_mem_nil (w : Chromogram) :
    Restriction.mem Restriction.nil w = false := rfl

/-- Boolean partition of chromogram predicates: the two parts cover the whole
and are disjoint. -/
def SpecPartition
    (whole left right : Chromogram → Bool) : Prop :=
  Bool.SpecPartition whole left right

/-- A tree pair partitions a chromogram tree. -/
def Partition (t : GTree) (pt : Pair) : Prop :=
  SpecPartition (mem t) (mem pt.left) (mem pt.right)

theorem specPartition_symm
    {whole left right : Chromogram → Bool}
    (h : SpecPartition whole left right) :
    SpecPartition whole right left :=
  Bool.specPartition_symm h

theorem partition_empty_self (t : GTree) :
    Partition t ⟨empty, t⟩ := by
  constructor
  · intro w
    simp [mem_empty]
  · intro w h
    simp [mem_empty] at h

theorem partition_self_empty (t : GTree) :
    Partition t ⟨t, empty⟩ := by
  exact specPartition_symm (partition_empty_self t)

theorem mem_consPairs_left_nil
    (pPush pSkip pPop0 pPop1 : Pair) :
    mem (consPairs pPush pSkip pPop0 pPop1).left [] = false := by
  simp [consPairs, mem]

theorem mem_consPairs_right_nil
    (pPush pSkip pPop0 pPop1 : Pair) :
    mem (consPairs pPush pSkip pPop0 pPop1).right [] = false := by
  simp [consPairs, mem]

theorem mem_consPairs_left_symbol
    (pPush pSkip pPop0 pPop1 : Pair)
    (s : GramSymbol) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).left (s :: w) =
      mem (match s with
        | GramSymbol.push => pPush.left
        | GramSymbol.skip => pSkip.left
        | GramSymbol.pop0 => pPop0.left
        | GramSymbol.pop1 => pPop1.left) w := by
  cases s <;> simp only
  all_goals
    unfold consPairs
    dsimp only
    split
    next hleft =>
      rcases GTree.empty4_eq_true hleft with
        ⟨hPush, hSkip, hPop0, hPop1⟩
      simp [hPush, hSkip, hPop0, hPop1]
    next hleft =>
      split <;> rfl

theorem mem_consPairs_right_symbol
    (pPush pSkip pPop0 pPop1 : Pair)
    (s : GramSymbol) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).right (s :: w) =
      mem (match s with
        | GramSymbol.push => pPush.right
        | GramSymbol.skip => pSkip.right
        | GramSymbol.pop0 => pPop0.right
        | GramSymbol.pop1 => pPop1.right) w := by
  cases s <;> simp only
  all_goals
    unfold consPairs
    dsimp only
    split
    next hleft => rfl
    next hleft =>
      split
      next hright =>
        rcases GTree.empty4_eq_true hright with
          ⟨hPush, hSkip, hPop0, hPop1⟩
        simp [hPush, hSkip, hPop0, hPop1]
      next hright => rfl

theorem mem_consPairs_pairSub_nil
    (pPush pSkip pPop0 pPop1 : Pair) (side : Bool) :
    mem (pairSub (consPairs pPush pSkip pPop0 pPop1) side) [] = false := by
  cases side
  · simpa [pairSub] using
      mem_consPairs_left_nil pPush pSkip pPop0 pPop1
  · simpa [pairSub] using
      mem_consPairs_right_nil pPush pSkip pPop0 pPop1

theorem mem_consPairs_pairSub_symbol
    (pPush pSkip pPop0 pPop1 : Pair)
    (side : Bool) (s : GramSymbol) (w : Chromogram) :
    mem (pairSub (consPairs pPush pSkip pPop0 pPop1) side) (s :: w) =
      mem (pairSub
        (match s with
        | GramSymbol.push => pPush
        | GramSymbol.skip => pSkip
        | GramSymbol.pop0 => pPop0
        | GramSymbol.pop1 => pPop1) side) w := by
  cases side <;> cases s <;>
    simp [pairSub, mem_consPairs_left_symbol, mem_consPairs_right_symbol]

theorem consPairs_partition
    {tPush tSkip tPop0 tPop1 : GTree}
    {pPush pSkip pPop0 pPop1 : Pair}
    (hPush : Partition tPush pPush)
    (hSkip : Partition tSkip pSkip)
    (hPop0 : Partition tPop0 pPop0)
    (hPop1 : Partition tPop1 pPop1) :
    Partition (node tPush tSkip tPop0 tPop1)
      (consPairs pPush pSkip pPop0 pPop1) := by
  constructor
  · intro w
    cases w with
    | nil =>
        rw [mem_consPairs_left_nil, mem_consPairs_right_nil]
        rfl
    | cons s w =>
        cases s with
        | push =>
            rw [mem_consPairs_left_symbol, mem_consPairs_right_symbol]
            exact hPush.1 w
        | skip =>
            rw [mem_consPairs_left_symbol, mem_consPairs_right_symbol]
            exact hSkip.1 w
        | pop0 =>
            rw [mem_consPairs_left_symbol, mem_consPairs_right_symbol]
            exact hPop0.1 w
        | pop1 =>
            rw [mem_consPairs_left_symbol, mem_consPairs_right_symbol]
            exact hPop1.1 w
  · intro w hleft
    cases w with
    | nil =>
        simp [mem] at hleft
    | cons s w =>
        cases s with
        | push =>
            rw [mem_consPairs_left_symbol] at hleft
            rw [mem_consPairs_right_symbol]
            exact hPush.2 w hleft
        | skip =>
            rw [mem_consPairs_left_symbol] at hleft
            rw [mem_consPairs_right_symbol]
            exact hSkip.2 w hleft
        | pop0 =>
            rw [mem_consPairs_left_symbol] at hleft
            rw [mem_consPairs_right_symbol]
            exact hPop0.2 w hleft
        | pop1 =>
            rw [mem_consPairs_left_symbol] at hleft
            rw [mem_consPairs_right_symbol]
            exact hPop1.2 w hleft

theorem partition_leaf01_pair01 :
    Partition leaf01 pair01 := by
  constructor
  · intro w
    cases w with
    | nil => rfl
    | cons s w =>
        cases w <;> cases s <;> rfl
  · intro w hleft
    cases w with
    | nil => simp [pair01, treePair, mem] at hleft
    | cons s w =>
        cases w <;> cases s <;> simp [pair01, treePair, mem] at hleft ⊢

theorem partition_leaf01_pair10 :
    Partition leaf01 pair10 := by
  exact specPartition_symm partition_leaf01_pair01

theorem partition_leaf12_pair12 :
    Partition leaf12 pair12 := by
  constructor
  · intro w
    cases w with
    | nil => rfl
    | cons s w =>
        cases w <;> cases s <;> rfl
  · intro w hleft
    cases w with
    | nil => simp [pair12, treePair, mem] at hleft
    | cons s w =>
        cases w <;> cases s <;> simp [pair12, treePair, mem] at hleft ⊢

theorem partition_leaf12_pair21 :
    Partition leaf12 pair21 := by
  exact specPartition_symm partition_leaf12_pair12

theorem partition_leaf13_pair13 :
    Partition leaf13 pair13 := by
  constructor
  · intro w
    cases w with
    | nil => rfl
    | cons s w =>
        cases w <;> cases s <;> rfl
  · intro w hleft
    cases w with
    | nil => simp [pair13, treePair, mem] at hleft
    | cons s w =>
        cases w <;> cases s <;> simp [pair13, treePair, mem] at hleft ⊢

theorem partition_leaf13_pair31 :
    Partition leaf13 pair31 := by
  exact specPartition_symm partition_leaf13_pair13

theorem partition_leaf23_pair23 :
    Partition leaf23 pair23 := by
  constructor
  · intro w
    cases w with
    | nil => rfl
    | cons s w =>
        cases w <;> cases s <;> rfl
  · intro w hleft
    cases w with
    | nil => simp [pair23, treePair, mem] at hleft
    | cons s w =>
        cases w <;> cases s <;> simp [pair23, treePair, mem] at hleft ⊢

theorem partition_leaf23_pair32 :
    Partition leaf23 pair32 := by
  exact specPartition_symm partition_leaf23_pair23

theorem restrict_nil_partition (t : GTree) :
    Partition t (restrict t Restriction.nil) := by
  rw [restrict_nil]
  exact partition_empty_self t

theorem restrict_nil_left (t : GTree) :
    (restrict t Restriction.nil).left = empty := by
  rw [restrict_nil]
  rfl

theorem restrict_nil_right (t : GTree) :
    (restrict t Restriction.nil).right = t := by
  rw [restrict_nil]
  rfl

theorem restrict_nil_left_mem
    (t : GTree) (w : Chromogram) :
    mem (restrict t Restriction.nil).left w =
      (mem t w && Restriction.mem Restriction.nil w) := by
  rw [restrict_nil]
  simp [treePair]

theorem restrict_nil_right_mem
    (t : GTree) (w : Chromogram) :
    mem (restrict t Restriction.nil).right w =
      (mem t w && !(Restriction.mem Restriction.nil w)) := by
  rw [restrict_nil]
  simp [treePair]

theorem mem_consPairs_left_push
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).left
      (GramSymbol.push :: w) =
      mem pPush.left w := by
  exact mem_consPairs_left_symbol _ _ _ _ GramSymbol.push w

theorem mem_consPairs_left_skip
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).left
      (GramSymbol.skip :: w) =
      mem pSkip.left w := by
  exact mem_consPairs_left_symbol _ _ _ _ GramSymbol.skip w

theorem mem_consPairs_left_pop0
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).left
      (GramSymbol.pop0 :: w) =
      mem pPop0.left w := by
  exact mem_consPairs_left_symbol _ _ _ _ GramSymbol.pop0 w

theorem mem_consPairs_left_pop1
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).left
      (GramSymbol.pop1 :: w) =
      mem pPop1.left w := by
  exact mem_consPairs_left_symbol _ _ _ _ GramSymbol.pop1 w

theorem mem_consPairs_right_push
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).right
      (GramSymbol.push :: w) =
      mem pPush.right w := by
  exact mem_consPairs_right_symbol _ _ _ _ GramSymbol.push w

theorem mem_consPairs_right_skip
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).right
      (GramSymbol.skip :: w) =
      mem pSkip.right w := by
  exact mem_consPairs_right_symbol _ _ _ _ GramSymbol.skip w

theorem mem_consPairs_right_pop0
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).right
      (GramSymbol.pop0 :: w) =
      mem pPop0.right w := by
  exact mem_consPairs_right_symbol _ _ _ _ GramSymbol.pop0 w

theorem mem_consPairs_right_pop1
    (pPush pSkip pPop0 pPop1 : Pair) (w : Chromogram) :
    mem (consPairs pPush pSkip pPop0 pPop1).right
      (GramSymbol.pop1 :: w) =
      mem pPop1.right w := by
  exact mem_consPairs_right_symbol _ _ _ _ GramSymbol.pop1 w

end GTree

end FourColor

end Schematic.Math.GraphTheory
