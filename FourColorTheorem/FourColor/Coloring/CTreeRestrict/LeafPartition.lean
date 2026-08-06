import FourColorTheorem.FourColor.Coloring.CTreeRestrict.Restriction
import FourColorTheorem.FourColor.Coloring.BoolPartition

/-! Leaf operations and the base partition construction for trace trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

/-- Decrement a leaf stack by `n`, stopping at non-leaves. -/
def decr : CTree → Nat → CTree
  | leaf lf, n + 1 => decr lf n
  | lf, _ => lf

theorem decr_zero (lf : CTree) :
    decr lf 0 = lf := by
  cases lf <;> rfl

theorem decr_non_leaf
    {t : CTree} (h : isLeaf t = false) (n : Nat) :
    decr t n = t := by
  cases t <;> cases n <;> simp [decr, isLeaf] at h ⊢

theorem decr_leafOf :
    ∀ (m n : Nat), decr (leafOf m) n = leafOf (m - n)
  | m, 0 => by
      simp [decr, Nat.sub_zero]
  | 0, n + 1 => by
      simp [leafOf, decr]
  | m + 1, n + 1 => by
      change decr (leafOf m) n = leafOf ((m + 1) - (n + 1))
      rw [decr_leafOf m n]
      simp [Nat.succ_sub_succ_eq_sub]

theorem proper_decr_leafOf (m n : Nat) :
    Proper 0 (decr (leafOf m) n) := by
  rw [decr_leafOf]
  exact proper_leafOf _

/-- Decrement one of the three height-one leaf stacks according to a single
chromogram-tree restriction entry. -/
def entryDecr
    (bs : Chromogram.BitStack) (gt : GTree) (e : Color) (lf : CTree) :
    CTree :=
  decr lf (GTree.sub gt bs [e])

/-- Decrement all three height-one leaf stacks by all entries of a
restriction.  This is the specification-shaped version of Coq's optimized
`ctr_decr`. -/
def decrLeaves :
    CTree → CTree → CTree → Restriction → CTree × CTree × CTree
  | lf1, lf2, lf3, Restriction.nil => (lf1, lf2, lf3)
  | lf1, lf2, lf3, Restriction.cons bs gt r =>
      decrLeaves
        (entryDecr bs gt Color.one lf1)
        (entryDecr bs gt Color.two lf2)
        (entryDecr bs gt Color.three lf3)
        r

theorem decrLeaves_leafOf :
    ∀ (r : Restriction) (n1 n2 n3 : Nat),
      decrLeaves (leafOf n1) (leafOf n2) (leafOf n3) r =
        (leafOf (n1 - Restriction.sub r [Color.one]),
          leafOf (n2 - Restriction.sub r [Color.two]),
          leafOf (n3 - Restriction.sub r [Color.three]))
  | Restriction.nil, n1, n2, n3 => by
      simp [decrLeaves, Restriction.sub]
  | Restriction.cons bs gt r, n1, n2, n3 => by
      simp [decrLeaves, entryDecr, decr_leafOf,
        Restriction.sub, decrLeaves_leafOf r]
      simp [Nat.sub_sub]

/-- Assemble a pair of trace trees from three pairs of subtrees. -/
def consPairs (pt1 pt2 pt3 : Pair) : Pair where
  left := cons pt1.left pt2.left pt3.left
  right := cons pt1.right pt2.right pt3.right

theorem consPairs_spec (pt1 pt2 pt3 : Pair) :
    consPairs pt1 pt2 pt3 =
      ⟨cons pt1.left pt2.left pt3.left,
        cons pt1.right pt2.right pt3.right⟩ := rfl

@[simp]
theorem consPairs_left (pt1 pt2 pt3 : Pair) :
    (consPairs pt1 pt2 pt3).left =
      cons pt1.left pt2.left pt3.left := rfl

@[simp]
theorem consPairs_right (pt1 pt2 pt3 : Pair) :
    (consPairs pt1 pt2 pt3).right =
      cons pt1.right pt2.right pt3.right := rfl

theorem sub_left_consPairs
    (pt1 pt2 pt3 : Pair) (et : ColSeq) :
    sub (consPairs pt1 pt2 pt3).left et =
      sub (node pt1.left pt2.left pt3.left) et := by
  cases pt1 with
  | mk l1 r1 =>
      cases pt2 with
      | mk l2 r2 =>
          cases pt3 with
          | mk l3 r3 =>
              cases l1 <;> cases l2 <;> cases l3 <;>
                cases et with
                | nil => rfl
                | cons e et =>
                    cases e <;> rfl

theorem sub_right_consPairs
    (pt1 pt2 pt3 : Pair) (et : ColSeq) :
    sub (consPairs pt1 pt2 pt3).right et =
      sub (node pt1.right pt2.right pt3.right) et := by
  cases pt1 with
  | mk l1 r1 =>
      cases pt2 with
      | mk l2 r2 =>
          cases pt3 with
          | mk l3 r3 =>
              cases r1 <;> cases r2 <;> cases r3 <;>
                cases et with
                | nil => rfl
                | cons e et =>
                    cases e <;> rfl

/-- Base-case leaf partition after decrementing. -/
def leafPair
    (lf1 lf2 lf3 lf1' lf2' lf3' : CTree) : Pair where
  left := cons lf1' lf2' lf3'
  right :=
    cons
      (if isEmpty lf1' then lf1 else empty)
      (if isEmpty lf2' then lf2 else empty)
      (if isEmpty lf3' then lf3 else empty)

theorem leafPair_spec
    (lf1 lf2 lf3 lf1' lf2' lf3' : CTree) :
    leafPair lf1 lf2 lf3 lf1' lf2' lf3' =
      ⟨cons lf1' lf2' lf3',
        cons
          (if isEmpty lf1' then lf1 else empty)
          (if isEmpty lf2' then lf2 else empty)
          (if isEmpty lf3' then lf3 else empty)⟩ := rfl

/-- Restrict a trace tree of height `h + 1` by subtracting all match counts in
a trace restriction. -/
def restrict : Nat → CTree → Restriction → Pair
  | _, t, Restriction.nil => ⟨t, empty⟩
  | h + 1, node t1 t2 t3, r =>
      let cont r1 r2 r3 :=
        consPairs
          (restrict h t1 r1)
          (restrict h t2 r2)
          (restrict h t3 r3)
      Restriction.split cont Restriction.nil Restriction.nil Restriction.nil r
  | 0, node lf1 lf2 lf3, r =>
      let dec := decrLeaves lf1 lf2 lf3 r
      leafPair lf1 lf2 lf3 dec.1 dec.2.1 dec.2.2
  | _, _, _ => emptyPair

@[simp]
theorem restrict_nil (h : Nat) (t : CTree) :
    restrict h t Restriction.nil = ⟨t, empty⟩ := by
  cases h <;> cases t <;> rfl

@[simp]
theorem decrLeaves_nil (lf1 lf2 lf3 : CTree) :
    decrLeaves lf1 lf2 lf3 Restriction.nil = (lf1, lf2, lf3) := rfl

/-- Boolean partition of trace predicates: the two parts cover the whole and
are disjoint. -/
def SpecPartition
    (whole left right : ColSeq → Bool) : Prop :=
  Bool.SpecPartition whole left right

/-- A tree pair partitions a trace tree. -/
def Partition (t : CTree) (pt : Pair) : Prop :=
  SpecPartition (mem t) (mem pt.left) (mem pt.right)

theorem specPartition_symm
    {whole left right : ColSeq → Bool}
    (h : SpecPartition whole left right) :
    SpecPartition whole right left :=
  Bool.specPartition_symm h

theorem partition_self_empty (t : CTree) :
    Partition t ⟨t, empty⟩ := by
  constructor
  · intro et
    simp [mem_empty]
  · intro et _h
    simp [mem_empty]

theorem partition_empty_self (t : CTree) :
    Partition t ⟨empty, t⟩ := by
  exact specPartition_symm (partition_self_empty t)

theorem leafOf_decr_partition (n k : Nat) :
    Partition (leafOf n)
      ⟨leafOf (n - k),
        if isEmpty (leafOf (n - k)) then leafOf n else empty⟩ := by
  constructor
  · intro et
    cases et with
    | nil =>
        change mem (leafOf n) [] =
          (mem (leafOf (n - k)) [] ||
            mem (if isEmpty (leafOf (n - k)) then leafOf n else empty) [])
        by_cases h : n - k = 0
        · simp [isEmpty_leafOf, h, mem_leafOf_nil]
        · have hn : n ≠ 0 := by omega
          have hnBool : (n != 0) = true := by simp [hn]
          have hsubBool : (n - k != 0) = true := by simp [h]
          simp [isEmpty_leafOf, h, mem_leafOf_nil, hnBool, hsubBool]
    | cons e et =>
        change mem (leafOf n) (e :: et) =
          (mem (leafOf (n - k)) (e :: et) ||
            mem (if isEmpty (leafOf (n - k)) then leafOf n else empty)
              (e :: et))
        by_cases h : isEmpty (leafOf (n - k)) = true <;> simp [h]
  · intro et hleft
    cases et with
    | nil =>
        change mem
          (if isEmpty (leafOf (n - k)) then leafOf n else empty) [] = false
        by_cases h : n - k = 0
        · simp [h, mem_leafOf_nil] at hleft
        · simp [isEmpty_leafOf, h]
    | cons e et =>
        simp at hleft

theorem consPairs_partition
    {t1 t2 t3 : CTree} {pt1 pt2 pt3 : Pair}
    (h1 : Partition t1 pt1)
    (h2 : Partition t2 pt2)
    (h3 : Partition t3 pt3) :
    Partition (node t1 t2 t3) (consPairs pt1 pt2 pt3) := by
  constructor
  · intro et
    cases et with
    | nil =>
        change mem (node t1 t2 t3) [] =
          (mem (cons pt1.left pt2.left pt3.left) [] ||
            mem (cons pt1.right pt2.right pt3.right) [])
        rw [mem_cons, mem_cons]
        rfl
    | cons e et =>
      cases e with
      | zero =>
            change mem (node t1 t2 t3) (Color.zero :: et) =
              (mem (cons pt1.left pt2.left pt3.left) (Color.zero :: et) ||
                mem (cons pt1.right pt2.right pt3.right) (Color.zero :: et))
            rw [mem_cons, mem_cons]
            rfl
      | one =>
            change mem (node t1 t2 t3) (Color.one :: et) =
              (mem (cons pt1.left pt2.left pt3.left) (Color.one :: et) ||
                mem (cons pt1.right pt2.right pt3.right) (Color.one :: et))
            rw [mem_cons, mem_cons]
            exact h1.1 et
      | two =>
            change mem (node t1 t2 t3) (Color.two :: et) =
              (mem (cons pt1.left pt2.left pt3.left) (Color.two :: et) ||
                mem (cons pt1.right pt2.right pt3.right) (Color.two :: et))
            rw [mem_cons, mem_cons]
            exact h2.1 et
      | three =>
            change mem (node t1 t2 t3) (Color.three :: et) =
              (mem (cons pt1.left pt2.left pt3.left) (Color.three :: et) ||
                mem (cons pt1.right pt2.right pt3.right) (Color.three :: et))
            rw [mem_cons, mem_cons]
            exact h3.1 et
  · intro et hleft
    cases et with
    | nil =>
        change mem (cons pt1.right pt2.right pt3.right) [] = false
        rw [mem_cons]
        rfl
    | cons e et =>
      cases e with
      | zero =>
            change mem (cons pt1.right pt2.right pt3.right)
              (Color.zero :: et) = false
            rw [mem_cons]
            rfl
      | one =>
            change mem (cons pt1.left pt2.left pt3.left)
              (Color.one :: et) = true at hleft
            change mem (cons pt1.right pt2.right pt3.right)
              (Color.one :: et) = false
            rw [mem_cons] at hleft ⊢
            change mem pt1.right et = false
            exact h1.2 et (by
              simpa [mem, sub] using hleft)
      | two =>
            change mem (cons pt1.left pt2.left pt3.left)
              (Color.two :: et) = true at hleft
            change mem (cons pt1.right pt2.right pt3.right)
              (Color.two :: et) = false
            rw [mem_cons] at hleft ⊢
            change mem pt2.right et = false
            exact h2.2 et (by
              simpa [mem, sub] using hleft)
      | three =>
            change mem (cons pt1.left pt2.left pt3.left)
              (Color.three :: et) = true at hleft
            change mem (cons pt1.right pt2.right pt3.right)
              (Color.three :: et) = false
            rw [mem_cons] at hleft ⊢
            change mem pt3.right et = false
            exact h3.2 et (by
              simpa [mem, sub] using hleft)

theorem leafPair_leafOf_partition
    (n1 n2 n3 k1 k2 k3 : Nat) :
    Partition (node (leafOf n1) (leafOf n2) (leafOf n3))
      (leafPair
        (leafOf n1) (leafOf n2) (leafOf n3)
        (leafOf (n1 - k1)) (leafOf (n2 - k2)) (leafOf (n3 - k3))) := by
  simpa [leafPair, consPairs] using
    consPairs_partition
      (leafOf_decr_partition n1 k1)
      (leafOf_decr_partition n2 k2)
      (leafOf_decr_partition n3 k3)

theorem leafPair_leafOf_proper
    (n1 n2 n3 k1 k2 k3 : Nat) :
    Proper 1
        (leafPair
          (leafOf n1) (leafOf n2) (leafOf n3)
          (leafOf (n1 - k1)) (leafOf (n2 - k2)) (leafOf (n3 - k3))).left ∧
      Proper 1
        (leafPair
          (leafOf n1) (leafOf n2) (leafOf n3)
          (leafOf (n1 - k1)) (leafOf (n2 - k2)) (leafOf (n3 - k3))).right := by
  constructor
  · rw [leafPair_spec]
    exact proper_cons (proper_leafOf _) (proper_leafOf _) (proper_leafOf _)
  · rw [leafPair_spec]
    apply proper_cons
    · by_cases h : isEmpty (leafOf (n1 - k1)) = true <;>
        simp [h, proper_leafOf, proper_empty]
    · by_cases h : isEmpty (leafOf (n2 - k2)) = true <;>
        simp [h, proper_leafOf, proper_empty]
    · by_cases h : isEmpty (leafOf (n3 - k3)) = true <;>
        simp [h, proper_leafOf, proper_empty]

end CTree

end FourColor

end Schematic.Math.GraphTheory
