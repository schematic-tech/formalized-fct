import FourColorTheorem.FourColor.Coloring.GTreeRestrict.LeafCases

/-! Exact membership and partition correctness for chromogram-tree restriction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

theorem restrict_left_mem
    (t : GTree) (r : Restriction) (w : Chromogram) :
    mem (restrict t r).left w = (mem t w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_pairSub_mem t r w false

theorem restrict_right_mem
    (t : GTree) (r : Restriction) (w : Chromogram) :
    mem (restrict t r).right w = (mem t w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_pairSub_mem t r w true

theorem restrict_partition_exact (t : GTree) (r : Restriction) :
    Partition t (restrict t r) := by
  constructor
  · intro w
    rw [restrict_left_mem, restrict_right_mem]
    cases ht : mem t w <;> cases hr : Restriction.mem r w <;> rfl
  · intro w hleft
    rw [restrict_left_mem] at hleft
    rw [restrict_right_mem]
    cases ht : mem t w <;> cases hr : Restriction.mem r w <;>
      simp [ht, hr] at hleft ⊢

theorem restrict_sub_add
    (t : GTree) (r : Restriction)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub t bs et =
      sub (restrict t r).left bs et +
        sub (restrict t r).right bs et := by
  have hpart := restrict_partition_exact t r
  exact matchCount_partition hpart.1 hpart.2 bs et

theorem restrict_leaf0_partition (r : Restriction) :
    Partition leaf0 (restrict leaf0 r) := by
  cases h : Restriction.match0 r
  · simpa [h, pairEmpty0, treePair] using partition_empty_self leaf0
  · simpa [h, pair0Empty, treePair] using partition_self_empty leaf0

theorem restrict_leaf1_partition (r : Restriction) :
    Partition leaf1 (restrict leaf1 r) := by
  cases h : Restriction.match1 r
  · simpa [h, pairEmpty1, treePair] using partition_empty_self leaf1
  · simpa [h, pair1Empty, treePair] using partition_self_empty leaf1

theorem restrict_leaf2_partition (r : Restriction) :
    Partition leaf2 (restrict leaf2 r) := by
  cases h : Restriction.match2 r
  · simpa [h, pairEmpty2, treePair] using partition_empty_self leaf2
  · simpa [h, pair2Empty, treePair] using partition_self_empty leaf2

theorem restrict_leaf3_partition (r : Restriction) :
    Partition leaf3 (restrict leaf3 r) := by
  cases h : Restriction.match3 r
  · simpa [h, pairEmpty3, treePair] using partition_empty_self leaf3
  · simpa [h, pair3Empty, treePair] using partition_self_empty leaf3

theorem restrict_leaf01_partition (r : Restriction) :
    Partition leaf01 (restrict leaf01 r) := by
  cases h0 : Restriction.match0 r <;> cases h1 : Restriction.match1 r
  · simpa [h0, h1, pairEmpty01, treePair] using partition_empty_self leaf01
  · simpa [h0, h1, pair10, treePair] using partition_leaf01_pair10
  · simpa [h0, h1, pair01, treePair] using partition_leaf01_pair01
  · simpa [h0, h1, pair01Empty, treePair] using partition_self_empty leaf01

theorem restrict_leaf12_partition (r : Restriction) :
    Partition leaf12 (restrict leaf12 r) := by
  cases h1 : Restriction.match1 r <;> cases h2 : Restriction.match2 r
  · simpa [h1, h2, pairEmpty12, treePair] using partition_empty_self leaf12
  · simpa [h1, h2, pair21, treePair] using partition_leaf12_pair21
  · simpa [h1, h2, pair12, treePair] using partition_leaf12_pair12
  · simpa [h1, h2, pair12Empty, treePair] using partition_self_empty leaf12

theorem restrict_leaf13_partition (r : Restriction) :
    Partition leaf13 (restrict leaf13 r) := by
  cases h1 : Restriction.match1 r <;> cases h3 : Restriction.match3 r
  · simpa [h1, h3, pairEmpty13, treePair] using partition_empty_self leaf13
  · simpa [h1, h3, pair31, treePair] using partition_leaf13_pair31
  · simpa [h1, h3, pair13, treePair] using partition_leaf13_pair13
  · simpa [h1, h3, pair13Empty, treePair] using partition_self_empty leaf13

theorem restrict_leaf23_partition (r : Restriction) :
    Partition leaf23 (restrict leaf23 r) := by
  cases h2 : Restriction.match2 r <;> cases h3 : Restriction.match3 r
  · simpa [h2, h3, pairEmpty23, treePair] using partition_empty_self leaf23
  · simpa [h2, h3, pair32, treePair] using partition_leaf23_pair32
  · simpa [h2, h3, pair23, treePair] using partition_leaf23_pair23
  · simpa [h2, h3, pair23Empty, treePair] using partition_self_empty leaf23

theorem restrict_partition (t : GTree) (r : Restriction) :
    Partition t (restrict t r) :=
  restrict_partition_exact t r

end GTree

end FourColor

end Schematic.Math.GraphTheory
