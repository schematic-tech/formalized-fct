import FourColorTheorem.FourColor.Coloring.GTree.CountingSemantics

/-! Color symmetry and additive partitions of chromogram match counts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

theorem matchCount_flip_perm132
    {st : SpecGTree} :
    ∀ (bs : Chromogram.BitStack) (et : ColSeq),
      matchCount st bs.flip (ColSeq.perm EdgePerm.p132 et) =
        matchCount st bs et
  | bs, [] => by
      simp [matchCount, ColSeq.perm]
  | bs, Color.zero :: et => rfl
  | bs, Color.one :: et => by
      exact matchCount_flip_perm132
        (st := fun w => st (GramSymbol.skip :: w)) bs et
  | bs, Color.two :: et => by
      cases bs with
      | empty =>
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push0 Chromogram.BitStack.empty) et
      | push0 bs' =>
          have hpush :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push0 (Chromogram.BitStack.push0 bs')) et
          have hpop :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.pop0 :: w)) bs' et
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using congrArg₂ Nat.add hpush hpop
      | push1 bs' =>
          have hpush :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push0 (Chromogram.BitStack.push1 bs')) et
          have hpop :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.pop1 :: w)) bs' et
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using congrArg₂ Nat.add hpush hpop
  | bs, Color.three :: et => by
      cases bs with
      | empty =>
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push1 Chromogram.BitStack.empty) et
      | push0 bs' =>
          have hpush :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push1 (Chromogram.BitStack.push0 bs')) et
          have hpop :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.pop1 :: w)) bs' et
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using congrArg₂ Nat.add hpush hpop
      | push1 bs' =>
          have hpush :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push1 (Chromogram.BitStack.push1 bs')) et
          have hpop :=
            matchCount_flip_perm132
              (st := fun w => st (GramSymbol.pop0 :: w)) bs' et
          simpa [matchCount, ColSeq.perm, EdgePerm.apply,
            Chromogram.BitStack.flip] using congrArg₂ Nat.add hpush hpop

theorem matchCount_empty_perm132
    (st : SpecGTree) (et : ColSeq) :
    matchCount st Chromogram.BitStack.empty
        (ColSeq.perm EdgePerm.p132 et) =
      matchCount st Chromogram.BitStack.empty et := by
  simpa using matchCount_flip_perm132
    (st := st) Chromogram.BitStack.empty et

theorem matchCount_empty_etrace
    (st : SpecGTree) (et : ColSeq) :
    matchCount st Chromogram.BitStack.empty (ColSeq.etrace et) =
      matchCount st Chromogram.BitStack.empty et := by
  by_cases heven : ColSeq.evenTrace et = true
  · rw [ColSeq.etrace_of_even heven]
  · have hfalse : ColSeq.evenTrace et = false := by
      cases h : ColSeq.evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    rw [ColSeq.etrace_of_not_even hfalse]
    exact matchCount_empty_perm132 st et

theorem sub_empty_etrace (t : GTree) (et : ColSeq) :
    sub t Chromogram.BitStack.empty (ColSeq.etrace et) =
      sub t Chromogram.BitStack.empty et :=
  matchCount_empty_etrace (mem t) et

@[simp]
theorem sub_nil (t : GTree) (bs : Chromogram.BitStack) :
    sub t bs [] = 0 := by
  cases t <;> rfl

@[simp]
theorem matchCount_false
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun _ => false) bs et = 0 := by
  exact matchCount_eq_zero_of_false (st := fun _ => false)
    (by intro w; rfl) bs et

theorem matchCount_congr
    {st st' : SpecGTree}
    (hst : ∀ w, st w = st' w) :
    ∀ (bs : Chromogram.BitStack) (et : ColSeq),
      matchCount st bs et = matchCount st' bs et
  | bs, [] => by
      simp [matchCount, hst]
  | bs, Color.zero :: et => rfl
  | bs, Color.one :: et => by
      exact matchCount_congr
        (st := fun w => st (GramSymbol.skip :: w))
        (st' := fun w => st' (GramSymbol.skip :: w))
        (fun w => hst (GramSymbol.skip :: w)) bs et
  | bs, Color.two :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_congr
            (st := fun w => st (GramSymbol.push :: w))
            (st' := fun w => st' (GramSymbol.push :: w))
            (fun w => hst (GramSymbol.push :: w)),
          matchCount_congr
            (st := fun w => st (GramSymbol.pop0 :: w))
            (st' := fun w => st' (GramSymbol.pop0 :: w))
            (fun w => hst (GramSymbol.pop0 :: w)),
          matchCount_congr
            (st := fun w => st (GramSymbol.pop1 :: w))
            (st' := fun w => st' (GramSymbol.pop1 :: w))
            (fun w => hst (GramSymbol.pop1 :: w))]
  | bs, Color.three :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_congr
            (st := fun w => st (GramSymbol.push :: w))
            (st' := fun w => st' (GramSymbol.push :: w))
            (fun w => hst (GramSymbol.push :: w)),
          matchCount_congr
            (st := fun w => st (GramSymbol.pop0 :: w))
            (st' := fun w => st' (GramSymbol.pop0 :: w))
            (fun w => hst (GramSymbol.pop0 :: w)),
          matchCount_congr
            (st := fun w => st (GramSymbol.pop1 :: w))
            (st' := fun w => st' (GramSymbol.pop1 :: w))
            (fun w => hst (GramSymbol.pop1 :: w))]

theorem matchCount_partition
    {st sl sr : SpecGTree}
    (hpart : ∀ w, st w = (sl w || sr w))
    (hdisj : ∀ w, sl w = true → sr w = false) :
    ∀ (bs : Chromogram.BitStack) (et : ColSeq),
      matchCount st bs et =
        matchCount sl bs et + matchCount sr bs et
  | bs, [] => by
      have hp := hpart []
      cases hl : sl [] <;> cases hr : sr []
      · simpa [matchCount, hl, hr] using hp
      · simpa [matchCount, hl, hr] using hp
      · simpa [matchCount, hl, hr] using hp
      · have hfalse := hdisj [] hl
        simp [hr] at hfalse
  | bs, Color.zero :: et => rfl
  | bs, Color.one :: et => by
      exact matchCount_partition
        (st := fun w => st (GramSymbol.skip :: w))
        (sl := fun w => sl (GramSymbol.skip :: w))
        (sr := fun w => sr (GramSymbol.skip :: w))
        (fun w => hpart (GramSymbol.skip :: w))
        (fun w => hdisj (GramSymbol.skip :: w)) bs et
  | bs, Color.two :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_partition
            (st := fun w => st (GramSymbol.push :: w))
            (sl := fun w => sl (GramSymbol.push :: w))
            (sr := fun w => sr (GramSymbol.push :: w))
            (fun w => hpart (GramSymbol.push :: w))
            (fun w => hdisj (GramSymbol.push :: w)),
          matchCount_partition
            (st := fun w => st (GramSymbol.pop0 :: w))
            (sl := fun w => sl (GramSymbol.pop0 :: w))
            (sr := fun w => sr (GramSymbol.pop0 :: w))
            (fun w => hpart (GramSymbol.pop0 :: w))
            (fun w => hdisj (GramSymbol.pop0 :: w)),
          matchCount_partition
            (st := fun w => st (GramSymbol.pop1 :: w))
            (sl := fun w => sl (GramSymbol.pop1 :: w))
            (sr := fun w => sr (GramSymbol.pop1 :: w))
            (fun w => hpart (GramSymbol.pop1 :: w))
            (fun w => hdisj (GramSymbol.pop1 :: w)),
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | bs, Color.three :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_partition
            (st := fun w => st (GramSymbol.push :: w))
            (sl := fun w => sl (GramSymbol.push :: w))
            (sr := fun w => sr (GramSymbol.push :: w))
            (fun w => hpart (GramSymbol.push :: w))
            (fun w => hdisj (GramSymbol.push :: w)),
          matchCount_partition
            (st := fun w => st (GramSymbol.pop0 :: w))
            (sl := fun w => sl (GramSymbol.pop0 :: w))
            (sr := fun w => sr (GramSymbol.pop0 :: w))
            (fun w => hpart (GramSymbol.pop0 :: w))
            (fun w => hdisj (GramSymbol.pop0 :: w)),
          matchCount_partition
            (st := fun w => st (GramSymbol.pop1 :: w))
            (sl := fun w => sl (GramSymbol.pop1 :: w))
            (sr := fun w => sr (GramSymbol.pop1 :: w))
            (fun w => hpart (GramSymbol.pop1 :: w))
            (fun w => hdisj (GramSymbol.pop1 :: w)),
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end GTree

end FourColor

end Schematic.Math.GraphTheory
