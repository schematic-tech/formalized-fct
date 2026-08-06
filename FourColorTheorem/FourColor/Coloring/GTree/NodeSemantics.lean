import FourColorTheorem.FourColor.Coloring.GTree.Symmetry

/-! Node formulas and executable matching semantics for chromogram trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

@[simp]
theorem sub_node_nil
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) :
    sub (node tPush tSkip tPop0 tPop1) bs [] = 0 := rfl

@[simp]
theorem sub_node_zero
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (node tPush tSkip tPop0 tPop1) bs
      (Color.zero :: et) = 0 := rfl

@[simp]
theorem sub_node_one
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (node tPush tSkip tPop0 tPop1) bs
      (Color.one :: et) = sub tSkip bs et := rfl

@[simp]
theorem sub_node_two
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (node tPush tSkip tPop0 tPop1) bs
      (Color.two :: et) =
      sub tPush (Chromogram.BitStack.push0 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' => sub tPop0 bs' et
        | Chromogram.BitStack.push1 bs' => sub tPop1 bs' et := by
  cases bs <;> rfl

@[simp]
theorem sub_node_three
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (node tPush tSkip tPop0 tPop1) bs
      (Color.three :: et) =
      sub tPush (Chromogram.BitStack.push1 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' => sub tPop1 bs' et
        | Chromogram.BitStack.push1 bs' => sub tPop0 bs' et := by
  cases bs <;> rfl

@[simp]
theorem sub_leaf0_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf0 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf1_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf1 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf2_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf2 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf3_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf3 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf01_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf01 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf12_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf12 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf13_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf13 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

@[simp]
theorem sub_leaf23_cons_cons
    (bs : Chromogram.BitStack) (e1 e2 : Color) (et : ColSeq) :
    sub leaf23 bs (e1 :: e2 :: et) = 0 := by
  cases e1 <;> cases e2 <;> cases bs <;> simp [sub, matchCount, mem]
  all_goals (repeat' split <;> rfl)

theorem hasMatch_eq_false_of_false
    {ct : SpecCTree}
    (hct : ∀ et, ct et = false) :
    ∀ (bs : Chromogram.BitStack) (w : Chromogram),
      hasMatch bs ct w = false
  | bs, [] => by
      simp [hasMatch, hct]
  | bs, GramSymbol.push :: w => by
      simp [hasMatch,
        hasMatch_eq_false_of_false
          (ct := fun et => ct (Color.two :: et))
          (fun et => hct (Color.two :: et)),
        hasMatch_eq_false_of_false
          (ct := fun et => ct (Color.three :: et))
          (fun et => hct (Color.three :: et))]
  | bs, GramSymbol.skip :: w => by
      simp [hasMatch,
        hasMatch_eq_false_of_false
          (ct := fun et => ct (Color.one :: et))
          (fun et => hct (Color.one :: et))]
  | Chromogram.BitStack.empty, GramSymbol.pop0 :: w => rfl
  | Chromogram.BitStack.push0 bs, GramSymbol.pop0 :: w => by
      exact hasMatch_eq_false_of_false
        (ct := fun et => ct (Color.two :: et))
        (fun et => hct (Color.two :: et)) bs w
  | Chromogram.BitStack.push1 bs, GramSymbol.pop0 :: w => by
      exact hasMatch_eq_false_of_false
        (ct := fun et => ct (Color.three :: et))
        (fun et => hct (Color.three :: et)) bs w
  | Chromogram.BitStack.empty, GramSymbol.pop1 :: w => rfl
  | Chromogram.BitStack.push0 bs, GramSymbol.pop1 :: w => by
      exact hasMatch_eq_false_of_false
        (ct := fun et => ct (Color.three :: et))
        (fun et => hct (Color.three :: et)) bs w
  | Chromogram.BitStack.push1 bs, GramSymbol.pop1 :: w => by
      exact hasMatch_eq_false_of_false
        (ct := fun et => ct (Color.two :: et))
        (fun et => hct (Color.two :: et)) bs w

@[simp]
theorem hasMatch_false
    (bs : Chromogram.BitStack) (w : Chromogram) :
    hasMatch bs (fun _ => false) w = false := by
  exact hasMatch_eq_false_of_false (ct := fun _ => false) (by intro et; rfl)
    bs w

theorem hasMatch_eq_true_iff :
    ∀ (bs : Chromogram.BitStack) (ct : SpecCTree) (w : Chromogram),
      hasMatch bs ct w = true ↔
        ∃ et : ColSeq, ct et = true ∧ matchOpen bs et w = true
  | bs, ct, [] => by
      constructor
      · intro h
        exact ⟨[], h, rfl⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et <;> simp [matchOpen] at hmatch
        exact hct
  | bs, ct, GramSymbol.push :: w => by
      constructor
      · intro h
        simp [hasMatch] at h
        rcases h with h | h
        · rcases (hasMatch_eq_true_iff
            (Chromogram.BitStack.push0 bs)
            (fun et => ct (Color.two :: et)) w).mp h with
            ⟨et, hct, hmatch⟩
          exact ⟨Color.two :: et, hct, by simpa [matchOpen] using hmatch⟩
        · rcases (hasMatch_eq_true_iff
            (Chromogram.BitStack.push1 bs)
            (fun et => ct (Color.three :: et)) w).mp h with
            ⟨et, hct, hmatch⟩
          exact ⟨Color.three :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff
                  (Chromogram.BitStack.push0 bs)
                  (fun et => ct (Color.two :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simp [hasMatch, hbranch]
            · have hbranch :=
                (hasMatch_eq_true_iff
                  (Chromogram.BitStack.push1 bs)
                  (fun et => ct (Color.three :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simp [hasMatch, hbranch]
  | bs, ct, GramSymbol.skip :: w => by
      constructor
      · intro h
        rcases (hasMatch_eq_true_iff bs
          (fun et => ct (Color.one :: et)) w).mp h with
          ⟨et, hct, hmatch⟩
        exact ⟨Color.one :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff bs
                  (fun et => ct (Color.one :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simpa [hasMatch] using hbranch
  | Chromogram.BitStack.empty, ct, GramSymbol.pop0 :: w => by
      constructor
      · intro h
        simp [hasMatch] at h
      · rintro ⟨et, _, hmatch⟩
        cases et <;> simp [matchOpen] at hmatch
  | Chromogram.BitStack.push0 bs, ct, GramSymbol.pop0 :: w => by
      constructor
      · intro h
        rcases (hasMatch_eq_true_iff bs
          (fun et => ct (Color.two :: et)) w).mp h with
          ⟨et, hct, hmatch⟩
        exact ⟨Color.two :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff bs
                  (fun et => ct (Color.two :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simpa [hasMatch] using hbranch
  | Chromogram.BitStack.push1 bs, ct, GramSymbol.pop0 :: w => by
      constructor
      · intro h
        rcases (hasMatch_eq_true_iff bs
          (fun et => ct (Color.three :: et)) w).mp h with
          ⟨et, hct, hmatch⟩
        exact ⟨Color.three :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff bs
                  (fun et => ct (Color.three :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simpa [hasMatch] using hbranch
  | Chromogram.BitStack.empty, ct, GramSymbol.pop1 :: w => by
      constructor
      · intro h
        simp [hasMatch] at h
      · rintro ⟨et, _, hmatch⟩
        cases et <;> simp [matchOpen] at hmatch
  | Chromogram.BitStack.push0 bs, ct, GramSymbol.pop1 :: w => by
      constructor
      · intro h
        rcases (hasMatch_eq_true_iff bs
          (fun et => ct (Color.three :: et)) w).mp h with
          ⟨et, hct, hmatch⟩
        exact ⟨Color.three :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff bs
                  (fun et => ct (Color.three :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simpa [hasMatch] using hbranch
  | Chromogram.BitStack.push1 bs, ct, GramSymbol.pop1 :: w => by
      constructor
      · intro h
        rcases (hasMatch_eq_true_iff bs
          (fun et => ct (Color.two :: et)) w).mp h with
          ⟨et, hct, hmatch⟩
        exact ⟨Color.two :: et, hct, by simpa [matchOpen] using hmatch⟩
      · rintro ⟨et, hct, hmatch⟩
        cases et with
        | nil =>
            simp [matchOpen] at hmatch
        | cons e et =>
            cases e <;> simp [matchOpen] at hmatch
            · have hbranch :=
                (hasMatch_eq_true_iff bs
                  (fun et => ct (Color.two :: et)) w).mpr
                  ⟨et, hct, hmatch⟩
              simpa [hasMatch] using hbranch

theorem emptyAnd_spec (t : GTree) (b : Bool) :
    emptyAnd t b = (isEmpty t && b) := by
  cases t <;> cases b <;> rfl

theorem empty4_eq_true
    {tPush tSkip tPop0 tPop1 : GTree}
    (h : empty4 (node tPush tSkip tPop0 tPop1) = true) :
    tPush = empty ∧ tSkip = empty ∧ tPop0 = empty ∧ tPop1 = empty := by
  simp [empty4, emptyAnd_spec] at h
  exact ⟨isEmpty_eq h.1, isEmpty_eq h.2.1,
    isEmpty_eq h.2.2.1, isEmpty_eq h.2.2.2⟩

end GTree

end FourColor

end Schematic.Math.GraphTheory
