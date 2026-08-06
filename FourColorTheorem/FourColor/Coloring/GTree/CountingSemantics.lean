import FourColorTheorem.FourColor.Coloring.GTree.Definitions

/-! Membership and match-count semantics for chromogram trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

theorem isEmpty_eq {t : GTree} :
    isEmpty t = true → t = empty := by
  cases t <;> simp [isEmpty]

@[simp]
theorem mem_empty (w : Chromogram) :
    mem empty w = false := by
  cases w <;> rfl

@[simp]
theorem select_empty (s : GramSymbol) :
    select empty s = empty := by
  cases s <;> rfl

theorem mem_node_select
    (tPush tSkip tPop0 tPop1 : GTree) (s : GramSymbol) (w : Chromogram) :
    mem (node tPush tSkip tPop0 tPop1) (s :: w) =
      mem (select (node tPush tSkip tPop0 tPop1) s) w := by
  cases s <;> rfl

@[simp]
theorem matchCount_node_push
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount
        (fun w => mem (node tPush tSkip tPop0 tPop1)
          (GramSymbol.push :: w)) bs et =
      sub tPush bs et := rfl

@[simp]
theorem matchCount_node_skip
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount
        (fun w => mem (node tPush tSkip tPop0 tPop1)
          (GramSymbol.skip :: w)) bs et =
      sub tSkip bs et := rfl

@[simp]
theorem matchCount_node_pop0
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount
        (fun w => mem (node tPush tSkip tPop0 tPop1)
          (GramSymbol.pop0 :: w)) bs et =
      sub tPop0 bs et := rfl

@[simp]
theorem matchCount_node_pop1
    (tPush tSkip tPop0 tPop1 : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount
        (fun w => mem (node tPush tSkip tPop0 tPop1)
          (GramSymbol.pop1 :: w)) bs et =
      sub tPop1 bs et := rfl

theorem matchCount_eq_zero_of_false
    {st : SpecGTree}
    (h : ∀ w, st w = false) :
    ∀ (bs : Chromogram.BitStack) (et : ColSeq),
      matchCount st bs et = 0
  | bs, [] => by
      simp [matchCount, h]
  | bs, Color.zero :: et => rfl
  | bs, Color.one :: et => by
      exact matchCount_eq_zero_of_false
        (st := fun w => st (GramSymbol.skip :: w))
        (fun w => h (GramSymbol.skip :: w)) bs et
  | bs, Color.two :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.push :: w))
            (fun w => h (GramSymbol.push :: w)),
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.pop0 :: w))
            (fun w => h (GramSymbol.pop0 :: w)),
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.pop1 :: w))
            (fun w => h (GramSymbol.pop1 :: w))]
  | bs, Color.three :: et => by
      cases bs <;>
        simp [matchCount,
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.push :: w))
            (fun w => h (GramSymbol.push :: w)),
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.pop0 :: w))
            (fun w => h (GramSymbol.pop0 :: w)),
          matchCount_eq_zero_of_false
            (st := fun w => st (GramSymbol.pop1 :: w))
            (fun w => h (GramSymbol.pop1 :: w))]

theorem sub_empty (bs : Chromogram.BitStack) (et : ColSeq) :
    sub empty bs et = 0 := by
  exact matchCount_eq_zero_of_false (st := mem empty) (by simp) bs et

theorem matchCount_eq_zero_of_no_match
    {st : SpecGTree} :
    ∀ {bs : Chromogram.BitStack} {et : ColSeq},
      (∀ w : Chromogram, matchOpen bs et w = true → st w = false) →
        matchCount st bs et = 0
  | bs, [], h => by
      have hnil := h [] rfl
      simp [matchCount, hnil]
  | bs, Color.zero :: et, _ => rfl
  | bs, Color.one :: et, h => by
      exact matchCount_eq_zero_of_no_match
        (st := fun w => st (GramSymbol.skip :: w))
        (bs := bs) (et := et)
        (by
          intro w hmatch
          exact h (GramSymbol.skip :: w) (by simpa [matchOpen] using hmatch))
  | bs, Color.two :: et, h => by
      cases bs with
      | empty =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push0 Chromogram.BitStack.empty)
                    et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush]
      | push0 bs' =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push0
                    (Chromogram.BitStack.push0 bs')) et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          have hpop0 :
              ∀ w : Chromogram,
                matchOpen bs' et w = true →
                  st (GramSymbol.pop0 :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.pop0 :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.pop0 :: w)) hpop0]
      | push1 bs' =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push0
                    (Chromogram.BitStack.push1 bs')) et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          have hpop1 :
              ∀ w : Chromogram,
                matchOpen bs' et w = true →
                  st (GramSymbol.pop1 :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.pop1 :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.pop1 :: w)) hpop1]
  | bs, Color.three :: et, h => by
      cases bs with
      | empty =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push1 Chromogram.BitStack.empty)
                    et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush]
      | push0 bs' =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push1
                    (Chromogram.BitStack.push0 bs')) et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          have hpop1 :
              ∀ w : Chromogram,
                matchOpen bs' et w = true →
                  st (GramSymbol.pop1 :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.pop1 :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.pop1 :: w)) hpop1]
      | push1 bs' =>
          have hpush :
              ∀ w : Chromogram,
                matchOpen (Chromogram.BitStack.push1
                    (Chromogram.BitStack.push1 bs')) et w = true →
                  st (GramSymbol.push :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.push :: w)
              (by simpa [matchOpen] using hmatch)
          have hpop0 :
              ∀ w : Chromogram,
                matchOpen bs' et w = true →
                  st (GramSymbol.pop0 :: w) = false := by
            intro w hmatch
            exact h (GramSymbol.pop0 :: w)
              (by simpa [matchOpen] using hmatch)
          simp [matchCount,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.push :: w)) hpush,
            matchCount_eq_zero_of_no_match (st := fun w =>
              st (GramSymbol.pop0 :: w)) hpop0]

theorem exists_match_of_matchCount_ne_zero
    {st : SpecGTree} :
    ∀ {bs : Chromogram.BitStack} {et : ColSeq},
      matchCount st bs et ≠ 0 →
        ∃ w : Chromogram, st w = true ∧ matchOpen bs et w = true
  | bs, [], hpos => by
      cases hst : st []
      · simp [matchCount, hst] at hpos
      · exact ⟨[], hst, rfl⟩
  | bs, Color.zero :: et, hpos => by
      exact False.elim (hpos rfl)
  | bs, Color.one :: et, hpos => by
      rcases exists_match_of_matchCount_ne_zero
          (st := fun w => st (GramSymbol.skip :: w))
          (bs := bs) (et := et) hpos with
        ⟨w, hst, hmatch⟩
      exact ⟨GramSymbol.skip :: w, hst, by simpa [matchOpen] using hmatch⟩
  | bs, Color.two :: et, hpos => by
      cases bs with
      | empty =>
          rcases exists_match_of_matchCount_ne_zero
              (st := fun w => st (GramSymbol.push :: w))
              (bs := Chromogram.BitStack.push0 Chromogram.BitStack.empty)
              (et := et) (by simpa [matchCount] using hpos) with
            ⟨w, hst, hmatch⟩
          exact ⟨GramSymbol.push :: w, hst,
            by simpa [matchOpen] using hmatch⟩
      | push0 bs' =>
          let a :=
            matchCount (fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push0 (Chromogram.BitStack.push0 bs')) et
          let b :=
            matchCount (fun w => st (GramSymbol.pop0 :: w)) bs' et
          have hsum : a + b ≠ 0 := by
            simpa [a, b, matchCount] using hpos
          by_cases ha : a = 0
          · have hb : b ≠ 0 := by
              intro hb
              exact hsum (by simp [ha, hb])
            rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.pop0 :: w))
                (bs := bs') (et := et) hb with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.pop0 :: w, hst,
              by simpa [matchOpen] using hmatch⟩
          · rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.push :: w))
                (bs := Chromogram.BitStack.push0
                  (Chromogram.BitStack.push0 bs')) (et := et) ha with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.push :: w, hst,
              by simpa [matchOpen] using hmatch⟩
      | push1 bs' =>
          let a :=
            matchCount (fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push0 (Chromogram.BitStack.push1 bs')) et
          let b :=
            matchCount (fun w => st (GramSymbol.pop1 :: w)) bs' et
          have hsum : a + b ≠ 0 := by
            simpa [a, b, matchCount] using hpos
          by_cases ha : a = 0
          · have hb : b ≠ 0 := by
              intro hb
              exact hsum (by simp [ha, hb])
            rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.pop1 :: w))
                (bs := bs') (et := et) hb with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.pop1 :: w, hst,
              by simpa [matchOpen] using hmatch⟩
          · rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.push :: w))
                (bs := Chromogram.BitStack.push0
                  (Chromogram.BitStack.push1 bs')) (et := et) ha with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.push :: w, hst,
              by simpa [matchOpen] using hmatch⟩
  | bs, Color.three :: et, hpos => by
      cases bs with
      | empty =>
          rcases exists_match_of_matchCount_ne_zero
              (st := fun w => st (GramSymbol.push :: w))
              (bs := Chromogram.BitStack.push1 Chromogram.BitStack.empty)
              (et := et) (by simpa [matchCount] using hpos) with
            ⟨w, hst, hmatch⟩
          exact ⟨GramSymbol.push :: w, hst,
            by simpa [matchOpen] using hmatch⟩
      | push0 bs' =>
          let a :=
            matchCount (fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push1 (Chromogram.BitStack.push0 bs')) et
          let b :=
            matchCount (fun w => st (GramSymbol.pop1 :: w)) bs' et
          have hsum : a + b ≠ 0 := by
            simpa [a, b, matchCount] using hpos
          by_cases ha : a = 0
          · have hb : b ≠ 0 := by
              intro hb
              exact hsum (by simp [ha, hb])
            rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.pop1 :: w))
                (bs := bs') (et := et) hb with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.pop1 :: w, hst,
              by simpa [matchOpen] using hmatch⟩
          · rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.push :: w))
                (bs := Chromogram.BitStack.push1
                  (Chromogram.BitStack.push0 bs')) (et := et) ha with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.push :: w, hst,
              by simpa [matchOpen] using hmatch⟩
      | push1 bs' =>
          let a :=
            matchCount (fun w => st (GramSymbol.push :: w))
              (Chromogram.BitStack.push1 (Chromogram.BitStack.push1 bs')) et
          let b :=
            matchCount (fun w => st (GramSymbol.pop0 :: w)) bs' et
          have hsum : a + b ≠ 0 := by
            simpa [a, b, matchCount] using hpos
          by_cases ha : a = 0
          · have hb : b ≠ 0 := by
              intro hb
              exact hsum (by simp [ha, hb])
            rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.pop0 :: w))
                (bs := bs') (et := et) hb with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.pop0 :: w, hst,
              by simpa [matchOpen] using hmatch⟩
          · rcases exists_match_of_matchCount_ne_zero
                (st := fun w => st (GramSymbol.push :: w))
                (bs := Chromogram.BitStack.push1
                  (Chromogram.BitStack.push1 bs')) (et := et) ha with
              ⟨w, hst, hmatch⟩
            exact ⟨GramSymbol.push :: w, hst,
              by simpa [matchOpen] using hmatch⟩

theorem exists_mem_match_of_sub_ne_zero
    {t : GTree} {bs : Chromogram.BitStack} {et : ColSeq}
    (hpos : sub t bs et ≠ 0) :
    ∃ w : Chromogram, mem t w = true ∧ matchOpen bs et w = true :=
  exists_match_of_matchCount_ne_zero (st := mem t) hpos

theorem matchCount_ne_zero_of_match
    {st : SpecGTree} :
    ∀ {bs : Chromogram.BitStack} {et : ColSeq} {w : Chromogram},
      st w = true → matchOpen bs et w = true →
        matchCount st bs et ≠ 0
  | bs, [], w, hst, hmatch => by
      cases w with
      | nil =>
          simp [matchCount, hst]
      | cons s w =>
          simp [matchOpen] at hmatch
  | bs, Color.zero :: et, w, _hst, hmatch => by
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases s <;> cases bs <;> simp [matchOpen] at hmatch
  | bs, Color.one :: et, w, hst, hmatch => by
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases s <;> cases bs <;> simp [matchOpen] at hmatch ⊢
          all_goals
            exact matchCount_ne_zero_of_match
              (st := fun w => st (GramSymbol.skip :: w)) hst hmatch
  | bs, Color.two :: et, w, hst, hmatch => by
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases bs with
          | empty =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 => simp [matchOpen] at hmatch
              | pop1 => simp [matchOpen] at hmatch
          | push0 bs' =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.pop0 :: w)) hst hmatch
                  omega
              | pop1 => simp [matchOpen] at hmatch
          | push1 bs' =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 => simp [matchOpen] at hmatch
              | pop1 =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.pop1 :: w)) hst hmatch
                  omega
  | bs, Color.three :: et, w, hst, hmatch => by
      cases w with
      | nil =>
          simp [matchOpen] at hmatch
      | cons s w =>
          cases bs with
          | empty =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 => simp [matchOpen] at hmatch
              | pop1 => simp [matchOpen] at hmatch
          | push0 bs' =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 => simp [matchOpen] at hmatch
              | pop1 =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.pop1 :: w)) hst hmatch
                  omega
          | push1 bs' =>
              cases s with
              | push =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.push :: w)) hst hmatch
                  omega
              | skip => simp [matchOpen] at hmatch
              | pop0 =>
                  simp [matchOpen, matchCount] at hmatch ⊢
                  have hpos := matchCount_ne_zero_of_match
                    (st := fun w => st (GramSymbol.pop0 :: w)) hst hmatch
                  omega
              | pop1 => simp [matchOpen] at hmatch

theorem sub_ne_zero_of_mem_match
    {t : GTree} {bs : Chromogram.BitStack} {et : ColSeq}
    {w : Chromogram}
    (hmem : mem t w = true) (hmatch : matchOpen bs et w = true) :
    sub t bs et ≠ 0 :=
  matchCount_ne_zero_of_match (st := mem t) hmem hmatch

theorem mem_eq_false_of_sub_eq_zero_of_match
    {t : GTree} {bs : Chromogram.BitStack} {et : ColSeq}
    {w : Chromogram}
    (hzero : sub t bs et = 0)
    (hmatch : matchOpen bs et w = true) :
    mem t w = false := by
  cases hmem : mem t w
  · rfl
  · have hpos := sub_ne_zero_of_mem_match hmem hmatch
    contradiction

end GTree

end FourColor

end Schematic.Math.GraphTheory
