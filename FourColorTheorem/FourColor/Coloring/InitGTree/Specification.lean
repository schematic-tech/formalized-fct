import FourColorTheorem.FourColor.Coloring.InitGTree.Tables

/-! Final membership and count specification of initial chromogram trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

theorem initSpec_length_of_true
    {h : Nat} {w : Chromogram}
    (hspec : initSpec h w = true) :
    w.length = h := by
  simp [initSpec] at hspec
  exact hspec.1

theorem initSpec_balanced_of_true
    {h : Nat} {w : Chromogram}
    (hspec : initSpec h w = true) :
    Chromogram.balanced 0 false (Chromogram.complete 0 false w) = true := by
  simp [initSpec] at hspec
  exact hspec.2

theorem initSpec_nil (h : Nat) :
    initSpec h [] = false := by
  cases h <;> rfl

theorem initSpec_add_two_push (h : Nat) (w : Chromogram) :
    initSpec (h + 2) (GramSymbol.push :: w) =
      tableMemSpec h 1 false w := by
  simp [initSpec, tableMemSpec, Chromogram.complete,
    Chromogram.balanced]

theorem initSpec_add_two_skip (h : Nat) (w : Chromogram) :
    initSpec (h + 2) (GramSymbol.skip :: w) =
      tableMemSpec h 0 true w := by
  simp [initSpec, tableMemSpec, Chromogram.complete,
    Chromogram.balanced]

theorem initSpec_succ_pop0 (h : Nat) (w : Chromogram) :
    initSpec (h + 1) (GramSymbol.pop0 :: w) = false := by
  simp [initSpec, Chromogram.complete, Chromogram.balanced]

theorem initSpec_succ_pop1 (h : Nat) (w : Chromogram) :
    initSpec (h + 1) (GramSymbol.pop1 :: w) = false := by
  simp [initSpec, Chromogram.complete, Chromogram.balanced]

theorem initCountSpec_succ_zero (h : Nat) (et : ColSeq) :
    initCountSpec (h + 1) (Color.zero :: et) = 0 := by
  simp [initCountSpec]

theorem initCountSpec_succ_one (h : Nat) (et : ColSeq) :
    initCountSpec (h + 1) (Color.one :: et) =
      if decide (et.length = h) &&
          decide (Color.zero ∉ et ++ [Color.one + ColSeq.sum et]) then
        dyck (ColSeq.countBit1 (et ++ [Color.one + ColSeq.sum et]))
      else
        0 := by
  simp [initCountSpec, ColSeq.ctrace_cons, Color.bit1]

theorem initCountSpec_succ_two (h : Nat) (et : ColSeq) :
    initCountSpec (h + 1) (Color.two :: et) =
      if decide (et.length = h) &&
          decide (Color.zero ∉ et ++ [Color.two + ColSeq.sum et]) then
        dyck (ColSeq.countBit1 (et ++ [Color.two + ColSeq.sum et]) + 1)
      else
        0 := by
  simp [initCountSpec, ColSeq.ctrace_cons, Color.bit1]

theorem initCountSpec_succ_three (h : Nat) (et : ColSeq) :
    initCountSpec (h + 1) (Color.three :: et) =
      if decide (et.length = h) &&
          decide (Color.zero ∉ et ++ [Color.three + ColSeq.sum et]) then
        dyck (ColSeq.countBit1 (et ++ [Color.three + ColSeq.sum et]) + 1)
      else
        0 := by
  simp [initCountSpec, ColSeq.ctrace_cons, Color.bit1]

theorem matchCount_initSpec_add_two_zero (h : Nat) (et : ColSeq) :
    matchCount (initSpec (h + 2)) Chromogram.BitStack.empty
        (Color.zero :: et) = 0 := rfl

theorem matchCount_initSpec_add_two_one (h : Nat) (et : ColSeq) :
    matchCount (initSpec (h + 2)) Chromogram.BitStack.empty
        (Color.one :: et) =
      matchCount (tableMemSpec h 0 true) Chromogram.BitStack.empty et := by
  exact matchCount_congr (fun w => initSpec_add_two_skip h w) _ _

theorem matchCount_initSpec_add_two_two (h : Nat) (et : ColSeq) :
    matchCount (initSpec (h + 2)) Chromogram.BitStack.empty
        (Color.two :: et) =
      matchCount (tableMemSpec h 1 false)
        (Chromogram.BitStack.push0 Chromogram.BitStack.empty) et := by
  simp [matchCount]
  exact matchCount_congr (fun w => initSpec_add_two_push h w) _ _

theorem matchCount_initSpec_add_two_three (h : Nat) (et : ColSeq) :
    matchCount (initSpec (h + 2)) Chromogram.BitStack.empty
        (Color.three :: et) =
      matchCount (tableMemSpec h 1 false)
        (Chromogram.BitStack.push1 Chromogram.BitStack.empty) et := by
  simp [matchCount]
  exact matchCount_congr (fun w => initSpec_add_two_push h w) _ _

@[simp]
theorem initTree_one :
    initTree 1 = leaf01 := rfl

@[simp]
theorem initTree_two :
    initTree 2 = node leaf13 leaf0 empty empty := rfl

theorem initSpec_zero_false (w : Chromogram) :
    initSpec 0 w = false := by
  cases w with
  | nil =>
      rfl
  | cons s w =>
      rfl

theorem matchCount_initSpec_zero
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (initSpec 0) bs et = 0 :=
  matchCount_eq_zero_of_false (st := initSpec 0) initSpec_zero_false bs et

theorem initCountSpec_zero (et : ColSeq) :
    initCountSpec 0 et = 0 := by
  cases et with
  | nil =>
      simp [initCountSpec, ColSeq.ctrace]
  | cons e et =>
      simp [initCountSpec]

theorem matchCount_initSpec_zero_eq_initCountSpec
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (initSpec 0) bs et = initCountSpec 0 et := by
  rw [matchCount_initSpec_zero, initCountSpec_zero]

theorem initSpec_append_eq_false_of_length_gt
    {h : Nat} {pref : Chromogram}
    (hpref : h < pref.length) (w : Chromogram) :
    initSpec h (pref ++ w) = false := by
  simp [initSpec]
  omega

theorem matchCount_initSpec_pref_too_long
    (h : Nat) (pref : Chromogram)
    (hpref : h < pref.length) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => initSpec h (pref ++ w)) bs et = 0 :=
  matchCount_eq_zero_of_false
    (st := fun w => initSpec h (pref ++ w))
    (initSpec_append_eq_false_of_length_gt hpref) bs et

theorem matchCount_initSpec_eq_initCountSpec
    (h : Nat) (et : ColSeq) :
    matchCount (initSpec h) Chromogram.BitStack.empty et =
      initCountSpec h et := by
  change
    matchCount (contextMemSpec h ([] : List Bool).length false)
        (Chromogram.BitStack.ofList ([] : List Bool)) et =
      contextCountSpec h Color.zero [] et
  exact matchCount_contextMemSpec et h Color.zero [] false rfl rfl

theorem matchCount_initSpec_one_pref_two
    (s t : GramSymbol) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => initSpec 1 (s :: t :: w)) bs et = 0 :=
  matchCount_initSpec_pref_too_long 1 [s, t] (by simp) bs et

theorem matchCount_initSpec_one_eq_initCountSpec (et : ColSeq) :
    matchCount (initSpec 1) Chromogram.BitStack.empty et =
      initCountSpec 1 et :=
  matchCount_initSpec_eq_initCountSpec 1 et

theorem matchCount_initSpec_two_pref_three
    (s t u : GramSymbol) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => initSpec 2 (s :: t :: u :: w)) bs et = 0 :=
  matchCount_initSpec_pref_too_long 2 [s, t, u] (by simp) bs et

theorem matchCount_initSpec_two_eq_initCountSpec (et : ColSeq) :
    matchCount (initSpec 2) Chromogram.BitStack.empty et =
      initCountSpec 2 et :=
  matchCount_initSpec_eq_initCountSpec 2 et

theorem matchCount_initSpec_three_pref_four
    (s t u v : GramSymbol) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => initSpec 3 (s :: t :: u :: v :: w)) bs et = 0 :=
  matchCount_initSpec_pref_too_long 3 [s, t, u, v] (by simp) bs et

theorem matchCount_initSpec_three_eq_initCountSpec (et : ColSeq) :
    matchCount (initSpec 3) Chromogram.BitStack.empty et =
      initCountSpec 3 et :=
  matchCount_initSpec_eq_initCountSpec 3 et

theorem matchCount_initSpec_four_pref_five
    (s t u v x : GramSymbol) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => initSpec 4 (s :: t :: u :: v :: x :: w)) bs et = 0 :=
  matchCount_initSpec_pref_too_long 4 [s, t, u, v, x] (by simp) bs et

theorem matchCount_initSpec_four_eq_initCountSpec (et : ColSeq) :
    matchCount (initSpec 4) Chromogram.BitStack.empty et =
      initCountSpec 4 et :=
  matchCount_initSpec_eq_initCountSpec 4 et

theorem mem_initTree_zero (w : Chromogram) :
    mem (initTree 0) w = initSpec 0 w := by
  rw [initTree_zero, initSpec_zero_false]
  simp

theorem mem_initTree (h : Nat) (w : Chromogram) :
    mem (initTree h) w = initSpec h w := by
  cases h with
  | zero =>
      exact mem_initTree_zero w
  | succ h =>
      rw [initTree_succ_eq_tableSub]
      have htab := mem_initTable_tableSub h 0 0 false w (Nat.le_refl 0)
      simpa [initSpec, tableMemSpec, Nat.succ_eq_add_one] using htab

theorem mem_initTree_one (w : Chromogram) :
    mem (initTree 1) w = initSpec 1 w :=
  mem_initTree 1 w

theorem mem_initTree_two (w : Chromogram) :
    mem (initTree 2) w = initSpec 2 w :=
  mem_initTree 2 w

theorem sub_initTree_eq_matchCount_initSpec
    (h : Nat) (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (initTree h) bs et = matchCount (initSpec h) bs et :=
  matchCount_congr (fun w => mem_initTree h w) bs et

theorem sub_initTree_eq_initCountSpec
    (h : Nat) (et : ColSeq) :
    sub (initTree h) Chromogram.BitStack.empty et = initCountSpec h et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_eq_initCountSpec]

theorem sub_initTree_zero_eq_initCountSpec
    (bs : Chromogram.BitStack) (et : ColSeq) :
    sub (initTree 0) bs et = initCountSpec 0 et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_zero_eq_initCountSpec]

theorem sub_initTree_one_eq_initCountSpec (et : ColSeq) :
    sub (initTree 1) Chromogram.BitStack.empty et = initCountSpec 1 et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_one_eq_initCountSpec]

theorem sub_initTree_two_eq_initCountSpec (et : ColSeq) :
    sub (initTree 2) Chromogram.BitStack.empty et = initCountSpec 2 et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_two_eq_initCountSpec]

theorem sub_initTree_three_eq_initCountSpec (et : ColSeq) :
    sub (initTree 3) Chromogram.BitStack.empty et = initCountSpec 3 et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_three_eq_initCountSpec]

theorem sub_initTree_four_eq_initCountSpec (et : ColSeq) :
    sub (initTree 4) Chromogram.BitStack.empty et = initCountSpec 4 et := by
  rw [sub_initTree_eq_matchCount_initSpec,
    matchCount_initSpec_four_eq_initCountSpec]

end GTree

end FourColor

end Schematic.Math.GraphTheory
