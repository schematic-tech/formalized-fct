import FourColorTheorem.FourColor.Coloring.InitGTree.Completion

/-! Dynamic-programming tables for initial chromogram trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

@[simp]
theorem initH1_length :
    initH1.length = 3 := rfl

@[simp]
theorem initTree_zero :
    initTree 0 = empty := rfl

@[simp]
theorem initTable_zero (d : Nat) :
    initTable d 0 = initH1 := rfl

theorem mergeLine_ne_nil
    (pt0 pt1 pt2 : Pair) (tab : Table) (d : Nat) :
    mergeLine pt0 pt1 pt2 tab d ≠ [] := by
  cases d <;> cases tab <;> simp [mergeLine]

@[simp]
theorem mergeLine_zero
    (pt0 pt1 pt2 : Pair) (tab : Table) :
    mergeLine pt0 pt1 pt2 tab 0 = [mergePairs pt0 pt1 pt2] := by
  cases tab <;> rfl

theorem mergeLine_length_pos
    (pt0 pt1 pt2 : Pair) (tab : Table) (d : Nat) :
    0 < (mergeLine pt0 pt1 pt2 tab d).length := by
  cases d <;> cases tab <;> simp [mergeLine]

theorem mergeLine_length_succ_gt_one
    (pt0 pt1 pt2 : Pair) (tab : Table) (d : Nat) :
    1 < (mergeLine pt0 pt1 pt2 tab (d + 1)).length := by
  cases tab with
  | nil =>
      simp [mergeLine]
  | cons pt tab =>
      simp [mergeLine, mergeLine_length_pos]

theorem initTable_ne_nil :
    ∀ d h : Nat, initTable d h ≠ []
  | d, 0 => by
      simp [initTable, initH1]
  | d, h + 1 => by
      simp [initTable]
      cases ht : initTable (d + 1) h with
      | nil =>
          exact False.elim (initTable_ne_nil (d + 1) h ht)
      | cons pt1 rest =>
          cases rest with
          | nil =>
              simp
          | cons pt0 lpt =>
              exact mergeLine_ne_nil pt0 pt1 emptyPair lpt d

theorem initTree_succ_eq_head (h : Nat) :
    initTree h.succ = ((initTable 0 h).headD emptyPair).left := by
  simp [initTree]
  cases initTable 0 h <;> rfl

theorem initTable_length_pos (d h : Nat) :
    0 < (initTable d h).length := by
  cases ht : initTable d h with
  | nil =>
      exact False.elim (initTable_ne_nil d h ht)
  | cons pt rest =>
      simp

theorem initTable_length_gt_bne_zero :
    ∀ d h : Nat, (if d = 0 then 0 else 1) < (initTable d h).length
  | d, 0 => by
      cases d <;> simp [initTable, initH1]
  | d, h + 1 => by
      have hnext := initTable_length_gt_bne_zero (d + 1) h
      simp [initTable]
      cases ht : initTable (d + 1) h with
      | nil =>
          simp [ht] at hnext
      | cons pt1 rest =>
          cases rest with
          | nil =>
              simp [ht] at hnext
          | cons pt0 lpt =>
              cases d with
              | zero =>
                  exact mergeLine_length_pos pt0 pt1 emptyPair lpt 0
              | succ d =>
                  exact mergeLine_length_succ_gt_one pt0 pt1 emptyPair lpt d

theorem initTable_succ_has_two (d h : Nat) :
    ∃ pt1 pt0 lpt, initTable (d + 1) h = pt1 :: pt0 :: lpt := by
  have hlen := initTable_length_gt_bne_zero (d + 1) h
  simp at hlen
  cases ht : initTable (d + 1) h with
  | nil =>
      simp [ht] at hlen
  | cons pt1 rest =>
      cases rest with
      | nil =>
          simp [ht] at hlen
      | cons pt0 lpt =>
          refine ⟨pt1, pt0, lpt, ?_⟩
          rfl

@[simp]
theorem tableSub_nil (i : Nat) (b : Bool) :
    tableSub [] i b = empty := by
  cases b <;> cases i <;> rfl

@[simp]
theorem tableSub_zero (pt : Pair) (tab : Table) (b : Bool) :
    tableSub (pt :: tab) 0 b = pairSub pt b := rfl

@[simp]
theorem tableSub_succ (pt : Pair) (tab : Table) (i : Nat) (b : Bool) :
    tableSub (pt :: tab) (i + 1) b = tableSub tab i b := rfl

theorem mem_tableSub_mergeLine_eq_contextNode
    (pt0 pt1 pt2 : Pair) (lpt : Table) :
    ∀ (d dw : Nat), dw ≤ d → ∀ (b : Bool) (w : Chromogram),
      mem (tableSub (mergeLine pt0 pt1 pt2 lpt d) dw b) w =
        mem
          (node
            (tableSub (pt2 :: pt1 :: pt0 :: lpt) (dw + 2) b)
            (tableSub (pt2 :: pt1 :: pt0 :: lpt) (dw + 1) (!b))
            (tableSub (pt2 :: pt1 :: pt0 :: lpt) dw b)
            (tableSub (pt2 :: pt1 :: pt0 :: lpt) dw (!b))) w := by
  intro d dw hdw b w
  induction dw generalizing d pt0 pt1 pt2 lpt b w with
  | zero =>
      cases b <;> cases w <;> cases d <;> cases lpt <;> rfl
  | succ dw ih =>
      cases d with
      | zero =>
          omega
      | succ d =>
          cases lpt with
          | nil =>
              cases dw with
              | zero =>
                  cases b <;> rfl
              | succ dw =>
                  cases dw with
                  | zero =>
                      cases b <;> rfl
                  | succ dw =>
                      cases b <;> cases w with
                      | nil => simp [tableSub, mergeLine, emptyPair, pairSub, mem]
                      | cons s w =>
                          cases s <;>
                            simp [tableSub, mergeLine, emptyPair, pairSub, mem, select]
          | cons pt lpt =>
              have hdw' : dw ≤ d := Nat.succ_le_succ_iff.mp hdw
              simpa [mergeLine, Nat.add_assoc] using
                ih pt pt0 pt1 lpt d hdw' b w

theorem mem_tableSub_initTable_succ_eq_contextNode
    (d h dw : Nat) (hdw : dw ≤ d) (b : Bool) (w : Chromogram) :
    mem (tableSub (initTable d (h + 1)) dw b) w =
      mem
        (node
          (tableSub (emptyPair :: initTable (d + 1) h) (dw + 2) b)
          (tableSub (emptyPair :: initTable (d + 1) h) (dw + 1) (!b))
          (tableSub (emptyPair :: initTable (d + 1) h) dw b)
          (tableSub (emptyPair :: initTable (d + 1) h) dw (!b))) w := by
  rcases initTable_succ_has_two d h with ⟨pt1, pt0, lpt, htab⟩
  simp [initTable, htab]
  simpa [htab] using
    mem_tableSub_mergeLine_eq_contextNode pt0 pt1 emptyPair lpt d dw hdw b w

theorem initTree_succ_eq_tableSub (h : Nat) :
    initTree h.succ = tableSub (initTable 0 h) 0 false := by
  rw [initTree_succ_eq_head]
  cases initTable 0 h <;> rfl

theorem tableMemSpec_push (h i : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) i b (GramSymbol.push :: w) =
      tableMemSpec h (i + 1) b w := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_push (h + 1) i b w

theorem tableMemSpec_skip (h i : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) i b (GramSymbol.skip :: w) =
      tableMemSpec h i (!b) w := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_skip (h + 1) i b w

theorem tableMemSpec_pop0_succ (h i : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) (i + 1) b (GramSymbol.pop0 :: w) =
      tableMemSpec h i b w := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_pop0_succ (h + 1) i b w

theorem tableMemSpec_pop1_succ (h i : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) (i + 1) b (GramSymbol.pop1 :: w) =
      tableMemSpec h i (!b) w := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_pop1_succ (h + 1) i b w

theorem tableMemSpec_pop0_zero (h : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) 0 b (GramSymbol.pop0 :: w) = false := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_pop0_zero (h + 1) b w

theorem tableMemSpec_pop1_zero (h : Nat) (b : Bool) (w : Chromogram) :
    tableMemSpec (h + 1) 0 b (GramSymbol.pop1 :: w) = false := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    contextMemSpec_pop1_zero (h + 1) b w

@[simp]
theorem matchCount_tableMemSpec_zero
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec h i b) bs (Color.zero :: et) = 0 := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_zero (h + 1) i b bs et

theorem matchCount_tableMemSpec_succ_one
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec (h + 1) i b) bs (Color.one :: et) =
      matchCount (tableMemSpec h i (!b)) bs et := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_succ_one (h + 1) i b bs et

theorem matchCount_tableMemSpec_zero_depth_two
    (h : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec (h + 1) 0 b) bs (Color.two :: et) =
      matchCount (tableMemSpec h 1 b) (Chromogram.BitStack.push0 bs) et := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_zero_depth_two (h + 1) b bs et

theorem matchCount_tableMemSpec_zero_depth_three
    (h : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec (h + 1) 0 b) bs (Color.three :: et) =
      matchCount (tableMemSpec h 1 b) (Chromogram.BitStack.push1 bs) et := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_zero_depth_three (h + 1) b bs et

theorem matchCount_tableMemSpec_succ_depth_two
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec (h + 1) (i + 1) b) bs (Color.two :: et) =
      matchCount (tableMemSpec h (i + 2) b)
          (Chromogram.BitStack.push0 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (tableMemSpec h i b) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (tableMemSpec h i (!b)) bs' et := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_succ_depth_two (h + 1) i b bs et

theorem matchCount_tableMemSpec_succ_depth_three
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (tableMemSpec (h + 1) (i + 1) b) bs (Color.three :: et) =
      matchCount (tableMemSpec h (i + 2) b)
          (Chromogram.BitStack.push1 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (tableMemSpec h i (!b)) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (tableMemSpec h i b) bs' et := by
  simpa only [tableMemSpec_eq_contextMemSpec] using
    matchCount_contextMemSpec_succ_depth_three (h + 1) i b bs et

theorem tableMemSpec_append_eq_false_of_length_gt
    {h i : Nat} {b : Bool} {pref : Chromogram}
    (hpref : h + 1 < pref.length) (w : Chromogram) :
    tableMemSpec h i b (pref ++ w) = false := by
  simp [tableMemSpec]
  omega

theorem matchCount_tableMemSpec_pref_too_long
    (h i : Nat) (b : Bool) (pref : Chromogram)
    (hpref : h + 1 < pref.length)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (fun w => tableMemSpec h i b (pref ++ w)) bs et = 0 :=
  matchCount_eq_zero_of_false
    (st := fun w => tableMemSpec h i b (pref ++ w))
    (tableMemSpec_append_eq_false_of_length_gt hpref) bs et

theorem mem_initH1_tableSub (i : Nat) (b : Bool) (w : Chromogram) :
    mem (tableSub initH1 i b) w = tableMemSpec 0 i b w := by
  cases i with
  | zero =>
      cases b <;>
        cases w with
        | nil => rfl
        | cons s w =>
            cases w with
            | nil => cases s <;> rfl
            | cons s' w => cases s <;> rfl
  | succ i =>
      cases i with
      | zero =>
          cases b <;>
            cases w with
            | nil => rfl
            | cons s w =>
                cases w with
                | nil => cases s <;> rfl
                | cons s' w => cases s <;> rfl
      | succ i =>
          cases i with
          | zero =>
              cases b <;>
                cases w with
                | nil => rfl
                | cons s w =>
                    cases w with
                    | nil => cases s <;> rfl
                    | cons s' w => cases s <;> rfl
          | succ i =>
              cases b <;>
                cases w with
                | nil => rfl
                | cons s w =>
                    cases w with
                    | nil =>
                        cases s <;>
                          simp [tableSub, initH1, tableMemSpec,
                            Chromogram.complete, Chromogram.balanced,
                            emptyPair, pairSub]
                    | cons s' w =>
                        cases s <;> rfl

theorem mem_initTable_tableSub :
    ∀ (h d i : Nat) (b : Bool) (w : Chromogram), i ≤ d →
      mem (tableSub (initTable d h) i b) w = tableMemSpec h i b w
  | 0, d, i, b, w, _ => by
      simpa [initTable] using mem_initH1_tableSub i b w
  | h + 1, d, i, b, w, hi => by
      rw [mem_tableSub_initTable_succ_eq_contextNode d h i hi b w]
      cases w with
      | nil =>
          simp [mem, tableMemSpec]
      | cons s w =>
          cases s with
          | push =>
              have hi' : i + 1 ≤ d + 1 := Nat.succ_le_succ hi
              have hrec := mem_initTable_tableSub h (d + 1) (i + 1) b w hi'
              rw [tableMemSpec_push]
              simpa [mem, select, tableSub, Nat.add_assoc] using hrec
          | skip =>
              have hi' : i ≤ d + 1 := Nat.le_trans hi (Nat.le_succ d)
              have hrec := mem_initTable_tableSub h (d + 1) i (!b) w hi'
              rw [tableMemSpec_skip]
              simpa [mem, select, tableSub] using hrec
          | pop0 =>
              cases i with
              | zero =>
                  rw [tableMemSpec_pop0_zero]
                  simp [mem, select, tableSub, emptyPair, pairSub]
              | succ i =>
                  have hi' : i ≤ d + 1 := by omega
                  have hrec := mem_initTable_tableSub h (d + 1) i b w hi'
                  rw [tableMemSpec_pop0_succ]
                  simpa [mem, select, tableSub] using hrec
          | pop1 =>
              cases i with
              | zero =>
                  rw [tableMemSpec_pop1_zero]
                  simp [mem, select, tableSub, emptyPair, pairSub]
              | succ i =>
                  have hi' : i ≤ d + 1 := by omega
                  have hrec := mem_initTable_tableSub h (d + 1) i (!b) w hi'
                  rw [tableMemSpec_pop1_succ]
                  simpa [mem, select, tableSub] using hrec

@[simp]
theorem mem_mergePairs_left_push
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).left (GramSymbol.push :: w) =
      mem pt0.left w := rfl

@[simp]
theorem mem_mergePairs_left_skip
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).left (GramSymbol.skip :: w) =
      mem pt1.right w := rfl

@[simp]
theorem mem_mergePairs_left_pop0
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).left (GramSymbol.pop0 :: w) =
      mem pt2.left w := rfl

@[simp]
theorem mem_mergePairs_left_pop1
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).left (GramSymbol.pop1 :: w) =
      mem pt2.right w := rfl

@[simp]
theorem mem_mergePairs_right_push
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).right (GramSymbol.push :: w) =
      mem pt0.right w := rfl

@[simp]
theorem mem_mergePairs_right_skip
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).right (GramSymbol.skip :: w) =
      mem pt1.left w := rfl

@[simp]
theorem mem_mergePairs_right_pop0
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).right (GramSymbol.pop0 :: w) =
      mem pt2.right w := rfl

@[simp]
theorem mem_mergePairs_right_pop1
    (pt0 pt1 pt2 : Pair) (w : Chromogram) :
    mem (mergePairs pt0 pt1 pt2).right (GramSymbol.pop1 :: w) =
      mem pt2.left w := rfl

end GTree

end FourColor

end Schematic.Math.GraphTheory
