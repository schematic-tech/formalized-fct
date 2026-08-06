import FourColorTheorem.FourColor.Coloring.GTree
import FourColorTheorem.FourColor.Coloring.Dyck

/-!
Initial chromogram trees.

This ports the executable table construction at the front of Gonthier's
`initgtree.v`.  The main correctness theorem relating `initTree` to
`initSpec` is a later proof layer.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace GTree

/-- Tables used to build full chromogram trees. -/
abbrev Table := List Pair

/-- Height-one initial table. -/
def initH1 : Table :=
  [⟨leaf01, leaf0⟩,
    ⟨leaf13, leaf12⟩,
    ⟨leaf23, leaf23⟩]

/-- Merge three neighbouring table entries into a higher table entry. -/
def mergePairs (pt0 pt1 pt2 : Pair) : Pair where
  left := node pt0.left pt1.right pt2.left pt2.right
  right := node pt0.right pt1.left pt2.right pt2.left

/-- Merge one table line. -/
def mergeLine (pt0 pt1 pt2 : Pair) : Table → Nat → Table
  | _, 0 => [mergePairs pt0 pt1 pt2]
  | [], _ + 1 =>
      [mergePairs pt0 pt1 pt2,
        mergePairs emptyPair pt0 pt1,
        mergePairs emptyPair emptyPair pt0]
  | pt :: lpt, d + 1 =>
      mergePairs pt0 pt1 pt2 :: mergeLine pt pt0 pt1 lpt d

/-- Dynamic-programming table for initial chromogram trees. -/
def initTable (d h : Nat) : Table :=
  match h with
  | 0 => initH1
  | h' + 1 =>
      match initTable (d + 1) h' with
      | pt1 :: pt0 :: lpt => mergeLine pt0 pt1 emptyPair lpt d
      | tab => tab

/-- Full initial chromogram tree for ring size `h`. -/
def initTree : Nat → GTree
  | 0 => empty
  | h + 1 =>
      match initTable 0 h with
      | pt :: _ => pt.left
      | [] => empty

/-- Select a table entry and then one component of the pair. -/
def tableSub (tab : Table) (i : Nat) (b : Bool) : GTree :=
  pairSub (tab.getD i emptyPair) b

/-- Specification for initial chromogram trees: balanced completed
chromograms of length `h`. -/
def initSpec (h : Nat) (w : Chromogram) : Bool :=
  decide (w.length = h) &&
    Chromogram.balanced 0 false (Chromogram.complete 0 false w)

/-- General balanced-completion predicate used by the generalized
`match_count_balanced` induction.  `initSpec` and `tableMemSpec` are the empty
and shifted table instances of this predicate. -/
def contextMemSpec (h i : Nat) (b : Bool) (w : Chromogram) : Bool :=
  decide (w.length = h) &&
    Chromogram.balanced i b (Chromogram.complete i b w)

/-- Target count formula for initial G-trees, matching Coq's
`match_count_balanced`. -/
def initCountSpec (h : Nat) (et : ColSeq) : Nat :=
  if decide (et.length = h) && decide (Color.zero ∉ ColSeq.ctrace et) then
    dyck (ColSeq.countBit1 (ColSeq.ctrace et))
  else
    0

theorem initCountSpec_ne_zero_length
    {h : Nat} {et : ColSeq}
    (hne : initCountSpec h et ≠ 0) :
    et.length = h := by
  by_contra hlen
  exact hne (by simp [initCountSpec, hlen])

theorem initCountSpec_ne_zero_not_mem_zero_ctrace
    {h : Nat} {et : ColSeq}
    (hne : initCountSpec h et ≠ 0) :
    Color.zero ∉ ColSeq.ctrace et := by
  by_contra hzero
  exact hne (by simp [initCountSpec, hzero])

theorem initCountSpec_eq_dyck
    {h : Nat} {et : ColSeq}
    (hlen : et.length = h)
    (hzero : Color.zero ∉ ColSeq.ctrace et) :
    initCountSpec h et =
      dyck (ColSeq.countBit1 (ColSeq.ctrace et)) := by
  simp [initCountSpec, hlen, hzero]

theorem initCountSpec_ne_zero_of_length_not_mem_zero_ctrace
    {h : Nat} {et : ColSeq}
    (hlen : et.length = h)
    (hzero : Color.zero ∉ ColSeq.ctrace et) :
    initCountSpec h et ≠ 0 := by
  rw [initCountSpec_eq_dyck hlen hzero]
  exact Nat.ne_of_gt
    (dyck_pos_of_bodd_false
      (ColSeq.countBit1 (ColSeq.ctrace et))
      (ColSeq.countBit1_ctrace_bodd et))

/-- General count formula used by Coq's proof of `match_count_balanced`.  The
context colour `c` is constrained in the induction by the current stack depth
and parity bits. -/
def contextCountSpec (h : Nat) (c : Color) (lb : List Bool) (et : ColSeq) :
    Nat :=
  let cet := et ++ [c + ColSeq.sum et]
  if decide (et.length = h) && decide (Color.zero ∉ cet) then
    genDyck (lb.length + 1) (ColSeq.countBit1 cet)
  else
    0

/-- Membership specification for an intermediate initial G-tree table entry.
The table entry is indexed by the open-depth/parity context in which the stored
chromograms are to be completed. -/
def tableMemSpec (h i : Nat) (b : Bool) (w : Chromogram) : Bool :=
  decide (w.length = h + 1) &&
    Chromogram.balanced i b (Chromogram.complete i b w)

theorem initSpec_eq_contextMemSpec (h : Nat) :
    initSpec h = contextMemSpec h 0 false := by
  funext w
  rfl

theorem tableMemSpec_eq_contextMemSpec (h i : Nat) (b : Bool) :
    tableMemSpec h i b = contextMemSpec (h + 1) i b := by
  funext w
  rfl

theorem initCountSpec_eq_contextCountSpec (h : Nat) (et : ColSeq) :
    initCountSpec h et = contextCountSpec h Color.zero [] et := by
  rfl

theorem contextCountSpec_nil (h : Nat) (c : Color) (lb : List Bool) :
    contextCountSpec h c lb [] =
      if decide (0 = h) && decide (c ≠ Color.zero) then
        genDyck (lb.length + 1) (if c.bit1 then 1 else 0)
      else
        0 := by
  cases h <;> cases c <;> simp [contextCountSpec, Color.bit1]

theorem matchCount_contextMemSpec_nil
    (h : Nat) (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity lb))
    (hc1 : c.bit1 = Chromogram.oddLength lb) :
    matchCount (contextMemSpec h lb.length b0)
        (Chromogram.BitStack.ofList lb) [] =
      contextCountSpec h c lb [] := by
  cases h with
  | succ h =>
      simp [matchCount, contextMemSpec, contextCountSpec]
  | zero =>
      cases lb with
      | nil =>
          cases c <;> cases b0 <;>
            simp [matchCount, contextMemSpec, contextCountSpec, Chromogram.complete,
              Chromogram.balanced, Chromogram.bitParity, Color.bit0,
              Color.bit1, genDyck] at hc0 hc1 ⊢
      | cons b lb =>
          cases lb with
          | nil =>
              cases b <;> cases c <;> cases b0 <;>
                simp [matchCount, contextMemSpec, contextCountSpec, Chromogram.complete,
                  Chromogram.balanced, Chromogram.bitParity, Color.bit0,
                  Color.bit1, genDyck] at hc0 hc1 ⊢
          | cons b' lb =>
              have hmax0 : genDyck (lb.length + 3) 0 = 0 :=
                genDyck_max (lb.length + 3) 0 (by omega)
              have hmax1 : genDyck (lb.length + 3) 1 = 0 :=
                genDyck_max (lb.length + 3) 1 (by omega)
              cases b <;> cases b' <;> cases c <;> cases b0 <;>
                simp [matchCount, contextMemSpec, contextCountSpec, Chromogram.complete,
                  Chromogram.balanced, Chromogram.bitParity, Color.bit0,
                  Color.bit1, hmax0, hmax1] at hc0 hc1 ⊢

theorem context_bit0_push_two
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity lb)) :
    (Color.two + c).bit0 =
      Bool.xor b0 (Chromogram.bitParity (false :: lb)) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_push_two
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength lb) :
    (Color.two + c).bit1 = Chromogram.oddLength (false :: lb) := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_push_three
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity lb)) :
    (Color.three + c).bit0 =
      Bool.xor b0 (Chromogram.bitParity (true :: lb)) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_push_three
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength lb) :
    (Color.three + c).bit1 = Chromogram.oddLength (true :: lb) := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_skip_one
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity lb)) :
    (Color.one + c).bit0 =
      Bool.xor (!b0) (Chromogram.bitParity lb) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_skip_one
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength lb) :
    (Color.one + c).bit1 = Chromogram.oddLength lb := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_pop_two_zero
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity (false :: lb))) :
    (Color.two + c).bit0 =
      Bool.xor b0 (Chromogram.bitParity lb) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_pop_two_zero
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength (false :: lb)) :
    (Color.two + c).bit1 = Chromogram.oddLength lb := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_pop_two_one
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity (true :: lb))) :
    (Color.two + c).bit0 =
      Bool.xor (!b0) (Chromogram.bitParity lb) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_pop_two_one
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength (true :: lb)) :
    (Color.two + c).bit1 = Chromogram.oddLength lb := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_pop_three_one
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity (true :: lb))) :
    (Color.three + c).bit0 =
      Bool.xor b0 (Chromogram.bitParity lb) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_pop_three_one
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength (true :: lb)) :
    (Color.three + c).bit1 = Chromogram.oddLength lb := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem context_bit0_pop_three_zero
    (c : Color) (lb : List Bool) (b0 : Bool)
    (hc0 : c.bit0 = Bool.xor b0 (Chromogram.bitParity (false :: lb))) :
    (Color.three + c).bit0 =
      Bool.xor (!b0) (Chromogram.bitParity lb) := by
  cases hpar : Chromogram.bitParity lb <;> cases c <;> cases b0 <;>
    simp [Color.bit0, Bool.xor, hpar] at hc0 ⊢

theorem context_bit1_pop_three_zero
    (c : Color) (lb : List Bool)
    (hc1 : c.bit1 = Chromogram.oddLength (false :: lb)) :
    (Color.three + c).bit1 = Chromogram.oddLength lb := by
  cases hodd : Chromogram.oddLength lb <;> cases c <;>
    simp [Color.bit1, hodd] at hc1 ⊢

theorem contextMemSpec_push (h i : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) i b (GramSymbol.push :: w) =
      contextMemSpec h (i + 1) b w := by
  simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

theorem contextMemSpec_skip (h i : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) i b (GramSymbol.skip :: w) =
      contextMemSpec h i (!b) w := by
  cases b <;>
    simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

theorem contextMemSpec_pop0_succ (h i : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) (i + 1) b (GramSymbol.pop0 :: w) =
      contextMemSpec h i b w := by
  simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

theorem contextMemSpec_pop1_succ (h i : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) (i + 1) b (GramSymbol.pop1 :: w) =
      contextMemSpec h i (!b) w := by
  cases b <;>
    simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

theorem contextMemSpec_pop0_zero (h : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) 0 b (GramSymbol.pop0 :: w) = false := by
  simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

theorem contextMemSpec_pop1_zero (h : Nat) (b : Bool) (w : Chromogram) :
    contextMemSpec (h + 1) 0 b (GramSymbol.pop1 :: w) = false := by
  simp [contextMemSpec, Chromogram.complete, Chromogram.balanced]

@[simp]
theorem matchCount_contextMemSpec_zero
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec h i b) bs (Color.zero :: et) = 0 := rfl

theorem matchCount_contextMemSpec_succ_one
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) i b) bs (Color.one :: et) =
      matchCount (contextMemSpec h i (!b)) bs et :=
  matchCount_congr (fun w => contextMemSpec_skip h i b w) bs et

private theorem matchCount_contextMemSpec_zero_depth_cons
    (h : Nat) (b d : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) 0 b) bs
        (Color.cons true d :: et) =
      matchCount (contextMemSpec h 1 b)
        (if d then Chromogram.BitStack.push1 bs
          else Chromogram.BitStack.push0 bs) et := by
  cases d <;> cases bs <;>
    simp [Color.cons, matchCount,
      matchCount_congr
        (st := fun w => contextMemSpec (h + 1) 0 b (GramSymbol.push :: w))
        (st' := contextMemSpec h 1 b)
        (fun w => contextMemSpec_push h 0 b w),
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec (h + 1) 0 b (GramSymbol.pop0 :: w))
        (fun w => contextMemSpec_pop0_zero h b w),
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec (h + 1) 0 b (GramSymbol.pop1 :: w))
        (fun w => contextMemSpec_pop1_zero h b w)]

theorem matchCount_contextMemSpec_zero_depth_two
    (h : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) 0 b) bs (Color.two :: et) =
      matchCount (contextMemSpec h 1 b) (Chromogram.BitStack.push0 bs) et := by
  simpa [Color.cons] using
    matchCount_contextMemSpec_zero_depth_cons h b false bs et

theorem matchCount_contextMemSpec_zero_depth_three
    (h : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) 0 b) bs (Color.three :: et) =
      matchCount (contextMemSpec h 1 b) (Chromogram.BitStack.push1 bs) et := by
  simpa [Color.cons] using
    matchCount_contextMemSpec_zero_depth_cons h b true bs et

private theorem matchCount_contextMemSpec_succ_depth_cons
    (h i : Nat) (b d : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) (i + 1) b) bs
        (Color.cons true d :: et) =
      matchCount (contextMemSpec h (i + 2) b)
          (if d then Chromogram.BitStack.push1 bs
            else Chromogram.BitStack.push0 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (contextMemSpec h i (if d then !b else b)) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (contextMemSpec h i (if d then b else !b)) bs' et := by
  cases d <;> cases bs <;>
    simp [Color.cons, matchCount,
      matchCount_congr
        (st := fun w => contextMemSpec (h + 1) (i + 1) b (GramSymbol.push :: w))
        (st' := contextMemSpec h (i + 2) b)
        (fun w => contextMemSpec_push h (i + 1) b w),
      matchCount_congr
        (st := fun w => contextMemSpec (h + 1) (i + 1) b (GramSymbol.pop0 :: w))
        (st' := contextMemSpec h i b)
        (fun w => contextMemSpec_pop0_succ h i b w),
      matchCount_congr
        (st := fun w => contextMemSpec (h + 1) (i + 1) b (GramSymbol.pop1 :: w))
        (st' := contextMemSpec h i (!b))
        (fun w => contextMemSpec_pop1_succ h i b w)]

theorem matchCount_contextMemSpec_succ_depth_two
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) (i + 1) b) bs (Color.two :: et) =
      matchCount (contextMemSpec h (i + 2) b)
          (Chromogram.BitStack.push0 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (contextMemSpec h i b) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (contextMemSpec h i (!b)) bs' et := by
  simpa [Color.cons] using
    matchCount_contextMemSpec_succ_depth_cons h i b false bs et

theorem matchCount_contextMemSpec_succ_depth_three
    (h i : Nat) (b : Bool) (bs : Chromogram.BitStack) (et : ColSeq) :
    matchCount (contextMemSpec (h + 1) (i + 1) b) bs (Color.three :: et) =
      matchCount (contextMemSpec h (i + 2) b)
          (Chromogram.BitStack.push1 bs) et +
        match bs with
        | Chromogram.BitStack.empty => 0
        | Chromogram.BitStack.push0 bs' =>
            matchCount (contextMemSpec h i (!b)) bs' et
        | Chromogram.BitStack.push1 bs' =>
            matchCount (contextMemSpec h i b) bs' et := by
  simpa [Color.cons] using
    matchCount_contextMemSpec_succ_depth_cons h i b true bs et

theorem contextCountSpec_succ_zero
    (h : Nat) (c : Color) (lb : List Bool) (et : ColSeq) :
    contextCountSpec (h + 1) c lb (Color.zero :: et) = 0 := by
  simp [contextCountSpec]

theorem contextCountSpec_succ_one
    (h : Nat) (c : Color) (lb : List Bool) (et : ColSeq) :
    contextCountSpec (h + 1) c lb (Color.one :: et) =
      contextCountSpec h (Color.one + c) lb et := by
  cases hsum : ColSeq.sum et <;> cases c <;>
    simp [contextCountSpec, hsum, Color.bit1]

private theorem contextCountSpec_succ_cons
    (h : Nat) (c : Color) (d : Bool) (lb : List Bool) (et : ColSeq) :
    contextCountSpec (h + 1) c lb (Color.cons true d :: et) =
      contextCountSpec h (Color.cons true d + c) (d :: lb) et +
        match lb with
        | [] => 0
        | _ :: lb' => contextCountSpec h (Color.cons true d + c) lb' et := by
  cases d <;> cases hsum : ColSeq.sum et <;> cases c <;>
    cases lb with
    | nil =>
        simp [contextCountSpec, Color.cons, hsum, Color.bit1]
        try rw [ite_genDyck_succ_succ]
        try simp
    | cons b lb =>
        cases b <;>
          simp [contextCountSpec, Color.cons, hsum, Color.bit1] <;>
          try rw [ite_genDyck_succ_succ]

theorem contextCountSpec_succ_two
    (h : Nat) (c : Color) (lb : List Bool) (et : ColSeq) :
    contextCountSpec (h + 1) c lb (Color.two :: et) =
      contextCountSpec h (Color.two + c) (false :: lb) et +
        match lb with
        | [] => 0
        | _ :: lb' => contextCountSpec h (Color.two + c) lb' et := by
  simpa [Color.cons] using contextCountSpec_succ_cons h c false lb et

theorem contextCountSpec_succ_three
    (h : Nat) (c : Color) (lb : List Bool) (et : ColSeq) :
    contextCountSpec (h + 1) c lb (Color.three :: et) =
      contextCountSpec h (Color.three + c) (true :: lb) et +
        match lb with
        | [] => 0
        | _ :: lb' => contextCountSpec h (Color.three + c) lb' et := by
  simpa [Color.cons] using contextCountSpec_succ_cons h c true lb et

theorem contextMemSpec_zero_cons
    (i : Nat) (b : Bool) (s : GramSymbol) (w : Chromogram) :
    contextMemSpec 0 i b (s :: w) = false := by
  simp [contextMemSpec]

theorem matchCount_contextMemSpec_height_zero_cons
    (i : Nat) (b : Bool) (bs : Chromogram.BitStack)
    (e : Color) (et : ColSeq) :
    matchCount (contextMemSpec 0 i b) bs (e :: et) = 0 := by
  cases e <;> cases bs <;>
    simp [matchCount,
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec 0 i b (GramSymbol.push :: w))
        (fun w => contextMemSpec_zero_cons i b GramSymbol.push w),
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec 0 i b (GramSymbol.skip :: w))
        (fun w => contextMemSpec_zero_cons i b GramSymbol.skip w),
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec 0 i b (GramSymbol.pop0 :: w))
        (fun w => contextMemSpec_zero_cons i b GramSymbol.pop0 w),
      matchCount_eq_zero_of_false
        (st := fun w => contextMemSpec 0 i b (GramSymbol.pop1 :: w))
        (fun w => contextMemSpec_zero_cons i b GramSymbol.pop1 w)]

theorem contextCountSpec_zero_cons
    (c : Color) (lb : List Bool) (e : Color) (et : ColSeq) :
    contextCountSpec 0 c lb (e :: et) = 0 := by
  simp [contextCountSpec]

theorem matchCount_contextMemSpec
    (et : ColSeq) :
    ∀ (h : Nat) (c : Color) (lb : List Bool) (b0 : Bool),
      c.bit0 = Bool.xor b0 (Chromogram.bitParity lb) →
      c.bit1 = Chromogram.oddLength lb →
      matchCount (contextMemSpec h lb.length b0)
          (Chromogram.BitStack.ofList lb) et =
        contextCountSpec h c lb et := by
  induction et with
  | nil =>
      intro h c lb b0 hc0 hc1
      exact matchCount_contextMemSpec_nil h c lb b0 hc0 hc1
  | cons e et ih =>
      intro h c lb b0 hc0 hc1
      cases h with
      | zero =>
          rw [matchCount_contextMemSpec_height_zero_cons,
            contextCountSpec_zero_cons]
      | succ h =>
          cases e with
          | zero =>
              simp [contextCountSpec_succ_zero]
          | one =>
              rw [matchCount_contextMemSpec_succ_one,
                contextCountSpec_succ_one]
              exact ih h (Color.one + c) lb (!b0)
                (context_bit0_skip_one c lb b0 hc0)
                (context_bit1_skip_one c lb hc1)
          | two =>
              cases lb with
              | nil =>
                  change
                    matchCount (contextMemSpec (h + 1) 0 b0)
                        Chromogram.BitStack.empty (Color.two :: et) =
                      contextCountSpec (h + 1) c [] (Color.two :: et)
                  rw [matchCount_contextMemSpec_zero_depth_two,
                    contextCountSpec_succ_two]
                  simpa using
                    ih h (Color.two + c) [false] b0
                      (context_bit0_push_two c [] b0 hc0)
                      (context_bit1_push_two c [] hc1)
              | cons top lb =>
                  cases top with
                  | false =>
                      change
                        matchCount (contextMemSpec (h + 1) (lb.length + 1) b0)
                            (Chromogram.BitStack.push0
                              (Chromogram.BitStack.ofList lb)) (Color.two :: et) =
                          contextCountSpec (h + 1) c (false :: lb)
                            (Color.two :: et)
                      rw [matchCount_contextMemSpec_succ_depth_two,
                        contextCountSpec_succ_two]
                      simp
                      have hpush :=
                        ih h (Color.two + c) (false :: false :: lb) b0
                          (context_bit0_push_two c (false :: lb) b0 hc0)
                          (context_bit1_push_two c (false :: lb) hc1)
                      simp at hpush
                      rw [hpush,
                        ih h (Color.two + c) lb b0
                          (context_bit0_pop_two_zero c lb b0 hc0)
                          (context_bit1_pop_two_zero c lb hc1)]
                  | true =>
                      change
                        matchCount (contextMemSpec (h + 1) (lb.length + 1) b0)
                            (Chromogram.BitStack.push1
                              (Chromogram.BitStack.ofList lb)) (Color.two :: et) =
                          contextCountSpec (h + 1) c (true :: lb)
                            (Color.two :: et)
                      rw [matchCount_contextMemSpec_succ_depth_two,
                        contextCountSpec_succ_two]
                      simp
                      have hpush :=
                        ih h (Color.two + c) (false :: true :: lb) b0
                          (context_bit0_push_two c (true :: lb) b0 hc0)
                          (context_bit1_push_two c (true :: lb) hc1)
                      simp at hpush
                      rw [hpush,
                        ih h (Color.two + c) lb (!b0)
                          (context_bit0_pop_two_one c lb b0 hc0)
                          (context_bit1_pop_two_one c lb hc1)]
          | three =>
              cases lb with
              | nil =>
                  change
                    matchCount (contextMemSpec (h + 1) 0 b0)
                        Chromogram.BitStack.empty (Color.three :: et) =
                      contextCountSpec (h + 1) c [] (Color.three :: et)
                  rw [matchCount_contextMemSpec_zero_depth_three,
                    contextCountSpec_succ_three]
                  simpa using
                    ih h (Color.three + c) [true] b0
                      (context_bit0_push_three c [] b0 hc0)
                      (context_bit1_push_three c [] hc1)
              | cons top lb =>
                  cases top with
                  | false =>
                      change
                        matchCount (contextMemSpec (h + 1) (lb.length + 1) b0)
                            (Chromogram.BitStack.push0
                              (Chromogram.BitStack.ofList lb)) (Color.three :: et) =
                          contextCountSpec (h + 1) c (false :: lb)
                            (Color.three :: et)
                      rw [matchCount_contextMemSpec_succ_depth_three,
                        contextCountSpec_succ_three]
                      simp
                      have hpush :=
                        ih h (Color.three + c) (true :: false :: lb) b0
                          (context_bit0_push_three c (false :: lb) b0 hc0)
                          (context_bit1_push_three c (false :: lb) hc1)
                      simp at hpush
                      rw [hpush,
                        ih h (Color.three + c) lb (!b0)
                          (context_bit0_pop_three_zero c lb b0 hc0)
                          (context_bit1_pop_three_zero c lb hc1)]
                  | true =>
                      change
                        matchCount (contextMemSpec (h + 1) (lb.length + 1) b0)
                            (Chromogram.BitStack.push1
                              (Chromogram.BitStack.ofList lb)) (Color.three :: et) =
                          contextCountSpec (h + 1) c (true :: lb)
                            (Color.three :: et)
                      rw [matchCount_contextMemSpec_succ_depth_three,
                        contextCountSpec_succ_three]
                      simp
                      have hpush :=
                        ih h (Color.three + c) (true :: true :: lb) b0
                          (context_bit0_push_three c (true :: lb) b0 hc0)
                          (context_bit1_push_three c (true :: lb) hc1)
                      simp at hpush
                      rw [hpush,
                        ih h (Color.three + c) lb b0
                          (context_bit0_pop_three_one c lb b0 hc0)
                          (context_bit1_pop_three_one c lb hc1)]

end GTree

end FourColor

end Schematic.Math.GraphTheory
