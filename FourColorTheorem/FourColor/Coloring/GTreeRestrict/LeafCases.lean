import FourColorTheorem.FourColor.Coloring.GTreeRestrict.Partition

/-! Restriction formulas for canonical chromogram-tree leaves. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

@[simp]
theorem restrict_leaf0 (r : Restriction) :
    restrict leaf0 r =
      if Restriction.match0 r then pair0Empty else pairEmpty0 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf1 (r : Restriction) :
    restrict leaf1 r =
      if Restriction.match1 r then pair1Empty else pairEmpty1 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf2 (r : Restriction) :
    restrict leaf2 r =
      if Restriction.match2 r then pair2Empty else pairEmpty2 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf3 (r : Restriction) :
    restrict leaf3 r =
      if Restriction.match3 r then pair3Empty else pairEmpty3 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf01 (r : Restriction) :
    restrict leaf01 r =
      if Restriction.match0 r then
        if Restriction.match1 r then pair01Empty else pair01
      else
        if Restriction.match1 r then pair10 else pairEmpty01 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf12 (r : Restriction) :
    restrict leaf12 r =
      if Restriction.match1 r then
        if Restriction.match2 r then pair12Empty else pair12
      else
        if Restriction.match2 r then pair21 else pairEmpty12 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf13 (r : Restriction) :
    restrict leaf13 r =
      if Restriction.match1 r then
        if Restriction.match3 r then pair13Empty else pair13
      else
        if Restriction.match3 r then pair31 else pairEmpty13 := by
  cases r <;> rfl

@[simp]
theorem restrict_leaf23 (r : Restriction) :
    restrict leaf23 r =
      if Restriction.match2 r then
        if Restriction.match3 r then pair23Empty else pair23
      else
        if Restriction.match3 r then pair32 else pairEmpty23 := by
  cases r <;> rfl

private theorem restrict_leaf0_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf0 r) side) w =
      (mem leaf0 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf0, Restriction.match0_eq_mem] <;>
    cases h : Restriction.mem r [GramSymbol.push] <;> cases w with
  | nil =>
      simp [pair0Empty, pairEmpty0, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair0Empty, pairEmpty0, treePair, mem, h]

private theorem restrict_leaf1_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf1 r) side) w =
      (mem leaf1 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf1, Restriction.match1_eq_mem] <;>
    cases h : Restriction.mem r [GramSymbol.skip] <;> cases w with
  | nil =>
      simp [pair1Empty, pairEmpty1, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair1Empty, pairEmpty1, treePair, mem, h]

private theorem restrict_leaf2_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf2 r) side) w =
      (mem leaf2 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf2, Restriction.match2_eq_mem] <;>
    cases h : Restriction.mem r [GramSymbol.pop0] <;> cases w with
  | nil =>
      simp [pair2Empty, pairEmpty2, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair2Empty, pairEmpty2, treePair, mem, h]

private theorem restrict_leaf3_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf3 r) side) w =
      (mem leaf3 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf3, Restriction.match3_eq_mem] <;>
    cases h : Restriction.mem r [GramSymbol.pop1] <;> cases w with
  | nil =>
      simp [pair3Empty, pairEmpty3, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair3Empty, pairEmpty3, treePair, mem, h]

private theorem restrict_leaf01_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf01 r) side) w =
      (mem leaf01 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf01, Restriction.match0_eq_mem,
      Restriction.match1_eq_mem] <;>
    cases h0 : Restriction.mem r [GramSymbol.push] <;>
    cases h1 : Restriction.mem r [GramSymbol.skip] <;>
    cases w with
  | nil =>
      simp [pair01Empty, pair01, pair10, pairEmpty01, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair01Empty, pair01, pair10, pairEmpty01, treePair, mem, h0, h1]

private theorem restrict_leaf12_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf12 r) side) w =
      (mem leaf12 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf12, Restriction.match1_eq_mem,
      Restriction.match2_eq_mem] <;>
    cases h1 : Restriction.mem r [GramSymbol.skip] <;>
    cases h2 : Restriction.mem r [GramSymbol.pop0] <;>
    cases w with
  | nil =>
      simp [pair12Empty, pair12, pair21, pairEmpty12, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair12Empty, pair12, pair21, pairEmpty12, treePair, mem, h1, h2]

private theorem restrict_leaf13_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf13 r) side) w =
      (mem leaf13 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf13, Restriction.match1_eq_mem,
      Restriction.match3_eq_mem] <;>
    cases h1 : Restriction.mem r [GramSymbol.skip] <;>
    cases h3 : Restriction.mem r [GramSymbol.pop1] <;>
    cases w with
  | nil =>
      simp [pair13Empty, pair13, pair31, pairEmpty13, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair13Empty, pair13, pair31, pairEmpty13, treePair, mem, h1, h3]

private theorem restrict_leaf23_pairSub_mem
    (r : Restriction) (w : Chromogram) (side : Bool) :
    mem (pairSub (restrict leaf23 r) side) w =
      (mem leaf23 w && if side then !(Restriction.mem r w)
        else Restriction.mem r w) := by
  cases side <;> simp only [pairSub] <;>
    rw [restrict_leaf23, Restriction.match2_eq_mem,
      Restriction.match3_eq_mem] <;>
    cases h2 : Restriction.mem r [GramSymbol.pop0] <;>
    cases h3 : Restriction.mem r [GramSymbol.pop1] <;>
    cases w with
  | nil =>
      simp [pair23Empty, pair23, pair32, pairEmpty23, treePair, mem]
  | cons s w =>
      cases w <;> cases s <;>
        simp [pair23Empty, pair23, pair32, pairEmpty23, treePair, mem, h2, h3]

theorem restrict_leaf0_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf0 r).left w =
      (mem leaf0 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf0_pairSub_mem r w false

theorem restrict_leaf0_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf0 r).right w =
      (mem leaf0 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf0_pairSub_mem r w true

theorem restrict_leaf1_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf1 r).left w =
      (mem leaf1 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf1_pairSub_mem r w false

theorem restrict_leaf1_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf1 r).right w =
      (mem leaf1 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf1_pairSub_mem r w true

theorem restrict_leaf2_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf2 r).left w =
      (mem leaf2 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf2_pairSub_mem r w false

theorem restrict_leaf2_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf2 r).right w =
      (mem leaf2 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf2_pairSub_mem r w true

theorem restrict_leaf3_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf3 r).left w =
      (mem leaf3 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf3_pairSub_mem r w false

theorem restrict_leaf3_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf3 r).right w =
      (mem leaf3 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf3_pairSub_mem r w true

theorem restrict_leaf01_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf01 r).left w =
      (mem leaf01 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf01_pairSub_mem r w false

theorem restrict_leaf01_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf01 r).right w =
      (mem leaf01 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf01_pairSub_mem r w true

theorem restrict_leaf12_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf12 r).left w =
      (mem leaf12 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf12_pairSub_mem r w false

theorem restrict_leaf12_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf12 r).right w =
      (mem leaf12 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf12_pairSub_mem r w true

theorem restrict_leaf13_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf13 r).left w =
      (mem leaf13 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf13_pairSub_mem r w false

theorem restrict_leaf13_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf13 r).right w =
      (mem leaf13 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf13_pairSub_mem r w true

theorem restrict_leaf23_left_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf23 r).left w =
      (mem leaf23 w && Restriction.mem r w) := by
  simpa [pairSub] using restrict_leaf23_pairSub_mem r w false

theorem restrict_leaf23_right_mem
    (r : Restriction) (w : Chromogram) :
    mem (restrict leaf23 r).right w =
      (mem leaf23 w && !(Restriction.mem r w)) := by
  simpa [pairSub] using restrict_leaf23_pairSub_mem r w true

theorem restrict_pairSub_mem :
    ∀ (t : GTree) (r : Restriction) (w : Chromogram) (side : Bool),
      mem (pairSub (restrict t r) side) w =
        (mem t w && if side then !(Restriction.mem r w)
          else Restriction.mem r w)
  | node tPush tSkip tPop0 tPop1, r, w, side => by
      cases r with
      | nil =>
          cases side
          · simpa [pairSub] using
              restrict_nil_left_mem (node tPush tSkip tPop0 tPop1) w
          · simpa [pairSub] using
              restrict_nil_right_mem (node tPush tSkip tPop0 tPop1) w
      | cons bs ct r =>
          change
            mem
              (pairSub
                (Restriction.split
                  (fun rPush rSkip rPop0 rPop1 =>
                    consPairs
                      (restrict tPush rPush)
                      (restrict tSkip rSkip)
                      (restrict tPop0 rPop0)
                      (restrict tPop1 rPop1))
                  Restriction.nil Restriction.nil Restriction.nil
                  Restriction.nil (Restriction.cons bs ct r)) side) w =
              (mem (node tPush tSkip tPop0 tPop1) w &&
                if side then !(Restriction.mem (Restriction.cons bs ct r) w)
                else Restriction.mem (Restriction.cons bs ct r) w)
          cases w with
          | nil =>
              rw [Restriction.split_eq]
              simp [mem_consPairs_pairSub_nil, mem]
          | cons s w =>
              rw [Restriction.split_eq]
              cases s <;>
                simp [mem_consPairs_pairSub_symbol, restrict_pairSub_mem,
                  Restriction.splitSymbol_mem, mem, select]
  | leaf0, r, w, side => by
      exact restrict_leaf0_pairSub_mem r w side
  | leaf1, r, w, side => by
      exact restrict_leaf1_pairSub_mem r w side
  | leaf2, r, w, side => by
      exact restrict_leaf2_pairSub_mem r w side
  | leaf3, r, w, side => by
      exact restrict_leaf3_pairSub_mem r w side
  | leaf01, r, w, side => by
      exact restrict_leaf01_pairSub_mem r w side
  | leaf12, r, w, side => by
      exact restrict_leaf12_pairSub_mem r w side
  | leaf13, r, w, side => by
      exact restrict_leaf13_pairSub_mem r w side
  | leaf23, r, w, side => by
      exact restrict_leaf23_pairSub_mem r w side
  | empty, r, w, side => by
      cases side <;> cases r <;> cases w <;>
        simp [restrict, emptyPair, pairSub, treePair]

end GTree

end FourColor

end Schematic.Math.GraphTheory
