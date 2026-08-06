import FourColorTheorem.FourColor.Coloring.InitCTree.Construction

/-! Table-count semantics for initial trace-colouring trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree
/-- Target trace-count specification for `initTree`, matching
`ctree_sub_init_tree` in the Coq development. -/
def initSubSpec (h : Nat) (et : ColSeq) : Nat :=
  if decide (et.length = h) &&
      decide (Color.zero ∉ ColSeq.ctrace et) &&
      ColSeq.evenTrace et then
    dyck (ColSeq.countBit1 (ColSeq.ctrace et))
  else
    0

/-- Count specification for an intermediate initial C-tree table entry.  The
entry index records the number of high-bit colours already forced by the prefix,
and the boolean component records the low-bit parity of that prefix. -/
def tableSubSpec (h i : Nat) (b : Bool) (et : ColSeq) : Nat :=
  let cet := et ++ [Color.cons i.bodd b + ColSeq.sum et]
  if decide (et.length = h) && decide (Color.zero ∉ cet) then
    dyck (i + ColSeq.countBit1 cet)
  else
    0

def leafTableTreeSpec (i : Nat) (b : Bool) : CTree :=
  let c := Color.cons i.bodd b
  if c = Color.zero then empty
  else leafOf (dyck (i + if c.bit1 then 1 else 0))

@[simp]
theorem bodd_two_mul (n : Nat) :
    (2 * n).bodd = false := by
  rw [show 2 * n = n + n by omega, Nat.bodd_add]
  cases n.bodd <;> rfl

@[simp]
theorem bodd_two_mul_add_one (n : Nat) :
    (2 * n + 1).bodd = true := by
  rw [show 2 * n + 1 = (2 * n).succ by omega, Nat.bodd_succ,
    bodd_two_mul]
  rfl

@[simp]
theorem bodd_two_mul_add_two (n : Nat) :
    (2 * n + 2).bodd = false := by
  rw [show 2 * n + 2 = (2 * n + 1).succ by omega, Nat.bodd_succ,
    bodd_two_mul_add_one]
  rfl

private theorem tableSubSpec_cons_one
    (h i : Nat) (b : Bool) (et : ColSeq) :
    tableSubSpec (h + 1) i b (Color.one :: et) =
      tableSubSpec h i (!b) et := by
  cases b <;> cases hb : i.bodd <;> cases hs : ColSeq.sum et <;>
    simp [tableSubSpec, hb, hs, Color.cons, Color.bit1]

theorem tableSubSpec_cons_one_left
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i false (Color.one :: et) =
      tableSubSpec h i true et := by
  simpa using tableSubSpec_cons_one h i false et

theorem tableSubSpec_cons_one_right
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i true (Color.one :: et) =
      tableSubSpec h i false et := by
  simpa using tableSubSpec_cons_one h i true et

private theorem tableSubSpec_cons_high
    (h i : Nat) (b d : Bool) (et : ColSeq) :
    tableSubSpec (h + 1) i b (Color.cons true d :: et) =
      tableSubSpec h (i + 1) (b != d) et := by
  cases b <;> cases d <;> cases hb : i.bodd <;>
    cases hs : ColSeq.sum et <;>
    simp [tableSubSpec, Nat.bodd_succ, hb, hs, Color.cons, Color.bit1,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem tableSubSpec_cons_two_left
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i false (Color.two :: et) =
      tableSubSpec h (i + 1) false et := by
  simpa [Color.cons] using tableSubSpec_cons_high h i false false et

theorem tableSubSpec_cons_two_right
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i true (Color.two :: et) =
      tableSubSpec h (i + 1) true et := by
  simpa [Color.cons] using tableSubSpec_cons_high h i true false et

theorem tableSubSpec_cons_three_left
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i false (Color.three :: et) =
      tableSubSpec h (i + 1) true et := by
  simpa [Color.cons] using tableSubSpec_cons_high h i false true et

theorem tableSubSpec_cons_three_right
    (h i : Nat) (et : ColSeq) :
    tableSubSpec (h + 1) i true (Color.three :: et) =
      tableSubSpec h (i + 1) false et := by
  simpa [Color.cons] using tableSubSpec_cons_high h i true true et

theorem sub_mergePair_left_spec
    {h i : Nat} {tu tu' : Pair}
    (htu_right :
      ∀ et, sub tu.right et = tableSubSpec h i true et)
    (htu'_left :
      ∀ et, sub tu'.left et = tableSubSpec h (i + 1) false et)
    (htu'_right :
      ∀ et, sub tu'.right et = tableSubSpec h (i + 1) true et) :
    ∀ et, sub (mergePair tu tu').left et =
      tableSubSpec (h + 1) i false et
  | [] => by
      rw [mergePair_left, sub_cons]
      simp [sub, tableSubSpec]
  | Color.zero :: et => by
      rw [mergePair_left, sub_cons]
      simp [sub, tableSubSpec]
  | Color.one :: et => by
      rw [sub_mergePair_left_one, htu_right et,
        tableSubSpec_cons_one_left]
  | Color.two :: et => by
      rw [sub_mergePair_left_two, htu'_left et,
        tableSubSpec_cons_two_left]
  | Color.three :: et => by
      rw [sub_mergePair_left_three, htu'_right et,
        tableSubSpec_cons_three_left]

theorem sub_mergePair_right_spec
    {h i : Nat} {tu tu' : Pair}
    (htu_left :
      ∀ et, sub tu.left et = tableSubSpec h i false et)
    (htu'_left :
      ∀ et, sub tu'.left et = tableSubSpec h (i + 1) false et)
    (htu'_right :
      ∀ et, sub tu'.right et = tableSubSpec h (i + 1) true et) :
    ∀ et, sub (mergePair tu tu').right et =
      tableSubSpec (h + 1) i true et
  | [] => by
      rw [mergePair_right, sub_cons]
      simp [sub, tableSubSpec]
  | Color.zero :: et => by
      rw [mergePair_right, sub_cons]
      simp [sub, tableSubSpec]
  | Color.one :: et => by
      rw [sub_mergePair_right_one, htu_left et,
        tableSubSpec_cons_one_right]
  | Color.two :: et => by
      rw [sub_mergePair_right_two, htu'_right et,
        tableSubSpec_cons_two_right]
  | Color.three :: et => by
      rw [sub_mergePair_right_three, htu'_left et,
        tableSubSpec_cons_three_right]

@[simp]
theorem iterate_zero {α : Type _} (f : α → α) (x : α) :
    iterate 0 f x = x := rfl

@[simp]
theorem mergeTable_nil :
    mergeTable [] = [] := rfl

theorem length_leafTableFrom :
    ∀ (lf : CTree) (n h : Nat), (leafTableFrom lf n h).length = h
  | lf, n, 0 => rfl
  | lf, n, 1 => rfl
  | lf, n, h + 2 => by
      simp [leafTableFrom, length_leafTableFrom]

theorem length_leafTable (h : Nat) :
    (leafTable h).length = h + 1 := by
  simp [leafTable, length_leafTableFrom]

theorem mergeTableAux_length (prev : Pair) :
    ∀ tab : Table, (mergeTableAux prev tab).length = tab.length
  | [] => rfl
  | pt :: tab => by
      simp [mergeTableAux, mergeTableAux_length pt tab]

theorem sub_mergeTableAux_spec
    {h offset : Nat} {prev : Pair} :
    ∀ tab : Table,
      (∀ et, sub prev.left et = tableSubSpec h offset false et) →
      (∀ et, sub prev.right et = tableSubSpec h offset true et) →
      (∀ i, i < tab.length → ∀ b et,
        sub (tableSub tab i b) et =
          tableSubSpec h (offset + i + 1) b et) →
      ∀ i, i < (mergeTableAux prev tab).length → ∀ b et,
        sub (tableSub (mergeTableAux prev tab) i b) et =
          tableSubSpec (h + 1) (offset + i) b et
  | [], hprev_left, hprev_right, htab, i, hi, b, et => by
      simp [mergeTableAux] at hi
  | pt :: tab, hprev_left, hprev_right, htab, i, hi, b, et => by
      cases i with
      | zero =>
          have hpt_left :
              ∀ et, sub pt.left et = tableSubSpec h (offset + 1) false et := by
            intro et
            simpa using htab 0 (by simp) false et
          have hpt_right :
              ∀ et, sub pt.right et = tableSubSpec h (offset + 1) true et := by
            intro et
            simpa using htab 0 (by simp) true et
          cases b
          · simpa [mergeTableAux, tableSub, pairSub] using
              sub_mergePair_left_spec hprev_right hpt_left
                hpt_right et
          · simpa [mergeTableAux, tableSub, pairSub] using
              sub_mergePair_right_spec hprev_left hpt_left
                hpt_right et
      | succ i =>
          have hpt_left :
              ∀ et, sub pt.left et = tableSubSpec h (offset + 1) false et := by
            intro et
            simpa using htab 0 (by simp) false et
          have hpt_right :
              ∀ et, sub pt.right et = tableSubSpec h (offset + 1) true et := by
            intro et
            simpa using htab 0 (by simp) true et
          have htail :
              ∀ j, j < tab.length → ∀ b et,
                sub (tableSub tab j b) et =
                  tableSubSpec h ((offset + 1) + j + 1) b et := by
            intro j hj b et
            have hsrc := htab (j + 1) (by simpa using Nat.succ_lt_succ hj) b et
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsrc
          have hi_tail : i < (mergeTableAux pt tab).length := by
            simpa [mergeTableAux] using hi
          have hrec :=
            sub_mergeTableAux_spec (h := h) (offset := offset + 1)
              (prev := pt) tab hpt_left hpt_right htail i hi_tail b et
          simpa [mergeTableAux, tableSub, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hrec

theorem length_mergeTable :
    ∀ tab : Table, (mergeTable tab).length = tab.length - 1
  | [] => rfl
  | _ :: tab => by
      simp [mergeTable, mergeTableAux_length]

theorem sub_mergeTable_spec
    {h : Nat} {tab : Table}
    (htab : ∀ i, i < tab.length → ∀ b et,
      sub (tableSub tab i b) et = tableSubSpec h i b et) :
    ∀ i, i < (mergeTable tab).length → ∀ b et,
      sub (tableSub (mergeTable tab) i b) et =
        tableSubSpec (h + 1) i b et := by
  cases tab with
  | nil =>
      intro i hi b et
      simp [mergeTable] at hi
  | cons line tab =>
      intro i hi b et
      have hline_left :
          ∀ et, sub line.left et = tableSubSpec h 0 false et := by
        intro et
        simpa [tableSub, pairSub] using htab 0 (by simp) false et
      have hline_right :
          ∀ et, sub line.right et = tableSubSpec h 0 true et := by
        intro et
        simpa [tableSub, pairSub] using htab 0 (by simp) true et
      have htail :
          ∀ j, j < tab.length → ∀ b et,
            sub (tableSub tab j b) et = tableSubSpec h (0 + j + 1) b et := by
        intro j hj b et
        have hsrc := htab (j + 1) (by simpa using Nat.succ_lt_succ hj) b et
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsrc
      have haux :=
        sub_mergeTableAux_spec (h := h) (offset := 0) (prev := line)
          tab hline_left hline_right htail i (by simpa [mergeTable] using hi) b et
      simpa [mergeTable] using haux

theorem length_iterate_mergeTable
    (n : Nat) (tab : Table) :
    (iterate n mergeTable tab).length = tab.length - n := by
  induction n generalizing tab with
  | zero =>
      rfl
  | succ n ih =>
      change (mergeTable (iterate n mergeTable tab)).length =
        tab.length - (n + 1)
      rw [length_mergeTable, ih]
      omega

theorem length_iterate_mergeTable_leafTable
    (n h : Nat) :
    (iterate n mergeTable (leafTable h)).length = h + 1 - n := by
  rw [length_iterate_mergeTable, length_leafTable]

theorem sub_iterate_mergeTable_spec
    (n h : Nat) (tab : Table)
    (htab : ∀ i, i < tab.length → ∀ b et,
      sub (tableSub tab i b) et = tableSubSpec h i b et) :
    ∀ i, i < (iterate n mergeTable tab).length → ∀ b et,
      sub (tableSub (iterate n mergeTable tab) i b) et =
        tableSubSpec (h + n) i b et := by
  induction n generalizing tab h with
  | zero =>
      intro i hi b et
      simpa using htab i hi b et
  | succ n ih =>
      intro i hi b et
      change
        sub (tableSub (mergeTable (iterate n mergeTable tab)) i b) et =
          tableSubSpec (h + (n + 1)) i b et
      have hprev :
          ∀ i, i < (iterate n mergeTable tab).length → ∀ b et,
            sub (tableSub (iterate n mergeTable tab) i b) et =
              tableSubSpec (h + n) i b et :=
        ih h tab htab
      have hstep :=
        sub_mergeTable_spec (h := h + n)
          (tab := iterate n mergeTable tab) hprev i hi b et
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

end CTree

end FourColor

end Schematic.Math.GraphTheory
