import FourColorTheorem.FourColor.Coloring.CFColor
import FourColorTheorem.FourColor.Coloring.CTreeRestrict
import FourColorTheorem.FourColor.Coloring.GTreeRestrict
import FourColorTheorem.FourColor.Coloring.InitCTree
import FourColorTheorem.FourColor.Coloring.InitGTree
import FourColorTheorem.FourColor.Coloring.Kempe

/-!
Kempe closure trees.

This ports the executable front of Gonthier's `kempetree.v`: the closure state,
one closure-improvement step, the iterated closure algorithm, and the final
program-indexed Kempe tree.  The semantic correctness theorem is deliberately
stated separately from these executable definitions so the proof can be built
against the already ported restriction layers.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace KempeTree

/-- State returned by a Kempe closure computation: an unremoved trace tree and
a chromogram-tree partition. -/
structure State where
  ctu : CTree
  gtp : GTree.Pair
  deriving DecidableEq

/-- Type of closure functions used by the iterative algorithm. -/
abbrev ClosureFun := CTree → CTree → GTree → State

/-- Initial restriction passed to `GTree.restrict` in the base closure. -/
def baseGRestriction (ctr : CTree) : GTree.Restriction :=
  GTree.Restriction.cons Chromogram.BitStack.empty ctr GTree.Restriction.nil

/-- Initial restriction passed to `CTree.restrict` when feeding deleted
chromograms back into trace counts. -/
def baseCRestriction (gtr : GTree) : CTree.Restriction :=
  CTree.Restriction.cons Chromogram.BitStack.empty gtr CTree.Restriction.nil

@[simp]
theorem baseGRestriction_mem (ctr : CTree) (w : Chromogram) :
    GTree.Restriction.mem (baseGRestriction ctr) w =
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w := by
  simp [baseGRestriction, GTree.Restriction.mem]

@[simp]
theorem baseCRestriction_sub (gtr : GTree) (et : ColSeq) :
    CTree.Restriction.sub (baseCRestriction gtr) et =
      GTree.sub gtr Chromogram.BitStack.empty et := by
  simp [baseCRestriction, CTree.Restriction.sub]

theorem restrict_baseG_left_mem
    (gtu : GTree) (ctr : CTree) (w : Chromogram) :
    GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).left w =
      (GTree.mem gtu w &&
        GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w) := by
  rw [GTree.restrict_left_mem, baseGRestriction_mem]

theorem restrict_baseG_right_mem
    (gtu : GTree) (ctr : CTree) (w : Chromogram) :
    GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).right w =
      (GTree.mem gtu w &&
        !(GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w)) := by
  rw [GTree.restrict_right_mem, baseGRestriction_mem]

theorem restrict_baseG_left_mem_true
    {gtu : GTree} {ctr : CTree} {w : Chromogram}
    (hmem :
      GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).left w = true) :
    GTree.mem gtu w = true ∧
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w = true := by
  rw [restrict_baseG_left_mem] at hmem
  simpa using hmem

theorem restrict_baseG_left_mem_of_true
    {gtu : GTree} {ctr : CTree} {w : Chromogram}
    (hgtu : GTree.mem gtu w = true)
    (hmatch :
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w = true) :
    GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).left w = true := by
  rw [restrict_baseG_left_mem, hgtu, hmatch]
  rfl

theorem restrict_baseG_right_mem_true
    {gtu : GTree} {ctr : CTree} {w : Chromogram}
    (hmem :
      GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).right w = true) :
    GTree.mem gtu w = true ∧
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w = false := by
  rw [restrict_baseG_right_mem] at hmem
  simpa using hmem

theorem restrict_baseG_right_mem_of_true
    {gtu : GTree} {ctr : CTree} {w : Chromogram}
    (hgtu : GTree.mem gtu w = true)
    (hmatch :
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w = false) :
    GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).right w = true := by
  rw [restrict_baseG_right_mem, hgtu, hmatch]
  rfl

theorem restrict_baseG_mem_left_or_right
    (gtu : GTree) (ctr : CTree) {w : Chromogram}
    (hgtu : GTree.mem gtu w = true) :
    GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).left w = true ∨
      GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).right w = true := by
  cases hmatch :
      GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w
  · exact Or.inr (restrict_baseG_right_mem_of_true hgtu hmatch)
  · exact Or.inl (restrict_baseG_left_mem_of_true hgtu hmatch)

theorem restrict_baseG_sub_add
    (gtu : GTree) (ctr : CTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    GTree.sub gtu bs et =
      GTree.sub (GTree.restrict gtu (baseGRestriction ctr)).left bs et +
        GTree.sub (GTree.restrict gtu (baseGRestriction ctr)).right bs et :=
  GTree.restrict_sub_add gtu (baseGRestriction ctr) bs et

theorem restrict_baseC_left_sub_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) (et : ColSeq) :
    CTree.sub (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      CTree.sub ctu et -
        GTree.sub gtr Chromogram.BitStack.empty et := by
  rw [CTree.restrict_sub_left_of_proper h (baseCRestriction gtr) hproper et,
    baseCRestriction_sub]

theorem restrict_baseC_right_sub_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) (et : ColSeq) :
    CTree.sub (CTree.restrict h ctu (baseCRestriction gtr)).right et =
      if CTree.sub ctu et ≤ GTree.sub gtr Chromogram.BitStack.empty et then
        CTree.sub ctu et
      else
        0 := by
  rw [CTree.restrict_sub_right_of_proper h (baseCRestriction gtr) hproper et,
    baseCRestriction_sub]

theorem restrict_baseC_left_proper_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.Proper (h + 1)
      (CTree.restrict h ctu (baseCRestriction gtr)).left :=
  (CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper).1

theorem restrict_baseC_right_proper_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.Proper (h + 1)
      (CTree.restrict h ctu (baseCRestriction gtr)).right :=
  (CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper).2

theorem restrict_baseC_pair_proper_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.Proper (h + 1)
        (CTree.restrict h ctu (baseCRestriction gtr)).left ∧
      CTree.Proper (h + 1)
      (CTree.restrict h ctu (baseCRestriction gtr)).right :=
  CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper

theorem restrict_baseC_left_size_le_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left ≤
      CTree.size ctu :=
  CTree.restrict_left_size_le_of_proper h (baseCRestriction gtr) hproper

theorem restrict_baseC_right_size_le_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right ≤
      CTree.size ctu :=
  CTree.restrict_right_size_le_of_proper h (baseCRestriction gtr) hproper

theorem restrict_baseC_size_partition_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.size ctu =
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left +
        CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right :=
  CTree.restrict_size_partition_of_proper h (baseCRestriction gtr) hproper

theorem restrict_baseC_left_mem_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) (et : ColSeq) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      decide (GTree.sub gtr Chromogram.BitStack.empty et <
        CTree.sub ctu et) := by
  rw [CTree.restrict_left_mem_of_proper h (baseCRestriction gtr)
    hproper et, baseCRestriction_sub]

theorem restrict_baseC_left_mem_true_of_proper
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
        true) :
    GTree.sub gtr Chromogram.BitStack.empty et < CTree.sub ctu et := by
  rw [restrict_baseC_left_mem_of_proper h gtr hproper et] at hmem
  simpa using hmem

theorem restrict_baseC_left_mem_of_lt
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hlt : GTree.sub gtr Chromogram.BitStack.empty et < CTree.sub ctu et) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      true := by
  rw [restrict_baseC_left_mem_of_proper h gtr hproper et]
  simpa using hlt

theorem restrict_baseC_right_mem_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) (et : ColSeq) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right et =
      (CTree.mem ctu et &&
        decide (CTree.sub ctu et ≤
          GTree.sub gtr Chromogram.BitStack.empty et)) := by
  rw [CTree.restrict_right_mem_of_proper h (baseCRestriction gtr)
    hproper et, baseCRestriction_sub]

theorem restrict_baseC_right_mem_true_of_proper
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right et =
        true) :
    CTree.mem ctu et = true ∧
      CTree.sub ctu et ≤ GTree.sub gtr Chromogram.BitStack.empty et := by
  rw [restrict_baseC_right_mem_of_proper h gtr hproper et] at hmem
  simpa using hmem

theorem restrict_baseC_rotLR_right_mem_true_of_proper
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right
        (ColSeq.perm EdgePerm.p312 et) =
      true ∨
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right
          (ColSeq.perm EdgePerm.p231 et) =
        true := by
  have hright :
      CTree.Proper (h + 1)
        (CTree.restrict h ctu (baseCRestriction gtr)).right :=
    (CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper).2
  rw [CTree.mem_rotLR hright] at hmem
  simpa using hmem

theorem restrict_baseC_right_mem_of_le
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hctu : CTree.mem ctu et = true)
    (hle : CTree.sub ctu et ≤ GTree.sub gtr Chromogram.BitStack.empty et) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right et =
      true := by
  rw [restrict_baseC_right_mem_of_proper h gtr hproper et, hctu]
  simpa using hle

theorem restrict_baseC_rotLR_right_proper_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) :
    CTree.Proper (h + 1)
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right) := by
  exact CTree.proper_rotLR
    (CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper).2

theorem restrict_baseC_rotLR_right_mem_of_proper
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu) (et : ColSeq) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      ((CTree.mem ctu (ColSeq.perm EdgePerm.p312 et) &&
          decide (CTree.sub ctu (ColSeq.perm EdgePerm.p312 et) ≤
            GTree.sub gtr Chromogram.BitStack.empty
              (ColSeq.perm EdgePerm.p312 et))) ||
        (CTree.mem ctu (ColSeq.perm EdgePerm.p231 et) &&
          decide (CTree.sub ctu (ColSeq.perm EdgePerm.p231 et) ≤
            GTree.sub gtr Chromogram.BitStack.empty
              (ColSeq.perm EdgePerm.p231 et)))) := by
  have hright :
      CTree.Proper (h + 1)
        (CTree.restrict h ctu (baseCRestriction gtr)).right :=
    (CTree.restrict_proper_of_proper h (baseCRestriction gtr) hproper).2
  rw [CTree.mem_rotLR hright]
  rw [restrict_baseC_right_mem_of_proper h gtr hproper,
    restrict_baseC_right_mem_of_proper h gtr hproper]

private theorem restrict_baseC_rotLR_right_mem_of_perm
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {g : EdgePerm} {et : ColSeq}
    (hg : g = EdgePerm.p312 ∨ g = EdgePerm.p231)
    (hmem : CTree.mem ctu (ColSeq.perm g et) = true)
    (hle : CTree.sub ctu (ColSeq.perm g et) ≤
      GTree.sub gtr Chromogram.BitStack.empty (ColSeq.perm g et)) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et = true := by
  rcases hg with rfl | rfl
  · rw [restrict_baseC_rotLR_right_mem_of_proper h gtr hproper et, hmem]
    simp [hle]
  · rw [restrict_baseC_rotLR_right_mem_of_proper h gtr hproper et, hmem]
    simp [hle]

theorem restrict_baseC_rotLR_right_mem_of_p312
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem : CTree.mem ctu (ColSeq.perm EdgePerm.p312 et) = true)
    (hle :
      CTree.sub ctu (ColSeq.perm EdgePerm.p312 et) ≤
        GTree.sub gtr Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p312 et)) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      true := by
  exact restrict_baseC_rotLR_right_mem_of_perm h hproper (Or.inl rfl)
    hmem hle

theorem restrict_baseC_rotLR_right_mem_of_p231
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem : CTree.mem ctu (ColSeq.perm EdgePerm.p231 et) = true)
    (hle :
      CTree.sub ctu (ColSeq.perm EdgePerm.p231 et) ≤
        GTree.sub gtr Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p231 et)) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      true := by
  exact restrict_baseC_rotLR_right_mem_of_perm h hproper (Or.inr rfl)
    hmem hle

private theorem restrict_baseC_rotLR_right_mem_of_perm_left_false
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {g : EdgePerm} {et : ColSeq}
    (hg : g = EdgePerm.p312 ∨ g = EdgePerm.p231)
    (hmem : CTree.mem ctu (ColSeq.perm g et) = true)
    (hleft : CTree.mem
      (CTree.restrict h ctu (baseCRestriction gtr)).left
      (ColSeq.perm g et) = false) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et = true := by
  have hnot : ¬ GTree.sub gtr Chromogram.BitStack.empty (ColSeq.perm g et) <
      CTree.sub ctu (ColSeq.perm g et) := by
    rw [restrict_baseC_left_mem_of_proper h gtr hproper] at hleft
    simpa using hleft
  exact restrict_baseC_rotLR_right_mem_of_perm h hproper hg hmem
    (Nat.le_of_not_gt hnot)

theorem restrict_baseC_rotLR_right_mem_of_p312_left_false
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem : CTree.mem ctu (ColSeq.perm EdgePerm.p312 et) = true)
    (hleft :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
          (ColSeq.perm EdgePerm.p312 et) =
        false) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      true := by
  exact restrict_baseC_rotLR_right_mem_of_perm_left_false h hproper
    (Or.inl rfl) hmem hleft

theorem restrict_baseC_rotLR_right_mem_of_p231_left_false
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {et : ColSeq}
    (hmem : CTree.mem ctu (ColSeq.perm EdgePerm.p231 et) = true)
    (hleft :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
          (ColSeq.perm EdgePerm.p231 et) =
        false) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      true := by
  exact restrict_baseC_rotLR_right_mem_of_perm_left_false h hproper
    (Or.inr rfl) hmem hleft

theorem restrict_baseC_rotLR_right_mem_of_edgeRot_left_false
    (h : Nat) {ctu : CTree} {gtr : GTree}
    (hproper : CTree.Proper (h + 1) ctu) {e : Color} {et : ColSeq}
    (hleftEt :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
        true)
    (hmem :
      CTree.mem ctu (ColSeq.perm (EdgePerm.edgeRot e) et) = true)
    (hleft :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
          (ColSeq.perm (EdgePerm.edgeRot e) et) =
        false) :
    CTree.mem
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        et =
      true := by
  cases e with
  | zero =>
      simp [EdgePerm.edgeRot, ColSeq.perm_id] at hleft
      rw [hleftEt] at hleft
      contradiction
  | one =>
      simp [EdgePerm.edgeRot, ColSeq.perm_id] at hleft
      rw [hleftEt] at hleft
      contradiction
  | two =>
      simpa [EdgePerm.edgeRot] using
        restrict_baseC_rotLR_right_mem_of_p312_left_false
          h hproper hmem hleft
  | three =>
      simpa [EdgePerm.edgeRot] using
        restrict_baseC_rotLR_right_mem_of_p231_left_false
          h hproper hmem hleft


end KempeTree

end FourColor

end Schematic.Math.GraphTheory
