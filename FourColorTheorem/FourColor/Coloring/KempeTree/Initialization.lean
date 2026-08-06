import FourColorTheorem.FourColor.Coloring.KempeTree.ActiveRestriction

/-!
Initial trace and chromogram trees and their specifications.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

/-- Initial full trace tree for a program-ring height parameter. -/
def initialCTree (h : Nat) : CTree :=
  CTree.initTree (h + 1)

/-- Initial full chromogram tree for a program-ring height parameter. -/
def initialGTree (h : Nat) : GTree :=
  GTree.initTree (h + 1)

theorem initialGTree_mem (h : Nat) (w : Chromogram) :
    GTree.mem (initialGTree h) w = GTree.initSpec (h + 1) w := by
  simpa [initialGTree] using GTree.mem_initTree (h + 1) w

theorem initialGTree_sub_eq_matchCount_initSpec
    (h : Nat) (bs : Chromogram.BitStack) (et : ColSeq) :
    GTree.sub (initialGTree h) bs et =
      GTree.matchCount (GTree.initSpec (h + 1)) bs et := by
  simpa [initialGTree] using
    GTree.sub_initTree_eq_matchCount_initSpec (h + 1) bs et

theorem initialGTree_sub_eq_initCountSpec
    (h : Nat) (et : ColSeq) :
    GTree.sub (initialGTree h) Chromogram.BitStack.empty et =
      GTree.initCountSpec (h + 1) et := by
  simpa [initialGTree] using GTree.sub_initTree_eq_initCountSpec (h + 1) et

theorem initialGTree_sub_ne_zero_length
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0) :
    et.length = h + 1 := by
  apply GTree.initCountSpec_ne_zero_length
  rwa [← initialGTree_sub_eq_initCountSpec]

theorem initialGTree_sub_ne_zero_not_mem_zero_ctrace
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0) :
    Color.zero ∉ ColSeq.ctrace et := by
  apply GTree.initCountSpec_ne_zero_not_mem_zero_ctrace
  rwa [← initialGTree_sub_eq_initCountSpec]

theorem initialGTree_sub_zero_eq_initCountSpec (et : ColSeq) :
    GTree.sub (initialGTree 0) Chromogram.BitStack.empty et =
      GTree.initCountSpec 1 et := by
  simpa [initialGTree] using GTree.sub_initTree_one_eq_initCountSpec et

theorem initialGTree_sub_one_eq_initCountSpec (et : ColSeq) :
    GTree.sub (initialGTree 1) Chromogram.BitStack.empty et =
      GTree.initCountSpec 2 et := by
  simpa [initialGTree] using GTree.sub_initTree_two_eq_initCountSpec et

theorem initialGTree_sub_two_eq_initCountSpec (et : ColSeq) :
    GTree.sub (initialGTree 2) Chromogram.BitStack.empty et =
      GTree.initCountSpec 3 et := by
  simpa [initialGTree] using GTree.sub_initTree_three_eq_initCountSpec et

theorem initialGTree_sub_three_eq_initCountSpec (et : ColSeq) :
    GTree.sub (initialGTree 3) Chromogram.BitStack.empty et =
      GTree.initCountSpec 4 et := by
  simpa [initialGTree] using GTree.sub_initTree_four_eq_initCountSpec et

theorem initialCTree_proper (h : Nat) :
    CTree.Proper (h + 1) (initialCTree h) := by
  simpa [initialCTree] using CTree.proper_initTree (h + 1)

theorem initialCTree_size_le (h : Nat) :
    CTree.size (initialCTree h) ≤ 3 ^ (h + 1) :=
  CTree.size_le_pow_three_of_proper (initialCTree_proper h)

theorem initialCTree_size_lt_closure_bound (h : Nat) :
    CTree.size (initialCTree h) < 3 ^ (h + 2) := by
  have hle := initialCTree_size_le h
  have hpos : 0 < 3 ^ (h + 1) := Nat.pow_pos (by decide)
  have hlt : 3 ^ (h + 1) < 3 ^ (h + 2) := by
    rw [show h + 2 = Nat.succ (h + 1) by omega, Nat.pow_succ]
    exact (Nat.lt_mul_iff_one_lt_right hpos).2 (by decide)
  exact lt_of_le_of_lt hle hlt

theorem initialCTree_sub (h : Nat) (et : ColSeq) :
    CTree.sub (initialCTree h) et = CTree.initSubSpec (h + 1) et := by
  simpa [initialCTree] using CTree.sub_initTree (h + 1) et

theorem initSubSpec_eq_if_initCountSpec (h : Nat) (et : ColSeq) :
    CTree.initSubSpec h et =
      if ColSeq.evenTrace et then GTree.initCountSpec h et else 0 := by
  cases heven : ColSeq.evenTrace et <;>
    simp [CTree.initSubSpec, GTree.initCountSpec, heven]

theorem initialCTree_sub_eq_if_initialGTree_sub
    (h : Nat) (et : ColSeq) :
    CTree.sub (initialCTree h) et =
      if ColSeq.evenTrace et then
        GTree.sub (initialGTree h) Chromogram.BitStack.empty et
      else
        0 := by
  rw [initialCTree_sub, initSubSpec_eq_if_initCountSpec,
    initialGTree_sub_eq_initCountSpec]

theorem initialCTree_mem_of_initialGTree_sub_ne_zero_even
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0)
    (heven : ColSeq.evenTrace et = true) :
    CTree.mem (initialCTree h) et = true := by
  have hsub := initialCTree_sub_eq_if_initialGTree_sub h et
  rw [heven] at hsub
  unfold CTree.mem
  rw [hsub]
  simp [hne]

theorem initialCTree_mem_etrace_of_initialGTree_sub_ne_zero
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0) :
    CTree.mem (initialCTree h) (ColSeq.etrace et) = true := by
  have hneE :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty
          (ColSeq.etrace et) ≠ 0 := by
    rw [GTree.sub_empty_etrace]
    exact hne
  exact initialCTree_mem_of_initialGTree_sub_ne_zero_even hneE
    (ColSeq.even_etrace et)

theorem initialGTree_sub_edgeRot_etrace_ne_zero_of_sub_ne_zero
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0)
    (e : Color) :
    GTree.sub (initialGTree h) Chromogram.BitStack.empty
        (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) ≠
      0 := by
  let norm : ColSeq :=
    ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)
  have hlen : et.length = h + 1 :=
    initialGTree_sub_ne_zero_length hne
  have hlenNorm : norm.length = h + 1 := by
    simp [norm, ColSeq.length_perm, ColSeq.length_etrace, hlen]
  have hzero : Color.zero ∉ ColSeq.ctrace et :=
    initialGTree_sub_ne_zero_not_mem_zero_ctrace hne
  have hzeroE : Color.zero ∉ ColSeq.ctrace (ColSeq.etrace et) :=
    (ColSeq.not_mem_zero_ctrace_etrace_iff et).2 hzero
  have hzeroNorm : Color.zero ∉ ColSeq.ctrace norm := by
    simpa [norm] using
      (ColSeq.not_mem_zero_ctrace_perm_iff
        (EdgePerm.edgeRot e) (ColSeq.etrace et)).2 hzeroE
  have hdyckPos :
      0 < dyck (ColSeq.countBit1 (ColSeq.ctrace norm)) :=
    dyck_pos_of_bodd_false
      (ColSeq.countBit1 (ColSeq.ctrace norm))
      (ColSeq.countBit1_ctrace_bodd norm)
  rw [initialGTree_sub_eq_initCountSpec]
  unfold GTree.initCountSpec
  simp [norm, hlenNorm, hzeroNorm, Nat.ne_of_gt hdyckPos]

theorem initialCTree_mem_edgeRot_etrace_of_initialGTree_sub_ne_zero
    {h : Nat} {et : ColSeq}
    (hne :
      GTree.sub (initialGTree h) Chromogram.BitStack.empty et ≠ 0)
    (e : Color) :
    CTree.mem (initialCTree h)
        (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
      true := by
  have hnormNe :=
    initialGTree_sub_edgeRot_etrace_ne_zero_of_sub_ne_zero hne e
  have heven :
      ColSeq.evenTrace
          (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
        true := by
    rw [ColSeq.evenTrace_perm_edgeRot, ColSeq.even_etrace]
  exact initialCTree_mem_of_initialGTree_sub_ne_zero_even hnormNe heven

theorem initial_valid_of_ctr
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree}
    (hctr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1) :
    Valid h P (initialCTree h) ctr GTree.empty (initialGTree h) := by
  constructor
  · exact initialCTree_proper h
  constructor
  · intro et
    rw [initialCTree_sub_eq_if_initialGTree_sub]
    cases ColSeq.evenTrace et <;> simp [GTree.sub_empty]
  constructor
  · exact hctr
  constructor
  · intro w hmem
    simp at hmem
  constructor
  · intro w hmem
    rw [initialGTree_mem] at hmem
    exact hmem
  · intro w hmem hspec
    rw [initialGTree_mem, hspec] at hmem
    contradiction

theorem initial_valid (h : Nat) (P : ColSeq → Prop) :
    Valid h P (initialCTree h) CTree.empty GTree.empty (initialGTree h) :=
  initial_valid_of_ctr h (P := P) (ctr := CTree.empty) (by
    intro et hmem
    simp at hmem)

theorem initial_valid_of_ctr_mem
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree}
    (hctr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1) :
    Valid h P (initialCTree h) ctr GTree.empty (initialGTree h) :=
  valid_with_ctr_of_mem hctr (initial_valid h P)

theorem initial_complete_of_query
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree} {gtr : GTree}
    (hquery :
      ∀ et : ColSeq,
        (P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem (initialCTree h)
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false)) →
          CTree.mem ctr (ColSeq.etrace et) = true ∨
            GTree.sub (initialGTree h) Chromogram.BitStack.empty et = 0) :
    Complete (3 ^ (h + 2)) P (initialCTree h) ctr gtr (initialGTree h) :=
  Complete.intro_of_progress (initialCTree_size_lt_closure_bound h) hquery

theorem initial_complete_of_ctr_mem
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree} {gtr : GTree}
    (hctr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem ctr (ColSeq.etrace et) = true) :
    Complete (3 ^ (h + 2)) P (initialCTree h) ctr gtr
      (initialGTree h) :=
  initial_complete_of_query h (P := P) (ctr := ctr) (gtr := gtr) (by
    intro et hprem
    rcases hprem with hP | ⟨e, hmissing⟩
    · exact Or.inl (hctr et hP)
    · by_cases hzero :
        GTree.sub (initialGTree h) Chromogram.BitStack.empty et = 0
      · exact Or.inr hzero
      · have hmem :=
          initialCTree_mem_edgeRot_etrace_of_initialGTree_sub_ne_zero
            hzero e
        rw [hmem] at hmissing
        contradiction)

theorem initial_valid_complete_of_ctr_mem
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree}
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem ctr (ColSeq.etrace et) = true) :
    Valid h P (initialCTree h) ctr GTree.empty (initialGTree h) ∧
      Complete (3 ^ (h + 2)) P (initialCTree h) ctr GTree.empty
        (initialGTree h) :=
  ⟨initial_valid_of_ctr_mem h hvalidCtr,
    initial_complete_of_ctr_mem h hcompleteCtr⟩

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
