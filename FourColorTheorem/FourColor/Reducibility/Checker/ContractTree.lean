import FourColorTheorem.FourColor.Coloring.CFColor
import FourColorTheorem.FourColor.Coloring.KempeTree

/-!
Executable contract-tree checker front.

This ports the syntax-level part of Gonthier's `contract_ctree` and the final
disjointness test used by `check_reducible`.  The semantic theorem that the
computed contract tree is complete belongs to the later configuration-map and
Kempe-tree layers.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

/-- Initial ring mask used by `contract_ctree`: no ring edge is contracted. -/
def initialRingMask (cf : Config) : List Bool :=
  List.replicate (CProg.ringSize cf.program) false

/-- General contract-tree evaluator, parameterized by the colouring-tree
backend. -/
def contractTreeWith (colorTree : CProg → CTree) (cf : Config) :
    Option CTree :=
  let cp := cf.program
  let cm := cf.contractMask
  match CProg.contractProgram cf.initialRingMask cm cp with
  | some cpc =>
      if CfMask.validContractMask cm cp then some (colorTree cpc) else none
  | none => none

/-- Contract tree using the specification colouring-tree builder. -/
def contractTree (cf : Config) : Option CTree :=
  contractTreeWith CProg.cpColor cf

/-- Contract tree using the optimized colouring-tree builder. -/
def contractTreeFast (cf : Config) : Option CTree :=
  contractTreeWith CProg.cpColorFast cf

theorem contractTreeWith_eq_some_iff
    (colorTree : CProg → CTree) (cf : Config) (ct : CTree) :
    contractTreeWith colorTree cf = some ct ↔
      ∃ cpc : CProg,
        CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
          some cpc ∧
        CfMask.validContractMask cf.contractMask cf.program = true ∧
        colorTree cpc = ct := by
  unfold contractTreeWith
  cases hctr :
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program with
  | none =>
      simp [hctr]
  | some cpc =>
      cases hvalid : CfMask.validContractMask cf.contractMask cf.program <;>
        simp [hctr, hvalid]

theorem contractTree_eq_some_iff
    (cf : Config) (ct : CTree) :
    cf.contractTree = some ct ↔
      ∃ cpc : CProg,
        CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
          some cpc ∧
        CfMask.validContractMask cf.contractMask cf.program = true ∧
        CProg.cpColor cpc = ct :=
  contractTreeWith_eq_some_iff CProg.cpColor cf ct

theorem contractTreeFast_eq_some_iff
    (cf : Config) (ct : CTree) :
    cf.contractTreeFast = some ct ↔
      ∃ cpc : CProg,
        CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
          some cpc ∧
        CfMask.validContractMask cf.contractMask cf.program = true ∧
        CProg.cpColorFast cpc = ct :=
  contractTreeWith_eq_some_iff CProg.cpColorFast cf ct

theorem contractTreeFast_spec (cf : Config) :
    cf.contractTreeFast = cf.contractTree := by
  unfold contractTreeFast contractTree contractTreeWith
  cases hctr :
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program with
  | none =>
      simp [hctr]
  | some cpc =>
      cases hvalid : CfMask.validContractMask cf.contractMask cf.program <;>
        simp [hctr, hvalid, CProg.cpColorFast_spec]

theorem contractTreeWith_program_config
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CProg.config cf.program = true := by
  rcases (contractTreeWith_eq_some_iff colorTree cf ct).mp h with
    ⟨cpc, hctr, _, _⟩
  exact CProg.contractProgram_config hctr

theorem contractTreeWith_validMask
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CfMask.validContractMask cf.contractMask cf.program = true := by
  rcases (contractTreeWith_eq_some_iff colorTree cf ct).mp h with
    ⟨_, _, hvalid, _⟩
  exact hvalid

theorem contractTreeWith_contractBand_proper
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CfMask.Proper cf.program
      (CfMask.contractBand cf.contractMask cf.program) :=
  CfMask.proper_contractBand_of_length
    (cm := cf.contractMask) (cp := cf.program)
    (by simpa using cf.length_contractMask)
    (contractTreeWith_program_config h)

theorem contractTreeWith_contractProgram_exists
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask
          cf.contractMask cf.program =
        some cpc := by
  rcases (contractTreeWith_eq_some_iff colorTree cf ct).mp h with
    ⟨cpc, hctr, _, _⟩
  exact ⟨cpc, hctr⟩

theorem contractTreeWith_contractProgram_exists_noReverse
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask
          cf.contractMask cf.program =
        some cpc ∧
      CProg.noReverse cpc = true := by
  rcases (contractTreeWith_eq_some_iff colorTree cf ct).mp h with
    ⟨cpc, hctr, _, _⟩
  exact ⟨cpc, hctr, CProg.contractProgram_noReverse hctr⟩

theorem contractTreeWith_contractProgram_not_mem_reverse
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask
          cf.contractMask cf.program =
        some cpc ∧
      CpStep.reverseRotate ∉ cpc := by
  rcases contractTreeWith_contractProgram_exists_noReverse h with
    ⟨cpc, hctr, hnr⟩
  exact ⟨cpc, hctr,
    (CProg.noReverse_eq_true_iff_not_mem_reverse cpc).1 hnr⟩

theorem contractTreeWith_selected_count_pos
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    0 < CfMask.countTrue cf.contractMask :=
  CfMask.validContractMask_countTrue_pos
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndices_length_pos
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    0 < cf.selectedContractIndices.length :=
  selectedContractIndices_length_pos_of_validMask
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndexFinset_card_pos
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    0 < cf.selectedContractIndexFinset.card :=
  card_selectedContractIndexFinset_pos_of_validMask
    (contractTreeWith_validMask h)

theorem contractTreeWith_contractMask_exists_true
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    true ∈ cf.contractMask :=
  CfMask.validContractMask_exists_true
    (contractTreeWith_validMask h)

theorem contractTreeWith_contractRef_exists
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    ∃ k, k < CProg.contractEdgeSize cf.program ∧ k ∈ cf.contractRef :=
  contractRef_exists_of_validMask (contractTreeWith_validMask h)

theorem contractTreeWith_selected_count_le_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CfMask.countTrue cf.contractMask ≤ 4 :=
  CfMask.validContractMask_countTrue_le_four
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndices_length_le_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    cf.selectedContractIndices.length ≤ 4 :=
  selectedContractIndices_length_le_four_of_validMask
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndexFinset_card_le_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    cf.selectedContractIndexFinset.card ≤ 4 :=
  card_selectedContractIndexFinset_le_four_of_validMask
    (contractTreeWith_validMask h)

theorem contractTreeWith_contractMask_countFalse_pos_of_contractEdgeSize_gt_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    0 < CProg.countFalse cf.contractMask :=
  contractMask_countFalse_pos_of_contractEdgeSize_gt_four
    (contractTreeWith_validMask h) hlen

theorem contractTreeWith_contractMask_exists_false_of_contractEdgeSize_gt_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    false ∈ cf.contractMask :=
  contractMask_exists_false_of_contractEdgeSize_gt_four
    (contractTreeWith_validMask h) hlen

theorem contractTreeWith_contractMask_hasFalse_of_contractEdgeSize_gt_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    CfMask.hasFalse cf.contractMask = true :=
  contractMask_hasFalse_of_contractEdgeSize_gt_four
    (contractTreeWith_validMask h) hlen

theorem contractTreeWith_contractRef_missing_of_contractEdgeSize_gt_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    ∃ k, k < CProg.contractEdgeSize cf.program ∧ k ∉ cf.contractRef :=
  contractRef_missing_of_validMask_and_contractEdgeSize_gt_four
    (contractTreeWith_validMask h) hlen

theorem contractTreeWith_triad_of_selected_count_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : CfMask.countTrue cf.contractMask = 4) :
    CfMask.triad
      (CfMask.contractBand cf.contractMask cf.program)
      cf.program (CProg.kernelSize cf.program) = true :=
  CfMask.validContractMask_triad_of_countTrue_eq_four
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAt_of_selected_count_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : CfMask.countTrue cf.contractMask = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true :=
  CfMask.validContractMask_exists_triadAt_of_countTrue_eq_four
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_of_selected_count_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : CfMask.countTrue cf.contractMask = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i :=
  CfMask.validContractMask_exists_triadAtSources_of_countTrue_eq_four
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_count_gt_two_of_selected_count_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : CfMask.countTrue cf.contractMask = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i ∧
      2 <
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).ring +
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).kernel :=
  exists_triadAtSources_count_gt_two_of_validMask_four
    (contractTreeWith_program_config h)
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_triad_of_selectedContractIndices_length_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndices.length = 4) :
    CfMask.triad
      (CfMask.contractBand cf.contractMask cf.program)
      cf.program (CProg.kernelSize cf.program) = true :=
  triad_of_selectedContractIndices_length_eq_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAt_of_selectedContractIndices_length_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndices.length = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true :=
  exists_triadAt_of_selectedContractIndices_length_eq_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_of_selectedContractIndices_length_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndices.length = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i :=
  exists_triadAtSources_of_selectedContractIndices_length_eq_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_count_gt_two_of_selectedContractIndices_length_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndices.length = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i ∧
      2 <
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).ring +
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).kernel := by
  have hcount : CfMask.countTrue cf.contractMask = 4 := by
    rw [← selectedContractIndices_length_eq_countTrue_contractMask cf]
    exact hfour
  exact contractTreeWith_exists_triadAtSources_count_gt_two_of_selected_count_eq_four
    h hcount

theorem contractTreeWith_triad_of_selectedContractIndexFinset_card_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    CfMask.triad
      (CfMask.contractBand cf.contractMask cf.program)
      cf.program (CProg.kernelSize cf.program) = true :=
  triad_of_selectedContractIndexFinset_card_eq_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_of_selectedContractIndexFinset_card_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i :=
  exists_triadAtSources_of_selectedContractIndexFinset_card_eq_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_exists_triadAtSources_count_gt_two_of_selectedContractIndexFinset_card_eq_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i ∧
      2 <
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).ring +
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).kernel := by
  have hcount : CfMask.countTrue cf.contractMask = 4 := by
    rw [← card_selectedContractIndexFinset_eq_countTrue_contractMask cf]
    exact hfour
  exact contractTreeWith_exists_triadAtSources_count_gt_two_of_selected_count_eq_four
    h hcount

theorem contractTreeWith_selected_count_le_three_of_ne_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : CfMask.countTrue cf.contractMask ≠ 4) :
    CfMask.countTrue cf.contractMask ≤ 3 :=
  CfMask.validContractMask_countTrue_le_three_of_ne_four
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_selectedContractIndices_length_le_three_of_ne_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndices.length ≠ 4) :
    cf.selectedContractIndices.length ≤ 3 :=
  selectedContractIndices_length_le_three_of_ne_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_selectedContractIndexFinset_card_le_three_of_ne_four
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct)
    (hfour : cf.selectedContractIndexFinset.card ≠ 4) :
    cf.selectedContractIndexFinset.card ≤ 3 :=
  card_selectedContractIndexFinset_le_three_of_ne_four_of_validMask
    (contractTreeWith_validMask h) hfour

theorem contractTreeWith_selected_count_eq_four_or_le_three
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CfMask.countTrue cf.contractMask = 4 ∨
      CfMask.countTrue cf.contractMask ≤ 3 :=
  CfMask.validContractMask_countTrue_eq_four_or_le_three
    (contractTreeWith_validMask h)

theorem contractTreeWith_selected_count_eq_four_or_between
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    CfMask.countTrue cf.contractMask = 4 ∨
      (0 < CfMask.countTrue cf.contractMask ∧
        CfMask.countTrue cf.contractMask ≤ 3) :=
  CfMask.validContractMask_countTrue_eq_four_or_between
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndices_length_eq_four_or_between
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    cf.selectedContractIndices.length = 4 ∨
      (0 < cf.selectedContractIndices.length ∧
        cf.selectedContractIndices.length ≤ 3) :=
  selectedContractIndices_length_eq_four_or_between_of_validMask
    (contractTreeWith_validMask h)

theorem contractTreeWith_selectedContractIndexFinset_card_eq_four_or_between
    {colorTree : CProg → CTree} {cf : Config} {ct : CTree}
    (h : contractTreeWith colorTree cf = some ct) :
    cf.selectedContractIndexFinset.card = 4 ∨
      (0 < cf.selectedContractIndexFinset.card ∧
        cf.selectedContractIndexFinset.card ≤ 3) :=
  card_selectedContractIndexFinset_eq_four_or_between_of_validMask
    (contractTreeWith_validMask h)

theorem contractTree_mem_iff_exists_cpColorSpec_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {ct : CTree}
    (hcontract : cf.contractTree = some ct)
    (et : ColSeq) :
    CTree.mem ct et = true ↔
      ∃ cpc : CProg,
        CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
          some cpc ∧
        CfMask.validContractMask cf.contractMask cf.program = true ∧
        CProg.cpColor cpc = ct ∧
          CProg.cpColorSpec cpc et := by
  constructor
  · intro hmem
    rcases (contractTree_eq_some_iff cf ct).1 hcontract with
      ⟨cpc, hctr, hvalid, hct⟩
    refine ⟨cpc, hctr, hvalid, hct, ?_⟩
    exact (CProg.cpColor_mem_iff_of_branch_proper hbranch cpc et).1
      (by simpa [hct] using hmem)
  · rintro ⟨cpc, _hctr, _hvalid, hct, hspec⟩
    exact (by
      have hmem :
          CTree.mem (CProg.cpColor cpc) et = true :=
        (CProg.cpColor_mem_iff_of_branch_proper hbranch cpc et).2 hspec
      simpa [hct] using hmem)

theorem contractTree_mem_cpColorSpec_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {ct : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some ct)
    (hmem : CTree.mem ct et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
        some cpc ∧
      CfMask.validContractMask cf.contractMask cf.program = true ∧
      CProg.cpColor cpc = ct ∧
        CProg.cpColorSpec cpc et :=
  (contractTree_mem_iff_exists_cpColorSpec_of_branch_proper
    hbranch hcontract et).1 hmem

theorem contractTree_mem_cpColorSpec_noReverse_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {ct : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some ct)
    (hmem : CTree.mem ct et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
        some cpc ∧
      CProg.noReverse cpc = true ∧
      CfMask.validContractMask cf.contractMask cf.program = true ∧
      CProg.cpColor cpc = ct ∧
        CProg.cpColorSpec cpc et := by
  rcases contractTree_mem_cpColorSpec_of_branch_proper
      hbranch hcontract hmem with
    ⟨cpc, hctr, hvalid, hct, hspec⟩
  exact ⟨cpc, hctr, CProg.contractProgram_noReverse hctr,
    hvalid, hct, hspec⟩

theorem contractTree_mem_trace_normalized_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {ct : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some ct)
    (hmem : CTree.mem ct et = true) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et := by
  rcases contractTree_mem_cpColorSpec_of_branch_proper
      hbranch hcontract hmem with
    ⟨cpc, _hctr, _hvalid, _hct, hspec⟩
  exact CProg.cpColorSpec_trace_normalized hspec


end Config

end FourColor

end Schematic.Math.GraphTheory
