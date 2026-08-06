import FourColorTheorem.FourColor.Configuration.Encoding.Triads

/-! Configuration-level consequences of valid contract masks. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

theorem contractMask_countTrue_add_countFalse (cf : Config) :
    CfMask.countTrue cf.contractMask +
        CProg.countFalse cf.contractMask =
      CProg.contractEdgeSize cf.program := by
  rw [← length_contractMask cf]
  exact CfMask.countTrue_add_countFalse cf.contractMask

theorem selectedContractIndices_length_eq_countTrue_contractMask
    (cf : Config) :
    cf.selectedContractIndices.length = CfMask.countTrue cf.contractMask := by
  rw [Config.selectedContractIndices, Config.contractMask,
    CfMask.countTrue_contractMask_eq_length_selectedContractIndices]

theorem selectedContractIndices_length_pos_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    0 < cf.selectedContractIndices.length := by
  rw [selectedContractIndices_length_eq_countTrue_contractMask]
  exact CfMask.validContractMask_countTrue_pos h

theorem selectedContractIndices_length_le_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.selectedContractIndices.length ≤ 4 := by
  rw [selectedContractIndices_length_eq_countTrue_contractMask]
  exact CfMask.validContractMask_countTrue_le_four h

theorem selectedContractIndices_length_eq_four_or_between_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.selectedContractIndices.length = 4 ∨
      (0 < cf.selectedContractIndices.length ∧
        cf.selectedContractIndices.length ≤ 3) := by
  rw [selectedContractIndices_length_eq_countTrue_contractMask]
  exact CfMask.validContractMask_countTrue_eq_four_or_between h

theorem card_selectedContractIndexFinset_eq_countTrue_contractMask
    (cf : Config) :
    cf.selectedContractIndexFinset.card = CfMask.countTrue cf.contractMask := by
  rw [card_selectedContractIndexFinset_eq_length,
    selectedContractIndices_length_eq_countTrue_contractMask]

theorem card_selectedContractIndexFinset_pos_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    0 < cf.selectedContractIndexFinset.card := by
  rw [card_selectedContractIndexFinset_eq_length]
  exact selectedContractIndices_length_pos_of_validMask h

theorem card_selectedContractIndexFinset_le_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.selectedContractIndexFinset.card ≤ 4 := by
  rw [card_selectedContractIndexFinset_eq_length]
  exact selectedContractIndices_length_le_four_of_validMask h

theorem card_selectedContractIndexFinset_eq_four_or_between_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.selectedContractIndexFinset.card = 4 ∨
      (0 < cf.selectedContractIndexFinset.card ∧
        cf.selectedContractIndexFinset.card ≤ 3) := by
  rw [card_selectedContractIndexFinset_eq_length]
  exact selectedContractIndices_length_eq_four_or_between_of_validMask h

theorem triad_of_selectedContractIndices_length_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndices.length = 4) :
    CfMask.triad
      (CfMask.contractBand cf.contractMask cf.program)
      cf.program (CProg.kernelSize cf.program) = true := by
  exact CfMask.validContractMask_triad_of_countTrue_eq_four h
    (by
      rw [← selectedContractIndices_length_eq_countTrue_contractMask cf]
      exact hfour)

theorem exists_triadAt_of_selectedContractIndices_length_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndices.length = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true :=
  CfMask.triad_exists_triadAt_of_eq_true
    (triad_of_selectedContractIndices_length_eq_four_of_validMask h hfour)

theorem exists_triadAtSources_of_selectedContractIndices_length_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndices.length = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i := by
  have hcount : CfMask.countTrue cf.contractMask = 4 := by
    rw [← selectedContractIndices_length_eq_countTrue_contractMask cf]
    exact hfour
  exact CfMask.validContractMask_exists_triadAtSources_of_countTrue_eq_four
    h hcount

theorem triad_of_selectedContractIndexFinset_card_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    CfMask.triad
      (CfMask.contractBand cf.contractMask cf.program)
      cf.program (CProg.kernelSize cf.program) = true := by
  have hlen : cf.selectedContractIndices.length = 4 := by
    rwa [card_selectedContractIndexFinset_eq_length] at hfour
  exact triad_of_selectedContractIndices_length_eq_four_of_validMask h hlen

theorem exists_triadAt_of_selectedContractIndexFinset_card_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true :=
  CfMask.triad_exists_triadAt_of_eq_true
    (triad_of_selectedContractIndexFinset_card_eq_four_of_validMask h hfour)

theorem exists_triadAtSources_of_selectedContractIndexFinset_card_eq_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndexFinset.card = 4) :
    ∃ i, i < CProg.kernelSize cf.program ∧
      CfMask.triadAt
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i = true ∧
      CfMask.triadAtSources
        (CfMask.contractBand cf.contractMask cf.program)
        cf.program i := by
  have hlen : cf.selectedContractIndices.length = 4 := by
    rwa [card_selectedContractIndexFinset_eq_length] at hfour
  exact exists_triadAtSources_of_selectedContractIndices_length_eq_four_of_validMask
    h hlen

theorem card_selectedContractIndexFinset_le_three_of_ne_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndexFinset.card ≠ 4) :
    cf.selectedContractIndexFinset.card ≤ 3 := by
  rw [card_selectedContractIndexFinset_eq_countTrue_contractMask]
  exact CfMask.validContractMask_countTrue_le_three_of_ne_four h
    (by
      intro hcount
      exact hfour (by
        rwa [card_selectedContractIndexFinset_eq_countTrue_contractMask]))

theorem selectedContractIndices_length_le_three_of_ne_four_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.selectedContractIndices.length ≠ 4) :
    cf.selectedContractIndices.length ≤ 3 := by
  rw [selectedContractIndices_length_eq_countTrue_contractMask]
  exact CfMask.validContractMask_countTrue_le_three_of_ne_four h
    (by
      intro hcount
      exact hfour (by
        rwa [← selectedContractIndices_length_eq_countTrue_contractMask cf]
          at hcount))

theorem contractMask_countFalse_pos_of_contractEdgeSize_gt_four
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    0 < CProg.countFalse cf.contractMask := by
  have hmasklen : 4 < cf.contractMask.length := by
    rw [length_contractMask cf]
    exact hlen
  exact CfMask.validContractMask_countFalse_pos_of_length_gt_four
    h hmasklen

theorem contractMask_exists_false_of_contractEdgeSize_gt_four
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    false ∈ cf.contractMask :=
  (CfMask.countFalse_pos_iff_exists_false cf.contractMask).1
    (contractMask_countFalse_pos_of_contractEdgeSize_gt_four h hlen)

theorem contractMask_hasFalse_of_contractEdgeSize_gt_four
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    CfMask.hasFalse cf.contractMask = true :=
  (CfMask.hasFalse_eq_true_iff cf.contractMask).2
    (contractMask_exists_false_of_contractEdgeSize_gt_four h hlen)

theorem contractRef_exists_of_validMask
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true) :
    ∃ k, k < CProg.contractEdgeSize cf.program ∧ k ∈ cf.contractRef := by
  have htrue : true ∈ cf.contractMask :=
    CfMask.validContractMask_exists_true h
  simpa [Config.contractMask] using
    (CProg.true_mem_contractMask_iff cf.program cf.contractRef).1 htrue

theorem contractRef_missing_of_validMask_and_contractEdgeSize_gt_four
    {cf : Config}
    (h : CfMask.validContractMask cf.contractMask cf.program = true)
    (hlen : 4 < CProg.contractEdgeSize cf.program) :
    ∃ k, k < CProg.contractEdgeSize cf.program ∧ k ∉ cf.contractRef := by
  have hfalse : false ∈ cf.contractMask :=
    contractMask_exists_false_of_contractEdgeSize_gt_four h hlen
  simpa [Config.contractMask] using
    (CProg.false_mem_contractMask_iff cf.program cf.contractRef).1 hfalse

theorem contractBand_proper_of_program_config
    {cf : Config}
    (hcfg : CProg.config cf.program = true) :
    CfMask.Proper cf.program
      (CfMask.contractBand cf.contractMask cf.program) :=
  CfMask.proper_contractBand_of_length
    (cm := cf.contractMask) (cp := cf.program)
    (by simpa using cf.length_contractMask) hcfg

theorem exists_triadAtSources_count_gt_two_of_validMask_four
    {cf : Config}
    (hcfg : CProg.config cf.program = true)
    (hvalid :
      CfMask.validContractMask cf.contractMask cf.program = true)
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
          (CfMask.contractBand cf.contractMask cf.program).kernel := by
  rcases CfMask.validContractMask_exists_triadAtSources_of_countTrue_eq_four
      hvalid hfour with
    ⟨i, hi, htriad, hsources⟩
  have hproper := contractBand_proper_of_program_config (cf := cf) hcfg
  have hcount :
      2 <
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).ring +
        CfMask.countTrue
          (CfMask.contractBand cf.contractMask cf.program).kernel :=
    CfMask.triadAt_contractMask_countTrue_gt_two_of_proper
      (contractMask := CfMask.contractBand cf.contractMask cf.program)
      (cp := cf.program) (i := i) hproper htriad
  exact ⟨i, hi, htriad, hsources, hcount⟩

end Config

end FourColor

end Schematic.Math.GraphTheory
