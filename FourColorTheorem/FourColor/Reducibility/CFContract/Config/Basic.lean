import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Correct

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

/-- Coq `cfcontract`: the selected contract-edge transversal as a list. -/
noncomputable def contractDarts (cf : Config) : List cf.map.map.Dart :=
  CfMask.select cf.contractMask
    (PointedHypermap.cpContractDarts cf.program)

/-- Finset representation used by Lean's semantic `CReducible` interface. -/
noncomputable def contractFinset (cf : Config) : Finset cf.map.map.Dart :=
  cf.contractDarts.toFinset

@[simp]
theorem length_contractCandidates (cf : Config) :
    (PointedHypermap.cpContractDarts cf.program).length =
      CProg.contractEdgeSize cf.program :=
  PointedHypermap.length_cpContractDarts cf.program

@[simp]
theorem length_contractDarts (cf : Config) :
    cf.contractDarts.length = CfMask.countTrue cf.contractMask := by
  exact CfMask.length_select_eq_countTrue_of_length
    cf.contractMask
    (PointedHypermap.cpContractDarts cf.program)
    (by rw [PointedHypermap.length_cpContractDarts,
      Config.length_contractMask])

theorem nodup_contractCandidates_of_wellFormed
    {cf : Config}
    (hcf : cf.WellFormed) :
    (PointedHypermap.cpContractDarts cf.program).Nodup := by
  have hfull :=
    PointedHypermap.nodup_insertEdges_cpRing_contractDarts hcf
  rw [Hypermap.insertEdges_append] at hfull
  have hcandidates := hfull.of_append_right
  exact hcandidates.sublist
    (cf.map.map.sublist_insertEdges
      (PointedHypermap.cpContractDarts cf.program))

theorem nodup_contractDarts_of_wellFormed
    {cf : Config}
    (hcf : cf.WellFormed) :
    cf.contractDarts.Nodup := by
  exact CfMask.nodup_select cf.contractMask
    (nodup_contractCandidates_of_wellFormed hcf)

@[simp]
theorem card_contractFinset_of_wellFormed
    {cf : Config}
    (hcf : cf.WellFormed) :
    cf.contractFinset.card = CfMask.countTrue cf.contractMask := by
  rw [contractFinset,
    List.toFinset_card_of_nodup (nodup_contractDarts_of_wellFormed hcf),
    length_contractDarts]

theorem contractOffRing_of_wellFormed
    {cf : Config}
    (hcf : cf.WellFormed) :
    cf.map.map.ContractOffRing cf.ringDarts cf.contractFinset := by
  intro x hx hclosure
  have hfull :=
    PointedHypermap.nodup_insertEdges_cpRing_contractDarts hcf
  rw [Hypermap.insertEdges_append] at hfull
  have hdisjoint := List.disjoint_of_nodup_append hfull
  have hxRing : x ∈ cf.map.map.insertEdges cf.ringDarts :=
    cf.map.map.mem_insertEdges_self hx
  have selected_mem_candidate :
      ∀ {y : cf.map.map.Dart}, y ∈ cf.contractFinset →
        y ∈ PointedHypermap.cpContractDarts cf.program := by
    intro y hy
    have hyList : y ∈ cf.contractDarts := by
      simpa [contractFinset] using hy
    exact CfMask.mem_of_mem_select hyList
  rcases (cf.map.map.mem_contractClosure_iff).1 hclosure with hy | ⟨y, hy, hyx⟩
  · exact hdisjoint hxRing
      (cf.map.map.mem_insertEdges_self (selected_mem_candidate hy))
  · exact hdisjoint hxRing
      (by
        rw [← hyx]
        exact cf.map.map.mem_insertEdges_edge (selected_mem_candidate hy))

theorem contractFinset_card_pos_of_validMask
    {cf : Config}
    (hcf : cf.WellFormed)
    (hmask : CfMask.validContractMask cf.contractMask cf.program = true) :
    0 < cf.contractFinset.card := by
  rw [card_contractFinset_of_wellFormed hcf]
  exact CfMask.validContractMask_countTrue_pos hmask

theorem contractFinset_card_le_four_of_validMask
    {cf : Config}
    (hcf : cf.WellFormed)
    (hmask : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.contractFinset.card ≤ 4 := by
  rw [card_contractFinset_of_wellFormed hcf]
  exact CfMask.validContractMask_countTrue_le_four hmask

theorem cpContractSelection_initial_eq (cf : Config) :
    PointedHypermap.cpContractSelection
        cf.initialRingMask cf.contractMask cf.program =
      cf.contractDarts := by
  simp [PointedHypermap.cpContractSelection, initialRingMask,
    CfMask.select_replicate_false, contractDarts]
  rfl

theorem cpContractFinset_initial_eq (cf : Config) :
    PointedHypermap.cpContractFinset
        cf.initialRingMask cf.contractMask cf.program =
      cf.contractFinset := by
  rw [PointedHypermap.cpContractFinset, contractFinset,
    cpContractSelection_initial_eq]
  rfl

theorem cpSparseTail_initial_eq (cf : Config) :
    PointedHypermap.cpSparseTail cf.initialRingMask cf.contractMask cf.program =
      cf.map.map.contractClosure cf.contractFinset := by
  simp [PointedHypermap.cpSparseTail, initialRingMask,
    CfMask.select_replicate_false, contractFinset, contractDarts, map]
  congr 1

theorem rootSparse_contractProgram
    {cf : Config} {cpc : CProg}
    (hrun : CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
      some cpc) :
    PointedHypermap.RootSparse cf.map
      (cf.map.map.contractClosure cf.contractFinset) := by
  have h := PointedHypermap.rootSparse_contractProgram
    (mr := cf.initialRingMask) (mc := cf.contractMask)
    (cp := cf.program) (cpc := cpc)
    (by simp [initialRingMask]) (length_contractMask cf) hrun
  rw [cpSparseTail_initial_eq] at h
  exact h

theorem contractFinset_sparse_of_contractProgram
    {cf : Config} {cpc : CProg}
    (hrun : CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
      some cpc) :
    cf.map.map.Sparse (cf.map.map.contractClosure cf.contractFinset) :=
  (rootSparse_contractProgram hrun).sparse

end Config

end FourColor

end Schematic.Math.GraphTheory
