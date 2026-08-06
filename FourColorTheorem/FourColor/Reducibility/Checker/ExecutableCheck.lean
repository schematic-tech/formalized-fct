import FourColorTheorem.FourColor.Reducibility.Checker.ContractTreeConsequences

/-! Executable reducibility checks and their semantic consequences. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config
/-- Reducibility checker against a supplied Kempe-closure tree.  The later
Kempe-tree layer supplies that first argument as `Kempe_tree (cfprog cf)`. -/
def checkAgainstWith
    (colorTree : CProg → CTree) (kempeTree : CTree) (cf : Config) : Bool :=
  match contractTreeWith colorTree cf with
  | some contractTree => CTree.disjoint kempeTree contractTree
  | none => false

/-- Specification-backend checker against a supplied Kempe tree. -/
def checkAgainst (kempeTree : CTree) (cf : Config) : Bool :=
  checkAgainstWith CProg.cpColor kempeTree cf

/-- Optimized-backend checker against a supplied Kempe tree. -/
def checkAgainstFast (kempeTree : CTree) (cf : Config) : Bool :=
  checkAgainstWith CProg.cpColorFast kempeTree cf

/-- Full executable reducibility checker: compute the Kempe tree of the
configuration program, compute the contract tree, and test disjointness. -/
def checkReducible (cf : Config) : Bool :=
  checkAgainst (KempeTree.tree cf.program) cf

/-- Optimized full executable reducibility checker. -/
def checkReducibleFast (cf : Config) : Bool :=
  checkAgainstFast (KempeTree.treeFast cf.program) cf

theorem checkAgainstFast_spec (kempeTree : CTree) (cf : Config) :
    checkAgainstFast kempeTree cf = checkAgainst kempeTree cf := by
  unfold checkAgainstFast checkAgainst checkAgainstWith
  have h := contractTreeFast_spec cf
  unfold contractTreeFast contractTree at h
  rw [h]

theorem checkReducibleFast_spec (cf : Config) :
    checkReducibleFast cf = checkReducible cf := by
  unfold checkReducibleFast checkReducible
  rw [KempeTree.treeFast_spec]
  exact checkAgainstFast_spec (KempeTree.tree cf.program) cf

theorem checkAgainstWith_eq_true_iff
    (colorTree : CProg → CTree) (kempeTree : CTree) (cf : Config) :
    checkAgainstWith colorTree kempeTree cf = true ↔
      ∃ contractTree : CTree,
        contractTreeWith colorTree cf = some contractTree ∧
        CTree.disjoint kempeTree contractTree = true := by
  unfold checkAgainstWith
  cases hct : contractTreeWith colorTree cf with
  | none =>
      simp
  | some contractTree =>
      simp

theorem checkReducible_eq_true_iff (cf : Config) :
    checkReducible cf = true ↔
      ∃ contractTree : CTree,
        cf.contractTree = some contractTree ∧
        CTree.disjoint (KempeTree.tree cf.program) contractTree = true := by
  exact checkAgainstWith_eq_true_iff CProg.cpColor
    (KempeTree.tree cf.program) cf

theorem checkReducible_contractTree_exists
    {cf : Config}
    (hcheck : checkReducible cf = true) :
    ∃ contractTree : CTree, cf.contractTree = some contractTree :=
  let ⟨contractTree, hcontract, _hdisjoint⟩ :=
    (checkReducible_eq_true_iff cf).1 hcheck
  ⟨contractTree, hcontract⟩

lift_check_reducible_consequence_api

theorem checkAgainstWith_disjoint_of_contractTree
    {colorTree : CProg → CTree} {kempeTree : CTree}
    {cf : Config} {contractTree : CTree}
    (hcheck : checkAgainstWith colorTree kempeTree cf = true)
    (hcontract : contractTreeWith colorTree cf = some contractTree) :
    CTree.disjoint kempeTree contractTree = true := by
  unfold checkAgainstWith at hcheck
  rw [hcontract] at hcheck
  simpa using hcheck

theorem checkAgainstWith_contract_mem_not_kempe
    {colorTree : CProg → CTree} {kempeTree : CTree}
    {cf : Config} {contractTree : CTree}
    (hcheck : checkAgainstWith colorTree kempeTree cf = true)
    (hcontract : contractTreeWith colorTree cf = some contractTree)
    {et : ColSeq}
    (hmem : CTree.mem contractTree et = true) :
    CTree.mem kempeTree et = false := by
  exact CTree.mem_disjoint kempeTree contractTree et
    (checkAgainstWith_disjoint_of_contractTree hcheck hcontract) hmem

theorem checkAgainstWith_kempe_mem_not_contract
    {colorTree : CProg → CTree} {kempeTree : CTree}
    {cf : Config} {contractTree : CTree}
    (hcheck : checkAgainstWith colorTree kempeTree cf = true)
    (hcontract : contractTreeWith colorTree cf = some contractTree)
    {et : ColSeq}
    (hmem : CTree.mem kempeTree et = true) :
    CTree.mem contractTree et = false := by
  exact CTree.mem_disjoint_left kempeTree contractTree et
    (checkAgainstWith_disjoint_of_contractTree hcheck hcontract) hmem

theorem checkReducible_disjoint_of_contractTree
    {cf : Config} {contractTree : CTree}
    (hcheck : checkReducible cf = true)
    (hcontract : cf.contractTree = some contractTree) :
    CTree.disjoint (KempeTree.tree cf.program) contractTree = true :=
  checkAgainstWith_disjoint_of_contractTree hcheck hcontract

theorem checkReducible_contract_mem_not_kempe
    {cf : Config} {contractTree : CTree}
    (hcheck : checkReducible cf = true)
    (hcontract : cf.contractTree = some contractTree)
    {et : ColSeq}
    (hmem : CTree.mem contractTree et = true) :
    CTree.mem (KempeTree.tree cf.program) et = false :=
  checkAgainstWith_contract_mem_not_kempe hcheck hcontract hmem

theorem checkReducible_contractTree_mem_cpColorSpec_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {contractTree : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
        some cpc ∧
      CfMask.validContractMask cf.contractMask cf.program = true ∧
      CProg.cpColor cpc = contractTree ∧
        CProg.cpColorSpec cpc et :=
  contractTree_mem_cpColorSpec_of_branch_proper
    hbranch hcontract hmem

theorem checkReducible_contractTree_mem_cpColorSpec_noReverse_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {contractTree : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
        some cpc ∧
      CProg.noReverse cpc = true ∧
      CfMask.validContractMask cf.contractMask cf.program = true ∧
      CProg.cpColor cpc = contractTree ∧
        CProg.cpColorSpec cpc et :=
  contractTree_mem_cpColorSpec_noReverse_of_branch_proper
    hbranch hcontract hmem

theorem checkReducible_contractTree_mem_trace_normalized_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cf : Config} {contractTree : CTree} {et : ColSeq}
    (hcontract : cf.contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et :=
  contractTree_mem_trace_normalized_of_branch_proper
    hbranch hcontract hmem

theorem checkAgainstWith_contract_etrace_coclosure_of_treeOfHeight_spec
    {colorTree : CProg → CTree} {cf : Config}
    {contractTree ctr : CTree} {h : Nat} {P : ColSeq → Prop}
    (hcheck :
      checkAgainstWith colorTree (KempeTree.treeOfHeight h ctr) cf = true)
    (hcontract : contractTreeWith colorTree cf = some contractTree)
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem ctr (ColSeq.etrace et) = true)
    {et : ColSeq} (hlen : et.length = h + 1)
    (hmem : CTree.mem contractTree (ColSeq.etrace et) = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hnotKempe :
      CTree.mem (KempeTree.treeOfHeight h ctr) (ColSeq.etrace et) =
        false :=
    checkAgainstWith_contract_mem_not_kempe hcheck hcontract hmem
  exact
    (KempeTree.treeOfHeight_etrace_nonmem_iff_coclosure_of_ctr_mem
      h hvalidCtr hcompleteCtr hlen).mp hnotKempe

theorem checkReducible_contract_etrace_coclosure_of_cpColor_spec
    {cf : Config} {contractTree : CTree} {h : Nat}
    {P : ColSeq → Prop}
    (hring : CProg.ringSize cf.program = Nat.succ (Nat.succ h))
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem (CProg.cpColor cf.program) et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem (CProg.cpColor cf.program) (ColSeq.etrace et) = true)
    (hcheck : checkReducible cf = true)
    (hcontract : cf.contractTree = some contractTree)
    {et : ColSeq} (hlen : et.length = h + 1)
    (hmem : CTree.mem contractTree (ColSeq.etrace et) = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hnotKempe :
      CTree.mem (KempeTree.tree cf.program) (ColSeq.etrace et) = false :=
    checkReducible_contract_mem_not_kempe hcheck hcontract hmem
  exact
    (KempeTree.tree_etrace_nonmem_iff_coclosure_of_cpColor_spec
      cf.program hring hvalidCtr hcompleteCtr hlen).mp hnotKempe

theorem checkReducible_contract_etrace_coclosure_of_cpColorSpec
    {cf : Config} {contractTree : CTree} {h branchHeight : Nat}
    {P : ColSeq → Prop}
    (hring : CProg.ringSize cf.program = Nat.succ (Nat.succ h))
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    (hvalidSpec :
      ∀ et : ColSeq,
        CProg.cpColorSpec cf.program et →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteSpec :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CProg.cpColorSpec cf.program (ColSeq.etrace et))
    (hcheck : checkReducible cf = true)
    (hcontract : cf.contractTree = some contractTree)
    {et : ColSeq} (hlen : et.length = h + 1)
    (hmem : CTree.mem contractTree (ColSeq.etrace et) = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hnotKempe :
      CTree.mem (KempeTree.tree cf.program) (ColSeq.etrace et) = false :=
    checkReducible_contract_mem_not_kempe hcheck hcontract hmem
  exact
    (KempeTree.tree_etrace_nonmem_iff_coclosure_of_cpColorSpec
      cf.program hring hbranch hvalidSpec hcompleteSpec hlen).mp hnotKempe


end Config

end FourColor

end Schematic.Math.GraphTheory
