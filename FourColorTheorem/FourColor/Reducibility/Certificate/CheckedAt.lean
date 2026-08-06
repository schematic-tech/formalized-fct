import FourColorTheorem.FourColor.Reducibility.Checker

/-!
Certificate-range checking utilities.

This ports the proof shape around `reducible_in_range` from Gonthier's
`cfreducible.v` for the Lean executable checker.  The semantic theorem turning
`checkReducible` into `CReducible` is supplied later, once the Kempe-tree and
configuration-map correctness proofs are complete.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

/-- Fallback configuration used for out-of-range certificate indexing. -/
def default : Config where
  symmetric := false
  contractRef := []
  program := [CpStep.h]

/-- The executable checker succeeds for the configuration at index `i`. -/
def CheckedAt (cfs : List Config) (i : Nat) : Prop :=
  checkReducible (cfs.getD i default) = true

lift_checked_at_consequence_api

theorem CheckedAt.contractTree_mem_cpColorSpec_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cfs : List Config} {i : Nat}
    {contractTree : CTree} {et : ColSeq}
    (hcontract : (cfs.getD i default).contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram
          (cfs.getD i default).initialRingMask
          (cfs.getD i default).contractMask
          (cfs.getD i default).program =
        some cpc ∧
      CfMask.validContractMask
          (cfs.getD i default).contractMask
          (cfs.getD i default).program = true ∧
      CProg.cpColor cpc = contractTree ∧
        CProg.cpColorSpec cpc et :=
  checkReducible_contractTree_mem_cpColorSpec_of_branch_proper
    hbranch hcontract hmem

theorem CheckedAt.contractTree_mem_cpColorSpec_noReverse_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cfs : List Config} {i : Nat}
    {contractTree : CTree} {et : ColSeq}
    (hcontract : (cfs.getD i default).contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ∃ cpc : CProg,
      CProg.contractProgram
          (cfs.getD i default).initialRingMask
          (cfs.getD i default).contractMask
          (cfs.getD i default).program =
        some cpc ∧
      CProg.noReverse cpc = true ∧
      CfMask.validContractMask
          (cfs.getD i default).contractMask
          (cfs.getD i default).program = true ∧
      CProg.cpColor cpc = contractTree ∧
        CProg.cpColorSpec cpc et :=
  checkReducible_contractTree_mem_cpColorSpec_noReverse_of_branch_proper
    hbranch hcontract hmem

theorem CheckedAt.contractTree_mem_trace_normalized_of_branch_proper
    {branchHeight : Nat}
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    {cfs : List Config} {i : Nat}
    {contractTree : CTree} {et : ColSeq}
    (hcontract : (cfs.getD i default).contractTree = some contractTree)
    (hmem : CTree.mem contractTree et = true) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et :=
  checkReducible_contractTree_mem_trace_normalized_of_branch_proper
    hbranch hcontract hmem


end Config

end FourColor

end Schematic.Math.GraphTheory
