import FourColorTheorem.FourColor.Reducibility.Checker.ContractTree

/-!
Declaration generators for the contract-tree consequence API.

The substantive proofs live at the polymorphic `contractTreeWith_*` layer.
This module keeps the established specification, optimized, executable, and
certificate-facing APIs synchronized without restating their result types.
-/

namespace Schematic.Math.GraphTheory.FourColor.Config

open Lean Elab Command Meta

/-- The semantic consequences shared by every successful contract-tree
construction.  `contractTree_exists` belongs only to checker-based layers and
is therefore intentionally absent. -/
private def contractTreeConsequenceNames : Array String := #[
  "program_config",
  "validMask",
  "contractBand_proper",
  "contractProgram_exists",
  "contractProgram_exists_noReverse",
  "contractProgram_not_mem_reverse",
  "selected_count_pos",
  "selectedContractIndices_length_pos",
  "selectedContractIndexFinset_card_pos",
  "contractMask_exists_true",
  "contractRef_exists",
  "selected_count_le_four",
  "selectedContractIndices_length_le_four",
  "selectedContractIndexFinset_card_le_four",
  "contractMask_countFalse_pos_of_contractEdgeSize_gt_four",
  "contractMask_exists_false_of_contractEdgeSize_gt_four",
  "contractMask_hasFalse_of_contractEdgeSize_gt_four",
  "contractRef_missing_of_contractEdgeSize_gt_four",
  "triad_of_selected_count_eq_four",
  "exists_triadAt_of_selected_count_eq_four",
  "exists_triadAtSources_of_selected_count_eq_four",
  "exists_triadAtSources_count_gt_two_of_selected_count_eq_four",
  "triad_of_selectedContractIndices_length_eq_four",
  "exists_triadAt_of_selectedContractIndices_length_eq_four",
  "exists_triadAtSources_of_selectedContractIndices_length_eq_four",
  "exists_triadAtSources_count_gt_two_of_selectedContractIndices_length_eq_four",
  "triad_of_selectedContractIndexFinset_card_eq_four",
  "exists_triadAtSources_of_selectedContractIndexFinset_card_eq_four",
  "exists_triadAtSources_count_gt_two_of_selectedContractIndexFinset_card_eq_four",
  "selected_count_le_three_of_ne_four",
  "selectedContractIndices_length_le_three_of_ne_four",
  "selectedContractIndexFinset_card_le_three_of_ne_four",
  "selected_count_eq_four_or_le_three",
  "selected_count_eq_four_or_between",
  "selectedContractIndices_length_eq_four_or_between",
  "selectedContractIndexFinset_card_eq_four_or_between"
]

/-- The complete indexed/range consequence registry. -/
def checkedConsequenceNames : Array String :=
  contractTreeConsequenceNames.insertIdx 6 "contractTree_exists"

def checkedNormalizedConsequenceNames : Array String := #[
  "contractTree_mem_cpColorSpec_of_branch_proper",
  "contractTree_mem_cpColorSpec_noReverse_of_branch_proper",
  "contractTree_mem_trace_normalized_of_branch_proper"
]

private def addCheckedTheorem
    (name : Name) (levelParams : List Name) (type value : Expr) :
    TermElabM Unit := do
  if (← getEnv).contains name then
    throwError "declaration {name} already exists"
  unless ← isDefEq (← inferType value) type do
    throwError "generated value for {name} has the wrong type"
  addAndCompile <| Declaration.thmDecl {
    name
    levelParams
    type
    value
  }

/-- Specialize every polymorphic `contractTreeWith_*` consequence to one of
the two public contract-tree constructors. -/
private def liftContractTreeDecl
    (configNamespace : Name) (targetPrefix short : String) :
    TermElabM Unit := do
  let sourceName := Name.str configNamespace s!"contractTreeWith_{short}"
  let targetName := Name.str configNamespace s!"{targetPrefix}_{short}"
  let targetFunctionName := Name.str configNamespace targetPrefix
  let sourceInfo ← getConstInfo sourceName
  forallTelescope sourceInfo.type fun sourceArgs sourceResult => do
    unless sourceArgs.size >= 4 do
      throwError "{sourceName}: expected colorTree/cf/ct/proof binders"
    let colorTree := sourceArgs[0]!
    let cf := sourceArgs[1]!
    let ct := sourceArgs[2]!
    let sourceProof := sourceArgs[3]!
    let trailing := sourceArgs[4:]
    for arg in trailing do
      let argType ← inferType arg
      if argType.containsFVar colorTree.fvarId! ||
          argType.containsFVar sourceProof.fvarId! then
        throwError "{sourceName}: trailing binder depends on an erased binder"
    if sourceResult.containsFVar colorTree.fvarId! ||
        sourceResult.containsFVar sourceProof.fvarId! then
      throwError "{sourceName}: result depends on an erased binder"
    let targetTree := mkApp (mkConst targetFunctionName) cf
    let someCt ← mkAppM ``Option.some #[ct]
    let targetProofType ← mkAppM ``Eq #[targetTree, someCt]
    withLocalDecl `h .default targetProofType fun h => do
      let sourceValue ← mkAppM sourceName (#[h] ++ trailing)
      let targetArgs := #[cf, ct, h] ++ trailing
      let targetType ← mkForallFVars targetArgs sourceResult
      let targetValue ← mkLambdaFVars targetArgs sourceValue
      addCheckedTheorem targetName sourceInfo.levelParams
        targetType targetValue

syntax (name := liftContractTreeConsequenceApi)
  "lift_contract_tree_consequence_api " ident : command

elab_rules : command
  | `(lift_contract_tree_consequence_api $target:ident) => liftTermElabM do
      let configNamespace ← getCurrNamespace
      for short in contractTreeConsequenceNames do
        liftContractTreeDecl configNamespace target.getId.toString short

/-- Generate the executable-checker consequences from the specification
contract-tree API and `checkReducible_contractTree_exists`. -/
private def liftCheckReducibleDecl
    (configNamespace : Name) (short : String) : TermElabM Unit := do
  let sourceName := Name.str configNamespace s!"contractTree_{short}"
  let targetName := Name.str configNamespace s!"checkReducible_{short}"
  let checkerName := Name.str configNamespace "checkReducible"
  let existsName :=
    Name.str configNamespace "checkReducible_contractTree_exists"
  let sourceInfo ← getConstInfo sourceName
  forallTelescope sourceInfo.type fun sourceArgs sourceResult => do
    unless sourceArgs.size >= 3 do
      throwError "{sourceName}: expected cf/ct/proof binders"
    let cf := sourceArgs[0]!
    let ct := sourceArgs[1]!
    let sourceProof := sourceArgs[2]!
    let trailing := sourceArgs[3:]
    for arg in trailing do
      let argType ← inferType arg
      if argType.containsFVar ct.fvarId! ||
          argType.containsFVar sourceProof.fvarId! then
        throwError "{sourceName}: trailing binder depends on its tree witness"
    if sourceResult.containsFVar ct.fvarId! ||
        sourceResult.containsFVar sourceProof.fvarId! then
      throwError "{sourceName}: result depends on its tree witness"
    let checked := mkApp (mkConst checkerName) cf
    let checkedTrue ← mkAppM ``Eq #[checked, mkConst ``Bool.true]
    withLocalDecl `hcheck .default checkedTrue fun hcheck => do
      let existsValue ← mkAppM existsName #[hcheck]
      let targetCt ← mkAppM ``Exists.choose #[existsValue]
      let targetProof ← mkAppM ``Exists.choose_spec #[existsValue]
      let sourceValue ←
        mkAppM sourceName (#[targetProof] ++ trailing)
      let targetArgs := #[cf, hcheck] ++ trailing
      let targetType ← mkForallFVars targetArgs sourceResult
      let targetValue ← mkLambdaFVars targetArgs sourceValue
      -- Force the witness metavariable to the value selected above before
      -- checking the generated declaration.
      discard <| inferType targetCt
      addCheckedTheorem targetName sourceInfo.levelParams
        targetType targetValue

syntax (name := liftCheckReducibleConsequenceApi)
  "lift_check_reducible_consequence_api" : command

elab_rules : command
  | `(lift_check_reducible_consequence_api) => liftTermElabM do
      let configNamespace ← getCurrNamespace
      for short in contractTreeConsequenceNames do
        liftCheckReducibleDecl configNamespace short

private def replaceExprs (replacements : ExprMap Expr) (e : Expr) : Expr :=
  e.replace fun subterm => replacements[subterm]?

private partial def withReplacedLocals
    (sourceArgs : Array Expr) (index : Nat)
    (replacements : ExprMap Expr) (targetArgs : Array Expr)
    (k : ExprMap Expr → Array Expr → TermElabM Unit) :
    TermElabM Unit := do
  if hindex : index < sourceArgs.size then
    let sourceArg := sourceArgs[index]
    let sourceDecl ← getFVarLocalDecl sourceArg
    let targetType := replaceExprs replacements sourceDecl.type
    withLocalDecl sourceDecl.userName sourceDecl.binderInfo targetType
        fun targetArg =>
      withReplacedLocals sourceArgs (index + 1)
        (replacements.insert sourceArg targetArg)
        (targetArgs.push targetArg) k
  else
    k replacements targetArgs

/-- Specialize the checker consequences to `cfs.getD i default`, producing
the established `CheckedAt.*` API without copying any result statement. -/
private def liftCheckedAtDecl
    (configNamespace : Name) (short : String) : TermElabM Unit := do
  let sourceName := Name.str configNamespace s!"checkReducible_{short}"
  let checkedAtNamespace := Name.str configNamespace "CheckedAt"
  let targetName := Name.str checkedAtNamespace short
  let checkedAtName := Name.str configNamespace "CheckedAt"
  let defaultName := Name.str configNamespace "default"
  let configName := configNamespace
  let sourceInfo ← getConstInfo sourceName
  forallTelescope sourceInfo.type fun sourceArgs sourceResult => do
    unless sourceArgs.size >= 2 do
      throwError "{sourceName}: expected cf/checker-proof binders"
    let cf := sourceArgs[0]!
    let sourceProof := sourceArgs[1]!
    let trailing := sourceArgs[2:]
    for arg in trailing do
      if (← inferType arg).containsFVar sourceProof.fvarId! then
        throwError "{sourceName}: trailing binder depends on its checker proof"
    if sourceResult.containsFVar sourceProof.fvarId! then
      throwError "{sourceName}: result depends on its checker proof"
    let listConfig :=
      mkApp (mkConst ``List [Level.zero]) (mkConst configName)
    withLocalDecl `cfs .implicit listConfig fun cfs =>
      withLocalDecl `i .implicit (mkConst ``Nat) fun i => do
        let selectedConfig ←
          mkAppM ``List.getD #[cfs, i, mkConst defaultName]
        let checkedAt := mkApp2 (mkConst checkedAtName) cfs i
        withLocalDecl `h .default checkedAt fun h => do
          let replacements : ExprMap Expr :=
            ({} : ExprMap Expr)
              |>.insert cf selectedConfig
              |>.insert sourceProof h
          withReplacedLocals trailing 0 replacements #[]
              fun finalReplacements targetTrailing => do
            let targetResult := replaceExprs finalReplacements sourceResult
            let sourceValue ←
              mkAppM sourceName (#[h] ++ targetTrailing)
            let targetArgs := #[cfs, i, h] ++ targetTrailing
            let targetType ← mkForallFVars targetArgs targetResult
            let targetValue ← mkLambdaFVars targetArgs sourceValue
            addCheckedTheorem targetName sourceInfo.levelParams
              targetType targetValue

syntax (name := liftCheckedAtConsequenceApi)
  "lift_checked_at_consequence_api" : command

elab_rules : command
  | `(lift_checked_at_consequence_api) => liftTermElabM do
      let configNamespace ← getCurrNamespace
      for short in checkedConsequenceNames do
        liftCheckedAtDecl configNamespace short

end Schematic.Math.GraphTheory.FourColor.Config
