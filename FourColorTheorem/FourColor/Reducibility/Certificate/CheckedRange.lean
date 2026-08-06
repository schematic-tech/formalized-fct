import FourColorTheorem.FourColor.Reducibility.Certificate.CheckedAt

/-! Semantic consequences for half-open ranges of checked configurations. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

/-- All configurations in the half-open range `[j1, j2)` pass the executable
checker. -/
def CheckedInRange (j1 j2 : Nat) (cfs : List Config) : Prop :=
  ∀ i, j1 ≤ i → i < j2 → CheckedAt cfs i

/-! The range API below deliberately mirrors the pointwise `CheckedAt` API.
The declaration generator makes the pointwise API the single source of truth
while retaining every established range theorem name and type. -/

open Lean Elab Command Meta


/-- Generate the range lifting of one pointwise `CheckedAt` consequence.

The source must have the shape
`{cfs} → {i} → CheckedAt cfs i → ...`. The elaborator checks that shape
and that the pointwise proof is absent from every remaining binder and the
result, so API drift produces an error at the declaration site. -/
private def liftCheckedAtInRangeDecl
    (rangeNamespace : Name) (short : String) : TermElabM Unit := do
  let configNamespace := rangeNamespace.getPrefix
  let checkedAtName := Name.str configNamespace "CheckedAt"
  let sourceName := Name.str checkedAtName short
  let targetName := Name.str rangeNamespace short
  if (← getEnv).contains targetName then
    throwError "declaration {targetName} already exists"
  let sourceInfo ← getConstInfo sourceName
  let levels := sourceInfo.levelParams.map Level.param
  forallTelescope sourceInfo.type fun sourceArgs sourceResult => do
    let mut checkedProofIndex? : Option Nat := none
    for index in [:sourceArgs.size] do
      let argType ← inferType sourceArgs[index]!
      if argType.getAppFn.constName? == some checkedAtName then
        if checkedProofIndex?.isSome then
          throwError "{sourceName} has more than one CheckedAt hypothesis"
        checkedProofIndex? := some index
    let some checkedProofIndex := checkedProofIndex?
      | throwError "{sourceName} has no CheckedAt hypothesis"
    unless checkedProofIndex == 2 do
      throwError "{sourceName}: expected CheckedAt as binder 3, found binder {checkedProofIndex + 1}"
    let cfs := sourceArgs[0]!
    let i := sourceArgs[1]!
    let checkedProof := sourceArgs[checkedProofIndex]!
    let checkedType ← inferType checkedProof
    let checkedArgs := checkedType.getAppArgs
    unless checkedArgs.size == 2 && checkedArgs[0]! == cfs &&
        checkedArgs[1]! == i do
      throwError "{sourceName}: CheckedAt hypothesis does not use the leading cfs/i binders"
    let trailing := sourceArgs[(checkedProofIndex + 1):]
    for arg in trailing do
      if (← inferType arg).containsFVar checkedProof.fvarId! then
        throwError "{sourceName}: trailing binder depends on its CheckedAt proof"
    if sourceResult.containsFVar checkedProof.fvarId! then
      throwError "{sourceName}: result depends on its CheckedAt proof"
    let natType := mkConst ``Nat
    withLocalDecl `j1 .implicit natType fun j1 =>
      withLocalDecl `j2 .implicit natType fun j2 => do
        let checkedInRangeType :=
          mkApp3 (mkConst (Name.str configNamespace "CheckedInRange"))
            j1 j2 cfs
        withLocalDecl `h .default checkedInRangeType fun h => do
          let hi1Type ← mkAppM ``LE.le #[j1, i]
          let hi2Type ← mkAppM ``LT.lt #[i, j2]
          withLocalDecl `hi1 .default hi1Type fun hi1 =>
            withLocalDecl `hi2 .default hi2Type fun hi2 => do
              let checkedAt := mkApp3 h i hi1 hi2
              let sourceAppliedArgs :=
                (#[] |>.append sourceArgs[:checkedProofIndex]
                  |>.push checkedAt |>.append trailing)
              let sourceValue :=
                mkAppN (mkConst sourceName levels) sourceAppliedArgs
              let targetArgs :=
                #[j1, j2, cfs, h, i, hi1, hi2] ++ trailing
              let targetType ← mkForallFVars targetArgs sourceResult
              let targetValue ← mkLambdaFVars targetArgs sourceValue
              unless ← isDefEq (← inferType targetValue) targetType do
                throwError "generated value for {targetName} has the wrong type"
              addAndCompile <| Declaration.thmDecl {
                name := targetName
                levelParams := sourceInfo.levelParams
                type := targetType
                value := targetValue
              }

syntax (name := liftCheckedAtInRangeApi) "lift_checked_at_in_range_api" : command

elab_rules : command
  | `(lift_checked_at_in_range_api) => liftTermElabM do
      let rangeNamespace ← getCurrNamespace
      for short in checkedConsequenceNames do
        liftCheckedAtInRangeDecl rangeNamespace short

namespace CheckedInRange

lift_checked_at_in_range_api

end CheckedInRange

/-- Lift the complete `CheckedInRange` consequence API through an executable
Boolean checker and its soundness theorem.  Besides sharing the consequence
list, this validates the expected range-proof binder and the bridge result, so
the generated public signatures cannot silently drift. -/
private def liftCheckedRangeDecl
    (configNamespace : Name) (checker bridge : String) (short : String) :
    TermElabM Unit := do
  let checkedInRangeName := Name.str configNamespace "CheckedInRange"
  let sourceName := Name.str checkedInRangeName short
  let checkerName := Name.str configNamespace checker
  let bridgeName := Name.str configNamespace bridge
  let targetName := Name.str configNamespace s!"{checker}_{short}"
  if (← getEnv).contains targetName then
    throwError "declaration {targetName} already exists"
  let sourceInfo ← getConstInfo sourceName
  let levels := sourceInfo.levelParams.map Level.param
  forallTelescope sourceInfo.type fun sourceArgs sourceResult => do
    unless sourceArgs.size >= 7 do
      throwError "{sourceName}: expected at least seven range binders"
    let j1 := sourceArgs[0]!
    let j2 := sourceArgs[1]!
    let cfs := sourceArgs[2]!
    let rangeProof := sourceArgs[3]!
    let rangeProofType ← inferType rangeProof
    let rangeArgs := rangeProofType.getAppArgs
    unless rangeProofType.getAppFn.constName? == some checkedInRangeName &&
        rangeArgs.size == 3 && rangeArgs[0]! == j1 && rangeArgs[1]! == j2 &&
        rangeArgs[2]! == cfs do
      throwError "{sourceName}: binder 4 is not the expected CheckedInRange proof"
    for arg in sourceArgs[4:] do
      if (← inferType arg).containsFVar rangeProof.fvarId! then
        throwError "{sourceName}: trailing binder depends on its range proof"
    if sourceResult.containsFVar rangeProof.fvarId! then
      throwError "{sourceName}: result depends on its range proof"
    let checkerValue := mkApp3 (mkConst checkerName) j1 j2 cfs
    let checkerTrue :=
      mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
        checkerValue (mkConst ``Bool.true)
    withLocalDecl `h .default checkerTrue fun h => do
      let bridgeValue ← mkAppM bridgeName #[h]
      unless ← isDefEq (← inferType bridgeValue) rangeProofType do
        throwError "{bridgeName} does not turn {checkerName} = true into {checkedInRangeName}"
      let sourceAppliedArgs :=
        (#[] |>.append sourceArgs[:3] |>.push bridgeValue
          |>.append sourceArgs[4:])
      let sourceValue :=
        mkAppN (mkConst sourceName levels) sourceAppliedArgs
      let targetArgs :=
        (#[] |>.append sourceArgs[:3] |>.push h |>.append sourceArgs[4:])
      let targetType ← mkForallFVars targetArgs sourceResult
      let targetValue ← mkLambdaFVars targetArgs sourceValue
      unless ← isDefEq (← inferType targetValue) targetType do
        throwError "generated value for {targetName} has the wrong type"
      addAndCompile <| Declaration.thmDecl {
        name := targetName
        levelParams := sourceInfo.levelParams
        type := targetType
        value := targetValue
      }

syntax (name := liftCheckedRangeApi)
  "lift_checked_range_api " ident " using " ident : command

elab_rules : command
  | `(lift_checked_range_api $checker:ident using $bridge:ident) =>
      liftTermElabM do
        let configNamespace ← getCurrNamespace
        for short in checkedConsequenceNames do
          liftCheckedRangeDecl configNamespace checker.getId.toString
            bridge.getId.toString short


private def addTheoremAlias (targetName sourceName : Name) :
    TermElabM Unit := do
  if (← getEnv).contains targetName then
    throwError "declaration {targetName} already exists"
  let sourceInfo ← getConstInfo sourceName
  let levels := sourceInfo.levelParams.map Level.param
  addAndCompile <| Declaration.thmDecl {
    name := targetName
    levelParams := sourceInfo.levelParams
    type := sourceInfo.type
    value := mkConst sourceName levels
  }

/-- Copy the normalized pointwise consequences into the range namespace.
They are index-local facts and therefore need no range hypothesis. -/
syntax (name := liftCheckedNormalizedSourceApi)
  "lift_checked_normalized_source_api" : command

elab_rules : command
  | `(lift_checked_normalized_source_api) => liftTermElabM do
      let configNamespace ← getCurrNamespace
      let sourceNamespace := Name.str configNamespace "CheckedAt"
      let targetNamespace := Name.str configNamespace "CheckedInRange"
      for short in checkedNormalizedConsequenceNames do
        addTheoremAlias (Name.str targetNamespace short)
          (Name.str sourceNamespace short)

/-- Give an executable-checker API the normalized contract-tree consequences
whose proofs do not actually require a checker hypothesis. -/
syntax (name := liftCheckedNormalizedApi)
  "lift_checked_normalized_api " ident : command

elab_rules : command
  | `(lift_checked_normalized_api $checker:ident) => liftTermElabM do
      let configNamespace ← getCurrNamespace
      let sourceNamespace := Name.str configNamespace "CheckedInRange"
      for short in checkedNormalizedConsequenceNames do
        let sourceName := Name.str sourceNamespace short
        let targetName :=
          Name.str configNamespace s!"{checker.getId.toString}_{short}"
        addTheoremAlias targetName sourceName

/-! The normalized contract-tree consequences do not require a checker proof;
they remain direct aliases of the pointwise interface. -/

lift_checked_normalized_source_api

end Config

end FourColor

end Schematic.Math.GraphTheory
