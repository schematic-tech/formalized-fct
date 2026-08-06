import FourColorTheorem.FourColor.Reducibility.KernelCertificate.BaseSpec
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

/-! Chunked symbolic execution of configuration colouring programs. -/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

/-- All states admitted by one colouring-program step. -/
def stepSuccessors : CpStep → ColSeq → List ColSeq
  | .rotate n, et => [CProg.rotateLeft n et]
  | .reverseRotate, et =>
      if et.length ≤ 1 then [] else [CProg.rotateRight 1 et]
  | .u, et =>
      [Color.one :: Color.one :: et,
        Color.two :: Color.two :: et,
        Color.three :: Color.three :: et]
  | .k, e1 :: e2 :: et =>
      if e1 = e2 then [] else [(e1 + e2) :: et]
  | .k, _ => []
  | .y, e1 :: et =>
      [EdgePerm.p231 e1 :: EdgePerm.p312 e1 :: et,
        EdgePerm.p312 e1 :: EdgePerm.p231 e1 :: et]
  | .y, [] => []
  | .h, e1 :: e2 :: et =>
      if e1 = e2 then
        [EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: et,
          EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: et]
      else [e2 :: e1 :: et]
  | .h, _ => []
  | .a, e1 :: e2 :: et =>
      if e1 = e2 then [if et = [] then e1 :: e2 :: et else et] else []
  | .a, _ => []

theorem cpColorStepSpec_iff_exists_successor
    (step : CpStep) (P : ColSeq → ColSeq → Prop) (et out : ColSeq) :
    CProg.cpColorStepSpec step P et out ↔
      ∃ next ∈ stepSuccessors step et, P next out := by
  cases step <;> cases et with
  | nil => simp [stepSuccessors, CProg.cpColorStepSpec]
  | cons e1 et =>
      cases et with
      | nil => simp [stepSuccessors, CProg.cpColorStepSpec]
      | cons e2 et =>
          by_cases heq : e1 = e2 <;>
            simp [stepSuccessors, CProg.cpColorStepSpec, heq]

def successorKnown
    (nextLength : Nat) (nextSource : SourceTable) (nextCount : Nat)
    (nextRefs : RefTrie) (next : ColSeq) : Bool :=
  match nextRefs.get next with
  | none => false
  | some ref =>
      decide (ref < nextCount) &&
        match nextSource ref with
        | none => false
        | some code => decide (decodeTrace nextLength code = next)

theorem successorKnown_sound
    {nextLength : Nat} {nextSource : SourceTable} {nextCount : Nat}
    {nextRefs : RefTrie} {next : ColSeq}
    (hknown : successorKnown nextLength nextSource nextCount
      nextRefs next = true) :
    ∃ ref code, ref < nextCount ∧ nextSource ref = some code ∧
      decodeTrace nextLength code = next := by
  unfold successorKnown at hknown
  cases hget : nextRefs.get next with
  | none => simp [hget] at hknown
  | some ref =>
      simp only [hget, Bool.and_eq_true, decide_eq_true_eq] at hknown
      cases hsource : nextSource ref with
      | none => simp [hsource] at hknown
      | some code =>
          simp only [hsource, decide_eq_true_eq] at hknown
          exact ⟨ref, code, hknown.1, hsource, hknown.2⟩

def verifyTransitionRange
    (currentLength : Nat) (currentSource : SourceTable)
    (nextLength : Nat) (nextSource : SourceTable) (nextCount : Nat)
    (nextRefs : RefTrie) (step : CpStep) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
      match currentSource start with
      | none => false
      | some code =>
          (stepSuccessors step (decodeTrace currentLength code)).all
            (successorKnown nextLength nextSource nextCount nextRefs) &&
          verifyTransitionRange currentLength currentSource nextLength
            nextSource nextCount nextRefs step (start + 1) count

def TransitionRangeSound
    (currentLength : Nat) (currentSource : SourceTable)
    (nextLength : Nat) (nextSource : SourceTable) (nextCount : Nat)
    (step : CpStep) (start count : Nat) : Prop :=
  ∀ ref code, start ≤ ref → ref < start + count →
    currentSource ref = some code →
    ∀ next ∈ stepSuccessors step (decodeTrace currentLength code),
      ∃ nextRef nextCode, nextRef < nextCount ∧
        nextSource nextRef = some nextCode ∧
          decodeTrace nextLength nextCode = next

theorem verifyTransitionRange_sound
    {currentLength : Nat} {currentSource : SourceTable}
    {nextLength : Nat} {nextSource : SourceTable} {nextCount : Nat}
    {nextRefs : RefTrie} {step : CpStep} {start count : Nat}
    (hverify : verifyTransitionRange currentLength currentSource nextLength
      nextSource nextCount nextRefs step start count = true) :
    TransitionRangeSound currentLength currentSource nextLength nextSource
      nextCount step start count := by
  induction count generalizing start with
  | zero => intro ref code _ href; omega
  | succ count ih =>
      unfold verifyTransitionRange at hverify
      cases hsource : currentSource start with
      | none => simp [hsource] at hverify
      | some startCode =>
          simp only [hsource, Bool.and_eq_true] at hverify
          intro ref code hrefStart hrefFinish hrefSource next hnext
          by_cases href : ref = start
          · subst ref
            rw [hsource] at hrefSource
            injection hrefSource with hcode
            subst code
            exact successorKnown_sound
              (List.all_eq_true.mp hverify.1 next hnext)
          · exact ih hverify.2 ref code (by omega) (by omega)
              hrefSource next hnext

theorem TransitionRangeSound.concat
    {currentLength : Nat} {currentSource : SourceTable}
    {nextLength : Nat} {nextSource : SourceTable} {nextCount : Nat}
    {step : CpStep} {start left right : Nat}
    (hleft : TransitionRangeSound currentLength currentSource nextLength
      nextSource nextCount step start left)
    (hright : TransitionRangeSound currentLength currentSource nextLength
      nextSource nextCount step (start + left) right) :
    TransitionRangeSound currentLength currentSource nextLength nextSource
      nextCount step start (left + right) := by
  intro ref code hrefStart hrefFinish hsource next hnext
  by_cases href : ref < start + left
  · exact hleft ref code hrefStart href hsource next hnext
  · exact hright ref code (by omega) (by omega) hsource next hnext

def SourceFoldSound
    (P : ColSeq → Prop) (length : Nat) (source : SourceTable)
    (count : Nat) (cp : CProg) : Prop :=
  ∀ ref code, ref < count → source ref = some code →
    ∀ out, CProg.cpColorFoldSpec cp (decodeTrace length code) out → P out

theorem SourceFoldSound.step
    {P : ColSeq → Prop} {currentLength : Nat}
    {currentSource : SourceTable} {currentCount : Nat}
    {nextLength : Nat} {nextSource : SourceTable} {nextCount : Nat}
    {step : CpStep} {cp : CProg}
    (htransition : TransitionRangeSound currentLength currentSource nextLength
      nextSource nextCount step 0 currentCount)
    (hnext : SourceFoldSound P nextLength nextSource nextCount cp) :
    SourceFoldSound P currentLength currentSource currentCount (step :: cp) := by
  intro ref code href hsource out hspec
  have hstep : CProg.cpColorStepSpec step
      (CProg.cpColorFoldSpec cp) (decodeTrace currentLength code) out := by
    simpa [CProg.cpColorFoldSpec] using hspec
  rcases (cpColorStepSpec_iff_exists_successor _ _ _ _).1 hstep with
    ⟨next, hnextMem, htail⟩
  rcases htransition ref code (Nat.zero_le _) (by simpa using href)
      hsource next hnextMem with
    ⟨nextRef, nextCode, hrefNext, hsourceNext, hdecode⟩
  rw [← hdecode] at htail
  exact hnext nextRef nextCode hrefNext hsourceNext out htail

def ttailPreimages (tail : ColSeq) : List ColSeq :=
  [Color.one :: tail,
    Color.two :: ColSeq.perm EdgePerm.p231 tail,
    Color.three :: ColSeq.perm EdgePerm.p312 tail]

theorem mem_ttailPreimages
    {et tail : ColSeq} (hproper : ColSeq.ProperTrace et)
    (htail : ColSeq.ttail et = tail) :
    et ∈ ttailPreimages tail := by
  cases et with
  | nil => simp [ColSeq.ProperTrace, ColSeq.headColor] at hproper
  | cons color et =>
      cases color with
      | zero => simp [ColSeq.ProperTrace, ColSeq.headColor] at hproper
      | one =>
          simp [ttailPreimages, ColSeq.ttail, ColSeq.ProperTrace,
            ColSeq.headColor, EdgePerm.edgeRot] at htail ⊢
          exact htail
      | two =>
          simp [ttailPreimages, ColSeq.ttail, ColSeq.ProperTrace,
            ColSeq.headColor, EdgePerm.edgeRot] at htail ⊢
          have hinv := ColSeq.perm_inv EdgePerm.p312 et
          simpa [htail] using hinv.symm
      | three =>
          simp [ttailPreimages, ColSeq.ttail, ColSeq.ProperTrace,
            ColSeq.headColor, EdgePerm.edgeRot] at htail ⊢
          have hinv := ColSeq.perm_inv EdgePerm.p231 et
          simpa [htail] using hinv.symm

def verifyPreimages
    (h : Nat) (source : SourceTable) (limit : Nat)
    (refs : RefTrie) (tail : ColSeq) : Bool :=
  (ttailPreimages tail).all (targetKnown h source limit refs)

theorem verifyPreimages_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {limit : Nat}
    {refs : RefTrie} {tail : ColSeq}
    (hsound : SourceSound h P source limit)
    (hverify : verifyPreimages h source limit refs tail = true) :
    ∀ et, ColSeq.ProperTrace et → ColSeq.ttail et = tail →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro et hproper httail
  apply targetKnown_coclosure hsound
  exact List.all_eq_true.mp hverify et (mem_ttailPreimages hproper httail)

def verifyFinalRange
    (stateLength : Nat) (stateSource : SourceTable)
    (h : Nat) (source : SourceTable) (limit : Nat) (refs : RefTrie) :
    Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
      match stateSource start with
      | none => false
      | some code =>
          verifyPreimages h source limit refs
              (ColSeq.etail ((decodeTrace stateLength code).drop 1)) &&
            verifyFinalRange stateLength stateSource h source limit refs
              (start + 1) count

/-- Every proper trace normalising to `tail` is already in the certified
Kempe coclosure. -/
def TargetCoclosure (P : ColSeq → Prop) (tail : ColSeq) : Prop :=
  ∀ et, ColSeq.ProperTrace et → ColSeq.ttail et = tail →
    Chromogram.KempeCoclosure P (ColSeq.ctrace et)

def FinalRangeSound
    (P : ColSeq → Prop) (stateLength : Nat) (stateSource : SourceTable)
    (start count : Nat) : Prop :=
  ∀ ref code, start ≤ ref → ref < start + count →
    stateSource ref = some code →
    ∀ out, CProg.cpBranchTraceSpec (decodeTrace stateLength code) out →
      TargetCoclosure P out

theorem verifyFinalRange_sound
    {P : ColSeq → Prop} {stateLength : Nat} {stateSource : SourceTable}
    {h : Nat} {source : SourceTable} {limit : Nat} {refs : RefTrie}
    {start count : Nat}
    (hsound : SourceSound h P source limit)
    (hverify : verifyFinalRange stateLength stateSource h source limit refs
      start count = true) :
    FinalRangeSound P stateLength stateSource start count := by
  induction count generalizing start with
  | zero => intro ref code _ href; omega
  | succ count ih =>
      unfold verifyFinalRange at hverify
      cases hsource : stateSource start with
      | none => simp [hsource] at hverify
      | some startCode =>
          simp only [hsource, Bool.and_eq_true] at hverify
          intro ref code hrefStart hrefFinish hrefSource out hbranch
          by_cases href : ref = start
          · subst ref
            rw [hsource] at hrefSource
            injection hrefSource with hcode
            subst code
            rw [hbranch.2]
            exact verifyPreimages_sound hsound hverify.1
          · exact ih hverify.2 ref code (by omega) (by omega)
              hrefSource out hbranch

theorem FinalRangeSound.concat
    {P : ColSeq → Prop} {stateLength : Nat} {stateSource : SourceTable}
    {start left right : Nat}
    (hleft : FinalRangeSound P stateLength stateSource start left)
    (hright : FinalRangeSound P stateLength stateSource
      (start + left) right) :
    FinalRangeSound P stateLength stateSource start (left + right) := by
  intro ref code hrefStart hrefFinish hsource out hbranch
  by_cases href : ref < start + left
  · exact hleft ref code hrefStart href hsource out hbranch
  · exact hright ref code (by omega) (by omega) hsource out hbranch

theorem FinalRangeSound.sourceFoldSound
    {P : ColSeq → Prop} {stateLength : Nat} {stateSource : SourceTable}
    {count : Nat}
    (hsound : FinalRangeSound P stateLength stateSource 0 count) :
    SourceFoldSound (TargetCoclosure P) stateLength stateSource count [] := by
  intro ref code href hsource out hbranch
  exact hsound ref code (Nat.zero_le ref) (by simpa using href)
    hsource out (by simpa [CProg.cpColorFoldSpec] using hbranch)

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
