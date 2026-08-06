import FourColorTheorem.FourColor.Reducibility.KernelCertificate.BaseSpec
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

/-! Deterministic witnesses for membership in a configuration colouring tree. -/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

/-- Follow one chosen branch of a colouring-program step.  Deterministic
steps preserve the witness; binary and ternary steps consume one digit. -/
def cpColorStepChoice
    (s : CpStep) (witness : Nat) (et : ColSeq) : Option (ColSeq × Nat) :=
  match s with
  | .rotate n => some (CProg.rotateLeft n et, witness)
  | .reverseRotate =>
      if et.length ≤ 1 then none else some (CProg.rotateRight 1 et, witness)
  | .u =>
      match witness % 3 with
      | 0 => some (Color.one :: Color.one :: et, witness / 3)
      | 1 => some (Color.two :: Color.two :: et, witness / 3)
      | _ => some (Color.three :: Color.three :: et, witness / 3)
  | .k =>
      match et with
      | e1 :: e2 :: rest =>
          if e1 = e2 then none else some ((e1 + e2) :: rest, witness)
      | _ => none
  | .y =>
      match et with
      | e1 :: rest =>
          if witness % 2 = 0 then
            some (EdgePerm.p231 e1 :: EdgePerm.p312 e1 :: rest, witness / 2)
          else
            some (EdgePerm.p312 e1 :: EdgePerm.p231 e1 :: rest, witness / 2)
      | [] => none
  | .h =>
      match et with
      | e1 :: e2 :: rest =>
          if e1 = e2 then
            if witness % 2 = 0 then
              some (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest, witness / 2)
            else
              some (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest, witness / 2)
          else
            some (e2 :: e1 :: rest, witness)
      | _ => none
  | .a =>
      match et with
      | e1 :: e2 :: rest =>
          if e1 = e2 then
            some (if rest = [] then et else rest, witness)
          else
            none
      | _ => none

theorem cpColorStepChoice_sound
    {s : CpStep} {witness : Nat} {et next : ColSeq} {rest : Nat}
    (hchoice : cpColorStepChoice s witness et = some (next, rest))
    {P : ColSeq → ColSeq → Prop} {out : ColSeq}
    (hnext : P next out) :
    CProg.cpColorStepSpec s P et out := by
  cases s with
  | rotate n =>
      simp only [cpColorStepChoice] at hchoice
      injection hchoice with hpair
      cases hpair
      exact hnext
  | reverseRotate =>
      simp only [cpColorStepChoice] at hchoice
      split at hchoice
      · contradiction
      · injection hchoice with hpair
        cases hpair
        exact And.intro ‹¬ et.length ≤ 1› hnext
  | u =>
      simp only [cpColorStepChoice] at hchoice
      split at hchoice
      · injection hchoice with hpair
        cases hpair
        exact Or.inl hnext
      · injection hchoice with hpair
        cases hpair
        exact Or.inr (Or.inl hnext)
      · injection hchoice with hpair
        cases hpair
        exact Or.inr (Or.inr hnext)
  | k =>
      cases et with
      | nil => simp [cpColorStepChoice] at hchoice
      | cons e1 et =>
          cases et with
          | nil => simp [cpColorStepChoice] at hchoice
          | cons e2 rest' =>
              simp only [cpColorStepChoice] at hchoice
              split at hchoice
              · contradiction
              · injection hchoice with hpair
                cases hpair
                exact And.intro ‹e1 ≠ e2› hnext
  | y =>
      cases et with
      | nil => simp [cpColorStepChoice] at hchoice
      | cons e rest' =>
          simp only [cpColorStepChoice] at hchoice
          split at hchoice
          · injection hchoice with hpair
            cases hpair
            exact Or.inl hnext
          · injection hchoice with hpair
            cases hpair
            exact Or.inr hnext
  | h =>
      cases et with
      | nil => simp [cpColorStepChoice] at hchoice
      | cons e1 et =>
          cases et with
          | nil => simp [cpColorStepChoice] at hchoice
          | cons e2 rest' =>
              simp only [cpColorStepChoice] at hchoice
              split at hchoice
              · split at hchoice
                · injection hchoice with hpair
                  cases hpair
                  simp only [CProg.cpColorStepSpec, if_pos ‹e1 = e2›]
                  exact Or.inl hnext
                · injection hchoice with hpair
                  cases hpair
                  simp only [CProg.cpColorStepSpec, if_pos ‹e1 = e2›]
                  exact Or.inr hnext
              · injection hchoice with hpair
                cases hpair
                simp only [CProg.cpColorStepSpec, if_neg ‹e1 ≠ e2›]
                exact hnext
  | a =>
      cases et with
      | nil => simp [cpColorStepChoice] at hchoice
      | cons e1 et =>
          cases et with
          | nil => simp [cpColorStepChoice] at hchoice
          | cons e2 rest' =>
              simp only [cpColorStepChoice] at hchoice
              split at hchoice
              · injection hchoice with hpair
                cases hpair
                exact And.intro ‹e1 = e2› hnext
              · contradiction

/-- Check one deterministic witness for `cpColorFoldSpec`. -/
def cpColorFoldWitnessCheck : CProg → Nat → ColSeq → ColSeq → Bool
  | [], _, et, out => cpBranchTraceCheck et out
  | step :: cp, witness, et, out =>
      match cpColorStepChoice step witness et with
      | none => false
      | some (next, rest) => cpColorFoldWitnessCheck cp rest next out

theorem cpColorFoldWitnessCheck_sound
    {cp : CProg} {witness : Nat} {et out : ColSeq}
    (hcheck : cpColorFoldWitnessCheck cp witness et out = true) :
    CProg.cpColorFoldSpec cp et out := by
  induction cp generalizing witness et with
  | nil =>
      exact (cpBranchTraceCheck_eq_true_iff et out).1 hcheck
  | cons step cp ih =>
      unfold cpColorFoldWitnessCheck at hcheck
      cases hchoice : cpColorStepChoice step witness et with
      | none => simp [hchoice] at hcheck
      | some chosen =>
          rcases chosen with ⟨next, rest⟩
          rw [hchoice] at hcheck
          exact cpColorStepChoice_sound hchoice (ih hcheck)

/-- Check the initial symmetry-reduced colouring-program cases using one
deterministic fold witness. -/
def cpColor0WitnessCheck : CProg → Nat → ColSeq → Bool
  | .rotate _ :: cp, witness, out => cpColor0WitnessCheck cp witness out
  | .y :: cp, witness, out =>
      cpColorFoldWitnessCheck cp witness
        [Color.one, Color.two, Color.three] out
  | .u :: cp, witness, out =>
      if witness % 2 = 0 then
        cpColorFoldWitnessCheck cp (witness / 2)
          [Color.one, Color.one, Color.two, Color.two] out
      else
        cpColorFoldWitnessCheck cp (witness / 2)
          [Color.one, Color.one, Color.one, Color.one] out
  | cp, witness, out =>
      cpColorFoldWitnessCheck cp witness [Color.one, Color.one] out

theorem cpColor0WitnessCheck_sound
    {cp : CProg} {witness : Nat} {out : ColSeq}
    (hcheck : cpColor0WitnessCheck cp witness out = true) :
    CProg.cpColor0Spec cp out := by
  induction cp with
  | nil => exact cpColorFoldWitnessCheck_sound hcheck
  | cons step cp ih =>
      cases step with
      | rotate n => exact ih hcheck
      | y => exact cpColorFoldWitnessCheck_sound hcheck
      | u =>
          simp only [cpColor0WitnessCheck] at hcheck
          split at hcheck
          · exact Or.inl (cpColorFoldWitnessCheck_sound hcheck)
          · exact Or.inr (cpColorFoldWitnessCheck_sound hcheck)
      | k => exact cpColorFoldWitnessCheck_sound hcheck
      | h => exact cpColorFoldWitnessCheck_sound hcheck
      | a => exact cpColorFoldWitnessCheck_sound hcheck
      | reverseRotate => exact cpColorFoldWitnessCheck_sound hcheck

/-- Check a compact witness for membership in `cpColorSpec`. -/
def cpColorWitnessCheck
    (cp : CProg) (witness : Nat) (et : ColSeq) : Bool :=
  cpColor0WitnessCheck cp.reverse witness (ColSeq.ttail et)

theorem cpColorWitnessCheck_sound
    {cp : CProg} {witness : Nat} {et : ColSeq}
    (hcheck : cpColorWitnessCheck cp witness et = true) :
    CProg.cpColorSpec cp et :=
  cpColor0WitnessCheck_sound hcheck

/-- Verify consecutive source entries using one deterministic configuration
colouring witness per entry. -/
def verifyBaseWitnesses
    (h : Nat) (cp : CProg) (source : SourceTable) :
    Nat → List Nat → Bool
  | _, [] => true
  | start, witness :: witnesses =>
      match source start with
      | none => false
      | some code =>
          cpColorWitnessCheck cp witness (decodeTrace h code) &&
            verifyBaseWitnesses h cp source (start + 1) witnesses

theorem verifyBaseWitnesses_sound
    {h : Nat} {P : ColSeq → Prop} {cp : CProg} {source : SourceTable}
    {start : Nat} {witnesses : List Nat}
    (haccepted : ∀ et, CProg.cpColorSpec cp et →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hsound : SourceSound h P source start)
    (hverify : verifyBaseWitnesses h cp source start witnesses = true) :
    SourceSound h P source (start + witnesses.length) := by
  induction witnesses generalizing start with
  | nil => simpa using hsound
  | cons witness witnesses ih =>
      unfold verifyBaseWitnesses at hverify
      cases hsource : source start with
      | none => simp [hsource] at hverify
      | some code =>
          simp only [hsource, Bool.and_eq_true] at hverify
          have hclosure := haccepted (decodeTrace h code)
            (cpColorWitnessCheck_sound hverify.1)
          have hnext := hsound.succ hsource hclosure
          have hresult := ih hnext hverify.2
          have heq : start + (witnesses.length + 1) =
              start + 1 + witnesses.length := by omega
          change SourceSound h P source (start + (witnesses.length + 1))
          rw [heq]
          exact hresult

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
