import FourColorTheorem.FourColor.Coloring.CFColor.TraceTrees

/-! A per-trace Boolean interpreter for `CProg.cpColorSpec`. -/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def cpBranchTraceCheck (et et' : ColSeq) : Bool :=
  decide (Color.zero ∉ ColSeq.etail (et.drop 1)) &&
    decide (et' = ColSeq.etail (et.drop 1))

def cpColorStepCheck
    (s : CpStep) (P : ColSeq → ColSeq → Bool) : ColSeq → ColSeq → Bool
  | et, et' =>
      match s with
      | .rotate n => P (CProg.rotateLeft n et) et'
      | .reverseRotate =>
          decide (¬ et.length ≤ 1) && P (CProg.rotateRight 1 et) et'
      | .u =>
          P (Color.one :: Color.one :: et) et' ||
            P (Color.two :: Color.two :: et) et' ||
              P (Color.three :: Color.three :: et) et'
      | .k =>
          match et with
          | e1 :: e2 :: et'' =>
              decide (e1 ≠ e2) && P ((e1 + e2) :: et'') et'
          | _ => false
      | .y =>
          match et with
          | e1 :: et'' =>
              P (EdgePerm.p231 e1 :: EdgePerm.p312 e1 :: et'') et' ||
                P (EdgePerm.p312 e1 :: EdgePerm.p231 e1 :: et'') et'
          | [] => false
      | .h =>
          match et with
          | e1 :: e2 :: et'' =>
              if e1 = e2 then
                P (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: et'') et' ||
                  P (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: et'') et'
              else
                P (e2 :: e1 :: et'') et'
          | _ => false
      | .a =>
          match et with
          | e1 :: e2 :: et'' =>
              decide (e1 = e2) && P (if et'' = [] then et else et'') et'
          | _ => false

def cpColorFoldCheck (cp : CProg) : ColSeq → ColSeq → Bool :=
  cp.foldr cpColorStepCheck cpBranchTraceCheck

def cpColor0Check : CProg → ColSeq → Bool
  | .rotate _ :: cp, et' => cpColor0Check cp et'
  | .y :: cp, et' =>
      cpColorFoldCheck cp [Color.one, Color.two, Color.three] et'
  | .u :: cp, et' =>
      cpColorFoldCheck cp [Color.one, Color.one, Color.two, Color.two] et' ||
        cpColorFoldCheck cp [Color.one, Color.one, Color.one, Color.one] et'
  | cp, et' => cpColorFoldCheck cp [Color.one, Color.one] et'

def cpColorCheck (cp : CProg) (et : ColSeq) : Bool :=
  cpColor0Check cp.reverse (ColSeq.ttail et)

theorem cpBranchTraceCheck_eq_true_iff (et et' : ColSeq) :
    cpBranchTraceCheck et et' = true ↔ CProg.cpBranchTraceSpec et et' := by
  simp [cpBranchTraceCheck, CProg.cpBranchTraceSpec]

theorem cpColorStepCheck_eq_true_iff
    {P : ColSeq → ColSeq → Bool} {Q : ColSeq → ColSeq → Prop}
    (hPQ : ∀ et et', P et et' = true ↔ Q et et')
    (s : CpStep) (et et' : ColSeq) :
    cpColorStepCheck s P et et' = true ↔ CProg.cpColorStepSpec s Q et et' := by
  cases s <;> cases et with
  | nil => simp [cpColorStepCheck, CProg.cpColorStepSpec, hPQ] <;> tauto
  | cons e1 et =>
      cases et with
      | nil => simp [cpColorStepCheck, CProg.cpColorStepSpec, hPQ] <;> tauto
      | cons e2 et =>
          simp [cpColorStepCheck, CProg.cpColorStepSpec, hPQ] <;> tauto

theorem cpColorFoldCheck_eq_true_iff
    (cp : CProg) (et et' : ColSeq) :
    cpColorFoldCheck cp et et' = true ↔ CProg.cpColorFoldSpec cp et et' := by
  induction cp generalizing et et' with
  | nil => exact cpBranchTraceCheck_eq_true_iff et et'
  | cons s cp ih =>
      exact cpColorStepCheck_eq_true_iff
        (fun input output => ih input output) s et et'

theorem cpColor0Check_eq_true_iff (cp : CProg) (et : ColSeq) :
    cpColor0Check cp et = true ↔ CProg.cpColor0Spec cp et := by
  induction cp with
  | nil => exact cpColorFoldCheck_eq_true_iff [] [Color.one, Color.one] et
  | cons step cp ih =>
      cases step <;>
        simp [cpColor0Check, CProg.cpColor0Spec,
          cpColorFoldCheck_eq_true_iff, ih]

theorem cpColorCheck_eq_true_iff (cp : CProg) (et : ColSeq) :
    cpColorCheck cp et = true ↔ CProg.cpColorSpec cp et := by
  exact cpColor0Check_eq_true_iff cp.reverse (ColSeq.ttail et)

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
