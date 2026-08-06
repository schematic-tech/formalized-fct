import FourColorTheorem.FourColor.Coloring.CFColor.Branches

/-!
One-step configuration-colouring operations and their relational specification.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Add the same colour twice at the front of a trace before delegating to
`f`. -/
def sameHead (f : ColSeq → CTree) (c : Color) (et : ColSeq) : CTree :=
  f (c :: c :: et)

/-- One configuration-program step of the trace-colouring tree iterator. -/
def cpColorStep (s : CpStep) (f : ColSeq → CTree) (et : ColSeq) : CTree :=
  match s with
  | CpStep.rotate n => f (CProg.rotateLeft n et)
  | CpStep.reverseRotate =>
      if et.length ≤ 1 then CTree.empty else f (rotateRight 1 et)
  | CpStep.u =>
      CTree.union (sameHead f Color.one et)
        (CTree.union (sameHead f Color.two et) (sameHead f Color.three et))
  | CpStep.k =>
      match et with
      | e1 :: e2 :: et' =>
          if e1 = e2 then CTree.empty else f ((e1 + e2) :: et')
      | _ => CTree.empty
  | CpStep.y =>
      match et with
      | e1 :: et' =>
          let e2 := EdgePerm.p231 e1
          let e3 := EdgePerm.p312 e1
          CTree.union (f (e2 :: e3 :: et')) (f (e3 :: e2 :: et'))
      | _ => CTree.empty
  | CpStep.h =>
      match et with
      | e1 :: e2 :: et' =>
          if e1 = e2 then
            CTree.union (sameHead f (EdgePerm.p231 e1) et')
              (sameHead f (EdgePerm.p312 e1) et')
          else
            f (e2 :: e1 :: et')
      | _ => CTree.empty
  | CpStep.a =>
      match et with
      | e1 :: e2 :: et' =>
          if e1 = e2 then f (if et' = [] then et else et') else CTree.empty
      | _ => CTree.empty

/-- Exact trace predicate represented by `cpBranch`.  It is false for bad
normalised tails containing `Color.zero`. -/
def cpBranchTraceSpec (et et' : ColSeq) : Prop :=
  Color.zero ∉ ColSeq.etail (et.drop 1) ∧
    et' = ColSeq.etail (et.drop 1)

/-- Predicate transformer represented by one executable `cpColorStep`. -/
def cpColorStepSpec
    (s : CpStep) (P : ColSeq → ColSeq → Prop) :
    ColSeq → ColSeq → Prop
  | et, et' =>
      match s with
      | CpStep.rotate n => P (CProg.rotateLeft n et) et'
      | CpStep.reverseRotate =>
          ¬ et.length ≤ 1 ∧ P (rotateRight 1 et) et'
      | CpStep.u =>
          P (Color.one :: Color.one :: et) et' ∨
            P (Color.two :: Color.two :: et) et' ∨
              P (Color.three :: Color.three :: et) et'
      | CpStep.k =>
          match et with
          | e1 :: e2 :: et'' =>
              e1 ≠ e2 ∧ P ((e1 + e2) :: et'') et'
          | _ => False
      | CpStep.y =>
          match et with
          | e1 :: et'' =>
              P (EdgePerm.p231 e1 :: EdgePerm.p312 e1 :: et'') et' ∨
                P (EdgePerm.p312 e1 :: EdgePerm.p231 e1 :: et'') et'
          | [] => False
      | CpStep.h =>
          match et with
          | e1 :: e2 :: et'' =>
              if e1 = e2 then
                P (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: et'') et' ∨
                  P (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: et'') et'
              else
                P (e2 :: e1 :: et'') et'
          | _ => False
      | CpStep.a =>
          match et with
          | e1 :: e2 :: et'' =>
              e1 = e2 ∧ P (if et'' = [] then et else et'') et'
          | _ => False

theorem cpBranch_mem_iff (et et' : ColSeq) :
    CTree.mem (cpBranch et) et' = true ↔ cpBranchTraceSpec et et' := by
  simp [cpBranchTraceSpec, cpBranch, CTree.mem_ofTtail_iff_total]

theorem cpBranch_mem_length
    {et et' : ColSeq}
    (hmem : CTree.mem (cpBranch et) et' = true) :
    et'.length = (ColSeq.etail (et.drop 1)).length := by
  exact congrArg List.length ((cpBranch_mem_iff et et').1 hmem).2

theorem cpBranchTraceSpec_length
    {et et' : ColSeq}
    (hspec : cpBranchTraceSpec et et') :
    et'.length = (ColSeq.etail (et.drop 1)).length := by
  exact congrArg List.length hspec.2

theorem cpBranchTraceSpec_length_add_two
    {et et' : ColSeq}
    (hspec : cpBranchTraceSpec et et') :
    et'.length + 2 = et.length := by
  have hproper :
      ColSeq.ProperTrace (et.drop 1) :=
    ((ColSeq.not_mem_zero_etail_iff (et.drop 1)).1 hspec.1).1
  have htailLen := ColSeq.length_etail_of_proper hproper
  have hdropLen : (et.drop 1).length + 1 = et.length := by
    cases et with
    | nil =>
        simp [ColSeq.ProperTrace, ColSeq.headColor] at hproper
    | cons e et =>
        simp
  rw [hspec.2]
  omega

theorem cpBranch_mem_length_add_two
    {et et' : ColSeq}
    (hmem : CTree.mem (cpBranch et) et' = true) :
    et'.length + 2 = et.length :=
  cpBranchTraceSpec_length_add_two ((cpBranch_mem_iff et et').1 hmem)


end CProg

end FourColor

end Schematic.Math.GraphTheory
