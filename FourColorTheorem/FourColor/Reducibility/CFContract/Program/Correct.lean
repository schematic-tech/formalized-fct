import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Y
import FourColorTheorem.FourColor.Reducibility.CFContract.Program.H
import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Induction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Coq `cfctr_correct`: every successful execution of the contraction
program has the coloring semantics specified by `ContractProgramCorrect`. -/
theorem contractProgram_correct
    {mr mc : List Bool} {cp cpc : CProg}
    (hmr : mr.length = CProg.ringSize cp)
    (hmc : mc.length = CProg.contractEdgeSize cp)
    (hrun : CProg.contractProgram mr mc cp = some cpc) :
    ContractProgramCorrect mr mc cp cpc := by
  apply CFContract.Internal.contractProgram_induction
    (P := fun mr mc cp cpc => ContractProgramCorrect mr mc cp cpc)
  · intro n mr mc cp cpc hmr _ hrun hrec
    have hcfg := CProg.contractProgram_config hrun
    exact contractProgramCorrect_rotate n hcfg
      (by simpa [CProg.ringSize] using hmr) hrec
  · intro b1 b2 b3 hnsp
    cases b1 <;> cases b2 <;> cases b3 <;>
      simp [CProg.nonSparse] at hnsp ⊢
    all_goals first
      | exact contractProgramCorrect_y_nil_none
      | exact contractProgramCorrect_y_nil_third
      | exact contractProgramCorrect_y_nil_second
      | exact contractProgramCorrect_y_nil_first
  · intro b1 b2 b3 mr mc step cp cpc _ _ hnsp hrun hrec
    have hcfg := CProg.contractProgram_config hrun
    cases b1 <;> cases b2 <;> cases b3 <;>
      simp [CProg.nonSparse] at hnsp ⊢
    · exact contractProgramCorrect_y_cons_y hcfg hrec
    · exact contractProgramCorrect_y_cons_u hcfg hrec
    · exact contractProgramCorrect_y_cons_unchanged
        false true false hcfg (by decide) (by decide) hrec
    · exact contractProgramCorrect_y_cons_unchanged
        true false false hcfg (by decide) (by decide) hrec
  · intro b1 b2 b3 b4 b5 mr mc cp cpc hmr _ hnspL hnspR hall hrun hrec
    have hcfg := CProg.contractProgram_config hrun
    have hmr' : (b4 :: b5 :: mr).length = CProg.ringSize cp := by
      simpa [CProg.ringSize] using hmr
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      simp [CProg.nonSparse] at hnspL hnspR ⊢
    · exact contractProgramCorrect_h_h hcfg hmr' hrec
    · exact contractProgramCorrect_h_y hcfg (by decide) hrec
    · exact contractProgramCorrect_h_y hcfg (by decide) hrec
    · exact contractProgramCorrect_h_u hcfg hrec
    · exact contractProgramCorrect_h_crossbar hcfg hrec
    · exact contractProgramCorrect_h_right_k hcfg hmr' hrec
    · exact contractProgramCorrect_h_right_unchanged hcfg hrec
    · exact contractProgramCorrect_h_left_k hcfg hmr' hrec
    · exact contractProgramCorrect_h_left_unchanged hcfg hrec
    ·
      have hout := CProg.ringSize_contractProgram hmr' hrun
      have hall' : mr.all (fun b => b) = false := by
        simpa using hall
      have hpos : 0 < CProg.countFalse mr :=
        CProg.countFalse_pos_of_all_eq_false hall'
      have hsize : 2 < CProg.ringSize cpc := by
        simp [CProg.countFalse] at hout
        omega
      exact contractProgramCorrect_h_a hcfg hmr' hsize hrec
  all_goals assumption

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
