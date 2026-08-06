import FourColorTheorem.FourColor.Coloring.CFColor.GeneralFold

/-!
Exact general membership for initial and symmetry-reduced colouring trees.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Exact membership for Coq's symmetry-reduced initial coloring tree, with
no cubicity or configuration hypothesis on the program. -/
theorem cpColor0_mem_iff_general :
    ∀ (cp : CProg) (out : ColSeq),
      CTree.mem (cpColor0 cp) out = true ↔ cpColor0Spec cp out
  | CpStep.rotate _ :: cp, out => cpColor0_mem_iff_general cp out
  | CpStep.y :: cp, out => by
      have hzero : Color.zero ∉
          [Color.one, Color.two, Color.three] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero cp hzero out
  | CpStep.u :: cp, out => by
      have hleft : Color.zero ∉
          [Color.one, Color.one, Color.two, Color.two] := by simp
      have hright : Color.zero ∉
          [Color.one, Color.one, Color.one, Color.one] := by simp
      have hpLeft := cpColorFold_proper_of_not_mem_zero cp hleft
      have hpRight := cpColorFold_proper_of_not_mem_zero cp hright
      rw [show cpColor0 (CpStep.u :: cp) =
          CTree.union
            (cpColorFold cp
              [Color.one, Color.one, Color.two, Color.two])
            (cpColorFold cp
              [Color.one, Color.one, Color.one, Color.one]) by rfl]
      rw [CTree.mem_union_eq_true_iff hpLeft hpRight]
      change
        (CTree.mem (cpColorFold cp
            [Color.one, Color.one, Color.two, Color.two]) out = true ∨
          CTree.mem (cpColorFold cp
            [Color.one, Color.one, Color.one, Color.one]) out = true) ↔
        (cpColorFoldSpec cp
            [Color.one, Color.one, Color.two, Color.two] out ∨
          cpColorFoldSpec cp
            [Color.one, Color.one, Color.one, Color.one] out)
      exact or_congr
        (cpColorFold_mem_iff_of_not_mem_zero cp hleft out)
        (cpColorFold_mem_iff_of_not_mem_zero cp hright out)
  | CpStep.h :: cp, out => by
      have hzero : Color.zero ∉ [Color.one, Color.one] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero (CpStep.h :: cp) hzero out
  | CpStep.k :: cp, out => by
      have hzero : Color.zero ∉ [Color.one, Color.one] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero (CpStep.k :: cp) hzero out
  | CpStep.a :: cp, out => by
      have hzero : Color.zero ∉ [Color.one, Color.one] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero (CpStep.a :: cp) hzero out
  | CpStep.reverseRotate :: cp, out => by
      have hzero : Color.zero ∉ [Color.one, Color.one] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero
        (CpStep.reverseRotate :: cp) hzero out
  | [], out => by
      have hzero : Color.zero ∉ [Color.one, Color.one] := by simp
      exact cpColorFold_mem_iff_of_not_mem_zero [] hzero out

/-- General executable/syntactic specification theorem for `cpColor`. -/
theorem cpColor_mem_iff_general (cp : CProg) (et : ColSeq) :
    CTree.mem (cpColor cp) et = true ↔ cpColorSpec cp et := by
  rw [cpColor, CTree.mem_consRot]
  exact cpColor0_mem_iff_general cp.reverse (ColSeq.ttail et)


end CProg

end FourColor

end Schematic.Math.GraphTheory
