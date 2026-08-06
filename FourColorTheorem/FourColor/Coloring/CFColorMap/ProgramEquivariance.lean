import FourColorTheorem.FourColor.Coloring.CFColorMap.StepSemantics
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

theorem configStepSize_gt_one
    {s : CpStep} (hs : ColoringConfigStep s)
    {n : Nat} (hsize : 1 < n) :
    1 < configStepSize s n := by
  cases hs <;> simp [configStepSize] <;> omega

theorem configStepsSize_gt_one :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ {n : Nat}, 1 < n → 1 < configStepsSize n ss
  | [], _hss, n, hsize => by simpa [configStepsSize] using hsize
  | s :: ss, hss, n, hsize => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      exact configStepsSize_gt_one hparts.2
        (configStepSize_gt_one hparts.1 hsize)

theorem ringCycle_configSteps :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ {P : PointedHypermap} {n : Nat},
        RingCycle P n → 1 < n →
          RingCycle (applyConfigSteps P ss) (configStepsSize n ss)
  | [], _hss, P, n, hcycle, _hsize => by
      simpa [applyConfigSteps, configStepsSize] using hcycle
  | s :: ss, hss, P, n, hcycle, hsize => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have hcycle' := ringCycle_configStep hparts.1 hcycle hsize
      have hsize' := configStepSize_gt_one hparts.1 hsize
      simpa [applyConfigSteps, configStepsSize] using
        ringCycle_configSteps hparts.2 hcycle' hsize'

/-- Exact equivalence between the abstract `cpColorFoldSpec` and the
relational construction-order trace fold. -/
theorem cpColorFoldSpec_iff_exists_configTraceFold :
    ∀ {ss : CProg},
      List.Forall ColoringConfigStep ss →
      ∀ input out,
        CProg.cpColorFoldSpec ss input out ↔
          ∃ final,
            ConfigTraceFold ss input final ∧
              CProg.cpBranchTraceSpec final out := by
  intro ss hss input out
  rw [cpColorFoldSpec_iff_exists_programTraceFold]
  constructor
  · rintro ⟨final, hfold, hbranch⟩
    exact ⟨final,
      (configTraceFold_iff_programTraceFold hss _ _).2 hfold, hbranch⟩
  · rintro ⟨final, hfold, hbranch⟩
    exact ⟨final,
      (configTraceFold_iff_programTraceFold hss _ _).1 hfold, hbranch⟩

theorem cpBranchTraceSpec_perm
    {full out : ColSeq} (g : EdgePerm)
    (hbranch : CProg.cpBranchTraceSpec full out) :
    CProg.cpBranchTraceSpec (ColSeq.perm g full) out := by
  have hdrop :
      (ColSeq.perm g full).drop 1 = ColSeq.perm g (full.drop 1) := by
    simp [ColSeq.perm]
  constructor
  · rw [hdrop, ColSeq.etail_perm_eq]
    exact hbranch.1
  · rw [hdrop, ColSeq.etail_perm_eq]
    exact hbranch.2

/-- The normalized terminal branch forgets a global edge-color permutation
for arbitrary, not only cubic, coloring programs. -/
theorem cpColorFoldSpec_perm_input_general
    {ss : CProg} (g : EdgePerm) {input out : ColSeq}
    (hspec : CProg.cpColorFoldSpec ss input out) :
    CProg.cpColorFoldSpec ss (ColSeq.perm g input) out := by
  rcases (cpColorFoldSpec_iff_exists_programTraceFold
      ss input out).1 hspec with ⟨final, hfold, hbranch⟩
  exact (cpColorFoldSpec_iff_exists_programTraceFold ss _ _).2
    ⟨ColSeq.perm g final, programTraceFold_perm g hfold,
      cpBranchTraceSpec_perm g hbranch⟩

/-- Coq's `cpcolor0` initial shortcuts represent the same normalized branches
for arbitrary programs, including contracted programs with `K` and `A`. -/
theorem cpColorFoldSpec_base_to_cpColor0Spec_general :
    ∀ {ss : CProg} {out : ColSeq},
      CProg.cpColorFoldSpec ss [Color.one, Color.one] out →
        CProg.cpColor0Spec ss out
  | [], out, hspec => by
      simpa [CProg.cpColor0Spec] using hspec
  | CpStep.rotate r :: ss, out, hspec => by
      have hrot : CProg.rotateLeft r [Color.one, Color.one] =
          [Color.one, Color.one] := by
        by_cases hr : r ≤ 2
        · rw [CProg.rotateLeft_eq_rotate_of_le (by simpa using hr)]
          simpa using List.rotate_replicate Color.one 2 r
        · rw [CProg.rotateLeft_oversize (by simp; omega)]
      have hspec' : CProg.cpColorFoldSpec ss
          (CProg.rotateLeft r [Color.one, Color.one]) out := by
        simpa [CProg.cpColorFoldSpec, CProg.cpColorStepSpec] using hspec
      rw [hrot] at hspec'
      exact cpColorFoldSpec_base_to_cpColor0Spec_general
        (ss := ss) hspec'
  | CpStep.y :: ss, out, hspec => by
      have hy :
          CProg.cpColorFoldSpec ss
              [Color.two, Color.three, Color.one] out ∨
            CProg.cpColorFoldSpec ss
              [Color.three, Color.two, Color.one] out := by
        simpa [CProg.cpColorFoldSpec, CProg.cpColorStepSpec,
          EdgePerm.apply] using hspec
      change CProg.cpColorFoldSpec ss
        [Color.one, Color.two, Color.three] out
      rcases hy with hleft | hright
      · simpa [ColSeq.perm, EdgePerm.apply] using
          cpColorFoldSpec_perm_input_general EdgePerm.p312 hleft
      · simpa [ColSeq.perm, EdgePerm.apply] using
          cpColorFoldSpec_perm_input_general EdgePerm.p321 hright
  | CpStep.u :: ss, out, hspec => by
      have hu :
          CProg.cpColorFoldSpec ss
              [Color.one, Color.one, Color.one, Color.one] out ∨
            CProg.cpColorFoldSpec ss
                [Color.two, Color.two, Color.one, Color.one] out ∨
              CProg.cpColorFoldSpec ss
                [Color.three, Color.three, Color.one, Color.one] out := by
        simpa [CProg.cpColorFoldSpec, CProg.cpColorStepSpec] using hspec
      change
        CProg.cpColorFoldSpec ss
            [Color.one, Color.one, Color.two, Color.two] out ∨
          CProg.cpColorFoldSpec ss
            [Color.one, Color.one, Color.one, Color.one] out
      rcases hu with hone | htwo | hthree
      · exact Or.inr hone
      · exact Or.inl (by
          simpa [ColSeq.perm, EdgePerm.apply] using
            cpColorFoldSpec_perm_input_general EdgePerm.p213 htwo)
      · exact Or.inl (by
          simpa [ColSeq.perm, EdgePerm.apply] using
            cpColorFoldSpec_perm_input_general EdgePerm.p231 hthree)
  | CpStep.reverseRotate :: ss, out, hspec => by
      simpa [CProg.cpColor0Spec] using hspec
  | CpStep.h :: ss, out, hspec => by
      simpa [CProg.cpColor0Spec] using hspec
  | CpStep.k :: ss, out, hspec => by
      simpa [CProg.cpColor0Spec] using hspec
  | CpStep.a :: ss, out, hspec => by
      simpa [CProg.cpColor0Spec] using hspec

/-- The normalized terminal branch forgets a global edge-color permutation,
so a complete cubic trace fold may be globally normalized at its input. -/
theorem cpColorFoldSpec_perm_input
    {ss : CProg} (g : EdgePerm) {input out : ColSeq}
    (hspec : CProg.cpColorFoldSpec ss input out) :
    CProg.cpColorFoldSpec ss (ColSeq.perm g input) out := by
  exact cpColorFoldSpec_perm_input_general g hspec

/-- Coq's `cpcolor0` initial `Y`/`U` shortcuts represent the same normalized
branches as starting the full cubic fold from the canonical base trace. -/
theorem cpColorFoldSpec_base_to_cpColor0Spec :
    ∀ {ss : CProg} {out : ColSeq},
        CProg.cpColorFoldSpec ss [Color.one, Color.one] out →
          CProg.cpColor0Spec ss out := by
  intro ss out hspec
  exact cpColorFoldSpec_base_to_cpColor0Spec_general hspec

theorem cpColor0_mem_iff_of_configSteps :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ out : ColSeq,
        CTree.mem (CProg.cpColor0 ss) out = true ↔
          CProg.cpColor0Spec ss out
  | [], hss, out => by
      simpa [CProg.cpColor0, CProg.cpColor0Spec] using
        cpColorFold_mem_iff_of_configSteps hss
          (input := [Color.one, Color.one]) (by decide) (by decide) out
  | s :: ss, hss, out => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have htail := hparts.2
      cases hparts.1 with
      | rotate r =>
          simpa [CProg.cpColor0, CProg.cpColor0Spec] using
            cpColor0_mem_iff_of_configSteps htail out
      | y =>
          simpa [CProg.cpColor0, CProg.cpColor0Spec] using
            cpColorFold_mem_iff_of_configSteps htail
              (input := [Color.one, Color.two, Color.three])
              (by decide) (by decide) out
      | h =>
          simpa [CProg.cpColor0, CProg.cpColor0Spec] using
            cpColorFold_mem_iff_of_configSteps hss
              (input := [Color.one, Color.one]) (by decide) (by decide) out
      | u =>
          let left := [Color.one, Color.one, Color.two, Color.two]
          let right := [Color.one, Color.one, Color.one, Color.one]
          have hleftProper := cpColorFold_proper_of_configSteps htail
            (input := left) (by decide) (by decide)
          have hrightProper := cpColorFold_proper_of_configSteps htail
            (input := right) (by decide) (by decide)
          change CTree.mem
              (CTree.union (CProg.cpColorFold ss left)
                (CProg.cpColorFold ss right)) out = true ↔
            CProg.cpColorFoldSpec ss left out ∨
              CProg.cpColorFoldSpec ss right out
          rw [CTree.mem_union_eq_true_iff hleftProper hrightProper,
            cpColorFold_mem_iff_of_configSteps htail
              (input := left) (by decide) (by decide) out,
            cpColorFold_mem_iff_of_configSteps htail
              (input := right) (by decide) (by decide) out]

theorem cpColor_mem_iff_cpColorSpec_of_cubic
    {cp : CProg} (hcp : CProg.cubic cp = true) (et : ColSeq) :
    CTree.mem (CProg.cpColor cp) et = true ↔ CProg.cpColorSpec cp et := by
  rw [CProg.cpColor, CTree.mem_consRot]
  exact cpColor0_mem_iff_of_configSteps
    (coloringConfigSteps_reverse_of_cubic hcp) (ColSeq.ttail et)


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
