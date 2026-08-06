import FourColorTheorem.FourColor.Coloring.CFColor.StepDefinitions

/-!
Semantic preservation properties of configuration-colouring steps.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

theorem cpColorStepSpec_mono
    {s : CpStep} {P Q : ColSeq → ColSeq → Prop}
    (hPQ : ∀ et et', P et et' → Q et et')
    {et et' : ColSeq} :
    cpColorStepSpec s P et et' → cpColorStepSpec s Q et et' := by
  cases s with
  | rotate n =>
      exact hPQ _ _
  | reverseRotate =>
      intro hspec
      exact ⟨hspec.1, hPQ _ _ hspec.2⟩
  | y =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e et =>
          intro hspec
          rcases hspec with hleft | hright
          · exact Or.inl (hPQ _ _ hleft)
          · exact Or.inr (hPQ _ _ hright)
  | h =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStepSpec, heq]
                intro hspec
                rcases hspec with hleft | hright
                · exact Or.inl (hPQ _ _ hleft)
                · exact Or.inr (hPQ _ _ hright)
              · simp [cpColorStepSpec, heq]
                exact hPQ _ _
  | u =>
      intro hspec
      rcases hspec with h1 | h2 | h3
      · exact Or.inl (hPQ _ _ h1)
      · exact Or.inr (Or.inl (hPQ _ _ h2))
      · exact Or.inr (Or.inr (hPQ _ _ h3))
  | k =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              intro hspec
              exact ⟨hspec.1, hPQ _ _ hspec.2⟩
  | a =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              intro hspec
              exact ⟨hspec.1, hPQ _ _ hspec.2⟩

theorem cpColorStep_mem_iff
    {height : Nat} (s : CpStep) (f : ColSeq → CTree)
    (P : ColSeq → ColSeq → Prop)
    (hfproper : ∀ et, CTree.Proper height (f et))
    (hfspec :
      ∀ et et', CTree.mem (f et) et' = true ↔ P et et')
    (et et' : ColSeq) :
    CTree.mem (cpColorStep s f et) et' = true ↔
      cpColorStepSpec s P et et' := by
  cases s with
  | rotate n =>
      simp [cpColorStep, cpColorStepSpec, hfspec]
  | reverseRotate =>
      by_cases hle : et.length ≤ 1
      · simp [cpColorStep, cpColorStepSpec, hle]
      · simp [cpColorStep, cpColorStepSpec, hle, hfspec]
  | y =>
      cases et with
      | nil =>
          simp [cpColorStep, cpColorStepSpec]
      | cons e et =>
          change CTree.mem
              (CTree.union
                (f (EdgePerm.p231 e :: EdgePerm.p312 e :: et))
                (f (EdgePerm.p312 e :: EdgePerm.p231 e :: et))) et' =
              true ↔ cpColorStepSpec CpStep.y P (e :: et) et'
          rw [CTree.mem_union (h := height)
            (t := f (EdgePerm.p231 e :: EdgePerm.p312 e :: et))
            (u := f (EdgePerm.p312 e :: EdgePerm.p231 e :: et))
            et' (hfproper _) (hfproper _)]
          simp [cpColorStepSpec, hfspec]
  | h =>
      cases et with
      | nil =>
          simp [cpColorStep, cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep, cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · subst e2
                rw [show
                    cpColorStep CpStep.h f (e1 :: e1 :: et) =
                      CTree.union
                      (sameHead f (EdgePerm.p231 e1) et)
                        (sameHead f (EdgePerm.p312 e1) et) by
                    simp [cpColorStep, sameHead]]
                rw [CTree.mem_union (h := height)
                  (t := sameHead f (EdgePerm.p231 e1) et)
                  (u := sameHead f (EdgePerm.p312 e1) et)
                  et' (hfproper _) (hfproper _)]
                simp [cpColorStepSpec, sameHead, hfspec]
              · simp [cpColorStep, cpColorStepSpec, heq, hfspec]
  | u =>
      change CTree.mem
          (CTree.union (sameHead f Color.one et)
            (CTree.union (sameHead f Color.two et)
              (sameHead f Color.three et))) et' =
          true ↔ cpColorStepSpec CpStep.u P et et'
      rw [CTree.mem_union (h := height)
        (t := sameHead f Color.one et)
        (u := CTree.union (sameHead f Color.two et)
          (sameHead f Color.three et))
        et' (hfproper _)
        (CTree.proper_union (hfproper _) (hfproper _))]
      rw [CTree.mem_union (h := height)
        (t := sameHead f Color.two et)
        (u := sameHead f Color.three et)
        et' (hfproper _) (hfproper _)]
      simp [cpColorStepSpec, sameHead, hfspec]
  | k =>
      cases et with
      | nil =>
          simp [cpColorStep, cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep, cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStep, cpColorStepSpec, heq]
              · simp [cpColorStep, cpColorStepSpec, heq, hfspec]
  | a =>
      cases et with
      | nil =>
          simp [cpColorStep, cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep, cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStep, cpColorStepSpec, heq, hfspec]
              · simp [cpColorStep, cpColorStepSpec, heq]

theorem cpBranchFast_mem_iff (et et' : ColSeq) :
    CTree.mem (cpBranchFast et) et' = true ↔
      cpBranchTraceSpec et et' := by
  rw [cpBranchFast_spec]
  exact cpBranch_mem_iff et et'

theorem cpBranchFast_mem_length
    {et et' : ColSeq}
    (hmem : CTree.mem (cpBranchFast et) et' = true) :
    et'.length = (ColSeq.etail (et.drop 1)).length := by
  rw [cpBranchFast_spec] at hmem
  exact cpBranch_mem_length hmem

theorem cpBranchFast_mem_length_add_two
    {et et' : ColSeq}
    (hmem : CTree.mem (cpBranchFast et) et' = true) :
    et'.length + 2 = et.length := by
  rw [cpBranchFast_spec] at hmem
  exact cpBranch_mem_length_add_two hmem

private theorem cpColorStepSpec_propertyCore
    {s : CpStep} {P : ColSeq → ColSeq → Prop}
    {Q : ColSeq → Prop} {et et' : ColSeq}
    (hP : ∀ et et', P et et' → Q et')
    (hspec : cpColorStepSpec s P et et') :
    Q et' := by
  cases s with
  | rotate k =>
      exact hP _ _ hspec
  | reverseRotate =>
      exact hP _ _ hspec.2
  | y =>
      cases et with
      | nil =>
          simp [cpColorStepSpec] at hspec
      | cons e et =>
          rcases hspec with hleft | hright
          · exact hP _ _ hleft
          · exact hP _ _ hright
  | h =>
      cases et with
      | nil =>
          simp [cpColorStepSpec] at hspec
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec] at hspec
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStepSpec, heq] at hspec
                rcases hspec with hleft | hright
                · exact hP _ _ hleft
                · exact hP _ _ hright
              · simp [cpColorStepSpec, heq] at hspec
                exact hP _ _ hspec
  | u =>
      rcases hspec with h1 | h2 | h3
      · exact hP _ _ h1
      · exact hP _ _ h2
      · exact hP _ _ h3
  | k =>
      cases et with
      | nil =>
          simp [cpColorStepSpec] at hspec
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec] at hspec
          | cons e2 et =>
              exact hP _ _ hspec.2
  | a =>
      cases et with
      | nil =>
          simp [cpColorStepSpec] at hspec
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec] at hspec
          | cons e2 et =>
              exact hP _ _ hspec.2

theorem cpColorStepSpec_length
    {s : CpStep} {P : ColSeq → ColSeq → Prop}
    {et et' : ColSeq} {n : Nat}
    (hP : ∀ et et', P et et' → et'.length = n)
    (hspec : cpColorStepSpec s P et et') :
    et'.length = n :=
  cpColorStepSpec_propertyCore hP hspec

theorem cpColorStepSpec_property
    {s : CpStep} {P : ColSeq → ColSeq → Prop}
    {Q : ColSeq → Prop} {et et' : ColSeq}
    (hP : ∀ et et', P et et' → Q et')
    (hspec : cpColorStepSpec s P et et') :
    Q et' :=
  cpColorStepSpec_propertyCore hP hspec

end CProg

end FourColor

end Schematic.Math.GraphTheory
