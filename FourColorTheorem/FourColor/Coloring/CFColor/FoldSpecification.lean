import FourColorTheorem.FourColor.Coloring.CFColor.StepSemantics

/-!
Folded configuration-colouring predicates and normalized trace invariants.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Fold the colouring iterator over a program. -/
def cpColorFold (cp : CProg) : ColSeq → CTree :=
  cp.foldr cpColorStep cpBranch

/-- Predicate computed by `cpColorFold`, before the later configuration-map
layer identifies it with actual colourings of a configuration. -/
def cpColorFoldSpec (cp : CProg) : ColSeq → ColSeq → Prop :=
  cp.foldr cpColorStepSpec cpBranchTraceSpec

theorem cpColorFoldSpec_property
    {Q : ColSeq → Prop}
    (cp : CProg)
    (hbranch : ∀ et et', cpBranchTraceSpec et et' → Q et')
    {et et' : ColSeq}
    (hspec : cpColorFoldSpec cp et et') :
    Q et' := by
  induction cp generalizing et et' with
  | nil =>
      exact hbranch et et' hspec
  | cons s cp ih =>
      exact cpColorStepSpec_property
        (fun et et' h => ih (et := et) (et' := et') h)
        (by simpa [cpColorFoldSpec] using hspec)

theorem cpColorFoldSpec_length
    (cp : CProg) {n : Nat}
    (hbranch : ∀ et et', cpBranchTraceSpec et et' → et'.length = n)
    {et et' : ColSeq}
    (hspec : cpColorFoldSpec cp et et') :
    et'.length = n :=
  cpColorFoldSpec_property cp hbranch hspec

/-- Executable fold using the optimized branch builder. -/
def cpColorFoldFast (cp : CProg) : ColSeq → CTree :=
  cp.foldr cpColorStep cpBranchFast

/-- Initial trace-colouring tree, with the same symmetry reductions as Coq's
`cpcolor0`. -/
def cpColor0 : CProg → CTree
  | CpStep.rotate _ :: cp => cpColor0 cp
  | CpStep.y :: cp => cpColorFold cp [Color.one, Color.two, Color.three]
  | CpStep.u :: cp =>
      CTree.union
        (cpColorFold cp [Color.one, Color.one, Color.two, Color.two])
        (cpColorFold cp [Color.one, Color.one, Color.one, Color.one])
  | cp => cpColorFold cp [Color.one, Color.one]

/-- Fast initial trace-colouring tree. -/
def cpColor0Fast : CProg → CTree
  | CpStep.rotate _ :: cp => cpColor0Fast cp
  | CpStep.y :: cp => cpColorFoldFast cp [Color.one, Color.two, Color.three]
  | CpStep.u :: cp =>
      CTree.union
        (cpColorFoldFast cp [Color.one, Color.one, Color.two, Color.two])
        (cpColorFoldFast cp [Color.one, Color.one, Color.one, Color.one])
  | cp => cpColorFoldFast cp [Color.one, Color.one]

/-- Predicate computed by `cpColor0`, including the initial symmetry
reductions. -/
def cpColor0Spec : CProg → ColSeq → Prop
  | CpStep.rotate _ :: cp, et' => cpColor0Spec cp et'
  | CpStep.y :: cp, et' =>
      cpColorFoldSpec cp [Color.one, Color.two, Color.three] et'
  | CpStep.u :: cp, et' =>
      cpColorFoldSpec cp [Color.one, Color.one, Color.two, Color.two] et' ∨
        cpColorFoldSpec cp [Color.one, Color.one, Color.one, Color.one] et'
  | cp, et' =>
      cpColorFoldSpec cp [Color.one, Color.one] et'

/-- Predicate computed by `cpColor`, after the final `consRot`
normalisation. -/
def cpColorSpec (cp : CProg) (et : ColSeq) : Prop :=
  cpColor0Spec cp.reverse (ColSeq.ttail et)

theorem cpBranchTraceSpec_not_mem_zero
    {et et' : ColSeq}
    (hspec : cpBranchTraceSpec et et') :
    Color.zero ∉ et' := by
  rw [hspec.2]
  exact hspec.1

theorem cpBranchTraceSpec_evenTail
    {et et' : ColSeq}
    (hspec : cpBranchTraceSpec et et') :
    ColSeq.evenTail et' = true := by
  rw [hspec.2]
  exact ColSeq.even_etail (et.drop 1)

theorem cpColorFoldSpec_not_mem_zero
    (cp : CProg) {et et' : ColSeq}
    (hspec : cpColorFoldSpec cp et et') :
    Color.zero ∉ et' :=
  cpColorFoldSpec_property cp
    (fun _ _ => cpBranchTraceSpec_not_mem_zero) hspec

theorem cpColorFoldSpec_evenTail
    (cp : CProg) {et et' : ColSeq}
    (hspec : cpColorFoldSpec cp et et') :
    ColSeq.evenTail et' = true :=
  cpColorFoldSpec_property cp
    (fun _ _ => cpBranchTraceSpec_evenTail) hspec

theorem cpColor0Spec_not_mem_zero :
    ∀ {cp : CProg} {et' : ColSeq},
      cpColor0Spec cp et' → Color.zero ∉ et' := by
  intro cp
  induction cp with
  | nil =>
      intro et' hspec
      exact cpColorFoldSpec_not_mem_zero [] hspec
  | cons s cp ih =>
      intro et' hspec
      cases s with
      | rotate n =>
          exact ih hspec
      | y =>
          exact cpColorFoldSpec_not_mem_zero cp hspec
      | u =>
          rcases hspec with hleft | hright
          · exact cpColorFoldSpec_not_mem_zero cp hleft
          · exact cpColorFoldSpec_not_mem_zero cp hright
      | h =>
          exact cpColorFoldSpec_not_mem_zero (CpStep.h :: cp) hspec
      | k =>
          exact cpColorFoldSpec_not_mem_zero (CpStep.k :: cp) hspec
      | a =>
          exact cpColorFoldSpec_not_mem_zero (CpStep.a :: cp) hspec
      | reverseRotate =>
          exact cpColorFoldSpec_not_mem_zero (CpStep.reverseRotate :: cp) hspec

theorem cpColor0Spec_evenTail :
    ∀ {cp : CProg} {et' : ColSeq},
      cpColor0Spec cp et' → ColSeq.evenTail et' = true := by
  intro cp
  induction cp with
  | nil =>
      intro et' hspec
      exact cpColorFoldSpec_evenTail [] hspec
  | cons s cp ih =>
      intro et' hspec
      cases s with
      | rotate n =>
          exact ih hspec
      | y =>
          exact cpColorFoldSpec_evenTail cp hspec
      | u =>
          rcases hspec with hleft | hright
          · exact cpColorFoldSpec_evenTail cp hleft
          · exact cpColorFoldSpec_evenTail cp hright
      | h =>
          exact cpColorFoldSpec_evenTail (CpStep.h :: cp) hspec
      | k =>
          exact cpColorFoldSpec_evenTail (CpStep.k :: cp) hspec
      | a =>
          exact cpColorFoldSpec_evenTail (CpStep.a :: cp) hspec
      | reverseRotate =>
          exact cpColorFoldSpec_evenTail (CpStep.reverseRotate :: cp) hspec

theorem cpColorSpec_ttail_not_mem_zero
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    Color.zero ∉ ColSeq.ttail et :=
  cpColor0Spec_not_mem_zero hspec

theorem cpColorSpec_ttail_evenTail
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    ColSeq.evenTail (ColSeq.ttail et) = true :=
  cpColor0Spec_evenTail hspec

theorem cpColorSpec_evenTrace
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    ColSeq.evenTrace et = true :=
  cpColorSpec_ttail_evenTail hspec

theorem cpColorSpec_etail_eq_ttail
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    ColSeq.etail et = ColSeq.ttail et := by
  exact ColSeq.etail_eq_ttail_of_evenTrace (cpColorSpec_evenTrace hspec)

theorem cpColorSpec_properTrace
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    ColSeq.ProperTrace et := by
  have htail := cpColorSpec_ttail_not_mem_zero hspec
  by_contra hbad
  exact htail ((ColSeq.mem_zero_ttail et).2 (Or.inl hbad))

theorem cpColorSpec_not_mem_zero
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    Color.zero ∉ et := by
  have htail := cpColorSpec_ttail_not_mem_zero hspec
  intro hzero
  exact htail ((ColSeq.mem_zero_ttail et).2 (Or.inr hzero))

theorem cpColorSpec_trace_normalized
    {cp : CProg} {et : ColSeq}
    (hspec : cpColorSpec cp et) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et := by
  exact ⟨cpColorSpec_properTrace hspec,
    cpColorSpec_not_mem_zero hspec,
      cpColorSpec_evenTrace hspec,
        cpColorSpec_etail_eq_ttail hspec⟩

end CProg

end FourColor

end Schematic.Math.GraphTheory
