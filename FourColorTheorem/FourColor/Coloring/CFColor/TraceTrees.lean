import FourColorTheorem.FourColor.Coloring.CFColor.Expansion

/-!
Proper trace-tree specifications and exact membership transfer.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

theorem cpColorStep_proper
    {h : Nat} (s : CpStep) (f : ColSeq → CTree)
    (hf : ∀ et, CTree.Proper h (f et)) (et : ColSeq) :
    CTree.Proper h (cpColorStep s f et) := by
  cases s with
  | rotate n =>
      exact hf _
  | reverseRotate =>
      simp [cpColorStep]
      split
      · exact CTree.proper_empty h
      · exact hf _
  | y =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e et =>
          simp [cpColorStep]
          exact CTree.proper_union (hf _) (hf _)
  | h =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              simp [cpColorStep, sameHead]
              split
              · exact CTree.proper_union (hf _) (hf _)
              · exact hf _
  | u =>
      simp [cpColorStep, sameHead]
      exact CTree.proper_union (hf _)
        (CTree.proper_union (hf _) (hf _))
  | k =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              simp [cpColorStep]
              split
              · exact CTree.proper_empty h
              · exact hf _
  | a =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              simp [cpColorStep]
              split
              · exact hf _
              · exact CTree.proper_empty h

/-- A tree-valued trace transformer, together with the exact predicate its
membership test decides, at a fixed tree height. -/
structure TraceTreeSpec
    (height : Nat) (f : ColSeq → CTree)
    (P : ColSeq → ColSeq → Prop) : Prop where
  proper : ∀ et, CTree.Proper height (f et)
  mem_iff : ∀ et et', CTree.mem (f et) et' = true ↔ P et et'

theorem TraceTreeSpec.step
    {height : Nat} {f : ColSeq → CTree}
    {P : ColSeq → ColSeq → Prop}
    (h : TraceTreeSpec height f P) (s : CpStep) :
    TraceTreeSpec height
      (fun et => cpColorStep s f et)
      (cpColorStepSpec s P) := by
  refine ⟨?_, ?_⟩
  · intro et
    exact cpColorStep_proper s f h.proper et
  · intro et et'
    exact cpColorStep_mem_iff s f P h.proper h.mem_iff et et'

theorem TraceTreeSpec.fold
    {height : Nat} {f : ColSeq → CTree}
    {P : ColSeq → ColSeq → Prop}
    (h : TraceTreeSpec height f P) :
    ∀ cp : CProg,
      TraceTreeSpec height
        (cp.foldr cpColorStep f)
        (cp.foldr cpColorStepSpec P)
  | [] => h
  | s :: cp => by
      exact TraceTreeSpec.step (TraceTreeSpec.fold h cp) s

theorem cpColorFold_mem_iff_of_branch_proper
    {height : Nat} (cp : CProg)
    (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    (et et' : ColSeq) :
    CTree.mem (cpColorFold cp et) et' = true ↔
      cpColorFoldSpec cp et et' := by
  let hbase : TraceTreeSpec height cpBranch cpBranchTraceSpec := {
    proper := hbranch
    mem_iff := cpBranch_mem_iff
  }
  exact (TraceTreeSpec.fold hbase cp).mem_iff et et'

theorem cpColorFoldFast_mem_iff_of_branch_proper
    {height : Nat} (cp : CProg)
    (hbranch : ∀ et, CTree.Proper height (cpBranchFast et))
    (et et' : ColSeq) :
    CTree.mem (cpColorFoldFast cp et) et' = true ↔
      cpColorFoldSpec cp et et' := by
  let hbase : TraceTreeSpec height cpBranchFast cpBranchTraceSpec := {
    proper := hbranch
    mem_iff := cpBranchFast_mem_iff
  }
  exact (TraceTreeSpec.fold hbase cp).mem_iff et et'

theorem cpColor0_mem_iff_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et)) :
    ∀ (cp : CProg) (et' : ColSeq),
      CTree.mem (cpColor0 cp) et' = true ↔ cpColor0Spec cp et'
  | CpStep.rotate _ :: cp, et' =>
      cpColor0_mem_iff_of_branch_proper hbranch cp et'
  | CpStep.y :: cp, et' => by
      exact cpColorFold_mem_iff_of_branch_proper cp hbranch _ _
  | CpStep.u :: cp, et' => by
      let hbase : TraceTreeSpec height cpBranch cpBranchTraceSpec := {
        proper := hbranch
        mem_iff := cpBranch_mem_iff
      }
      change CTree.mem
          (CTree.union
            (cpColorFold cp [Color.one, Color.one, Color.two, Color.two])
            (cpColorFold cp [Color.one, Color.one, Color.one, Color.one]))
          et' = true ↔ cpColor0Spec (CpStep.u :: cp) et'
      rw [CTree.mem_union (h := height)
        (t := cpColorFold cp [Color.one, Color.one, Color.two, Color.two])
        (u := cpColorFold cp [Color.one, Color.one, Color.one, Color.one])
        et'
        ((TraceTreeSpec.fold hbase cp).proper _)
        ((TraceTreeSpec.fold hbase cp).proper _)]
      simp [cpColor0Spec, cpColorFold_mem_iff_of_branch_proper cp hbranch]
  | CpStep.h :: cp, et' => by
      exact cpColorFold_mem_iff_of_branch_proper _ hbranch _ _
  | CpStep.k :: cp, et' => by
      exact cpColorFold_mem_iff_of_branch_proper _ hbranch _ _
  | CpStep.a :: cp, et' => by
      exact cpColorFold_mem_iff_of_branch_proper _ hbranch _ _
  | CpStep.reverseRotate :: cp, et' => by
      exact cpColorFold_mem_iff_of_branch_proper _ hbranch _ _
  | [], et' => by
      exact cpColorFold_mem_iff_of_branch_proper [] hbranch _ _

theorem cpColor0Fast_mem_iff_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    (cp : CProg) (et' : ColSeq) :
    CTree.mem (cpColor0Fast cp) et' = true ↔ cpColor0Spec cp et' := by
  rw [cpColor0Fast_spec]
  exact cpColor0_mem_iff_of_branch_proper hbranch cp et'

theorem cpColor_mem_iff_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    (cp : CProg) (et : ColSeq) :
    CTree.mem (cpColor cp) et = true ↔ cpColorSpec cp et := by
  simp [cpColor, cpColorSpec, CTree.mem_consRot,
    cpColor0_mem_iff_of_branch_proper hbranch]

theorem cpColorFast_mem_iff_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    (cp : CProg) (et : ColSeq) :
    CTree.mem (cpColorFast cp) et = true ↔ cpColorSpec cp et := by
  rw [cpColorFast_spec]
  exact cpColor_mem_iff_of_branch_proper hbranch cp et

theorem cpColor_mem_ttail_not_mem_zero_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    Color.zero ∉ ColSeq.ttail et :=
  cpColorSpec_ttail_not_mem_zero
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_ttail_evenTail_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    ColSeq.evenTail (ColSeq.ttail et) = true :=
  cpColorSpec_ttail_evenTail
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_ttail_not_mem_zero_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    Color.zero ∉ ColSeq.ttail et :=
  cpColorSpec_ttail_not_mem_zero
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_ttail_evenTail_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    ColSeq.evenTail (ColSeq.ttail et) = true :=
  cpColorSpec_ttail_evenTail
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_evenTrace_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    ColSeq.evenTrace et = true :=
  cpColorSpec_evenTrace
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_properTrace_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    ColSeq.ProperTrace et :=
  cpColorSpec_properTrace
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_not_mem_zero_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    Color.zero ∉ et :=
  cpColorSpec_not_mem_zero
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_etail_eq_ttail_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    ColSeq.etail et = ColSeq.ttail et :=
  cpColorSpec_etail_eq_ttail
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColor_mem_trace_normalized_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColor cp) et = true) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et :=
  cpColorSpec_trace_normalized
    ((cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_evenTrace_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    ColSeq.evenTrace et = true :=
  cpColorSpec_evenTrace
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_properTrace_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    ColSeq.ProperTrace et :=
  cpColorSpec_properTrace
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_not_mem_zero_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    Color.zero ∉ et :=
  cpColorSpec_not_mem_zero
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_etail_eq_ttail_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    ColSeq.etail et = ColSeq.ttail et :=
  cpColorSpec_etail_eq_ttail
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFast_mem_trace_normalized_of_branch_proper
    {height : Nat} (hbranch : ∀ et, CTree.Proper height (cpBranch et))
    {cp : CProg} {et : ColSeq}
    (hmem : CTree.mem (cpColorFast cp) et = true) :
    ColSeq.ProperTrace et ∧
      Color.zero ∉ et ∧
        ColSeq.evenTrace et = true ∧
          ColSeq.etail et = ColSeq.ttail et :=
  cpColorSpec_trace_normalized
    ((cpColorFast_mem_iff_of_branch_proper hbranch cp et).1 hmem)

theorem cpColorFold_proper_of_branch
    {h : Nat} (cp : CProg)
    (hbranch : ∀ et, CTree.Proper h (cpBranch et)) :
    ∀ et, CTree.Proper h (cpColorFold cp et) := by
  induction cp with
  | nil =>
      intro et
      exact hbranch et
  | cons s cp ih =>
      intro et
      exact cpColorStep_proper s (cpColorFold cp) ih et

end CProg

end FourColor

end Schematic.Math.GraphTheory
