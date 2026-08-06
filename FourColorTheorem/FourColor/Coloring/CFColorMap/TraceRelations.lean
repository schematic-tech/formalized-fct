import FourColorTheorem.FourColor.Coloring.CFColorMap.YHSemantics
import FourColorTheorem.FourColor.Coloring.CFColorMap.ASemantics
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Exact one-step relation computed by `cpColorStepSpec`, for all seven Coq
program constructors. -/
def ProgramTraceStep (s : CpStep) (input output : ColSeq) : Prop :=
  CProg.cpColorStepSpec s (fun mid out => out = mid) input output

/-- Relational construction-order fold for an arbitrary one-step relation. -/
def TraceFold (Step : CpStep → ColSeq → ColSeq → Prop) :
    CProg → ColSeq → ColSeq → Prop
  | [], input, output => output = input
  | s :: ss, input, output =>
      ∃ mid, Step s input mid ∧ TraceFold Step ss mid output

/-- Map a relation-preserving transformation through a complete trace fold. -/
theorem TraceFold.map
    {Step : CpStep → ColSeq → ColSeq → Prop} (f : ColSeq → ColSeq)
    (hstep : ∀ s input output, Step s input output →
      Step s (f input) (f output)) :
    ∀ {ss input output}, TraceFold Step ss input output →
      TraceFold Step ss (f input) (f output)
  | [], input, output, hfold => by
      simpa [TraceFold] using congrArg f hfold
  | s :: ss, input, output, hfold => by
      rcases hfold with ⟨mid, hone, hrest⟩
      exact ⟨f mid, hstep s input mid hone, TraceFold.map f hstep hrest⟩

/-- Pointwise-equivalent step relations have equivalent folds over any stream
whose constructors satisfy the supplied admissibility predicate. -/
theorem TraceFold.congr_of_forall
    {Allowed : CpStep → Prop} {Left Right : CpStep → ColSeq → ColSeq → Prop}
    (hstep : ∀ {s}, Allowed s → ∀ input output,
      Left s input output ↔ Right s input output) :
    ∀ {ss}, List.Forall Allowed ss → ∀ input output,
      TraceFold Left ss input output ↔ TraceFold Right ss input output
  | [], _hss, input, output => by simp [TraceFold]
  | s :: ss, hss, input, output => by
      have hparts := (List.forall_cons
        (p := Allowed) (x := s) (l := ss)).mp hss
      constructor
      · rintro ⟨mid, hone, hrest⟩
        exact ⟨mid, (hstep hparts.1 _ _).1 hone,
          (TraceFold.congr_of_forall hstep hparts.2 _ _).1 hrest⟩
      · rintro ⟨mid, hone, hrest⟩
        exact ⟨mid, (hstep hparts.1 _ _).2 hone,
          (TraceFold.congr_of_forall hstep hparts.2 _ _).2 hrest⟩

/-- Relational construction-order fold for arbitrary coloring programs. -/
def ProgramTraceFold : CProg → ColSeq → ColSeq → Prop :=
  TraceFold ProgramTraceStep

/-- The arbitrary predicate transformer factors through one exact trace
step, just as the configuration-only transformer does below. -/
theorem cpColorStepSpec_iff_exists_programTraceStep
    (s : CpStep) (Q : ColSeq → ColSeq → Prop)
    (input output : ColSeq) :
    CProg.cpColorStepSpec s Q input output ↔
      ∃ mid, ProgramTraceStep s input mid ∧ Q mid output := by
  cases s with
  | rotate r =>
      simp [ProgramTraceStep, CProg.cpColorStepSpec]
  | reverseRotate =>
      simp [ProgramTraceStep, CProg.cpColorStepSpec]
  | y =>
      cases input <;> simp [ProgramTraceStep, CProg.cpColorStepSpec]
  | h =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec]
      | cons e1 tail =>
          cases tail with
          | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec]
          | cons e2 rest =>
              by_cases heq : e1 = e2 <;>
                simp [ProgramTraceStep, CProg.cpColorStepSpec, heq]
  | u =>
      simp [ProgramTraceStep, CProg.cpColorStepSpec]
  | k =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec]
      | cons e tail =>
          cases tail <;> simp [ProgramTraceStep, CProg.cpColorStepSpec]
  | a =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec]
      | cons e tail =>
          cases tail <;> simp [ProgramTraceStep, CProg.cpColorStepSpec]

/-- Exact factorization of the arbitrary executable fold through the
construction-order trace relation. -/
theorem cpColorFoldSpec_iff_exists_programTraceFold :
    ∀ (ss : CProg) (input output : ColSeq),
      CProg.cpColorFoldSpec ss input output ↔
        ∃ final,
          ProgramTraceFold ss input final ∧
            CProg.cpBranchTraceSpec final output
  | [], input, output => by
      simp [CProg.cpColorFoldSpec, ProgramTraceFold, TraceFold]
  | s :: ss, input, output => by
      change
        CProg.cpColorStepSpec s
            (ss.foldr CProg.cpColorStepSpec CProg.cpBranchTraceSpec)
            input output ↔
          ∃ final,
            ProgramTraceFold (s :: ss) input final ∧
              CProg.cpBranchTraceSpec final output
      rw [cpColorStepSpec_iff_exists_programTraceStep]
      constructor
      · rintro ⟨mid, hstep, hrest⟩
        rcases (cpColorFoldSpec_iff_exists_programTraceFold
            ss mid output).1 hrest with ⟨final, hfold, hbranch⟩
        exact ⟨final, ⟨mid, hstep, hfold⟩, hbranch⟩
      · rintro ⟨final, ⟨mid, hstep, hfold⟩, hbranch⟩
        refine ⟨mid, hstep, ?_⟩
        exact (cpColorFoldSpec_iff_exists_programTraceFold
          ss mid output).2 ⟨final, hfold, hbranch⟩

/-- The constructors occurring in a cubic program when it is read in
construction order.  Genuine configurations use only `rotate`, `Y`, and `H`;
the Birkhoff basis checker additionally admits `U`. -/
inductive ColoringConfigStep : CpStep → Prop
  | rotate (r : Nat) : ColoringConfigStep (CpStep.rotate r)
  | y : ColoringConfigStep CpStep.y
  | h : ColoringConfigStep CpStep.h
  | u : ColoringConfigStep CpStep.u

theorem coloringConfigSteps_of_cubic :
    ∀ {ss : CProg}, CProg.cubic ss = true →
      List.Forall ColoringConfigStep ss
  | [], _ => by simp
  | CpStep.rotate r :: ss, h => by
      have ht : CProg.cubic ss = true := by simpa [CProg.cubic] using h
      exact (List.forall_cons (p := ColoringConfigStep)
        (x := CpStep.rotate r) (l := ss)).mpr
          ⟨ColoringConfigStep.rotate r, coloringConfigSteps_of_cubic ht⟩
  | CpStep.reverseRotate :: ss, h => by simp [CProg.cubic] at h
  | CpStep.y :: ss, h => by
      have ht : CProg.cubic ss = true := by simpa [CProg.cubic] using h
      exact (List.forall_cons (p := ColoringConfigStep)
        (x := CpStep.y) (l := ss)).mpr
          ⟨ColoringConfigStep.y, coloringConfigSteps_of_cubic ht⟩
  | CpStep.h :: ss, h => by
      have ht : CProg.cubic ss = true := by simpa [CProg.cubic] using h
      exact (List.forall_cons (p := ColoringConfigStep)
        (x := CpStep.h) (l := ss)).mpr
          ⟨ColoringConfigStep.h, coloringConfigSteps_of_cubic ht⟩
  | CpStep.u :: ss, h => by
      have ht : CProg.cubic ss = true := by simpa [CProg.cubic] using h
      exact (List.forall_cons (p := ColoringConfigStep)
        (x := CpStep.u) (l := ss)).mpr
          ⟨ColoringConfigStep.u, coloringConfigSteps_of_cubic ht⟩
  | CpStep.k :: ss, h => by simp [CProg.cubic] at h
  | CpStep.a :: ss, h => by simp [CProg.cubic] at h

theorem coloringConfigSteps_reverse_of_cubic
    {cp : CProg} (hcp : CProg.cubic cp = true) :
    List.Forall ColoringConfigStep cp.reverse := by
  apply coloringConfigSteps_of_cubic
  rw [← CProg.appendRev_nil_right cp]
  exact CProg.cubic_appendRev_eq_true_iff.mpr ⟨hcp, rfl⟩

/-- Exact one-step trace relation for configuration constructors. -/
def ConfigTraceStep : CpStep → ColSeq → ColSeq → Prop
  | CpStep.rotate r, et, out => out = CProg.rotateLeft r et
  | CpStep.y, [], _ => False
  | CpStep.y, e :: et, out =>
      out = EdgePerm.p231 e :: EdgePerm.p312 e :: et ∨
        out = EdgePerm.p312 e :: EdgePerm.p231 e :: et
  | CpStep.h, e1 :: e2 :: et, out =>
      if e1 = e2 then
        out = EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: et ∨
          out = EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: et
      else
        out = e2 :: e1 :: et
  | CpStep.h, _, _ => False
  | CpStep.u, et, out =>
      out = Color.one :: Color.one :: et ∨
        out = Color.two :: Color.two :: et ∨
          out = Color.three :: Color.three :: et
  | _, _, _ => False

/-- On the constructors admitted by a coloring configuration, the optimized
configuration relation is exactly the unrestricted program relation. -/
theorem configTraceStep_iff_programTraceStep
    {s : CpStep} (hs : ColoringConfigStep s) (input output : ColSeq) :
    ConfigTraceStep s input output ↔ ProgramTraceStep s input output := by
  cases hs with
  | rotate r => simp [ConfigTraceStep, ProgramTraceStep, CProg.cpColorStepSpec]
  | y => cases input <;>
      simp [ConfigTraceStep, ProgramTraceStep, CProg.cpColorStepSpec]
  | h =>
      cases input with
      | nil => simp [ConfigTraceStep, ProgramTraceStep, CProg.cpColorStepSpec]
      | cons e1 tail =>
          cases tail with
          | nil => simp [ConfigTraceStep, ProgramTraceStep, CProg.cpColorStepSpec]
          | cons e2 rest =>
              by_cases heq : e1 = e2 <;>
                simp [ConfigTraceStep, ProgramTraceStep,
                  CProg.cpColorStepSpec, heq]
  | u => simp [ConfigTraceStep, ProgramTraceStep, CProg.cpColorStepSpec]

/-- Every arbitrary coloring-program trace step commutes with a global
permutation of the three nonzero edge colors. -/
theorem programTraceStep_perm
    {s : CpStep} (g : EdgePerm) {input output : ColSeq}
    (hstep : ProgramTraceStep s input output) :
    ProgramTraceStep s (ColSeq.perm g input) (ColSeq.perm g output) := by
  cases s with
  | rotate r =>
      change output = CProg.rotateLeft r input at hstep
      change ColSeq.perm g output =
        CProg.rotateLeft r (ColSeq.perm g input)
      rw [hstep]
      exact CProg.map_rotateLeft g r input
  | reverseRotate =>
      rcases hstep with ⟨hlen, hout⟩
      constructor
      · simpa [ColSeq.perm] using hlen
      · rw [hout]
        exact CProg.map_rotateRight g 1 input
  | y =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
      | cons e tail =>
          rcases hstep with hleft | hright <;> subst output <;>
            cases g <;> cases e <;>
              simp [ProgramTraceStep, CProg.cpColorStepSpec,
                ColSeq.perm, EdgePerm.apply]
  | h =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
      | cons e1 tail =>
          cases tail with
          | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
          | cons e2 rest =>
              by_cases heq : e1 = e2
              · subst e2
                simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
                rcases hstep with hleft | hright <;> subst output <;>
                  cases g <;> cases e1 <;>
                    simp [ProgramTraceStep, CProg.cpColorStepSpec,
                      ColSeq.perm, EdgePerm.apply]
              · have hgne : g e1 ≠ g e2 := fun h =>
                  heq (EdgePerm.injective g h)
                simp [ProgramTraceStep, CProg.cpColorStepSpec, heq] at hstep
                subst output
                simp [ProgramTraceStep, CProg.cpColorStepSpec,
                  ColSeq.perm, hgne]
  | u =>
      rcases hstep with hstep | hstep | hstep <;> subst output <;>
        cases g <;>
          simp [ProgramTraceStep, CProg.cpColorStepSpec,
            ColSeq.perm, EdgePerm.apply]
  | k =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
      | cons e1 tail =>
          cases tail with
          | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
          | cons e2 rest =>
              rcases hstep with ⟨hne, hout⟩
              have hgne : g e1 ≠ g e2 := fun h =>
                hne (EdgePerm.injective g h)
              constructor
              · exact hgne
              · rw [hout]
                simp [ColSeq.perm, EdgePerm.map_add]
  | a =>
      cases input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
      | cons e1 tail =>
          cases tail with
          | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec] at hstep
          | cons e2 rest =>
              rcases hstep with ⟨heq, hout⟩
              subst e2
              cases rest <;> subst output <;>
                simp [ProgramTraceStep, CProg.cpColorStepSpec, ColSeq.perm]

/-- Global edge-color equivariance of an arbitrary construction-order fold. -/
theorem programTraceFold_perm :
    ∀ {ss : CProg} (g : EdgePerm) {input output : ColSeq},
      ProgramTraceFold ss input output →
        ProgramTraceFold ss (ColSeq.perm g input) (ColSeq.perm g output) := by
  intro ss g input output hfold
  change TraceFold ProgramTraceStep ss input output at hfold
  change TraceFold ProgramTraceStep ss (ColSeq.perm g input)
    (ColSeq.perm g output)
  exact TraceFold.map (ColSeq.perm g)
    (fun s input output hstep =>
      @programTraceStep_perm s g input output hstep) hfold

/-- Exact configuration trace steps commute with a global permutation of the
three nonzero edge colors.  Depending on the permutation, the two optimized
`Y` or equal-head `H` branches may exchange places. -/
theorem configTraceStep_perm
    {s : CpStep} (hs : ColoringConfigStep s)
    (g : EdgePerm) {input output : ColSeq}
    (hstep : ConfigTraceStep s input output) :
    ConfigTraceStep s (ColSeq.perm g input) (ColSeq.perm g output) := by
  apply (configTraceStep_iff_programTraceStep hs _ _).2
  exact programTraceStep_perm g
    ((configTraceStep_iff_programTraceStep hs _ _).1 hstep)

/-- Boundary length after one configuration constructor. -/
def configStepSize : CpStep → Nat → Nat
  | CpStep.y, n => n + 1
  | CpStep.u, n => n + 2
  | _, n => n

/-- Apply a construction-order stream of configuration steps to a pointed
map. -/
noncomputable def applyConfigSteps : PointedHypermap → CProg → PointedHypermap
  | P, [] => P
  | P, s :: ss => applyConfigSteps (step s P) ss

/-- Boundary length tracked alongside `applyConfigSteps`. -/
def configStepsSize : Nat → CProg → Nat
  | n, [] => n
  | n, s :: ss => configStepsSize (configStepSize s n) ss

/-- Relational fold of the exact one-step trace transformer. -/
def ConfigTraceFold : CProg → ColSeq → ColSeq → Prop :=
  TraceFold ConfigTraceStep

/-- Configuration folds are unrestricted program folds whose step stream is
known to consist only of configuration constructors. -/
theorem configTraceFold_iff_programTraceFold :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ input output,
        ConfigTraceFold ss input output ↔ ProgramTraceFold ss input output := by
  intro ss hss input output
  exact TraceFold.congr_of_forall
    (fun hs => configTraceStep_iff_programTraceStep hs) hss input output

/-- Global edge-color equivariance of the complete construction-order trace
fold. -/
theorem configTraceFold_perm :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ (g : EdgePerm) {input output : ColSeq},
        ConfigTraceFold ss input output →
        ConfigTraceFold ss (ColSeq.perm g input) (ColSeq.perm g output)
  | ss, hss, g, input, output, hfold => by
      apply (configTraceFold_iff_programTraceFold hss _ _).2
      exact programTraceFold_perm g
        ((configTraceFold_iff_programTraceFold hss _ _).1 hfold)

private theorem EdgePerm.apply_ne_zero
    (g : EdgePerm) {e : Color} (he : e ≠ Color.zero) :
    g e ≠ Color.zero := by
  intro h
  apply he
  exact EdgePerm.injective g (by simpa using h)

private theorem not_mem_zero_cons
    {e : Color} {tail : ColSeq} (hzero : Color.zero ∉ e :: tail) :
    e ≠ Color.zero ∧ Color.zero ∉ tail := by
  constructor
  · intro h
    subst e
    exact hzero (by simp)
  · intro h
    exact hzero (by simp [h])

private theorem perm_pair_not_mem_zero
    {e : Color} {tail : ColSeq} (he : e ≠ Color.zero)
    (htail : Color.zero ∉ tail) (g₁ g₂ : EdgePerm) :
    Color.zero ∉ g₁ e :: g₂ e :: tail := by
  simp only [List.mem_cons, not_or]
  exact ⟨(EdgePerm.apply_ne_zero g₁ he).symm,
    (EdgePerm.apply_ne_zero g₂ he).symm, htail⟩

theorem properTrace_drop_one_of_not_mem_zero
    {et : ColSeq} (hzero : Color.zero ∉ et) (hlen : 1 < et.length) :
    ColSeq.ProperTrace (et.drop 1) := by
  cases et with
  | nil => simp at hlen
  | cons e tail =>
      cases tail with
      | nil => simp at hlen
      | cons e' rest =>
          change e' ≠ Color.zero
          intro he'
          exact hzero (by simp [he'])

/-- Fixed-height properness along the reachable configuration-only fold.
Unlike the older unrestricted helper, this records the nonzero and length
invariants that make every terminal `cpBranch` have one common height. -/
theorem cpColorFold_proper_of_configSteps :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ {input : ColSeq}, Color.zero ∉ input → 1 < input.length →
        CTree.Proper (configStepsSize input.length ss - 2)
          (CProg.cpColorFold ss input)
  | [], _hss, input, hzero, hlen => by
      have hproper := properTrace_drop_one_of_not_mem_zero hzero hlen
      have htail := ColSeq.length_etail_of_proper hproper
      have hdrop : (input.drop 1).length + 1 = input.length := by
        cases input <;> simp_all
      have heq : (ColSeq.etail (input.drop 1)).length = input.length - 2 := by
        omega
      change CTree.Proper (input.length - 2) (CProg.cpBranch input)
      rw [← heq]
      exact CProg.cpBranch_proper input
  | s :: ss, hss, input, hzero, hlen => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have htail := hparts.2
      cases hparts.1 with
      | rotate r =>
          have hzero' : Color.zero ∉ CProg.rotateLeft r input :=
            (CProg.not_mem_rotateLeft Color.zero r input).2 hzero
          have hp := cpColorFold_proper_of_configSteps htail hzero'
            (by rw [CProg.length_rotateLeft]; exact hlen)
          rw [CProg.length_rotateLeft] at hp
          simpa [CProg.cpColorFold, CProg.cpColorStep,
            configStepsSize, configStepSize] using hp
      | y =>
          cases input with
          | nil => simp at hlen
          | cons e tail =>
              rcases not_mem_zero_cons hzero with ⟨he, htailZero⟩
              have hleftZero : Color.zero ∉
                  EdgePerm.p231 e :: EdgePerm.p312 e :: tail :=
                perm_pair_not_mem_zero he htailZero _ _
              have hrightZero : Color.zero ∉
                  EdgePerm.p312 e :: EdgePerm.p231 e :: tail :=
                perm_pair_not_mem_zero he htailZero _ _
              have hleft := cpColorFold_proper_of_configSteps htail
                hleftZero (by simp)
              have hright := cpColorFold_proper_of_configSteps htail
                hrightZero (by simp)
              simpa [CProg.cpColorFold, CProg.cpColorStep,
                configStepsSize, configStepSize] using
                CTree.proper_union hleft hright
      | h =>
          cases input with
          | nil => simp at hlen
          | cons e1 tail =>
              cases tail with
              | nil => simp at hlen
              | cons e2 rest =>
                  rcases not_mem_zero_cons hzero with ⟨he1, htailZero⟩
                  rcases not_mem_zero_cons htailZero with ⟨he2, hrestZero⟩
                  by_cases heq : e1 = e2
                  · subst e2
                    have hleftZero : Color.zero ∉
                        EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest :=
                      perm_pair_not_mem_zero he1 hrestZero _ _
                    have hrightZero : Color.zero ∉
                        EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest :=
                      perm_pair_not_mem_zero he1 hrestZero _ _
                    have hleft := cpColorFold_proper_of_configSteps htail
                      hleftZero (by simp)
                    have hright := cpColorFold_proper_of_configSteps htail
                      hrightZero (by simp)
                    simpa [CProg.cpColorFold, CProg.cpColorStep,
                      configStepsSize, configStepSize, CProg.sameHead] using
                      CTree.proper_union hleft hright
                  · have hswapZero : Color.zero ∉ e2 :: e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨he2.symm, he1.symm, hrestZero⟩
                    have hp := cpColorFold_proper_of_configSteps htail
                      hswapZero (by simp)
                    simpa [CProg.cpColorFold, CProg.cpColorStep, heq,
                      configStepsSize, configStepSize] using hp
      | u =>
          have h1 := cpColorFold_proper_of_configSteps htail
            (input := Color.one :: Color.one :: input) (by simpa using hzero)
            (by simp)
          have h2 := cpColorFold_proper_of_configSteps htail
            (input := Color.two :: Color.two :: input) (by simpa using hzero)
            (by simp)
          have h3 := cpColorFold_proper_of_configSteps htail
            (input := Color.three :: Color.three :: input) (by simpa using hzero)
            (by simp)
          simpa [CProg.cpColorFold, CProg.cpColorStep, CProg.sameHead,
            configStepsSize, configStepSize] using
            CTree.proper_union h1 (CTree.proper_union h2 h3)

/-- Exact executable membership on the reachable configuration-only fold.
The properness theorem above supplies the equal-height hypotheses needed by
each contracted tree union. -/
theorem cpColorFold_mem_iff_of_configSteps :
    ∀ {ss : CProg}, List.Forall ColoringConfigStep ss →
      ∀ {input : ColSeq}, Color.zero ∉ input → 1 < input.length →
        ∀ out : ColSeq,
          CTree.mem (CProg.cpColorFold ss input) out = true ↔
            CProg.cpColorFoldSpec ss input out
  | [], _hss, input, _hzero, _hlen, out => by
      simpa [CProg.cpColorFold, CProg.cpColorFoldSpec] using
        CProg.cpBranch_mem_iff input out
  | s :: ss, hss, input, hzero, hlen, out => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have htail := hparts.2
      cases hparts.1 with
      | rotate r =>
          have hzero' : Color.zero ∉ CProg.rotateLeft r input :=
            (CProg.not_mem_rotateLeft Color.zero r input).2 hzero
          simpa [CProg.cpColorFold, CProg.cpColorFoldSpec,
            CProg.cpColorStep, CProg.cpColorStepSpec] using
            cpColorFold_mem_iff_of_configSteps htail hzero'
              (by rw [CProg.length_rotateLeft]; exact hlen) out
      | y =>
          cases input with
          | nil => simp at hlen
          | cons e tail =>
              rcases not_mem_zero_cons hzero with ⟨he, htailZero⟩
              let left :=
                EdgePerm.p231 e :: EdgePerm.p312 e :: tail
              let right :=
                EdgePerm.p312 e :: EdgePerm.p231 e :: tail
              have hleftZero : Color.zero ∉ left :=
                perm_pair_not_mem_zero he htailZero _ _
              have hrightZero : Color.zero ∉ right :=
                perm_pair_not_mem_zero he htailZero _ _
              have hleftProper := cpColorFold_proper_of_configSteps htail
                hleftZero (by simp [left])
              have hrightProper := cpColorFold_proper_of_configSteps htail
                hrightZero (by simp [right])
              change CTree.mem
                  (CTree.union (CProg.cpColorFold ss left)
                    (CProg.cpColorFold ss right)) out = true ↔
                CProg.cpColorFoldSpec ss left out ∨
                  CProg.cpColorFoldSpec ss right out
              rw [CTree.mem_union_eq_true_iff hleftProper hrightProper,
                cpColorFold_mem_iff_of_configSteps htail hleftZero
                  (by simp [left]) out,
                cpColorFold_mem_iff_of_configSteps htail hrightZero
                  (by simp [right]) out]
      | h =>
          cases input with
          | nil => simp at hlen
          | cons e1 tail =>
              cases tail with
              | nil => simp at hlen
              | cons e2 rest =>
                  rcases not_mem_zero_cons hzero with ⟨he1, htailZero⟩
                  rcases not_mem_zero_cons htailZero with ⟨he2, hrestZero⟩
                  by_cases heq : e1 = e2
                  · subst e2
                    let left :=
                      EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest
                    let right :=
                      EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest
                    have hleftZero : Color.zero ∉ left :=
                      perm_pair_not_mem_zero he1 hrestZero _ _
                    have hrightZero : Color.zero ∉ right :=
                      perm_pair_not_mem_zero he1 hrestZero _ _
                    have hleftProper :=
                      cpColorFold_proper_of_configSteps htail hleftZero
                        (by simp [left])
                    have hrightProper :=
                      cpColorFold_proper_of_configSteps htail hrightZero
                        (by simp [right])
                    simp only [CProg.cpColorFold, List.foldr,
                      CProg.cpColorStep, CProg.cpColorFoldSpec,
                      CProg.cpColorStepSpec, CProg.sameHead]
                    change CTree.mem
                        (CTree.union (CProg.cpColorFold ss left)
                          (CProg.cpColorFold ss right)) out = true ↔
                      CProg.cpColorFoldSpec ss left out ∨
                        CProg.cpColorFoldSpec ss right out
                    rw [CTree.mem_union_eq_true_iff
                          hleftProper hrightProper,
                      cpColorFold_mem_iff_of_configSteps htail hleftZero
                        (by simp [left]) out,
                      cpColorFold_mem_iff_of_configSteps htail hrightZero
                        (by simp [right]) out]
                  · have hswapZero : Color.zero ∉ e2 :: e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨he2.symm, he1.symm, hrestZero⟩
                    simpa [CProg.cpColorFold, CProg.cpColorFoldSpec,
                      CProg.cpColorStep, CProg.cpColorStepSpec, heq] using
                      cpColorFold_mem_iff_of_configSteps htail hswapZero
                        (by simp) out
      | u =>
          let one := Color.one :: Color.one :: input
          let two := Color.two :: Color.two :: input
          let three := Color.three :: Color.three :: input
          have honeZero : Color.zero ∉ one := by simpa [one] using hzero
          have htwoZero : Color.zero ∉ two := by simpa [two] using hzero
          have hthreeZero : Color.zero ∉ three := by simpa [three] using hzero
          have honeProper := cpColorFold_proper_of_configSteps htail honeZero
            (by simp [one])
          have htwoProper := cpColorFold_proper_of_configSteps htail htwoZero
            (by simp [two])
          have hthreeProper := cpColorFold_proper_of_configSteps htail hthreeZero
            (by simp [three])
          change CTree.mem
              (CTree.union (CProg.cpColorFold ss one)
                (CTree.union (CProg.cpColorFold ss two)
                  (CProg.cpColorFold ss three))) out = true ↔
            CProg.cpColorFoldSpec ss one out ∨
              CProg.cpColorFoldSpec ss two out ∨
                CProg.cpColorFoldSpec ss three out
          rw [CTree.mem_union_eq_true_iff honeProper
                (CTree.proper_union htwoProper hthreeProper),
            CTree.mem_union_eq_true_iff htwoProper hthreeProper,
            cpColorFold_mem_iff_of_configSteps htail honeZero
              (by simp [one]) out,
            cpColorFold_mem_iff_of_configSteps htail htwoZero
              (by simp [two]) out,
            cpColorFold_mem_iff_of_configSteps htail hthreeZero
              (by simp [three]) out]


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
