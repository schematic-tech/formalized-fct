import FourColorTheorem.FourColor.Coloring.CFColorMap.TraceRelations
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- The abstract predicate transformer in `CFColor` factors through the exact
one-step relation above. -/
theorem cpColorStepSpec_iff_exists_configTraceStep
    {s : CpStep} (hs : ColoringConfigStep s)
    (Q : ColSeq → ColSeq → Prop) (et out : ColSeq) :
    CProg.cpColorStepSpec s Q et out ↔
      ∃ mid, ConfigTraceStep s et mid ∧ Q mid out := by
  rw [cpColorStepSpec_iff_exists_programTraceStep]
  constructor
  · rintro ⟨mid, hstep, hQ⟩
    exact ⟨mid, (configTraceStep_iff_programTraceStep hs _ _).2 hstep, hQ⟩
  · rintro ⟨mid, hstep, hQ⟩
    exact ⟨mid, (configTraceStep_iff_programTraceStep hs _ _).1 hstep, hQ⟩

/-- Soundness of the exact one-step relation against map ring traces. -/
theorem configTraceStep_ringTrace
    {P : PointedHypermap} {n : Nat} {s : CpStep}
    (hs : ColoringConfigStep s)
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {et out : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) et)
    (hstep : ConfigTraceStep s et out) :
    (step s P).map.RingTrace
      (ringDarts (step s P) (configStepSize s n)) out := by
  cases hs with
  | rotate r =>
      rw [show out = CProg.rotateLeft r et by
        simpa [ConfigTraceStep] using hstep]
      simpa [step, configStepSize] using
        ringTrace_rotate hcycle htrace r
  | y =>
      cases het : et with
      | nil => simp [ConfigTraceStep, het] at hstep
      | cons e tail =>
          have htrace' :
              P.map.RingTrace (ringDarts P n) (e :: tail) := by
            simpa [het] using htrace
          have he := ringTrace_head_ne_zero hsize htrace'
          simp [ConfigTraceStep, het] at hstep
          rcases hstep with hleft | hright
          · rw [hleft]
            simpa [step, configStepSize] using
              ringTrace_y_left hcycle (by omega) htrace' he
          · rw [hright]
            simpa [step, configStepSize] using
              ringTrace_y_right hcycle (by omega) htrace' he
  | h =>
      cases het : et with
      | nil => simp [ConfigTraceStep, het] at hstep
      | cons e1 tail =>
          cases htail : tail with
          | nil => simp [ConfigTraceStep, het, htail] at hstep
          | cons e2 rest =>
              have htrace' :
                  P.map.RingTrace (ringDarts P n) (e1 :: e2 :: rest) := by
                simpa [het, htail] using htrace
              have he1 := ringTrace_head_ne_zero hsize htrace'
              have hrot := ringTrace_rotate hcycle htrace' 1
              have hrot' :
                  (P.rotate 1).map.RingTrace
                    (ringDarts (P.rotate 1) n) (e2 :: (rest ++ [e1])) := by
                simpa using hrot
              have he2 := ringTrace_head_ne_zero hsize hrot'
              by_cases heq : e1 = e2
              · subst e2
                simp [ConfigTraceStep, het, htail] at hstep
                rcases hstep with hleft | hright
                · rw [hleft]
                  simpa [step, configStepSize] using
                    ringTrace_h_equal_left hcycle hsize
                      htrace' he1
                · rw [hright]
                  simpa [step, configStepSize] using
                    ringTrace_h_equal_right hcycle hsize
                      htrace' he1
              · simp [ConfigTraceStep, het, htail, heq] at hstep
                rw [hstep]
                simpa [step, configStepSize] using
                  ringTrace_h_unequal hcycle hsize htrace' he1 he2 heq
  | u =>
      rcases hstep with hstep | hstep | hstep <;> subst out <;>
        simpa [step, configStepSize] using
          ringTrace_u_of_ringTrace hcycle (by omega) htrace (by decide)

/-- Exhaustiveness of one configuration constructor: every resulting coloring
trace comes from one exact source branch. -/
theorem configTraceStep_ringTrace_elim
    {P : PointedHypermap} {n : Nat} {s : CpStep}
    (hs : ColoringConfigStep s)
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {out : ColSeq}
    (htrace : (step s P).map.RingTrace
      (ringDarts (step s P) (configStepSize s n)) out) :
    ∃ et,
      P.map.RingTrace (ringDarts P n) et ∧
      ConfigTraceStep s et out := by
  cases hs with
  | rotate r =>
      have hold := ringTrace_rotate_elim hcycle
        (by simpa [step, configStepSize] using htrace)
      refine ⟨CProg.rotateRight r out, hold, ?_⟩
      simpa [ConfigTraceStep] using
        (CProg.rotateLeft_rotateRight r out).symm
  | y =>
      have hy : P.y.map.RingTrace (ringDarts P.y (n + 1)) out := by
        simpa [step, configStepSize] using htrace
      rcases ringTrace_y_elim hcycle hsize hy with
        ⟨e, et, _he, hold, hbranch⟩
      exact ⟨e :: et, hold, by simpa [ConfigTraceStep] using hbranch⟩
  | h =>
      have hh : P.h.map.RingTrace (ringDarts P.h n) out := by
        simpa [step, configStepSize] using htrace
      rcases ringTrace_h_elim hcycle hsize hh with
        ⟨e1, e2, et, _he1, _he2, hold, hbranch⟩
      refine ⟨e1 :: e2 :: et, hold, ?_⟩
      simpa [ConfigTraceStep] using hbranch
  | u =>
      have hu : P.u.map.RingTrace (ringDarts P.u (n + 2)) out := by
        simpa [step, configStepSize] using htrace
      rcases ringTrace_u_elim hcycle (by omega) hu with
        ⟨e, et, he, hold, hout⟩
      refine ⟨et, hold, ?_⟩
      cases e with
      | zero => exact (he rfl).elim
      | one => exact Or.inl hout
      | two => exact Or.inr (Or.inl hout)
      | three => exact Or.inr (Or.inr hout)

/-- Ring-cycle preservation for one construction-order configuration step. -/
theorem ringCycle_configStep
    {P : PointedHypermap} {n : Nat} {s : CpStep}
    (hs : ColoringConfigStep s)
    (hcycle : RingCycle P n) (hsize : 1 < n) :
    RingCycle (step s P) (configStepSize s n) := by
  cases hs with
  | rotate r =>
      simpa [step, configStepSize] using rotate_ringCycle (r := r) hcycle
  | y =>
      simpa [step, configStepSize] using
        ringCycle_y_via_expand hcycle (by omega)
  | h =>
      simpa [step, configStepSize] using
        ringCycle_h_via_expand hcycle hsize
  | u =>
      simpa [step, configStepSize] using ringCycle_u hcycle (by omega)

private theorem programTraceStep_ringTrace_of_config
    {P : PointedHypermap} {s : CpStep} {input output : ColSeq}
    (hs : ColoringConfigStep s)
    (htrace : P.map.RingTrace (ringDarts P P.nodeOrder) input)
    (hstep : ProgramTraceStep s input output) :
    (step s P).map.RingTrace
      (ringDarts (step s P) (step s P).nodeOrder) output := by
  have hcycle : RingCycle P P.nodeOrder := nodeOrder_ringCycle P
  have hsize : 1 < P.nodeOrder :=
    Hypermap.RingTrace.nodeOrder_gt_one htrace
  have hcycle' := ringCycle_configStep hs hcycle hsize
  rw [hcycle'.nodeOrder_eq]
  exact configTraceStep_ringTrace hs hcycle hsize htrace
    ((configTraceStep_iff_programTraceStep hs _ _).2 hstep)

/-- Semantic soundness of one arbitrary coloring-program step on Coq's
dynamically sized ring. -/
theorem programTraceStep_ringTrace
    {P : PointedHypermap} {s : CpStep} {input output : ColSeq}
    (htrace : P.map.RingTrace
      (ringDarts P P.nodeOrder) input)
    (hstep : ProgramTraceStep s input output) :
    (step s P).map.RingTrace
      (ringDarts (step s P) (step s P).nodeOrder) output := by
  let n := P.nodeOrder
  have hcycle : RingCycle P n := nodeOrder_ringCycle P
  have hsize : 1 < n :=
    Hypermap.RingTrace.nodeOrder_gt_one htrace
  cases s with
  | rotate r =>
      exact programTraceStep_ringTrace_of_config
        (ColoringConfigStep.rotate r) htrace hstep
  | reverseRotate =>
      have hout : output = CProg.rotateRight 1 input := by
        simpa [ProgramTraceStep, CProg.cpColorStepSpec] using hstep.2
      subst output
      have hcycle' : RingCycle P.reverseRotate n :=
        ringCycle_reverseRotate hcycle (by omega)
      change P.reverseRotate.map.RingTrace
        (ringDarts P.reverseRotate P.reverseRotate.nodeOrder)
        (CProg.rotateRight 1 input)
      rw [hcycle'.nodeOrder_eq]
      simpa [step] using ringTrace_reverseRotate hcycle hsize htrace
  | y =>
      exact programTraceStep_ringTrace_of_config
        ColoringConfigStep.y htrace hstep
  | h =>
      exact programTraceStep_ringTrace_of_config
        ColoringConfigStep.h htrace hstep
  | u =>
      exact programTraceStep_ringTrace_of_config
        ColoringConfigStep.u htrace hstep
  | k =>
      cases hinput : input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec, hinput] at hstep
      | cons e1 tail =>
          cases htail : tail with
          | nil =>
              simp [ProgramTraceStep, CProg.cpColorStepSpec,
                hinput, htail] at hstep
          | cons e2 rest =>
              have htrace' : P.map.RingTrace (ringDarts P n)
                  (e1 :: e2 :: rest) := by simpa [hinput, htail] using htrace
              have hparts :
                  e1 ≠ e2 ∧ output = (e1 + e2) :: rest := by
                simpa [ProgramTraceStep, CProg.cpColorStepSpec,
                  hinput, htail] using hstep
              have hlen : (e1 :: e2 :: rest).length = n := by
                simpa using Hypermap.RingTrace.length
                  (G := P.map) htrace'
              have hlong : 2 < n := by
                by_contra hn
                have hnTwo : n = 2 := by omega
                have hrestLen : rest.length = 0 := by
                  simp only [List.length_cons] at hlen
                  omega
                have hrest : rest = [] :=
                  List.eq_nil_of_length_eq_zero hrestLen
                subst rest
                have hsum := Hypermap.RingTrace.sum_zero
                  (G := P.map) htrace'
                have hzero : e1 + e2 = Color.zero := by
                  simpa [ColSeq.sum] using hsum
                exact hparts.1 (Color.add_eq_zero_iff_eq e1 e2 |>.1 hzero)
              rw [hparts.2]
              have hcycle' := ringCycle_k hcycle hlong
              change P.k.map.RingTrace
                (ringDarts P.k P.k.nodeOrder) ((e1 + e2) :: rest)
              rw [hcycle'.nodeOrder_eq]
              simpa [step] using
                ringTrace_k_of_ringTrace hcycle hlong htrace' hparts.1
  | a =>
      cases hinput : input with
      | nil => simp [ProgramTraceStep, CProg.cpColorStepSpec, hinput] at hstep
      | cons e1 tail =>
          cases htail : tail with
          | nil =>
              simp [ProgramTraceStep, CProg.cpColorStepSpec,
                hinput, htail] at hstep
          | cons e2 rest =>
              have htrace' : P.map.RingTrace (ringDarts P n)
                  (e1 :: e2 :: rest) := by simpa [hinput, htail] using htrace
              have hparts :
                  e1 = e2 ∧
                    output = if rest = [] then e1 :: e2 :: rest else rest := by
                simpa [ProgramTraceStep, CProg.cpColorStepSpec,
                  hinput, htail] using hstep
              rcases hparts with ⟨rfl, hout⟩
              have hlen : (e1 :: e1 :: rest).length = n := by
                simpa using Hypermap.RingTrace.length
                  (G := P.map) htrace'
              by_cases hlong : 2 < n
              · have hrest : rest ≠ [] := by
                  intro hr
                  subst rest
                  simp only [List.length_cons, List.length_nil] at hlen
                  omega
                rw [hout, if_neg hrest]
                change P.a.map.RingTrace
                  (ringDarts P.a P.a.nodeOrder) rest
                have hcycle' := ringCycle_a hcycle hlong
                rw [hcycle'.nodeOrder_eq]
                simpa [step] using
                  ringTrace_a_of_ringTrace hcycle hlong htrace'
              · have hnTwo : n = 2 := by omega
                have hrestLen : rest.length = 0 := by
                  simp only [List.length_cons] at hlen
                  omega
                have hrest : rest = [] :=
                  List.eq_nil_of_length_eq_zero hrestLen
                subst rest
                have hout : output = [e1, e1] := by
                  simpa using hout
                rw [hout]
                change P.a.map.RingTrace
                  (ringDarts P.a P.a.nodeOrder) [e1, e1]
                have hcycle' := ringCycle_a_of_eq_two hcycle hnTwo
                rw [hcycle'.nodeOrder_eq]
                rw [hnTwo] at htrace'
                exact (ringTrace_a_iff_of_ringCycle_eq_two
                  hcycle hnTwo).2 htrace'

private theorem programTraceStep_ringTrace_elim_of_config
    {P : PointedHypermap} {n : Nat} {s : CpStep} {output : ColSeq}
    (hs : ColoringConfigStep s) (hcycle : RingCycle P n) (hsize : 1 < n)
    (htrace : (step s P).map.RingTrace
      (ringDarts (step s P) (step s P).nodeOrder) output) :
    ∃ input,
      P.map.RingTrace (ringDarts P P.nodeOrder) input ∧
        ProgramTraceStep s input output := by
  have hcycle' := ringCycle_configStep hs hcycle hsize
  have htrace' : (step s P).map.RingTrace
      (ringDarts (step s P) (configStepSize s n)) output := by
    rw [← hcycle'.nodeOrder_eq]
    exact htrace
  rcases configTraceStep_ringTrace_elim hs hcycle hsize htrace' with
    ⟨input, hinput, hstep⟩
  refine ⟨input, ?_, (configTraceStep_iff_programTraceStep hs _ _).1 hstep⟩
  rw [hcycle.nodeOrder_eq]
  exact hinput

/-- Converse semantic theorem for one arbitrary coloring-program step. -/
theorem programTraceStep_ringTrace_elim
    {P : PointedHypermap} {s : CpStep} {output : ColSeq}
    (htrace : (step s P).map.RingTrace
      (ringDarts (step s P) (step s P).nodeOrder) output) :
    ∃ input,
      P.map.RingTrace (ringDarts P P.nodeOrder) input ∧
        ProgramTraceStep s input output := by
  let n := P.nodeOrder
  have hcycle : RingCycle P n := nodeOrder_ringCycle P
  have hnpos : 0 < n := P.nodeOrder_pos
  cases s with
  | rotate r =>
      have hsize : 1 < n := by
        have htarget := Hypermap.RingTrace.nodeOrder_gt_one htrace
        change 1 < (P.rotate r).nodeOrder at htarget
        rw [(rotate_ringCycle (r := r) hcycle).nodeOrder_eq] at htarget
        exact htarget
      exact programTraceStep_ringTrace_elim_of_config
        (ColoringConfigStep.rotate r) hcycle hsize htrace
  | reverseRotate =>
      have hcycle' : RingCycle P.reverseRotate n :=
        ringCycle_reverseRotate hcycle hnpos
      have htrace' : P.reverseRotate.map.RingTrace
          (ringDarts P.reverseRotate n) output := by
        change P.reverseRotate.map.RingTrace
          (ringDarts P.reverseRotate P.reverseRotate.nodeOrder) output at htrace
        rwa [hcycle'.nodeOrder_eq] at htrace
      let input := CProg.rotateLeft 1 output
      have hold : P.map.RingTrace (ringDarts P n) input := by
        simpa [input] using
          ringTrace_reverseRotate_elim hcycle hnpos htrace'
      have hlen : input.length = n := by
        simpa using Hypermap.RingTrace.length (G := P.map) hold
      have hsize : 1 < n :=
        Hypermap.RingTrace.nodeOrder_gt_one hold
      refine ⟨input, hold, ?_⟩
      constructor
      · omega
      · simpa [input] using (CProg.rotateRight_rotateLeft 1 output).symm
  | y =>
      rcases htrace.exists_coloring with ⟨ky, hky, _⟩
      have hsourceColor : P.map.Coloring (restrictYColor P ky) :=
        restrictYColor_coloring hky
      have hsize : 1 < n :=
        hcycle.one_lt_of_properRingHead
          (hsourceColor.properRingHead P.point)
      exact programTraceStep_ringTrace_elim_of_config
        ColoringConfigStep.y hcycle hsize htrace
  | h =>
      rcases htrace.exists_coloring with ⟨kh, hkh, _⟩
      have hsourceColor : P.map.Coloring (restrictHColor P kh) :=
        restrictHColor_coloring hkh
      have hsize : 1 < n :=
        hcycle.one_lt_of_properRingHead
          (hsourceColor.properRingHead P.point)
      exact programTraceStep_ringTrace_elim_of_config
        ColoringConfigStep.h hcycle hsize htrace
  | u =>
      rcases htrace.exists_coloring with ⟨ku, hku, _⟩
      have hsourceColor : P.map.Coloring (restrictUColor P ku) :=
        restrictUColor_coloring hku
      have hsize : 1 < n :=
        hcycle.one_lt_of_properRingHead
          (hsourceColor.properRingHead P.point)
      exact programTraceStep_ringTrace_elim_of_config
        ColoringConfigStep.u hcycle hsize htrace
  | k =>
      rcases htrace.exists_coloring with ⟨kk, hkk, _⟩
      have hsourceColor : P.map.Coloring (restrictKColor P kk) :=
        restrictKColor_coloring hkk
      have hsize : 1 < n :=
        hcycle.one_lt_of_properRingHead
          (hsourceColor.properRingHead P.point)
      by_cases hlong : 2 < n
      · have hcycle' := ringCycle_k hcycle hlong
        have htrace' : P.k.map.RingTrace
            (ringDarts P.k (n - 2 + 1)) output := by
          change P.k.map.RingTrace
            (ringDarts P.k P.k.nodeOrder) output at htrace
          rwa [hcycle'.nodeOrder_eq] at htrace
        rcases ringTrace_k_elim hcycle hlong htrace' with
          ⟨e1, e2, rest, hne, hold, hout⟩
        refine ⟨e1 :: e2 :: rest, hold, ?_⟩
        simpa [ProgramTraceStep, CProg.cpColorStepSpec, hne] using
          And.intro hne hout
      · have hnTwo : n = 2 := by omega
        exact (not_coloring_k_of_ringCycle_eq_two hcycle hnTwo
          ⟨kk, hkk⟩).elim
  | a =>
      rcases htrace.exists_coloring with ⟨ka, hka, _⟩
      have hsourceColor : P.map.Coloring (restrictAColor P ka) :=
        restrictAColor_coloring hka
      have hsize : 1 < n :=
        hcycle.one_lt_of_properRingHead
          (hsourceColor.properRingHead P.point)
      by_cases hlong : 2 < n
      · have hcycle' := ringCycle_a hcycle hlong
        have htrace' : P.a.map.RingTrace
            (ringDarts P.a (n - 2)) output := by
          change P.a.map.RingTrace
            (ringDarts P.a P.a.nodeOrder) output at htrace
          rwa [hcycle'.nodeOrder_eq] at htrace
        rcases ringTrace_a_elim hcycle hlong htrace' with
          ⟨e1, e2, rest, heq, hold, hout⟩
        have hlen : (e1 :: e2 :: rest).length = n := by
          simpa using Hypermap.RingTrace.length (G := P.map) hold
        have hrest : rest ≠ [] := by
          intro hr
          have hnEq : n = 2 := by
            simpa [hr] using hlen.symm
          omega
        refine ⟨e1 :: e2 :: rest, hold, ?_⟩
        simp [ProgramTraceStep, CProg.cpColorStepSpec, heq, hrest, hout]
      · have hnTwo : n = 2 := by omega
        have hcycle' := ringCycle_a_of_eq_two hcycle hnTwo
        have htrace' : P.a.map.RingTrace (ringDarts P.a 2) output := by
          change P.a.map.RingTrace
            (ringDarts P.a P.a.nodeOrder) output at htrace
          rwa [hcycle'.nodeOrder_eq] at htrace
        have hold : P.map.RingTrace (ringDarts P 2) output :=
          (ringTrace_a_iff_of_ringCycle_eq_two hcycle hnTwo).1 htrace'
        have holdN : P.map.RingTrace (ringDarts P n) output := by
          rwa [hnTwo]
        have hlen : output.length = 2 := by
          simpa using Hypermap.RingTrace.length (G := P.map) hold
        have hsum := Hypermap.RingTrace.sum_zero (G := P.map) hold
        cases output with
        | nil => simp at hlen
        | cons e1 tail =>
            cases tail with
            | nil => simp at hlen
            | cons e2 rest =>
                have hrestLen : rest.length = 0 := by
                  simp only [List.length_cons] at hlen
                  omega
                have hrest : rest = [] :=
                  List.eq_nil_of_length_eq_zero hrestLen
                subst rest
                have heq : e1 = e2 :=
                  (Color.add_eq_zero_iff_eq e1 e2).1 (by
                    simpa [ColSeq.sum] using hsum)
                refine ⟨[e1, e2], holdN, ?_⟩
                simp [ProgramTraceStep, CProg.cpColorStepSpec, heq]

/-- Soundness of an arbitrary construction-order trace fold. -/
theorem programTraceFold_ringTrace :
    ∀ {ss : CProg} {P : PointedHypermap} {input output : ColSeq},
      P.map.RingTrace (ringDarts P P.nodeOrder) input →
      ProgramTraceFold ss input output →
      (applyConfigSteps P ss).map.RingTrace
        (ringDarts (applyConfigSteps P ss)
          (applyConfigSteps P ss).nodeOrder) output
  | [], P, input, output, htrace, hfold => by
      change output = input at hfold
      subst output
      simpa [applyConfigSteps] using htrace
  | s :: ss, P, input, output, htrace, hfold => by
      rcases hfold with ⟨mid, hstep, hrest⟩
      have hmid := programTraceStep_ringTrace htrace hstep
      simpa [applyConfigSteps] using
        programTraceFold_ringTrace hmid hrest

/-- Exhaustiveness of an arbitrary construction-order trace fold. -/
theorem programTraceFold_ringTrace_elim :
    ∀ {ss : CProg} {P : PointedHypermap} {output : ColSeq},
      (applyConfigSteps P ss).map.RingTrace
          (ringDarts (applyConfigSteps P ss)
            (applyConfigSteps P ss).nodeOrder) output →
        ∃ input,
          P.map.RingTrace (ringDarts P P.nodeOrder) input ∧
            ProgramTraceFold ss input output
  | [], P, output, htrace => by
      exact ⟨output, by simpa [applyConfigSteps] using htrace,
        by simp [ProgramTraceFold, TraceFold]⟩
  | s :: ss, P, output, htrace => by
      have htail :
          (applyConfigSteps (step s P) ss).map.RingTrace
            (ringDarts (applyConfigSteps (step s P) ss)
              (applyConfigSteps (step s P) ss).nodeOrder) output := by
        simpa [applyConfigSteps] using htrace
      rcases programTraceFold_ringTrace_elim htail with
        ⟨mid, hmid, hrest⟩
      rcases programTraceStep_ringTrace_elim hmid with
        ⟨input, hinput, hstep⟩
      exact ⟨input, hinput, ⟨mid, hstep, hrest⟩⟩


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
