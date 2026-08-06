import FourColorTheorem.FourColor.Coloring.CFColorMap.ProgramEquivariance
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Soundness of the relational trace fold. -/
theorem configTraceFold_ringTrace :
    ∀ {ss : CProg},
      List.Forall ColoringConfigStep ss →
      ∀ {P : PointedHypermap} {n : Nat} {input final : ColSeq},
        RingCycle P n →
        1 < n →
        P.map.RingTrace (ringDarts P n) input →
        ConfigTraceFold ss input final →
        (applyConfigSteps P ss).map.RingTrace
          (ringDarts (applyConfigSteps P ss) (configStepsSize n ss)) final
  | [], _hss, P, n, input, final, _hcycle, _hsize, htrace, hfold => by
      have hEq : final = input := by
        simpa [ConfigTraceFold, TraceFold] using hfold
      simpa [applyConfigSteps, configStepsSize, hEq] using htrace
  | s :: ss, hss, P, n, input, final, hcycle, hsize, htrace, hfold => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have hs := hparts.1
      have htail := hparts.2
      rcases hfold with ⟨mid, hstep, hrest⟩
      have hmid := configTraceStep_ringTrace hs hcycle hsize htrace hstep
      have hcycle' := ringCycle_configStep hs hcycle hsize
      have hsize' := configStepSize_gt_one hs hsize
      simpa [applyConfigSteps, configStepsSize] using
        (configTraceFold_ringTrace htail hcycle' hsize' hmid hrest)

/-- Exhaustiveness of the relational trace fold. -/
theorem configTraceFold_ringTrace_elim :
    ∀ {ss : CProg},
      List.Forall ColoringConfigStep ss →
      ∀ {P : PointedHypermap} {n : Nat} {final : ColSeq},
        RingCycle P n →
        1 < n →
        (applyConfigSteps P ss).map.RingTrace
            (ringDarts (applyConfigSteps P ss) (configStepsSize n ss)) final →
        ∃ input,
          P.map.RingTrace (ringDarts P n) input ∧
            ConfigTraceFold ss input final
  | [], _hss, P, n, final, _hcycle, _hsize, htrace => by
      exact ⟨final, by simpa [applyConfigSteps, configStepsSize] using htrace,
        by simp [ConfigTraceFold, TraceFold]⟩
  | s :: ss, hss, P, n, final, hcycle, hsize, htrace => by
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      have hs := hparts.1
      have htail := hparts.2
      have hcycle' := ringCycle_configStep hs hcycle hsize
      have hsize' := configStepSize_gt_one hs hsize
      have htrace' :
          (applyConfigSteps (step s P) ss).map.RingTrace
            (ringDarts (applyConfigSteps (step s P) ss)
              (configStepsSize (configStepSize s n) ss)) final := by
        simpa [applyConfigSteps, configStepsSize] using htrace
      rcases configTraceFold_ringTrace_elim htail hcycle' hsize' htrace' with
        ⟨mid, hmid, hrest⟩
      rcases configTraceStep_ringTrace_elim hs hcycle hsize hmid with
        ⟨input, hinput, hstep⟩
      exact ⟨input, hinput, ⟨mid, hstep, hrest⟩⟩

/-- A well-formed configuration, reversed into construction order, begins
with its required initial `Y`; every remaining step is `Y`, `H`, or rotation. -/
theorem config_reverse_decompose :
    ∀ {cp : CProg}, CProg.config cp = true →
      ∃ ss,
        cp.reverse = CpStep.y :: ss ∧
          List.Forall ColoringConfigStep ss
  | [], hcfg => by simp [CProg.config] at hcfg
  | CpStep.rotate r :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      rcases config_reverse_decompose htail with ⟨ss, hrev, hss⟩
      refine ⟨ss ++ [CpStep.rotate r], ?_, ?_⟩
      · simp [hrev]
      · exact (List.forall_append).2
          ⟨hss, by simp [ColoringConfigStep.rotate]⟩
  | CpStep.reverseRotate :: cp, hcfg => by
      simp [CProg.config] at hcfg
  | CpStep.y :: cp, hcfg => by
      cases cp with
      | nil => exact ⟨[], rfl, by simp⟩
      | cons s cp =>
          have htail : CProg.config (s :: cp) = true := by
            simpa [CProg.config] using hcfg
          rcases config_reverse_decompose htail with ⟨ss, hrev, hss⟩
          refine ⟨ss ++ [CpStep.y], ?_, ?_⟩
          · simp [hrev]
          · exact (List.forall_append).2
              ⟨hss, by simp [ColoringConfigStep.y]⟩
  | CpStep.h :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      rcases config_reverse_decompose htail with ⟨ss, hrev, hss⟩
      refine ⟨ss ++ [CpStep.h], ?_, ?_⟩
      · simp [hrev]
      · exact (List.forall_append).2
          ⟨hss, by simp [ColoringConfigStep.h]⟩
  | CpStep.u :: cp, hcfg => by simp [CProg.config] at hcfg
  | CpStep.k :: cp, hcfg => by simp [CProg.config] at hcfg
  | CpStep.a :: cp, hcfg => by simp [CProg.config] at hcfg

theorem cpmap_eq_foldr_step (cp : CProg) :
    cpmap cp = cp.foldr step base := by
  induction cp with
  | nil => rfl
  | cons s cp ih => simp [cpmap, ih]

theorem applyConfigSteps_eq_foldr_reverse
    (P : PointedHypermap) (ss : CProg) :
    applyConfigSteps P ss = ss.reverse.foldr step P := by
  induction ss generalizing P with
  | nil => rfl
  | cons s ss ih =>
      simp [applyConfigSteps, ih]

/-- Construction-order application agrees with `cpmap` on an arbitrary
already-built suffix. -/
theorem cpmap_reverse_append_eq_applyConfigSteps
    (Pfx cp : CProg) :
    cpmap (Pfx.reverse ++ cp) = applyConfigSteps (cpmap cp) Pfx := by
  rw [cpmap_eq_foldr_step, applyConfigSteps_eq_foldr_reverse,
    List.foldr_append, ← cpmap_eq_foldr_step]

/-- The syntactic ring-size recurrence is the corresponding construction-order
size fold. -/
theorem ringSize_reverse_append_eq_configStepsSize
    {ss : CProg} (hss : List.Forall ColoringConfigStep ss) (cp : CProg) :
    CProg.ringSize (ss.reverse ++ cp) =
      configStepsSize (CProg.ringSize cp) ss := by
  induction ss generalizing cp with
  | nil => simp [configStepsSize]
  | cons s ss ih =>
      have hparts := (List.forall_cons
        (p := ColoringConfigStep) (x := s) (l := ss)).mp hss
      rw [List.reverse_cons, List.append_assoc]
      change CProg.ringSize (ss.reverse ++ (s :: cp)) = _
      rw [ih hparts.2]
      cases hparts.1 <;> simp [CProg.ringSize, configStepsSize, configStepSize]

/-- The canonical two-dart base map has trace `[3,3]`. -/
theorem ringTrace_base_three :
    base.map.RingTrace (ringDarts base 2) [Color.three, Color.three] := by
  let k : base.map.Dart → Color :=
    fun b => if b = true then Color.three else Color.zero
  refine ⟨k, ?_, ?_⟩
  · constructor
    · intro b
      cases b <;> decide
    · intro b
      rfl
  · decide

/-- Every coloring trace of the two-dart base map is a global permutation of
Coq's canonical initial trace `[one, one]`. -/
theorem ringTrace_base_perm_one_one
    {et : ColSeq}
    (htrace : base.map.RingTrace (ringDarts base 2) et) :
    ∃ g : EdgePerm,
      ColSeq.perm g et = [Color.one, Color.one] := by
  have hlen : et.length = 2 := by
    simpa using Hypermap.RingTrace.length (G := base.map) htrace
  have hsum := Hypermap.RingTrace.sum_zero (G := base.map) htrace
  have hzero : Color.zero ∉ et :=
    ringTrace_not_mem_zero base_ringCycle (by decide) htrace
  cases et with
  | nil => simp at hlen
  | cons e1 tail =>
      cases tail with
      | nil => simp at hlen
      | cons e2 rest =>
          cases rest with
          | cons e3 rest => simp at hlen
          | nil =>
              have heq : e1 = e2 :=
                (Color.add_eq_zero_iff_eq e1 e2).1 (by
                  simpa [ColSeq.sum] using hsum)
              subst e2
              have he1 : e1 ≠ Color.zero := by
                intro hz
                subst e1
                exact hzero (by simp)
              refine ⟨EdgePerm.edgeRot e1, ?_⟩
              change [EdgePerm.edgeRot e1 e1, EdgePerm.edgeRot e1 e1] = _
              rw [ColSeq.edgeRot_apply_self he1]

/-- Completeness half of Coq `ctree_mem_cpcolor` for an arbitrary program
whose advertised boundary is its exact dynamic node ring. -/
theorem cpColorSpec_of_ringTrace
    {cp : CProg} (hcycle : cpRingCycle cp) {et : ColSeq}
    (heven : ColSeq.evenTrace et = true)
    (htrace : (cpmap cp).map.RingTrace
      (cpRing cp) (ColSeq.sum et :: et)) :
    CProg.cpColorSpec cp et := by
  let ss := cp.reverse
  have hmap : cpmap cp = applyConfigSteps base ss := by
    simpa [ss] using cpmap_reverse_append_eq_applyConfigSteps cp.reverse []
  have htraceDynamic :
      (cpmap cp).map.RingTrace
        (ringDarts (cpmap cp) (cpmap cp).nodeOrder)
        (ColSeq.sum et :: et) := by
    rw [hcycle.nodeOrder_eq]
    exact htrace
  have htraceApplied :
      (applyConfigSteps base ss).map.RingTrace
        (ringDarts (applyConfigSteps base ss)
          (applyConfigSteps base ss).nodeOrder)
        (ColSeq.sum et :: et) := by
    rw [← hmap]
    exact htraceDynamic
  rcases programTraceFold_ringTrace_elim htraceApplied with
    ⟨initial, hinitial, hfold⟩
  have hbaseOrder : base.nodeOrder = 2 := base_ringCycle.nodeOrder_eq
  rw [hbaseOrder] at hinitial
  rcases ringTrace_base_perm_one_one hinitial with ⟨g, hg⟩
  have hfold' := programTraceFold_perm g hfold
  rw [hg] at hfold'
  have hlong : 1 < (cpmap cp).nodeOrder :=
    Hypermap.RingTrace.nodeOrder_gt_one htraceDynamic
  have hfullNoZero : Color.zero ∉ ColSeq.sum et :: et :=
    ringTrace_not_mem_zero (nodeOrder_ringCycle (cpmap cp)) hlong
      htraceDynamic
  have hetNoZero : Color.zero ∉ et := by
    intro hz
    exact hfullNoZero (by simp [hz])
  have hfullLen :
      (ColSeq.sum et :: et).length = (cpmap cp).nodeOrder := by
    simpa using Hypermap.RingTrace.length
      (G := (cpmap cp).map) htraceDynamic
  have hetPos : 0 < et.length := by
    simp only [List.length_cons] at hfullLen
    omega
  have hetProper : ColSeq.ProperTrace et := by
    cases et with
    | nil => simp at hetPos
    | cons e tail =>
        simp only [ColSeq.ProperTrace, ColSeq.headColor]
        intro he
        subst e
        exact hetNoZero (by simp)
  have hrest :
      (ColSeq.perm g (ColSeq.sum et :: et)).drop 1 =
        ColSeq.perm g et := by
    simp [ColSeq.perm]
  have hpermNoZero : Color.zero ∉ ColSeq.perm g et := by
    simpa only [ColSeq.perm_zero_mem_iff] using hetNoZero
  have hpermProper : ColSeq.ProperTrace (ColSeq.perm g et) :=
    (ColSeq.proper_perm_iff g et).2 hetProper
  have hbranch : CProg.cpBranchTraceSpec
      (ColSeq.perm g (ColSeq.sum et :: et)) (ColSeq.ttail et) := by
    constructor
    · rw [hrest]
      exact (ColSeq.not_mem_zero_etail_iff _).2
        ⟨hpermProper, hpermNoZero⟩
    · rw [hrest, ColSeq.etail_perm_eq]
      exact (ColSeq.etail_eq_ttail_of_evenTrace heven).symm
  have hfoldSpec : CProg.cpColorFoldSpec ss
      [Color.one, Color.one] (ColSeq.ttail et) :=
    (cpColorFoldSpec_iff_exists_programTraceFold ss _ _).2
      ⟨ColSeq.perm g (ColSeq.sum et :: et), hfold', hbranch⟩
  change CProg.cpColor0Spec cp.reverse (ColSeq.ttail et)
  exact cpColorFoldSpec_base_to_cpColor0Spec_general hfoldSpec

/-- Executable completeness form of Coq `ctree_mem_cpcolor` for arbitrary
contracted programs. -/
theorem ctree_mem_cpColor
    {cp : CProg} (hcycle : cpRingCycle cp) {et : ColSeq}
    (heven : ColSeq.evenTrace et = true)
    (htrace : (cpmap cp).map.RingTrace
      (cpRing cp) (ColSeq.sum et :: et)) :
    CTree.mem (CProg.cpColor cp) et = true :=
  (CProg.cpColor_mem_iff_general cp et).2
    (cpColorSpec_of_ringTrace hcycle heven htrace)

/-- Completeness half of Coq `ctree_mem_cpcolor` for every cubic construction
program, including the checker-only base programs `[]` and `[U]`. -/
theorem cpColorSpec_of_ringTrace_of_cubic
    {cp : CProg} (hcp : CProg.cubic cp = true) {et : ColSeq}
    (heven : ColSeq.evenTrace et = true)
    (htrace : (cpmap cp).map.RingTrace
      (cpRing cp) (ColSeq.sum et :: et)) :
    CProg.cpColorSpec cp et := by
  let ss := cp.reverse
  have hss : List.Forall ColoringConfigStep ss := by
    simpa [ss] using coloringConfigSteps_reverse_of_cubic hcp
  have hmap : cpmap cp = applyConfigSteps base ss := by
    simpa [ss] using cpmap_reverse_append_eq_applyConfigSteps cp.reverse []
  have hsize : CProg.ringSize cp = configStepsSize 2 ss := by
    simpa [ss, CProg.ringSize] using
      ringSize_reverse_append_eq_configStepsSize hss ([] : CProg)
  have hcycleApplied :
      RingCycle (applyConfigSteps base ss) (configStepsSize 2 ss) :=
    ringCycle_configSteps hss base_ringCycle (by decide)
  have hcycle : cpRingCycle cp := by
    change RingCycle (cpmap cp) (CProg.ringSize cp)
    rw [hmap, hsize]
    exact hcycleApplied
  exact cpColorSpec_of_ringTrace hcycle heven htrace

theorem ctree_mem_cpColor_of_cubic
    {cp : CProg} (hcp : CProg.cubic cp = true) {et : ColSeq}
    (heven : ColSeq.evenTrace et = true)
    (htrace : (cpmap cp).map.RingTrace
      (cpRing cp) (ColSeq.sum et :: et)) :
    CTree.mem (CProg.cpColor cp) et = true :=
  (cpColor_mem_iff_cpColorSpec_of_cubic hcp et).2
    (cpColorSpec_of_ringTrace_of_cubic hcp heven htrace)

/-- Coq's normalized initial `Y` coloring trace. -/
theorem ringTrace_base_y_one_two_three :
    base.y.map.RingTrace (ringDarts base.y 3)
      [Color.one, Color.two, Color.three] := by
  have h := ringTrace_y_choice base_ringCycle (by decide)
    ringTrace_base_three (c := Color.one) (d := Color.two)
    (by decide) (by decide) (by decide)
  simpa using h

/-- The only even, nonzero pair with xor sum `one` is Coq's canonical tail
`[two, three]`. -/
theorem evenPair_eq_two_three
    {et : ColSeq}
    (hlen : et.length = 2)
    (hzero : Color.zero ∉ et)
    (hsum : ColSeq.sum et = Color.one)
    (heven : ColSeq.evenTail et = true) :
    et = [Color.two, Color.three] := by
  cases et with
  | nil => simp at hlen
  | cons e1 tail =>
      cases tail with
      | nil => simp at hlen
      | cons e2 rest =>
          cases rest with
          | nil =>
              cases e1 <;> cases e2 <;>
                simp_all [ColSeq.sum, ColSeq.evenTail]
          | cons e3 rest => simp at hlen

/-- Every coloring trace of the initial three-dart `Y` map is a global edge
color permutation of the canonical trace `[one, two, three]`. -/
theorem ringTrace_base_y_perm_canonical
    {et : ColSeq}
    (htrace : base.y.map.RingTrace (ringDarts base.y 3) et) :
    ∃ g : EdgePerm,
      ColSeq.perm g et = [Color.one, Color.two, Color.three] := by
  have hcycle : RingCycle base.y 3 := by
    simpa using ringCycle_y_via_expand base_ringCycle (by decide)
  have hlen : et.length = 3 := by
    simpa using Hypermap.RingTrace.length (G := base.y.map) htrace
  have hzero : Color.zero ∉ et :=
    ringTrace_not_mem_zero hcycle (by decide) htrace
  have hproper : ColSeq.ProperTrace et := by
    cases et with
    | nil => simp at hlen
    | cons e tail =>
        simp only [ColSeq.ProperTrace, ColSeq.headColor]
        intro he
        subst e
        exact hzero (by simp)
  rcases ColSeq.etail_perm hproper with ⟨g, hg⟩
  have htrace' := Hypermap.RingTrace.perm (G := base.y.map) htrace g
  rw [hg] at htrace'
  have hzero' : Color.zero ∉ ColSeq.etail et := by
    have hall := ringTrace_not_mem_zero hcycle (by decide) htrace'
    intro hz
    exact hall (by simp [hz])
  have htailLen : (ColSeq.etail et).length = 2 := by
    have htail := ColSeq.length_etail_of_proper hproper
    omega
  have htailSum : ColSeq.sum (ColSeq.etail et) = Color.one := by
    have hsum := Hypermap.RingTrace.sum_zero (G := base.y.map) htrace'
    have hone : Color.one = ColSeq.sum (ColSeq.etail et) :=
      (Color.add_eq_zero_iff_eq _ _).mp (by
        simpa [ColSeq.sum] using hsum)
    exact hone.symm
  have htail : ColSeq.etail et = [Color.two, Color.three] :=
    evenPair_eq_two_three htailLen hzero' htailSum (ColSeq.even_etail et)
  exact ⟨g, by simpa [htail] using hg⟩

/-- Semantic soundness of `cpColor0Spec` for a genuine configuration, before
the final global color normalization. -/
theorem cpColor0Spec_exists_ringTrace_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) {out : ColSeq}
    (hspec : CProg.cpColor0Spec cp.reverse out) :
    ∃ final,
      (cpmap cp).map.RingTrace (cpRing cp) final ∧
        CProg.cpBranchTraceSpec final out := by
  rcases config_reverse_decompose hcfg with ⟨ss, hrev, hss⟩
  have hspec' :
      CProg.cpColorFoldSpec ss
        [Color.one, Color.two, Color.three] out := by
    simpa [hrev, CProg.cpColor0Spec] using hspec
  rcases (cpColorFoldSpec_iff_exists_configTraceFold hss _ _).1 hspec' with
    ⟨final, hfold, hbranch⟩
  have hcycle0 : RingCycle base.y 3 := by
    simpa using ringCycle_y_via_expand base_ringCycle (by decide)
  have hfinal := configTraceFold_ringTrace hss hcycle0 (by decide)
    ringTrace_base_y_one_two_three hfold
  have hcp : cp = ss.reverse ++ [CpStep.y] := by
    calc
      cp = cp.reverse.reverse := (List.reverse_reverse cp).symm
      _ = (CpStep.y :: ss).reverse := by rw [hrev]
      _ = ss.reverse ++ [CpStep.y] := by simp
  have hmap : cpmap cp = applyConfigSteps base.y ss := by
    rw [hcp, cpmap_reverse_append_eq_applyConfigSteps]
    rfl
  have hsize : CProg.ringSize cp = configStepsSize 3 ss := by
    rw [hcp, ringSize_reverse_append_eq_configStepsSize hss]
    rfl
  refine ⟨final, ?_, hbranch⟩
  change (cpmap cp).map.RingTrace
    (ringDarts (cpmap cp) (CProg.ringSize cp)) final
  have htransport :
      (cpmap cp).map.RingTrace
        (ringDarts (cpmap cp) (configStepsSize 3 ss)) final :=
    hmap.symm ▸ hfinal
  rw [hsize]
  exact htransport

/-- The branch normalizer sends any represented ring trace to Coq's canonical
`sum et :: et` representative. -/
theorem ringTrace_normalize_of_cpBranch
    {G : Hypermap} {r : List G.Dart} {full et : ColSeq}
    (htrace : G.RingTrace r full)
    (hbranch : CProg.cpBranchTraceSpec full (ColSeq.ttail et))
    (hproper : ColSeq.ProperTrace et)
    (hetail : ColSeq.etail et = ColSeq.ttail et) :
    G.RingTrace r (ColSeq.sum et :: et) := by
  cases full with
  | nil =>
      exact (hbranch.1 (by decide)).elim
  | cons c rest =>
      have hrestProper : ColSeq.ProperTrace rest :=
        ((ColSeq.not_mem_zero_etail_iff rest).1 hbranch.1).1
      rcases ColSeq.etail_perm hrestProper with ⟨gr, hgr⟩
      rcases ColSeq.etail_perm hproper with ⟨ge, hge⟩
      have htails : ColSeq.etail rest = ColSeq.etail et :=
        hbranch.2.symm.trans hetail.symm
      have hnorm : ColSeq.perm gr rest = ColSeq.perm ge et := by
        rw [hgr, hge, htails]
      let g := EdgePerm.comp (EdgePerm.inv ge) gr
      have hrest : ColSeq.perm g rest = et := by
        change ColSeq.perm (EdgePerm.comp (EdgePerm.inv ge) gr) rest = et
        rw [ColSeq.perm_comp, hnorm, ColSeq.perm_inv]
      have hsum : c + ColSeq.sum rest = Color.zero := by
        simpa using Hypermap.RingTrace.sum_zero (G := G) htrace
      have hc : c = ColSeq.sum rest :=
        (Color.add_eq_zero_iff_eq c (ColSeq.sum rest)).1 hsum
      have hgc : g c = ColSeq.sum et := by
        calc
          g c = g (ColSeq.sum rest) := congrArg g hc
          _ = ColSeq.sum (ColSeq.perm g rest) :=
            (ColSeq.perm_sum g rest).symm
          _ = ColSeq.sum et := by rw [hrest]
      have hp := Hypermap.RingTrace.perm (G := G) htrace g
      have hperm :
          ColSeq.perm g (c :: rest) = ColSeq.sum et :: et := by
        change g c :: ColSeq.perm g rest = ColSeq.sum et :: et
        rw [hgc, hrest]
      rw [hperm] at hp
      exact hp

/-- Soundness half of Coq `ctree_mem_cpcolor`, at the declarative
`cpColorSpec` level. -/
theorem cpColorSpec_ringTrace_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) {et : ColSeq}
    (hspec : CProg.cpColorSpec cp et) :
    (cpmap cp).map.RingTrace (cpRing cp) (ColSeq.sum et :: et) := by
  rcases cpColor0Spec_exists_ringTrace_of_config hcfg hspec with
    ⟨full, htrace, hbranch⟩
  exact ringTrace_normalize_of_cpBranch htrace hbranch
    (CProg.cpColorSpec_properTrace hspec)
    (CProg.cpColorSpec_etail_eq_ttail hspec)

/-- Completeness half of Coq `ctree_mem_cpcolor`, at the declarative
`cpColorSpec` level.  A normalized ring trace is inverted through the exact
configuration fold and its initial coloring is globally normalized to
`[one, two, three]`. -/
theorem cpColorSpec_of_ringTrace_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) {et : ColSeq}
    (heven : ColSeq.evenTrace et = true)
    (htrace : (cpmap cp).map.RingTrace
      (cpRing cp) (ColSeq.sum et :: et)) :
    CProg.cpColorSpec cp et :=
  cpColorSpec_of_ringTrace (cpRingCycle_of_config hcfg) heven htrace

/-- Declarative form of Coq `ctree_mem_cpcolor`: for configurations, the
color-program semantics is exactly normalized ring-trace existence. -/
theorem cpColorSpec_iff_evenTrace_and_ringTrace_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) (et : ColSeq) :
    CProg.cpColorSpec cp et ↔
      ColSeq.evenTrace et = true ∧
        (cpmap cp).map.RingTrace
          (cpRing cp) (ColSeq.sum et :: et) := by
  constructor
  · intro hspec
    exact ⟨CProg.cpColorSpec_evenTrace hspec,
      cpColorSpec_ringTrace_of_config hcfg hspec⟩
  · rintro ⟨heven, htrace⟩
    exact cpColorSpec_of_ringTrace_of_config hcfg heven htrace

/-- Coq `cpcolor_proper` for genuine configuration programs.  The final
`consRot` restores the omitted first trace color, so the tree height is the
ring size minus one. -/
theorem cpColor_proper_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) :
    CTree.Proper (CProg.ringSize cp - 1) (CProg.cpColor cp) := by
  rcases config_reverse_decompose hcfg with ⟨ss, hrev, hss⟩
  have hcp : cp = ss.reverse ++ [CpStep.y] := by
    calc
      cp = cp.reverse.reverse := (List.reverse_reverse cp).symm
      _ = (CpStep.y :: ss).reverse := by rw [hrev]
      _ = ss.reverse ++ [CpStep.y] := by simp
  have hsize : CProg.ringSize cp = configStepsSize 3 ss := by
    rw [hcp, ringSize_reverse_append_eq_configStepsSize hss]
    rfl
  have hfold : CTree.Proper (configStepsSize 3 ss - 2)
      (CProg.cpColorFold ss [Color.one, Color.two, Color.three]) :=
    cpColorFold_proper_of_configSteps
      (input := [Color.one, Color.two, Color.three])
      hss (by decide) (by decide)
  have hbase : CTree.Proper (CProg.ringSize cp - 2)
      (CProg.cpColor0 cp.reverse) := by
    rw [hrev]
    simpa [CProg.cpColor0, hsize] using hfold
  have hfinal := CTree.proper_consRot hbase
  have hlong := CProg.ringSize_gt_two_of_config hcfg
  simpa [CProg.cpColor] using
    (show CTree.Proper (CProg.ringSize cp - 1)
        (CTree.consRot (CProg.cpColor0 cp.reverse)) by
      convert hfinal using 1
      all_goals omega)

/-- Executable-to-declarative membership equivalence on genuine
configurations, without the unrestricted uniform-branch-height assumption. -/
theorem cpColor_mem_iff_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) (et : ColSeq) :
    CTree.mem (CProg.cpColor cp) et = true ↔ CProg.cpColorSpec cp et := by
  rcases config_reverse_decompose hcfg with ⟨ss, hrev, hss⟩
  rw [CProg.cpColor, CTree.mem_consRot]
  change CTree.mem (CProg.cpColor0 cp.reverse) (ColSeq.ttail et) = true ↔
    CProg.cpColor0Spec cp.reverse (ColSeq.ttail et)
  rw [hrev]
  simpa [CProg.cpColor0, CProg.cpColor0Spec] using
    cpColorFold_mem_iff_of_configSteps
      (input := [Color.one, Color.two, Color.three])
      hss (by decide) (by decide)
      (ColSeq.ttail et)

/-- Lean form of Coq `ctree_mem_cpcolor`. -/
theorem ctree_mem_cpColor_iff_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) (et : ColSeq) :
    CTree.mem (CProg.cpColor cp) et = true ↔
      ColSeq.evenTrace et = true ∧
        (cpmap cp).map.RingTrace
          (cpRing cp) (ColSeq.sum et :: et) := by
  rw [cpColor_mem_iff_of_config hcfg]
  exact cpColorSpec_iff_evenTrace_and_ringTrace_of_config hcfg et


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
