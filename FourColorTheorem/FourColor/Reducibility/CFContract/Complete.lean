import FourColorTheorem.FourColor.Reducibility.CFContract.Config.Triad

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

/-- The normalization identity used in Coq `contract_ctreeP`: after applying
the even-trace permutation selected by the tail, a nonempty zero-sum cyclic
trace has the canonical `sum tail :: tail` form. -/
theorem perm_etraceTail_eq_sum_cons
    {et : ColSeq} (hne : et ≠ []) (hsum : ColSeq.sum et = Color.zero) :
    ColSeq.perm (ColSeq.etracePerm et.tail) et =
      ColSeq.sum (ColSeq.etrace et.tail) :: ColSeq.etrace et.tail := by
  cases et with
  | nil => exact (hne rfl).elim
  | cons e es =>
      have he : e = ColSeq.sum es :=
        (Color.add_eq_zero_iff_eq e (ColSeq.sum es)).1 (by
          simpa only [ColSeq.sum_cons] using hsum)
      simp only [List.tail_cons, ColSeq.perm, List.map_cons, ColSeq.etrace]
      congr 1
      calc
        ColSeq.etracePerm es e =
            ColSeq.etracePerm es (ColSeq.sum es) := congrArg _ he
        _ = ColSeq.sum (ColSeq.perm (ColSeq.etracePerm es) es) :=
          (ColSeq.perm_sum (ColSeq.etracePerm es) es).symm

theorem rot1_eq_rotateLeft_one (et : ColSeq) :
    ColSeq.rot1 et = CProg.rotateLeft 1 et := by
  cases et <;> simp [ColSeq.rot1, CProg.rotateLeft]

/-- Ring traces commute with MathComp-style left rotation of both the boundary
and trace. -/
theorem ringTrace_rotateLeft_boundary
    {G : Hypermap} {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) (n : Nat) :
    G.RingTrace (CProg.rotateLeft n r) (CProg.rotateLeft n et) := by
  rcases htrace with ⟨k, hk, het⟩
  refine ⟨k, hk, ?_⟩
  rw [het, Hypermap.colorsOn_rotateLeft, ColSeq.trace_rotateLeft]

/-- Eliminate a simultaneous left rotation from a ring trace. -/
theorem ringTrace_rotateLeft_boundary_elim
    {G : Hypermap} {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace (CProg.rotateLeft n r) et) :
    G.RingTrace r (CProg.rotateRight n et) := by
  rcases htrace with ⟨k, hk, het⟩
  refine ⟨k, hk, ?_⟩
  rw [het, Hypermap.colorsOn_rotateLeft, ColSeq.trace_rotateLeft,
    CProg.rotateRight_rotateLeft]

theorem rotateRight_one_ctrace (et : ColSeq) :
    CProg.rotateRight 1 (ColSeq.ctrace et) =
      ColSeq.sum et :: et := by
  exact CProg.rotateRight_one_append_singleton (ColSeq.sum et) et

theorem perm_sum_cons (g : EdgePerm) (et : ColSeq) :
    ColSeq.perm g (ColSeq.sum et :: et) =
      ColSeq.sum (ColSeq.perm g et) :: ColSeq.perm g et := by
  change g (ColSeq.sum et) :: ColSeq.perm g et =
    ColSeq.sum (ColSeq.perm g et) :: ColSeq.perm g et
  rw [ColSeq.perm_sum]

theorem rot1_eq_ctrace_tail_of_sum_zero
    {et : ColSeq} (hne : et ≠ []) (hsum : ColSeq.sum et = Color.zero) :
    ColSeq.rot1 et = ColSeq.ctrace et.tail := by
  cases et with
  | nil => exact (hne rfl).elim
  | cons e es =>
      have he : e = ColSeq.sum es :=
        (Color.add_eq_zero_iff_eq e (ColSeq.sum es)).1 (by
          simpa only [ColSeq.sum_cons] using hsum)
      simp [ColSeq.rot1, ColSeq.ctrace, he]

/-- Coq `check_reducible_valid`'s cyclic transport.  A coclosure statement for
the once-left-rotated boundary and trace transports back to the original
boundary and trace. -/
theorem kempeCoclosure_rot1_ringTrace_elim
    {G : Hypermap} {r : List G.Dart} {et : ColSeq}
    (hclose : Chromogram.KempeCoclosure
      (G.RingTrace (CProg.rotateLeft 1 r)) (ColSeq.rot1 et)) :
    Chromogram.KempeCoclosure (G.RingTrace r) et := by
  intro Q hQclosed hQet
  let Q1 : ColSeq → Prop := fun et1 => Q (CProg.rotateRight 1 et1)
  have hQ1closed : Chromogram.KempeClosed Q1 := by
    intro et1 hQ1et
    constructor
    · intro g
      have hp := hQclosed.perm hQ1et g
      simpa [Q1, ColSeq.perm, CProg.map_rotateRight] using hp
    · rcases hQclosed.chromogram hQ1et with ⟨w, hw, hall⟩
      refine ⟨Chromogram.gramRot w, ?_, ?_⟩
      · have hmatch := Chromogram.matchGramRot
          (CProg.rotateRight 1 et1) w
        rw [rot1_eq_rotateLeft_one,
          CProg.rotateLeft_rotateRight] at hmatch
        rwa [hmatch]
      · intro et2 het2
        have hmatch := Chromogram.matchGramRot
          (CProg.rotateRight 1 et2) w
        rw [rot1_eq_rotateLeft_one,
          CProg.rotateLeft_rotateRight] at hmatch
        exact hall _ (by rwa [← hmatch])
  have hQ1rot : Q1 (ColSeq.rot1 et) := by
    change Q (CProg.rotateRight 1 (ColSeq.rot1 et))
    rw [rot1_eq_rotateLeft_one, CProg.rotateRight_rotateLeft]
    exact hQet
  rcases hclose Q1 hQ1closed hQ1rot with ⟨et1, htrace, hQ1⟩
  refine ⟨CProg.rotateRight 1 et1, ?_, hQ1⟩
  exact ringTrace_rotateLeft_boundary_elim htrace

/-- Lean form of Coq `contract_ctreeP`.  A successful executable contract-tree
run yields a valid semantic contract, and every coloring trace of that
contract has its normalized tail in the returned color tree. -/
theorem contractTree_complete
    {cf : Config} {ct : CTree}
    (hcontract : cf.contractTree = some ct) :
    cf.map.map.ValidContract cf.reducibilityRingDarts cf.contractFinset ∧
      ∀ et : ColSeq,
        cf.map.map.ContractRingTrace cf.contractFinset cf.ringDarts et →
          CTree.mem ct (ColSeq.etrace et.tail) = true := by
  rcases (contractTree_eq_some_iff cf ct).1 hcontract with
    ⟨cpc, hrun, hmask, hct⟩
  have hcf : cf.WellFormed := CProg.contractProgram_config hrun
  refine ⟨validContract_of_contractProgram hcf hrun hmask, ?_⟩
  intro et htrace
  have hetLen : et.length = CProg.ringSize cf.program := by
    simpa using Hypermap.ContractRingTrace.length
      (G := cf.map.map) htrace
  have hetNe : et ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hetLen]
    exact CProg.ringSize_pos cf.program
  rcases htrace with ⟨k, hk, htraceEq⟩
  have hkSource :
      (PointedHypermap.cpmap cf.program).map.ContractColoring
        (PointedHypermap.cpContractFinset
          cf.initialRingMask cf.contractMask cf.program) k := by
    change cf.map.map.ContractColoring
      (PointedHypermap.cpContractFinset
        cf.initialRingMask cf.contractMask cf.program) k
    rw [cpContractFinset_initial_eq]
    exact hk
  have hcorrect := PointedHypermap.contractProgram_correct
    (mr := cf.initialRingMask) (mc := cf.contractMask)
    (cp := cf.program) (cpc := cpc)
    (by simp [initialRingMask]) cf.length_contractMask hrun
  rcases hcorrect k hkSource with
    ⟨k', hk', hcycle, hboundary⟩
  have hsurvive :
      CfMask.select (cf.initialRingMask.map Bool.not)
          (PointedHypermap.cpRing cf.program) =
        PointedHypermap.cpRing cf.program := by
    simpa [initialRingMask, PointedHypermap.length_cpRing] using
      (CfMask.select_replicate_true_length
        (PointedHypermap.cpRing cf.program))
  rw [hsurvive] at hboundary
  have hboundary' :
      (PointedHypermap.cpmap cpc).map.colorsOn k'
          (PointedHypermap.cpRing cpc) =
        cf.map.map.colorsOn k cf.ringDarts := by
    simpa [Config.map, Config.ringDarts] using hboundary
  have houtput :
      (PointedHypermap.cpmap cpc).map.RingTrace
        (PointedHypermap.cpRing cpc) et := by
    refine ⟨k', hk', ?_⟩
    calc
      et = ColSeq.trace (cf.map.map.colorsOn k cf.ringDarts) := htraceEq
      _ = ColSeq.trace
          ((PointedHypermap.cpmap cpc).map.colorsOn k'
            (PointedHypermap.cpRing cpc)) := congrArg ColSeq.trace hboundary'.symm
  let g := ColSeq.etracePerm et.tail
  have hnormalized := Hypermap.RingTrace.perm
    (G := (PointedHypermap.cpmap cpc).map) houtput g
  have hsum : ColSeq.sum et = Color.zero :=
    Hypermap.RingTrace.sum_zero (G := (PointedHypermap.cpmap cpc).map) houtput
  rw [perm_etraceTail_eq_sum_cons hetNe hsum] at hnormalized
  rw [← hct]
  exact PointedHypermap.ctree_mem_cpColor hcycle
    (ColSeq.even_etrace et.tail) hnormalized

/-- Coq `check_reducible_valid`: every configuration accepted by the
executable reducibility checker is semantically C-reducible. -/
theorem checkReducible_valid
    {cf : Config} (hcheck : cf.checkReducible = true) :
    cf.map.map.CReducible cf.reducibilityRingDarts cf.contractFinset := by
  rcases (checkReducible_eq_true_iff cf).1 hcheck with
    ⟨ct, hcontract, _hdisjoint⟩
  rcases contractTree_complete hcontract with ⟨hvalid, hcompleteContract⟩
  refine ⟨hvalid, ?_⟩
  have hcfg : CProg.config cf.program = true :=
    CProg.contractProgram_config
      ((contractTree_eq_some_iff cf ct).1 hcontract).choose_spec.1
  let h := CProg.ringSize cf.program - 2
  have hring :
      CProg.ringSize cf.program = Nat.succ (Nat.succ h) := by
    have hlong := CProg.ringSize_gt_two_of_config hcfg
    simp only [h]
    omega
  let P : ColSeq → Prop := fun cet =>
    cf.map.map.RingTrace (CProg.rotateLeft 1 cf.ringDarts) cet
  have hvalidColor : ∀ xs : ColSeq,
      CTree.mem (CProg.cpColor cf.program) xs = true →
        P (ColSeq.ctrace xs) ∧ xs.length = h + 1 := by
    intro xs hmem
    rcases (PointedHypermap.ctree_mem_cpColor_iff_of_config hcfg xs).1 hmem with
      ⟨_heven, htrace⟩
    constructor
    · have hrot := ringTrace_rotateLeft_boundary htrace 1
      simpa [P, CProg.rotateLeft_one_cons, ColSeq.ctrace] using hrot
    · have hlen := Hypermap.RingTrace.length
        (G := cf.map.map) htrace
      have hlen' :
          (ColSeq.sum xs :: xs).length = CProg.ringSize cf.program := by
        simpa [Config.map, Config.ringDarts] using hlen
      simp only [List.length_cons] at hlen'
      omega
  have hcompleteColor : ∀ xs : ColSeq,
      P (ColSeq.ctrace xs) →
        CTree.mem (CProg.cpColor cf.program) (ColSeq.etrace xs) = true := by
    intro xs htrace
    have hback := ringTrace_rotateLeft_boundary_elim
      (n := 1) (by simpa [P] using htrace)
    rw [rotateRight_one_ctrace] at hback
    have hperm := Hypermap.RingTrace.perm
      (G := cf.map.map) hback (ColSeq.etracePerm xs)
    rw [perm_sum_cons] at hperm
    change cf.map.map.RingTrace cf.ringDarts
      (ColSeq.sum (ColSeq.etrace xs) :: ColSeq.etrace xs) at hperm
    exact (PointedHypermap.ctree_mem_cpColor_iff_of_config
      hcfg (ColSeq.etrace xs)).2 ⟨ColSeq.even_etrace xs, hperm⟩
  intro et htrace
  have htraceRing :
      cf.map.map.ContractRingTrace cf.contractFinset cf.ringDarts et := by
    simpa using htrace
  have hetLen : et.length = CProg.ringSize cf.program := by
    simpa using Hypermap.ContractRingTrace.length
      (G := cf.map.map) htraceRing
  have hetNe : et ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hetLen]
    exact CProg.ringSize_pos cf.program
  have htailLen : et.tail.length = h + 1 := by
    rw [List.length_tail, hetLen, hring]
    omega
  have hmem := hcompleteContract et htraceRing
  have hcoclose :=
    checkReducible_contract_etrace_coclosure_of_cpColor_spec
      (cf := cf) (contractTree := ct) (h := h) (P := P)
      hring hvalidColor hcompleteColor hcheck hcontract htailLen hmem
  have hsum : ColSeq.sum et = Color.zero :=
    Hypermap.ContractRingTrace.sum_zero (G := cf.map.map) htraceRing
  have hrot := rot1_eq_ctrace_tail_of_sum_zero hetNe hsum
  have hcocloseRot : Chromogram.KempeCoclosure P (ColSeq.rot1 et) := by
    rwa [hrot]
  exact kempeCoclosure_rot1_ringTrace_elim
    (by simpa [P] using hcocloseRot)


end Config

end FourColor

end Schematic.Math.GraphTheory
