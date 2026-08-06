import FourColorTheorem.FourColor.Reducibility.CFContract.Foundations

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- The complete `CpR` branch of Coq `cfctr_correct`. -/
theorem contractProgramCorrect_rotate
    {cp cpc : CProg} {mr mc : List Bool} (n : Nat)
    (hcfg : CProg.config cp = true)
    (hmr : mr.length = CProg.ringSize cp)
    (hrec : ContractProgramCorrect (CProg.rotateRight n mr) mc cp cpc) :
    ContractProgramCorrect mr mc (CpStep.rotate n :: cp)
      (CpStep.rotate
        (CProg.countFalse ((CProg.rotateRight n mr).take n)) :: cpc) := by
  intro k hk
  have hkrec :
      (cpmap cp).map.ContractColoring
        (cpContractFinset (CProg.rotateRight n mr) mc cp) k := by
    rw [← cpContractFinset_rotate_eq hcfg hmr]
    exact hk
  rcases hrec k hkrec with ⟨k', hk', hcycleQ, hboundary⟩
  refine ⟨k', hk', cpRingCycle_rotate hcycleQ, ?_⟩
  let j := CProg.countFalse ((CProg.rotateRight n mr).take n)
  have hout :
      cpRing (CpStep.rotate j :: cpc) =
        CProg.rotateLeft j (cpRing cpc) :=
    cpRing_rotate_of_ringCycle (n := j) hcycleQ
  have hin :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle (n := n) (cpRingCycle_of_config hcfg)
  rw [hout, hin]
  change
    (cpmap cpc).map.colorsOn k' (CProg.rotateLeft j (cpRing cpc)) =
      (cpmap cp).map.colorsOn k
        (CfMask.select (mr.map Bool.not)
          (CProg.rotateLeft n (cpRing cp)))
  rw [Hypermap.colorsOn_rotateLeft, hboundary]
  change
    CProg.rotateLeft j
        ((CfMask.select ((CProg.rotateRight n mr).map Bool.not)
          (cpRing cp)).map k) =
      (CfMask.select (mr.map Bool.not)
        (CProg.rotateLeft n (cpRing cp))).map k
  rw [← CProg.map_rotateLeft]
  exact congrArg (List.map k)
    (CfMask.rotateLeft_select_map_not_rotateRight n mr (cpRing cp)
      (by simpa [length_cpRing] using hmr.symm))

theorem contractProgramCorrect_y_nil_first :
    ContractProgramCorrect [true, false, false] [] [CpStep.y] [] := by
  unfold ContractProgramCorrect
  intro k hk
  change base.y.map.ContractColoring
    ({ExtDart.old ExtDart.newEdge} : Finset base.y.map.Dart) k at hk
  let k' : Bool → Color := fun b => k (base.yOld b)
  refine ⟨k', ?_, cpRingCycle_nil, ?_⟩
  · constructor
    · intro b
      cases b
      · exact hk.2.1 (base.yOld false) (by fct_decide)
      · exact hk.2.1 (base.yOld true) (by fct_decide)
    · intro b
      cases b <;> rfl
  · change [k' false, k' true] =
      [k ExtDart.new, k (base.yOld true)]
    have hfirst : k (base.yOld false) = k ExtDart.new := by
      calc
        k (base.yOld false) = k (ExtDart.old ExtDart.newEdge) :=
          hk.2.2 (ExtDart.old ExtDart.newEdge)
        _ = k (ExtDart.old ExtDart.new) :=
          (hk.1 (ExtDart.old ExtDart.newEdge) (by fct_decide)).symm
        _ = k ExtDart.new := hk.2.2 ExtDart.new
    simp [k', hfirst]

theorem contractProgramCorrect_y_nil_second :
    ContractProgramCorrect [false, true, false] [] [CpStep.y] [] := by
  unfold ContractProgramCorrect
  intro k hk
  change base.y.map.ContractColoring
    ({ExtDart.new} : Finset base.y.map.Dart) k at hk
  let k' : Bool → Color := fun b => k (base.yOld b)
  refine ⟨k', ?_, cpRingCycle_nil, ?_⟩
  · constructor
    · intro b
      cases b
      · exact hk.2.1 (base.yOld false) (by fct_decide)
      · exact hk.2.1 (base.yOld true) (by fct_decide)
    · intro b
      cases b <;> rfl
  · change [k' false, k' true] =
      [k (ExtDart.old ExtDart.newEdge), k (base.yOld true)]
    have hfirst : k (base.yOld false) =
        k (ExtDart.old ExtDart.newEdge) :=
      hk.2.2 (ExtDart.old ExtDart.newEdge)
    simp [k', hfirst]

theorem contractProgramCorrect_y_nil_third :
    ContractProgramCorrect [false, false, true] [] [CpStep.y] [] := by
  unfold ContractProgramCorrect
  intro k hk
  change base.y.map.ContractColoring
    ({base.yOld true} : Finset base.y.map.Dart) k at hk
  let k' : Bool → Color := fun b =>
    k (if b then base.y.point else base.y.map.node base.y.point)
  have hfresh : k base.y.point ≠ k (base.y.map.node base.y.point) := by
    have hnot : ExtDart.new ∉
        base.y.map.contractClosure
          ({base.yOld true} : Finset base.y.map.Dart) := by
      fct_decide
    have hedge := hk.2.1 ExtDart.new hnot
    intro heq
    apply hedge
    calc
      k (base.y.map.edge ExtDart.new) = k (base.yOld true) :=
        (hk.2.2 ExtDart.newEdge).symm
      _ = k (base.yOld false) :=
        (hk.1 (base.yOld true) (by fct_decide)).symm
      _ = k (base.y.map.node base.y.point) :=
        hk.2.2 (base.y.map.node base.y.point)
      _ = k base.y.point := heq.symm
  refine ⟨k', ?_, cpRingCycle_nil, ?_⟩
  · constructor
    · intro b
      cases b
      · simpa [k', cpmap0] using hfresh
      · simpa [k', cpmap0] using hfresh.symm
    · intro b
      cases b <;> rfl
  · rfl

theorem contractProgramCorrect_y_nil_none :
    ContractProgramCorrect [false, false, false] [] [CpStep.y]
      [CpStep.y] := by
  unfold ContractProgramCorrect
  intro k hk
  have hk' : base.y.map.ContractColoring ∅ k := by
    simpa using hk
  exact ⟨k, (base.y.map.contractColoring_empty_iff k).1 hk',
    cpRingCycle_of_config (by decide), rfl⟩

theorem cpContractFinset_y_eq
    {s : CpStep} {cp : CProg} (b1 b2 b3 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config (s :: cp) = true) :
    cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp) =
      (if b1 then
        {(cpmap (CpStep.y :: s :: cp)).map.node
          (cpmap (CpStep.y :: s :: cp)).point} else ∅) ∪
      (if b2 then {(cpmap (CpStep.y :: s :: cp)).point} else ∅) ∪
      (cpContractFinset (b3 :: mr) mc (s :: cp)).image
        (cpmap (s :: cp)).yOld := by
  let P := cpmap (s :: cp)
  change cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
      (CpStep.y :: s :: cp) =
    (if b1 then {P.y.map.node P.y.point} else ∅) ∪
    (if b2 then {P.y.point} else ∅) ∪
    (cpContractFinset (b3 :: mr) mc (s :: cp)).image P.yOld
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hring :
      cpRing (CpStep.y :: s :: cp) =
        P.y.map.node P.y.point :: P.y.point ::
          ((cpRing (s :: cp)).drop 1).map P.yOld := by
    simpa [P] using cpRing_y_eq_of_ringCycle
      (cp := s :: cp) (cpRingCycle_of_config hcfg) hgeom.proper
  have holdRing :
      cpRing (s :: cp) =
        P.map.node P.point :: (cpRing (s :: cp)).drop 1 := by
    simpa [P] using cpRing_eq_nodePoint_cons_drop_one (s :: cp)
  unfold cpContractFinset cpContractSelection
  rw [hring, cpContractDarts_y_cons, holdRing]
  change
    (CfMask.select (b1 :: b2 :: mr)
        (P.y.map.node P.y.point :: P.y.point ::
          ((cpRing (s :: cp)).drop 1).map P.yOld) ++
      CfMask.select (b3 :: mc)
        ((P.map.node P.point :: cpContractDarts (s :: cp)).map
          P.yOld)).toFinset = _
  cases b1 <;> cases b2 <;> cases b3
  all_goals simp only [CfMask.select, Bool.false_eq_true, if_false, if_true,
    List.toFinset_append, List.toFinset_cons,
    Finset.image_union, Finset.image_insert,
    CfMask.toFinset_select_map]
  all_goals ext x
  all_goals simp only [Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  all_goals simp
  all_goals tauto

theorem yOld_mem_contractClosure_cpContractFinset_iff
    {s : CpStep} {cp : CProg} (b1 b2 b3 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config (s :: cp) = true)
    (x : (cpmap (s :: cp)).map.Dart) :
    (cpmap (s :: cp)).yOld x ∈
        (cpmap (CpStep.y :: s :: cp)).map.contractClosure
          (cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
            (CpStep.y :: s :: cp)) ↔
      x ∈ (cpmap (s :: cp)).map.contractClosure
        (cpContractFinset (b3 :: mr) mc (s :: cp)) := by
  let P := cpmap (s :: cp)
  change P.yOld x ∈ P.y.map.contractClosure
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp)) ↔
    x ∈ P.map.contractClosure
      (cpContractFinset (b3 :: mr) mc (s :: cp))
  let t := P.map.contractClosure
    (cpContractFinset (b3 :: mr) mc (s :: cp))
  change P.yOld x ∈ P.y.map.contractClosure
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp)) ↔ x ∈ t
  have himage : P.yOld x ∈ t.image P.yOld ↔ x ∈ t := by
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
      have : z = x := P.yOld_injective hzx
      simpa [this] using hz
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hq1 : P.yOld x ∉
      P.y.map.contractClosure {P.y.map.node P.y.point} := by
    intro hx
    rcases (P.y.map.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · exact P.yOld_ne_node_point x (Finset.mem_singleton.mp hx)
    · have hz' : z = P.y.map.node P.y.point := Finset.mem_singleton.mp hz
      subst z
      have hne : P.yOld x ≠
          P.y.map.edge (P.y.map.node P.y.point) := by
        change ExtDart.old (ExtDart.old x) ≠
          (Hypermap.extensionY P.map P.point).edge
            ((Hypermap.extensionY P.map P.point).node ExtDart.new)
        rw [Hypermap.extensionY_node_new]
        change ExtDart.old (ExtDart.old x) ≠
          ExtDart.old (ExtDart.new : ExtDart P.map.Dart)
        intro h
        injection h with h'
        cases h'
      exact hne hzx.symm
  have hq2 : P.yOld x ∉ P.y.map.contractClosure {P.y.point} := by
    intro hx
    rcases (P.y.map.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · exact P.yOld_ne_point x (Finset.mem_singleton.mp hx)
    · have hz' : z = P.y.point := Finset.mem_singleton.mp hz
      subst z
      have hne : P.yOld x ≠ P.y.map.edge P.y.point := by
        change ExtDart.old (ExtDart.old x) ≠ ExtDart.newEdge
        simp
      exact hne hzx.symm
  have hq0 : P.yOld x ∉ P.y.map.contractClosure ∅ := by
    rw [P.y.map.contractClosure_empty]
    intro hx
    nomatch hx
  rw [cpContractFinset_y_eq b1 b2 b3 mr mc hcfg,
    P.y.map.contractClosure_union, P.y.map.contractClosure_union,
    Hypermap.contractClosure_image_of_edge_commute P.yOld P.yOld_edge,
    Finset.mem_union, Finset.mem_union]
  change
    ((P.yOld x ∈ P.y.map.contractClosure
          (if b1 then {P.y.map.node P.y.point} else ∅) ∨
        P.yOld x ∈ P.y.map.contractClosure
          (if b2 then {P.y.point} else ∅)) ∨
      P.yOld x ∈ t.image P.yOld) ↔ x ∈ t
  have finish (q1 q2 : Finset P.y.map.Dart)
      (hq1 : P.yOld x ∉ P.y.map.contractClosure q1)
      (hq2 : P.yOld x ∉ P.y.map.contractClosure q2) :
      (((P.yOld x ∈ P.y.map.contractClosure q1 ∨
            P.yOld x ∈ P.y.map.contractClosure q2) ∨
          P.yOld x ∈ t.image P.yOld) ↔ x ∈ t) := by
    constructor
    · rintro ((hx | hx) | hx)
      · exact (hq1 hx).elim
      · exact (hq2 hx).elim
      · exact himage.mp hx
    · intro hx
      exact Or.inr (himage.mpr hx)
  cases b1 <;> cases b2
  · simpa only [if_false] using finish ∅ ∅ hq0 hq0
  · simpa only [if_false, if_true] using finish ∅ {P.y.point} hq0 hq2
  · simpa only [if_false, if_true] using
      finish {P.y.map.node P.y.point} ∅ hq1 hq0
  · simpa only [if_true] using
      finish {P.y.map.node P.y.point} {P.y.point} hq1 hq2

/-- The recursive contract coloring obtained by restricting a `Y`-extended
coloring to old darts.  This is Coq `cfctr_correct`'s local coloring `h`. -/
theorem contractColoring_pullback_y
    {s : CpStep} {cp : CProg} (b1 b2 b3 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config (s :: cp) = true)
    {k : (cpmap (CpStep.y :: s :: cp)).map.Dart → Color}
    (hk : (cpmap (CpStep.y :: s :: cp)).map.ContractColoring
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp)) k) :
    (cpmap (s :: cp)).map.ContractColoring
      (cpContractFinset (b3 :: mr) mc (s :: cp))
      (k ∘ (cpmap (s :: cp)).yOld) := by
  let P := cpmap (s :: cp)
  apply Hypermap.ContractColoring.pullback
    (G := P.map) (H := P.y.map) P.yOld P.yOld_edge
  · intro x
    exact P.yOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)
  · intro x
    exact yOld_mem_contractClosure_cpContractFinset_iff
      b1 b2 b3 mr mc hcfg x
  · simpa [P] using hk

theorem cpContractFinset_h_eq
    {cp : CProg} (b1 b2 b3 b4 b5 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config cp = true) :
    cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp) =
      (if b1 then
        {(cpmap (CpStep.h :: cp)).map.node
          (cpmap (CpStep.h :: cp)).point} else ∅) ∪
      (if b2 then {(cpmap (CpStep.h :: cp)).point} else ∅) ∪
      (if b3 then
        {(cpmap (CpStep.h :: cp)).map.face
          (cpmap (CpStep.h :: cp)).point} else ∅) ∪
      (cpContractFinset (b4 :: b5 :: mr) mc cp).image
        (cpmap cp).hOld := by
  let P := cpmap cp
  change cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
      (CpStep.h :: cp) =
    (if b1 then {P.h.map.node P.h.point} else ∅) ∪
    (if b2 then {P.h.point} else ∅) ∪
    (if b3 then {P.h.map.face P.h.point} else ∅) ∪
    (cpContractFinset (b4 :: b5 :: mr) mc cp).image P.hOld
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 1 < CProg.ringSize cp := by
    have := CProg.ringSize_gt_two_of_config hcfg
    omega
  have hring :
      cpRing (CpStep.h :: cp) =
        P.h.map.node P.h.point :: P.h.point ::
          ((cpRing cp).drop 2).map P.hOld := by
    simpa [P] using cpRing_h_eq_of_ringCycle
      (cp := cp) (cpRingCycle_of_config hcfg) hgeom.proper hgeom.long
      (CProg.ringSize_gt_two_of_config hcfg)
  have holdRing :
      cpRing cp =
        P.map.node P.point :: P.point :: (cpRing cp).drop 2 := by
    simpa [P] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
        (cp := cp) hsize
  unfold cpContractFinset cpContractSelection
  rw [hring, cpContractDarts_h, holdRing]
  change
    (CfMask.select (b1 :: b2 :: mr)
        (P.h.map.node P.h.point :: P.h.point ::
          ((cpRing cp).drop 2).map P.hOld) ++
      CfMask.select (b3 :: b4 :: b5 :: mc)
        (P.h.map.face P.h.point ::
          (P.map.node P.point :: P.point :: cpContractDarts cp).map
            P.hOld)).toFinset = _
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5
  all_goals simp only [CfMask.select, Bool.false_eq_true, if_false, if_true,
    List.toFinset_append, List.toFinset_cons,
    Finset.image_union, Finset.image_insert,
    CfMask.toFinset_select_map]
  all_goals ext x
  all_goals simp only [Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  all_goals simp
  all_goals tauto

theorem hOld_mem_contractClosure_cpContractFinset_iff
    {cp : CProg} (b1 b2 b3 b4 b5 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config cp = true)
    (x : (cpmap cp).map.Dart) :
    (cpmap cp).hOld x ∈
        (cpmap (CpStep.h :: cp)).map.contractClosure
          (cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
            (CpStep.h :: cp)) ↔
      x ∈ (cpmap cp).map.contractClosure
        (cpContractFinset (b4 :: b5 :: mr) mc cp) := by
  let P := cpmap cp
  change P.hOld x ∈ P.h.map.contractClosure
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp)) ↔
    x ∈ P.map.contractClosure
      (cpContractFinset (b4 :: b5 :: mr) mc cp)
  let t := P.map.contractClosure
    (cpContractFinset (b4 :: b5 :: mr) mc cp)
  change P.hOld x ∈ P.h.map.contractClosure
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp)) ↔ x ∈ t
  have himage : P.hOld x ∈ t.image P.hOld ↔ x ∈ t := by
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
      have : z = x := P.hOld_injective hzx
      simpa [this] using hz
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hq1 : P.hOld x ∉
      P.h.map.contractClosure {P.h.map.node P.h.point} := by
    intro hx
    rcases (P.h.map.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · exact P.hOld_ne_node_point x (Finset.mem_singleton.mp hx)
    · have hz' : z = P.h.map.node P.h.point := Finset.mem_singleton.mp hz
      subst z
      change P.h.map.edge (P.h.map.node P.h.point) =
        ExtDart.old (ExtDart.old (ExtDart.old x)) at hzx
      have hgeom := cpmap_configGeometry_of_config hcfg
      have hyLong : P.y.LongRingHead :=
        P.y_longRingHead_of_proper hgeom.proper
      have hyLong' :
          (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new := by
        simpa [PointedHypermap.y] using hyLong
      have hnode : P.h.map.node P.h.point =
          ExtDart.old (ExtDart.old ExtDart.newEdge) := by
        change (Hypermap.extensionH P.map P.point).node ExtDart.new = _
        unfold Hypermap.extensionH Hypermap.extensionN
        rw [Hypermap.ExtensionN.node_new,
          if_pos hyLong']
        exact congrArg ExtDart.old
          (Hypermap.extensionY_node_new P.map P.point)
      rw [hnode] at hzx
      cases hzx
  have hq2 : P.hOld x ∉ P.h.map.contractClosure {P.h.point} := by
    intro hx
    rcases (P.h.map.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · exact P.hOld_ne_point x (Finset.mem_singleton.mp hx)
    · have hz' : z = P.h.point := Finset.mem_singleton.mp hz
      subst z
      change ExtDart.newEdge =
        ExtDart.old (ExtDart.old (ExtDart.old x)) at hzx
      cases hzx
  have hq3 : P.hOld x ∉
      P.h.map.contractClosure {P.h.map.face P.h.point} := by
    intro hx
    rcases (P.h.map.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · have hz' : P.hOld x = P.h.map.face P.h.point :=
        Finset.mem_singleton.mp hx
      have hface : P.h.map.face P.h.point = ExtDart.old ExtDart.new := by
        exact Hypermap.extensionH_face_new P.map P.point
      rw [hface] at hz'
      cases hz'
    · have hz' : z = P.h.map.face P.h.point := Finset.mem_singleton.mp hz
      subst z
      change P.h.map.edge (P.h.map.face P.h.point) =
        ExtDart.old (ExtDart.old (ExtDart.old x)) at hzx
      have hface : P.h.map.face P.h.point = ExtDart.old ExtDart.new := by
        exact Hypermap.extensionH_face_new P.map P.point
      rw [hface] at hzx
      cases hzx
  have hq0 : P.hOld x ∉ P.h.map.contractClosure ∅ := by
    rw [P.h.map.contractClosure_empty]
    intro hx
    nomatch hx
  rw [cpContractFinset_h_eq b1 b2 b3 b4 b5 mr mc hcfg,
    P.h.map.contractClosure_union, P.h.map.contractClosure_union,
    P.h.map.contractClosure_union,
    Hypermap.contractClosure_image_of_edge_commute P.hOld P.hOld_edge,
    Finset.mem_union, Finset.mem_union, Finset.mem_union]
  change
    (((P.hOld x ∈ P.h.map.contractClosure
            (if b1 then {P.h.map.node P.h.point} else ∅) ∨
          P.hOld x ∈ P.h.map.contractClosure
            (if b2 then {P.h.point} else ∅)) ∨
        P.hOld x ∈ P.h.map.contractClosure
          (if b3 then {P.h.map.face P.h.point} else ∅)) ∨
      P.hOld x ∈ t.image P.hOld) ↔ x ∈ t
  have finish (q1 q2 q3 : Finset P.h.map.Dart)
      (hq1 : P.hOld x ∉ P.h.map.contractClosure q1)
      (hq2 : P.hOld x ∉ P.h.map.contractClosure q2)
      (hq3 : P.hOld x ∉ P.h.map.contractClosure q3) :
      ((((P.hOld x ∈ P.h.map.contractClosure q1 ∨
              P.hOld x ∈ P.h.map.contractClosure q2) ∨
            P.hOld x ∈ P.h.map.contractClosure q3) ∨
          P.hOld x ∈ t.image P.hOld) ↔ x ∈ t) := by
    constructor
    · rintro (((hx | hx) | hx) | hx)
      · exact (hq1 hx).elim
      · exact (hq2 hx).elim
      · exact (hq3 hx).elim
      · exact himage.mp hx
    · intro hx
      exact Or.inr (himage.mpr hx)
  cases b1 <;> cases b2 <;> cases b3
  · simpa only [if_false] using finish ∅ ∅ ∅ hq0 hq0 hq0
  · simpa only [if_false, if_true] using
      finish ∅ ∅ {P.h.map.face P.h.point} hq0 hq0 hq3
  · simpa only [if_false, if_true] using
      finish ∅ {P.h.point} ∅ hq0 hq2 hq0
  · simpa only [if_false, if_true] using
      finish ∅ {P.h.point} {P.h.map.face P.h.point} hq0 hq2 hq3
  · simpa only [if_false, if_true] using
      finish {P.h.map.node P.h.point} ∅ ∅ hq1 hq0 hq0
  · simpa only [if_false, if_true] using
      finish {P.h.map.node P.h.point} ∅
        {P.h.map.face P.h.point} hq1 hq0 hq3
  · simpa only [if_false, if_true] using
      finish {P.h.map.node P.h.point} {P.h.point} ∅ hq1 hq2 hq0
  · simpa only [if_true] using
      finish {P.h.map.node P.h.point} {P.h.point}
        {P.h.map.face P.h.point} hq1 hq2 hq3

/-- Coq `cfctr_correct`'s recursive coloring `h := k \o icpH`. -/
theorem contractColoring_pullback_h
    {cp : CProg} (b1 b2 b3 b4 b5 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config cp = true)
    {k : (cpmap (CpStep.h :: cp)).map.Dart → Color}
    (hk : (cpmap (CpStep.h :: cp)).map.ContractColoring
      (cpContractFinset (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp)) k) :
    (cpmap cp).map.ContractColoring
      (cpContractFinset (b4 :: b5 :: mr) mc cp)
      (k ∘ (cpmap cp).hOld) := by
  let P := cpmap cp
  apply Hypermap.ContractColoring.pullback
    (G := P.map) (H := P.h.map) P.hOld P.hOld_edge
  · intro x
    exact P.hOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)
  · intro x
    exact hOld_mem_contractClosure_cpContractFinset_iff
      b1 b2 b3 b4 b5 mr mc hcfg x
  · simpa [P] using hk

theorem h_node_hOld_point_eq_face_point
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    P.h.map.node (P.hOld P.point) = P.h.map.face P.h.point := by
  have hy : P.y.map.node (P.yOld P.point) = P.y.point := by
    rw [← P.y_node_symm_point_eq_yOld_point hproper]
    exact P.y.map.node.apply_symm_apply P.y.point
  change Hypermap.ExtensionN.node P.y.map P.y.point
      (ExtDart.old (P.yOld P.point)) = ExtDart.old P.y.point
  rw [Hypermap.ExtensionN.node_old, hy]
  rw [if_neg (P.yOld_ne_point P.point)]
  rw [if_neg (by
    change ¬ (Hypermap.extensionY P.map P.point).node ExtDart.new =
      ExtDart.new
    rw [Hypermap.extensionY_node_new]
    intro h
    cases h)]

theorem h_face_edge_face_point_eq_hOld_point
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    P.h.map.face (P.h.map.edge (P.h.map.face P.h.point)) =
      P.hOld P.point := by
  rw [Hypermap.face_edge_eq_node_symm]
  apply P.h.map.node.injective
  rw [Equiv.apply_symm_apply]
  exact (h_node_hOld_point_eq_face_point P hproper).symm

theorem h_node_point_eq_old_old_newEdge
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    P.h.map.node P.h.point =
      ExtDart.old (ExtDart.old ExtDart.newEdge) := by
  have hyLong : P.y.LongRingHead :=
    P.y_longRingHead_of_proper hproper
  have hyLong' :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new := by
    simpa [PointedHypermap.y] using hyLong
  change (Hypermap.extensionH P.map P.point).node ExtDart.new = _
  unfold Hypermap.extensionH Hypermap.extensionN
  rw [Hypermap.ExtensionN.node_new, if_pos hyLong']
  exact congrArg ExtDart.old
    (Hypermap.extensionY_node_new P.map P.point)

theorem h_edge_node_point_eq_old_old_new
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    P.h.map.edge (P.h.map.node P.h.point) =
      ExtDart.old (ExtDart.old ExtDart.new) := by
  rw [h_node_point_eq_old_old_newEdge P hproper]
  rfl

theorem face_edge_node_eq_self (G : Hypermap) (x : G.Dart) :
    G.face (G.edge (G.node x)) = x := by
  rw [Hypermap.face_edge_eq_node_symm]
  exact G.node.symm_apply_apply x

theorem map_comp_select_eq_select_map
    {α β : Type _} (k : β → Color) (f : α → β)
    (mask : List Bool) (xs : List α) :
    List.map (k ∘ f) (CfMask.select mask xs) =
      List.map k (CfMask.select mask (xs.map f)) := by
  calc
    List.map (k ∘ f) (CfMask.select mask xs) =
        List.map k ((CfMask.select mask xs).map f) := by
      rw [List.map_map]
    _ = List.map k (CfMask.select mask (xs.map f)) := by
      rw [CfMask.select_map]

/-- The head color of a recursively contracted ring is the source head color,
even when an initial run of source ring edges was selected.  This is Coq
`cfctr_correct`'s `h'nGc`. -/
theorem contractProgramCorrect_ringHead_eq
    {cp cpc : CProg} {mr mc : List Bool}
    {k : (cpmap cp).map.Dart → Color}
    {k' : (cpmap cpc).map.Dart → Color}
    (hk : (cpmap cp).map.ContractColoring
      (cpContractFinset mr mc cp) k)
    (hboundary :
      (cpmap cpc).map.colorsOn k' (cpRing cpc) =
        (cpmap cp).map.colorsOn k
          (CfMask.select (mr.map Bool.not) (cpRing cp))) :
    k' ((cpmap cpc).map.node (cpmap cpc).point) =
      k ((cpmap cp).map.node (cpmap cp).point) := by
  let P := cpmap cp
  let Q := cpmap cpc
  have hringP :
      cpRing cp = P.map.node P.point :: (cpRing cp).drop 1 := by
    simpa [P] using cpRing_eq_nodePoint_cons_drop_one cp
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: (cpRing cpc).drop 1 := by
    simpa [Q] using cpRing_eq_nodePoint_cons_drop_one cpc
  have hchain :
      List.IsChain (fun a b => P.map.node.symm a = b) (cpRing cp) := by
    simpa [P, cpRing] using ringDarts_isChain P (CProg.ringSize cp)
  cases hsurvive : CfMask.select (mr.map Bool.not) (cpRing cp) with
  | nil =>
      rw [hringQ, hsurvive] at hboundary
      change k' (Q.map.node Q.point) ::
          List.map k' ((cpRing cpc).drop 1) = [] at hboundary
      nomatch hboundary
  | cons y ys =>
      have hhead : k' (Q.map.node Q.point) = k y := by
        rw [hringQ, hsurvive] at hboundary
        exact (List.cons.inj hboundary).1
      apply hhead.trans
      have hchainHead := hchain
      rw [hringP] at hchainHead
      refine Hypermap.ContractColoring.eq_first_unselected_of_isChain
        (mask := mr) (x := P.map.node P.point)
        (xs := (cpRing cp).drop 1) (y := y) (ys := ys) hk hchainHead ?_ ?_
      · intro z hz
        apply (cpmap cp).map.mem_contractClosure_self
        unfold cpContractFinset cpContractSelection
        simp only [List.mem_toFinset, List.mem_append]
        apply Or.inl
        rw [hringP]
        exact hz
      · rw [hringP] at hsurvive
        exact hsurvive

/-- With an unselected source head, the second recursively contracted ring
color is the source point color.  This is Coq `cfctr_correct`'s `h'Gc`. -/
theorem contractProgramCorrect_ringSecond_eq
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hcycleQ : cpRingCycle cpc)
    (hproperQ : (cpmap cpc).ProperRingHead)
    {k : (cpmap cp).map.Dart → Color}
    {k' : (cpmap cpc).map.Dart → Color}
    (hk : (cpmap cp).map.ContractColoring
      (cpContractFinset (false :: mr) mc cp) k)
    (hboundary :
      (cpmap cpc).map.colorsOn k' (cpRing cpc) =
        (cpmap cp).map.colorsOn k
          (CfMask.select ((false :: mr).map Bool.not) (cpRing cp))) :
    k' (cpmap cpc).point = k (cpmap cp).point := by
  let P := cpmap cp
  let Q := cpmap cpc
  have hsizeP : 1 < CProg.ringSize cp := by
    have := CProg.ringSize_gt_two_of_config hcfg
    omega
  have hsizeQ : 1 < CProg.ringSize cpc := by
    exact hcycleQ.one_lt_of_properRingHead hproperQ
  have hringP :
      cpRing cp = P.map.node P.point :: P.point :: (cpRing cp).drop 2 := by
    simpa [P] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one hsizeP
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: Q.point :: (cpRing cpc).drop 2 := by
    simpa [Q] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one hsizeQ
  rw [hringP, hringQ] at hboundary
  simp only [List.map_cons, Bool.not_false,
    CfMask.select, if_true] at hboundary
  have htailBoundary := (List.cons.inj hboundary).2
  have hchain :
      List.IsChain (fun a b => P.map.node.symm a = b) (cpRing cp) := by
    simpa [P, cpRing] using ringDarts_isChain P (CProg.ringSize cp)
  rw [hringP] at hchain
  have hchainTail :
      List.IsChain (fun a b => P.map.node.symm a = b)
        (P.point :: (cpRing cp).drop 2) := by
    cases hchain with
    | cons_cons _ htail => exact htail
  cases hsurvive :
      CfMask.select (mr.map Bool.not) (P.point :: (cpRing cp).drop 2) with
  | nil =>
      rw [hsurvive] at htailBoundary
      change k' Q.point :: List.map k' ((cpRing cpc).drop 2) = []
        at htailBoundary
      nomatch htailBoundary
  | cons y ys =>
      rw [hsurvive] at htailBoundary
      have hpoint : k' Q.point = k y := (List.cons.inj htailBoundary).1
      apply hpoint.trans
      refine Hypermap.ContractColoring.eq_first_unselected_of_isChain
        (mask := mr) (x := P.point) (xs := (cpRing cp).drop 2)
        (y := y) (ys := ys) hk hchainTail ?_ hsurvive
      intro z hz
      apply P.map.mem_contractClosure_self
      unfold cpContractFinset cpContractSelection
      apply List.mem_toFinset.mpr
      apply List.mem_append.mpr
      apply Or.inl
      rw [hringP]
      simpa [CfMask.select] using hz

/-- With the first two source ring edges unselected, the third recursively
contracted ring color is the source third color.  Selected edges after that
corner may form an arbitrarily long prefix.  This is Coq `cfctr_correct`'s
`h'feGc`. -/
theorem contractProgramCorrect_ringThird_eq
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hcycleQ : cpRingCycle cpc)
    (hproperQ : (cpmap cpc).ProperRingHead)
    (hmr : (false :: false :: mr).length = CProg.ringSize cp)
    {k : (cpmap cp).map.Dart → Color}
    {k' : (cpmap cpc).map.Dart → Color}
    (hk : (cpmap cp).map.ContractColoring
      (cpContractFinset (false :: false :: mr) mc cp) k)
    (hboundary :
      (cpmap cpc).map.colorsOn k' (cpRing cpc) =
        (cpmap cp).map.colorsOn k
          (CfMask.select ((false :: false :: mr).map Bool.not)
            (cpRing cp))) :
    k' ((cpmap cpc).map.face
        ((cpmap cpc).map.edge (cpmap cpc).point)) =
      k ((cpmap cp).map.face
        ((cpmap cp).map.edge (cpmap cp).point)) := by
  let P := cpmap cp
  let Q := cpmap cpc
  have hringP :
      cpRing cp = P.map.node P.point :: P.point ::
        P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3 := by
    simpa [P] using
      cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
        (cp := cp) (CProg.ringSize_gt_two_of_config hcfg)
  have hchain :
      List.IsChain (fun a b => P.map.node.symm a = b) (cpRing cp) := by
    simpa [P, cpRing] using ringDarts_isChain P (CProg.ringSize cp)
  rw [hringP] at hchain
  have hchainTail :
      List.IsChain (fun a b => P.map.node.symm a = b)
        (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) := by
    cases hchain with
    | cons_cons _ htail =>
        cases htail with
        | cons_cons _ htail' => exact htail'
  by_cases hsizeQ : 2 < CProg.ringSize cpc
  · have hringQ :
        cpRing cpc = Q.map.node Q.point :: Q.point ::
          Q.map.face (Q.map.edge Q.point) :: (cpRing cpc).drop 3 := by
      simpa [Q] using
        cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
          (cp := cpc) hsizeQ
    rw [hringP, hringQ] at hboundary
    simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
      CfMask.select, if_true] at hboundary
    have htailBoundary :=
      (List.cons.inj (List.cons.inj hboundary).2).2
    cases hsurvive : CfMask.select (mr.map Bool.not)
        (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) with
    | nil =>
        rw [hsurvive] at htailBoundary
        change k' (Q.map.face (Q.map.edge Q.point)) ::
            List.map k' ((cpRing cpc).drop 3) = [] at htailBoundary
        nomatch htailBoundary
    | cons y ys =>
        rw [hsurvive] at htailBoundary
        have hthird : k' (Q.map.face (Q.map.edge Q.point)) = k y :=
          (List.cons.inj htailBoundary).1
        apply hthird.trans
        refine Hypermap.ContractColoring.eq_first_unselected_of_isChain
          (mask := mr) (x := P.map.face (P.map.edge P.point))
          (xs := (cpRing cp).drop 3) (y := y) (ys := ys)
          hk hchainTail ?_ hsurvive
        intro z hz
        apply P.map.mem_contractClosure_self
        unfold cpContractFinset cpContractSelection
        apply List.mem_toFinset.mpr
        apply List.mem_append.mpr
        apply Or.inl
        rw [hringP]
        simpa [CfMask.select] using hz
  · have honeQ : 1 < CProg.ringSize cpc :=
      hcycleQ.one_lt_of_properRingHead hproperQ
    have htwoQ : CProg.ringSize cpc = 2 := by omega
    have hfaceQ : Q.map.face (Q.map.edge Q.point) = Q.map.node Q.point := by
      simpa [Q] using hcycleQ.face_edge_eq_node_of_eq_two htwoQ
    have hdropQ : (cpRing cpc).drop 2 = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [length_cpRing, htwoQ]
    have hringQ :
        cpRing cpc = Q.map.node Q.point :: Q.point :: [] := by
      simpa [Q, hdropQ] using
        cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
          (cp := cpc) honeQ
    have hboundaryShort := hboundary
    rw [hringP, hringQ] at hboundaryShort
    simp only [Hypermap.colorsOn, List.map_cons, List.map_nil,
      Bool.not_false, CfMask.select, if_true] at hboundaryShort
    have hheadQ : k' (Q.map.node Q.point) = k (P.map.node P.point) :=
      (List.cons.inj hboundaryShort).1
    have hsurvive :
        CfMask.select (mr.map Bool.not)
          (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) = [] := by
      have htail := (List.cons.inj (List.cons.inj hboundaryShort).2).2
      simpa using htail.symm
    have hmaskLen :
        mr.length =
          (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3).length := by
      have hlen := length_cpRing cp
      rw [hringP] at hlen
      simp only [List.length_cons] at hmr hlen ⊢
      omega
    have hcyclic := (cpRingCycle_of_config hcfg).isChain_append_head
    change List.IsChain (fun a b => P.map.node.symm a = b)
      (cpRing cp ++ [P.map.node P.point]) at hcyclic
    have hle : 2 ≤ (cpRing cp).length := by
      rw [length_cpRing]
      have := CProg.ringSize_gt_two_of_config hcfg
      omega
    have hcyclicTail :
        List.IsChain (fun a b => P.map.node.symm a = b)
          ((P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) ++
            [P.map.node P.point]) := by
      have hdrop := hcyclic.drop 2
      rw [List.drop_append_of_le_length hle] at hdrop
      have hdropTwo :
          (cpRing cp).drop 2 =
            P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3 := by
        simpa [P] using
          cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
            (cp := cp) (CProg.ringSize_gt_two_of_config hcfg)
      rw [hdropTwo] at hdrop
      simpa [P, cpRing] using hdrop
    have hselected :
        ∀ z, z ∈ CfMask.select mr
              (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) →
          z ∈ P.map.contractClosure
            (cpContractFinset (false :: false :: mr) mc cp) := by
      intro z hz
      apply P.map.mem_contractClosure_self
      unfold cpContractFinset cpContractSelection
      apply List.mem_toFinset.mpr
      apply List.mem_append.mpr
      apply Or.inl
      rw [hringP]
      simpa [CfMask.select] using hz
    rw [hfaceQ]
    exact hheadQ.trans
      (Hypermap.ContractColoring.eq_terminal_of_all_selected_of_isChain
        hk hmaskLen hcyclicTail hselected hsurvive)

/-- If exactly one of the first two source ring edges is selected, the second
recursive boundary color is the source third color.  This packages the two
copies of Coq's selected-prefix induction used by the `H -> Y` branches. -/
theorem contractProgramCorrect_ringSecond_after_one_selected_eq
    {cp cpc : CProg} {b1 b2 : Bool} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hcycleQ : cpRingCycle cpc)
    (hproperQ : (cpmap cpc).ProperRingHead)
    (hone : b1 ≠ b2)
    {k : (cpmap cp).map.Dart → Color}
    {k' : (cpmap cpc).map.Dart → Color}
    (hk : (cpmap cp).map.ContractColoring
      (cpContractFinset (b1 :: b2 :: mr) mc cp) k)
    (hboundary :
      (cpmap cpc).map.colorsOn k' (cpRing cpc) =
        (cpmap cp).map.colorsOn k
          (CfMask.select ((b1 :: b2 :: mr).map Bool.not)
            (cpRing cp))) :
    k' (cpmap cpc).point =
      k ((cpmap cp).map.face
        ((cpmap cp).map.edge (cpmap cp).point)) := by
  let P := cpmap cp
  let Q := cpmap cpc
  have hringP :
      cpRing cp = P.map.node P.point :: P.point ::
        P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3 := by
    simpa [P] using
      cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
        (cp := cp) (CProg.ringSize_gt_two_of_config hcfg)
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: Q.point ::
        (cpRing cpc).drop 2 := by
    simpa [Q] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
        (cp := cpc) (hcycleQ.one_lt_of_properRingHead hproperQ)
  have hchain :
      List.IsChain (fun a b => P.map.node.symm a = b) (cpRing cp) := by
    simpa [P, cpRing] using ringDarts_isChain P (CProg.ringSize cp)
  rw [hringP] at hchain
  have hchainTail :
      List.IsChain (fun a b => P.map.node.symm a = b)
        (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) := by
    cases hchain with
    | cons_cons _ htail =>
        cases htail with
        | cons_cons _ htail' => exact htail'
  have finish :
      List.map k' (Q.point :: (cpRing cpc).drop 2) =
          List.map k (CfMask.select (mr.map Bool.not)
            (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3)) →
        k' Q.point = k (P.map.face (P.map.edge P.point)) := by
    intro htailBoundary
    cases hsurvive : CfMask.select (mr.map Bool.not)
        (P.map.face (P.map.edge P.point) :: (cpRing cp).drop 3) with
    | nil =>
        rw [hsurvive] at htailBoundary
        nomatch htailBoundary
    | cons y ys =>
        rw [hsurvive] at htailBoundary
        have hsecond : k' Q.point = k y :=
          (List.cons.inj htailBoundary).1
        apply hsecond.trans
        refine Hypermap.ContractColoring.eq_first_unselected_of_isChain
          (mask := mr) (x := P.map.face (P.map.edge P.point))
          (xs := (cpRing cp).drop 3) (y := y) (ys := ys)
          hk hchainTail ?_ hsurvive
        intro z hz
        apply P.map.mem_contractClosure_self
        unfold cpContractFinset cpContractSelection
        apply List.mem_toFinset.mpr
        apply List.mem_append.mpr
        apply Or.inl
        rw [hringP]
        cases b1 <;> cases b2
        · simpa [CfMask.select] using hz
        · simp only [CfMask.select, if_true]
          exact List.mem_cons_of_mem _ hz
        · simp only [CfMask.select, Bool.false_eq_true, if_false, if_true]
          exact List.mem_cons_of_mem _ hz
        · simp only [CfMask.select, if_true]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
  rw [hringP, hringQ] at hboundary
  cases b1 <;> cases b2
  · exact (hone rfl).elim
  · simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
      Bool.not_true, CfMask.select, if_true] at hboundary
    exact finish (List.cons.inj hboundary).2
  · simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
      Bool.not_true, CfMask.select, if_true] at hboundary
    exact finish (List.cons.inj hboundary).2
  · exact (hone rfl).elim

/-- Coq's short-`cpring` contradiction in the two `H -> K` cases: on a
two-dart ring the third boundary dart is the first, contradicting the fresh
color inequality used by `kColor`. -/
theorem ringSize_gt_two_of_kFresh
    {cp : CProg} (hcycle : cpRingCycle cp)
    {k : (cpmap cp).map.Dart → Color}
    (hk : (cpmap cp).map.Coloring k)
    (hfresh :
      k ((cpmap cp).map.node (cpmap cp).point) + k (cpmap cp).point ≠
        k (cpmap cp).point +
          k ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))) :
    2 < CProg.ringSize cp := by
  have hproper : (cpmap cp).ProperRingHead := by
    simpa [PointedHypermap.ProperRingHead] using
      hk.properRingHead (cpmap cp).point
  have hone : 1 < CProg.ringSize cp :=
    hcycle.one_lt_of_properRingHead hproper
  by_contra hnot
  have htwo : CProg.ringSize cp = 2 := by omega
  apply hfresh
  rw [hcycle.face_edge_eq_node_of_eq_two htwo]
  exact Color.add_comm _ _

namespace CFContract.Internal

theorem color_add_ne_zero_of_ne {a b : Color} (hne : a ≠ b) :
    a + b ≠ Color.zero :=
  fun hzero => hne ((Color.add_eq_zero_iff_eq _ _).1 hzero)

theorem color_add_add_eq_right {a b c : Color} (hc : c = a) :
    (a + b) + c = b := by
  rw [hc, Color.add_comm a b]
  simp

theorem extensionUColor_new_eq_right
    (Q : PointedHypermap) (k' : Q.map.Dart → Color) {a b : Color}
    (hhead : k' (Q.map.node Q.point) = a) :
    Hypermap.extensionUColor Q.map Q.point k' (a + b) ExtDart.new = b := by
  change (a + b) + k' (Q.map.node Q.point) = b
  exact color_add_add_eq_right hhead

theorem extensionU_node_symm_sq_new_eq_old_point
    (Q : PointedHypermap) (hproper : Q.ProperRingHead) :
    Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new) = Q.uOld Q.point := by
  have h := Q.y_node_symm_point_eq_yOld_point hproper
  change ExtDart.old
      (Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new)) =
    ExtDart.old (Q.uOld Q.point) at h
  exact ExtDart.old_injective h

end CFContract.Internal

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
