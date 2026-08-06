import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Initial

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

open CFContract.Internal

private theorem cpRing_head_pair_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) :
    cpRing cp =
      (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point ::
        (cpRing cp).drop 2 := by
  apply cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
  have := CProg.ringSize_gt_two_of_config hcfg
  omega

private theorem cpRing_h_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) :
    cpRing (CpStep.h :: cp) =
      (cpmap cp).h.map.node (cpmap cp).h.point :: (cpmap cp).h.point ::
        ((cpRing cp).drop 2).map (cpmap cp).hOld := by
  have hgeom := cpmap_configGeometry_of_config hcfg
  exact cpRing_h_eq_of_ringCycle (cpRingCycle_of_config hcfg)
    hgeom.proper hgeom.long (CProg.ringSize_gt_two_of_config hcfg)

private theorem cpRings_h_of_config
    {cp : CProg} (hcfg : CProg.config cp = true) :
    cpRing cp =
        (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point ::
          (cpRing cp).drop 2 ∧
      cpRing (CpStep.h :: cp) =
        (cpmap cp).h.map.node (cpmap cp).h.point :: (cpmap cp).h.point ::
          ((cpRing cp).drop 2).map (cpmap cp).hOld :=
  ⟨cpRing_head_pair_of_config hcfg, cpRing_h_of_config hcfg⟩

private theorem h_node_color_eq_old_node
    (P : PointedHypermap) {cc : Finset P.h.map.Dart}
    {k : P.h.map.Dart → Color}
    (hproper : P.ProperRingHead)
    (hk : P.h.map.ContractColoring cc k) :
    k (P.h.map.node P.h.point) = k (P.hOld (P.map.node P.point)) := by
  apply Eq.symm
  exact Hypermap.ContractColoring.eq_of_face_reachable (G := P.h.map) hk
    ((P.h_faceReachable_node_point_old_iff hproper).2
      (PermReachable.refl P.map.face (P.map.node P.point)))

private theorem h_edge_point_color_eq_old_faceEdge
    (P : PointedHypermap) {cc : Finset P.h.map.Dart}
    {k : P.h.map.Dart → Color}
    (hproper : P.ProperRingHead) (hlong : P.LongRingHead)
    (hk : P.h.map.ContractColoring cc k) :
    k (P.h.map.edge P.h.point) =
      k (P.hOld (P.map.face (P.map.edge P.point))) := by
  apply Eq.symm
  apply Hypermap.ContractColoring.eq_of_face_reachable (G := P.h.map) hk
  exact
    (Hypermap.extensionH_faceReachable_newEdge_old_iff_face_edge_of_proper_long
      (G := P.map) P.point hproper hlong).2
      (PermReachable.refl P.map.face (P.map.face (P.map.edge P.point)))

private theorem h_point_color_ne_old_faceEdge
    (P : PointedHypermap) {cc : Finset P.h.map.Dart}
    {k : P.h.map.Dart → Color}
    (hk : P.h.map.ContractColoring cc k)
    (hpointNot : P.h.point ∉ P.h.map.contractClosure cc)
    (hedgePointOld :
      k (P.h.map.edge P.h.point) =
        k (P.hOld (P.map.face (P.map.edge P.point)))) :
    k P.h.point ≠ k (P.hOld (P.map.face (P.map.edge P.point))) := by
  have hedgeNe := Hypermap.ContractColoring.edge_ne
    (G := P.h.map) hk P.h.point hpointNot
  intro heq
  exact hedgeNe (hedgePointOld.trans heq.symm)

private theorem h_node_point_not_contractClosure_old
    {cp : CProg} {mr mc : List Bool}
    (b4 b5 : Bool) (hcfg : CProg.config cp = true)
    (hproper : (cpmap cp).ProperRingHead) :
    (cpmap cp).h.map.node (cpmap cp).h.point ∉
      (cpmap cp).h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: b4 :: b5 :: mc) (CpStep.h :: cp)) := by
  rw [cpContractFinset_h_eq false false false b4 b5 mr mc hcfg]
  simp only [Bool.false_eq_true, if_false, Finset.empty_union]
  rw [Hypermap.contractClosure_image_of_edge_commute
    (cpmap cp).hOld (cpmap cp).hOld_edge]
  intro hn
  rcases Finset.mem_image.mp hn with ⟨x, _hx, hxn⟩
  rw [h_node_point_eq_old_old_newEdge (cpmap cp) hproper] at hxn
  change ExtDart.old (ExtDart.old (ExtDart.old x)) =
    ExtDart.old (ExtDart.old ExtDart.newEdge) at hxn
  injection hxn with hxn'
  injection hxn' with hxn''
  cases hxn''

private theorem h_node_point_color_ne
    (P : PointedHypermap) {cc : Finset P.h.map.Dart}
    {k : P.h.map.Dart → Color}
    (hk : P.h.map.ContractColoring cc k)
    (hnot : P.h.map.node P.h.point ∉ P.h.map.contractClosure cc) :
    k (P.h.map.node P.h.point) ≠ k P.h.point := by
  have hedgeNe := Hypermap.ContractColoring.edge_ne
    (G := P.h.map) hk (P.h.map.node P.h.point) hnot
  have hfaceNode := Hypermap.ContractColoring.face_eq
    (G := P.h.map) hk (P.h.map.edge (P.h.map.node P.h.point))
  rw [face_edge_node_eq_self P.h.map P.h.point] at hfaceNode
  intro heq
  exact hedgeNe (hfaceNode.symm.trans heq.symm)

private theorem h_node_point_mem_contractClosure_of_left
    {cp : CProg} {mr mc : List Bool} (b2 b3 b4 b5 : Bool)
    (hcfg : CProg.config cp = true) :
    (cpmap cp).h.map.node (cpmap cp).h.point ∈
      (cpmap cp).h.map.contractClosure
        (cpContractFinset (true :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
          (CpStep.h :: cp)) := by
  apply (cpmap cp).h.map.mem_contractClosure_self
  rw [cpContractFinset_h_eq true b2 b3 b4 b5 mr mc hcfg]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))))

private theorem h_point_color_eq_old_node_of_node_selected
    (P : PointedHypermap) {cc : Finset P.h.map.Dart}
    {k : P.h.map.Dart → Color}
    (hk : P.h.map.ContractColoring cc k)
    (hnodeOld :
      k (P.h.map.node P.h.point) = k (P.hOld (P.map.node P.point)))
    (hselected : P.h.map.node P.h.point ∈ P.h.map.contractClosure cc) :
    k P.h.point = k (P.hOld (P.map.node P.point)) := by
  have hfaceEdge := Hypermap.ContractColoring.face_eq
    (G := P.h.map) hk (P.h.map.edge (P.h.map.node P.h.point))
  rw [face_edge_node_eq_self P.h.map P.h.point] at hfaceEdge
  have hedgeNode := Hypermap.ContractColoring.edge_eq
    (G := P.h.map) hk (P.h.map.node P.h.point) hselected
  exact hfaceEdge.trans (hedgeNode.trans hnodeOld)

private theorem pairSums_ne_of_boundary_eq
    {a b c a' b' c' : Color}
    (ha : a' = a) (hb : b' = b) (hc : c' = c) (hne : a ≠ c) :
    a' + b' ≠ b' + c' := by
  intro hsum
  rw [ha, hb, hc] at hsum
  apply hne
  apply Color.add_left_cancel (a := b)
  exact (Color.add_comm b a).trans hsum

private theorem k_extension_result
    {cpc : CProg} {k' : (cpmap cpc).map.Dart → Color}
    (hcycle : cpRingCycle cpc)
    (hk' : (cpmap cpc).map.Coloring k')
    (hkFresh :
      k' ((cpmap cpc).map.node (cpmap cpc).point) + k' (cpmap cpc).point ≠
        k' (cpmap cpc).point +
          k' ((cpmap cpc).map.face ((cpmap cpc).map.edge (cpmap cpc).point)))
    {cs : List Color}
    (hboundary :
      k' ((cpmap cpc).map.node (cpmap cpc).point) ::
          ((cpmap cpc).map.colorsOn k' (cpRing cpc)).drop 2 = cs) :
    ∃ kk : (cpmap (CpStep.k :: cpc)).map.Dart → Color,
      (cpmap (CpStep.k :: cpc)).map.Coloring kk ∧
        cpRingCycle (CpStep.k :: cpc) ∧
          (cpmap (CpStep.k :: cpc)).map.colorsOn kk
            (cpRing (CpStep.k :: cpc)) = cs := by
  let Q := cpmap cpc
  have hsize : 2 < CProg.ringSize cpc :=
    ringSize_gt_two_of_kFresh hcycle hk' hkFresh
  let kk : Q.k.map.Dart → Color := kColor Q k'
  have hkk : Q.k.map.Coloring kk := kColor_coloring hk' hkFresh
  refine ⟨kk, by simpa [Q] using hkk, cpRingCycle_k hcycle hsize, ?_⟩
  calc
    (cpmap (CpStep.k :: cpc)).map.colorsOn kk
        (cpRing (CpStep.k :: cpc)) =
        k' (Q.map.node Q.point) ::
          (Q.map.colorsOn k' (cpRing cpc)).drop 2 := by
      change Q.k.map.colorsOn kk
          (ringDarts Q.k (CProg.ringSize cpc - 2 + 1)) = _
      simpa [kk] using colorsOn_kColor_ringDarts
        (P := Q) (n := CProg.ringSize cpc) hcycle hsize k'
    _ = cs := by simpa [Q] using hboundary

/-- `H` mask `00100`: the crossbar is contracted, so the executable output
is the recursive program unchanged. -/
theorem contractProgramCorrect_h_crossbar
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hrec : ContractProgramCorrect (false :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: false :: mr)
      (true :: false :: false :: mc) (CpStep.h :: cp) cpc := by
  intro k hk
  let P := cpmap cp
  have hkrec := contractColoring_pullback_h
    false false true false false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  refine ⟨k', hk', hcycleQ, ?_⟩
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  have hcrossSelected : P.h.map.face P.h.point ∈
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (true :: false :: false :: mc) (CpStep.h :: cp)) := by
    apply P.h.map.mem_contractClosure_self
    rw [cpContractFinset_h_eq false false true false false mr mc hcfg]
    exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))))
  have hpointOld : k P.h.point = k (P.hOld P.point) := by
    let z := P.h.map.face P.h.point
    have hfacePoint := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk P.h.point
    have hedgeCross := Hypermap.ContractColoring.edge_eq
      (G := P.h.map) hk z (by simpa [z] using hcrossSelected)
    have hfaceEdge := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk (P.h.map.edge z)
    rw [h_face_edge_face_point_eq_hOld_point P hgeom.proper] at hfaceEdge
    exact hfacePoint.symm.trans
      (hedgeCross.symm.trans hfaceEdge.symm)
  rw [hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    CfMask.select, if_true, Function.comp_apply]
  exact congrArg₂ List.cons hnodeOld.symm
    (congrArg₂ List.cons hpointOld.symm
      (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
        ((cpRing cp).drop 2)))

/-- `H` mask `10001`: contracting the new left ring edge and the old right
head leaves the recursive program unchanged. -/
theorem contractProgramCorrect_h_left_unchanged
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hrec : ContractProgramCorrect (false :: true :: mr) mc cp cpc) :
    ContractProgramCorrect (true :: false :: mr)
      (false :: false :: true :: mc) (CpStep.h :: cp) cpc := by
  intro k hk
  let P := cpmap cp
  have hkrec := contractColoring_pullback_h
    true false false false true mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  refine ⟨k', hk', hcycleQ, ?_⟩
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  have hnodeSelected : P.h.map.node P.h.point ∈
      P.h.map.contractClosure
        (cpContractFinset (true :: false :: mr)
          (false :: false :: true :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_mem_contractClosure_of_left
      (mr := mr) (mc := mc) false false false true hcfg
  have hpointHead :
      k P.h.point = k (P.hOld (P.map.node P.point)) := by
    exact h_point_color_eq_old_node_of_node_selected
      P hk hnodeOld hnodeSelected
  rw [hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false, Bool.not_true,
    CfMask.select, if_true, Function.comp_apply]
  exact congrArg₂ List.cons hpointHead.symm
    (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
      ((cpRing cp).drop 2))

/-- `H` mask `01010`: contracting the new right ring edge and the old left
head leaves the recursive program unchanged. -/
theorem contractProgramCorrect_h_right_unchanged
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hrec : ContractProgramCorrect (true :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: true :: mr)
      (false :: true :: false :: mc) (CpStep.h :: cp) cpc := by
  intro k hk
  let P := cpmap cp
  have hkrec := contractColoring_pullback_h
    false true false true false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  refine ⟨k', hk', hcycleQ, ?_⟩
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  have hsourceSelected : P.map.node P.point ∈
      P.map.contractClosure
        (cpContractFinset (true :: false :: mr) mc cp) := by
    apply P.map.mem_contractClosure_self
    unfold cpContractFinset cpContractSelection
    apply List.mem_toFinset.mpr
    apply List.mem_append.mpr
    apply Or.inl
    rw [hringP]
    exact List.mem_cons_self
  have hsourceHeads :
      k (P.hOld (P.map.node P.point)) = k (P.hOld P.point) := by
    have hedgeNode := Hypermap.ContractColoring.edge_eq
      (G := P.map) hkrec (P.map.node P.point) hsourceSelected
    have hfaceEdge := Hypermap.ContractColoring.face_eq
      (G := P.map) hkrec (P.map.edge (P.map.node P.point))
    rw [face_edge_node_eq_self P.map P.point] at hfaceEdge
    exact hedgeNode.symm.trans hfaceEdge.symm
  have hnodePoint :
      k (P.h.map.node P.h.point) = k (P.hOld P.point) :=
    hnodeOld.trans hsourceHeads
  rw [hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false, Bool.not_true,
    CfMask.select, if_true]
  exact congrArg₂ List.cons hnodePoint.symm
    (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
      ((cpRing cp).drop 2))

/-- `H` mask `10000`: the canonical `K` extension realizes the one surviving
fresh boundary color. -/
theorem contractProgramCorrect_h_left_k
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : (false :: false :: mr).length = CProg.ringSize cp)
    (hrec : ContractProgramCorrect (false :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (true :: false :: mr)
      (false :: false :: false :: mc) (CpStep.h :: cp)
      (CpStep.k :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    true false false false false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hsecond := contractProgramCorrect_ringSecond_eq hcfg hcycleQ hproperQ
    (by simpa [P] using hkrec) hboundary
  have hthird := contractProgramCorrect_ringThird_eq
    hcfg hcycleQ hproperQ hmr (by simpa [P] using hkrec) hboundary
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  have hnodeSelected : P.h.map.node P.h.point ∈
      P.h.map.contractClosure
        (cpContractFinset (true :: false :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_mem_contractClosure_of_left
      (mr := mr) (mc := mc) false false false false hcfg
  have hpointHead :
      k P.h.point = k (P.hOld (P.map.node P.point)) := by
    exact h_point_color_eq_old_node_of_node_selected
      P hk hnodeOld hnodeSelected
  let faceEdge := P.map.face (P.map.edge P.point)
  have hedgePointOld := h_edge_point_color_eq_old_faceEdge
    P hgeom.proper hgeom.long hk
  have hselEq :
      cpContractFinset (true :: false :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp) =
        {P.h.map.node P.h.point} ∪
          (cpContractFinset (false :: false :: mr) mc cp).image P.hOld := by
    simpa [P] using
      cpContractFinset_h_eq true false false false false mr mc hcfg
  have hpointNot : P.h.point ∉ P.h.map.contractClosure
      (cpContractFinset (true :: false :: mr)
        (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    intro hp
    rcases (P.h.map.mem_contractClosure_iff).1 hp with hp | ⟨z, hz, hez⟩
    · rw [hselEq] at hp
      rcases Finset.mem_union.mp hp with hp | hp
      · have hp' := Finset.mem_singleton.mp hp
        rw [h_node_point_eq_old_old_newEdge P hgeom.proper] at hp'
        cases hp'
      · rcases Finset.mem_image.mp hp with ⟨x, _hx, hxp⟩
        exact P.hOld_ne_point x hxp
    · rw [hselEq] at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hz' := Finset.mem_singleton.mp hz
        subst z
        rw [h_edge_node_point_eq_old_old_new P hgeom.proper] at hez
        cases hez
      · rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
        subst z
        rw [← P.hOld_edge] at hez
        exact P.hOld_ne_point (P.map.edge x) hez
  have hendpointNe :
      k (P.hOld (P.map.node P.point)) ≠ k (P.hOld faceEdge) := by
    have hedgeNe := Hypermap.ContractColoring.edge_ne
      (G := P.h.map) hk P.h.point hpointNot
    intro heq
    apply hedgeNe
    exact hedgePointOld.trans (heq.symm.trans hpointHead.symm)
  have hkFresh := pairSums_ne_of_boundary_eq
    hhead hsecond hthird hendpointNe
  apply k_extension_result hcycleQ hk' hkFresh
  rw [hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false, Bool.not_true,
    CfMask.select, if_true, Function.comp_apply]
  exact congrArg₂ List.cons (hhead.trans hpointHead.symm)
    (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
      ((cpRing cp).drop 2))

/-- `H` mask `01000`: the symmetric canonical `K` extension. -/
theorem contractProgramCorrect_h_right_k
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : (false :: false :: mr).length = CProg.ringSize cp)
    (hrec : ContractProgramCorrect (false :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: true :: mr)
      (false :: false :: false :: mc) (CpStep.h :: cp)
      (CpStep.k :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    false true false false false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hsecond := contractProgramCorrect_ringSecond_eq hcfg hcycleQ hproperQ
    (by simpa [P] using hkrec) hboundary
  have hthird := contractProgramCorrect_ringThird_eq
    hcfg hcycleQ hproperQ hmr (by simpa [P] using hkrec) hboundary
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  let faceEdge := P.map.face (P.map.edge P.point)
  have hedgePointOld := h_edge_point_color_eq_old_faceEdge
    P hgeom.proper hgeom.long hk
  have hpointSelected : P.h.point ∈ P.h.map.contractClosure
      (cpContractFinset (false :: true :: mr)
        (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    apply P.h.map.mem_contractClosure_self
    rw [cpContractFinset_h_eq false true false false false mr mc hcfg]
    exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
  have hpointOld : k P.h.point = k (P.hOld faceEdge) := by
    have hedgePoint := Hypermap.ContractColoring.edge_eq
      (G := P.h.map) hk P.h.point hpointSelected
    exact hedgePoint.symm.trans hedgePointOld
  have hselEq :
      cpContractFinset (false :: true :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp) =
        {P.h.point} ∪
          (cpContractFinset (false :: false :: mr) mc cp).image P.hOld := by
    simpa [P] using
      cpContractFinset_h_eq false true false false false mr mc hcfg
  have hnodeNot : P.h.map.node P.h.point ∉ P.h.map.contractClosure
      (cpContractFinset (false :: true :: mr)
        (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    intro hn
    rcases (P.h.map.mem_contractClosure_iff).1 hn with hn | ⟨z, hz, hez⟩
    · rw [hselEq] at hn
      rcases Finset.mem_union.mp hn with hn | hn
      · have hn' := Finset.mem_singleton.mp hn
        rw [h_node_point_eq_old_old_newEdge P hgeom.proper] at hn'
        cases hn'
      · rcases Finset.mem_image.mp hn with ⟨x, _hx, hxn⟩
        rw [h_node_point_eq_old_old_newEdge P hgeom.proper] at hxn
        change ExtDart.old (ExtDart.old (ExtDart.old x)) =
          ExtDart.old (ExtDart.old ExtDart.newEdge) at hxn
        injection hxn with hxn'
        injection hxn' with hxn''
        cases hxn''
    · rw [hselEq] at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hz' := Finset.mem_singleton.mp hz
        subst z
        change ExtDart.newEdge = P.h.map.node P.h.point at hez
        rw [h_node_point_eq_old_old_newEdge P hgeom.proper] at hez
        cases hez
      · rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
        subst z
        rw [← P.hOld_edge,
          h_node_point_eq_old_old_newEdge P hgeom.proper] at hez
        change ExtDart.old (ExtDart.old (ExtDart.old (P.map.edge x))) =
          ExtDart.old (ExtDart.old ExtDart.newEdge) at hez
        injection hez with hez'
        injection hez' with hez''
        cases hez''
  have hendpointNe :
      k (P.hOld (P.map.node P.point)) ≠ k (P.hOld faceEdge) := by
    have hedgeNe := Hypermap.ContractColoring.edge_ne
      (G := P.h.map) hk (P.h.map.node P.h.point) hnodeNot
    have hfaceEdge := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk (P.h.map.edge (P.h.map.node P.h.point))
    rw [face_edge_node_eq_self P.h.map P.h.point] at hfaceEdge
    intro heq
    apply hedgeNe
    exact hfaceEdge.symm.trans
      (hpointOld.trans (heq.symm.trans hnodeOld.symm))
  have hkFresh := pairSums_ne_of_boundary_eq
    hhead hsecond hthird hendpointNe
  apply k_extension_result hcycleQ hk' hkFresh
  rw [hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false, Bool.not_true,
    CfMask.select, if_true, Function.comp_apply]
  exact congrArg₂ List.cons (hhead.trans hnodeOld.symm)
    (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
      ((cpRing cp).drop 2))

/-- `H` mask `11000`: merging the two surviving recursive corners is Coq's
`A` output branch. -/
theorem contractProgramCorrect_h_a
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : (false :: false :: mr).length = CProg.ringSize cp)
    (hsizeQ : 2 < CProg.ringSize cpc)
    (hrec : ContractProgramCorrect (false :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (true :: true :: mr)
      (false :: false :: false :: mc) (CpStep.h :: cp)
      (CpStep.a :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    true true false false false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hthird := contractProgramCorrect_ringThird_eq
    hcfg hcycleQ hproperQ hmr (by simpa [P] using hkrec) hboundary
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  let faceEdge := P.map.face (P.map.edge P.point)
  have hedgePointOld := h_edge_point_color_eq_old_faceEdge
    P hgeom.proper hgeom.long hk
  have hnodeSelected : P.h.map.node P.h.point ∈
      P.h.map.contractClosure
        (cpContractFinset (true :: true :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_mem_contractClosure_of_left
      (mr := mr) (mc := mc) true false false false hcfg
  have hpointSelected : P.h.point ∈
      P.h.map.contractClosure
        (cpContractFinset (true :: true :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    apply P.h.map.mem_contractClosure_self
    rw [cpContractFinset_h_eq true true false false false mr mc hcfg]
    exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))))))
  have hsourceEq :
      k (P.hOld (P.map.node P.point)) = k (P.hOld faceEdge) := by
    have hedgeNode := Hypermap.ContractColoring.edge_eq
      (G := P.h.map) hk (P.h.map.node P.h.point) hnodeSelected
    have hfaceNode := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk (P.h.map.edge (P.h.map.node P.h.point))
    rw [face_edge_node_eq_self P.h.map P.h.point] at hfaceNode
    have hedgePoint := Hypermap.ContractColoring.edge_eq
      (G := P.h.map) hk P.h.point hpointSelected
    exact hnodeOld.symm.trans
      (hedgeNode.symm.trans
        (hfaceNode.symm.trans (hedgePoint.symm.trans hedgePointOld)))
  have hsourceEq' :
      (k ∘ P.hOld) (P.map.node P.point) =
        (k ∘ P.hOld) (P.map.face (P.map.edge P.point)) := by
    simpa [faceEdge] using hsourceEq
  have hmerge :
      k' (Q.map.node Q.point) =
        k' (Q.map.face (Q.map.edge Q.point)) := by
    exact hhead.trans (hsourceEq'.trans hthird.symm)
  have hkA : Q.a.map.Coloring k' :=
    Hypermap.extensionAColoring hk'
      (ringCycle_longRingHead_of_two_lt hcycleQ hsizeQ)
      hmerge
  refine ⟨k', by simpa [Q, cpmap, step] using hkA,
    cpRingCycle_a hcycleQ hsizeQ, ?_⟩
  have hringA :
      cpRing (CpStep.a :: cpc) = (cpRing cpc).drop 2 := by
    change ringDarts Q.a
        (if 2 < CProg.ringSize cpc then CProg.ringSize cpc - 2
          else CProg.ringSize cpc) = (cpRing cpc).drop 2
    rw [if_pos hsizeQ]
    simpa [Q, cpRing] using
      ringDarts_a_eq_drop_two Q hcycleQ hsizeQ
  change (cpmap (CpStep.a :: cpc)).map.colorsOn k'
      (cpRing (CpStep.a :: cpc)) =
    P.h.map.colorsOn k
      (CfMask.select ((true :: true :: mr).map Bool.not)
        (cpRing (CpStep.h :: cp)))
  rw [hringA]
  change Q.map.colorsOn k' ((cpRing cpc).drop 2) = _
  have hmapDrop :
      Q.map.colorsOn k' ((cpRing cpc).drop 2) =
        (Q.map.colorsOn k' (cpRing cpc)).drop 2 :=
    List.map_drop
  rw [hmapDrop, hboundary, hringP, hringH]
  simp only [List.map_cons, Bool.not_false, Bool.not_true, CfMask.select, if_true]
  exact map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
    ((cpRing cp).drop 2)

/-- `H` mask `00011`: the two fresh boundary colors are realized by a `U`
extension of the recursive coloring. -/
theorem contractProgramCorrect_h_u
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hrec : ContractProgramCorrect (true :: true :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: false :: mr)
      (false :: true :: true :: mc) (CpStep.h :: cp)
      (CpStep.u :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    false false false true true mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hnodeOld := h_node_color_eq_old_node P hgeom.proper hk
  have hheadFresh :
      k' (Q.map.node Q.point) = k (P.h.map.node P.h.point) :=
    hhead.trans hnodeOld.symm
  have hnodeNot : P.h.map.node P.h.point ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: true :: true :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_not_contractClosure_old
      (mr := mr) (mc := mc) true true hcfg hgeom.proper
  have hfreshNe := h_node_point_color_ne P hk hnodeNot
  let e := k (P.h.map.node P.h.point) + k P.h.point
  have he : e ≠ Color.zero := by
    simpa [e] using color_add_ne_zero_of_ne hfreshNe
  let ku : Q.u.map.Dart → Color :=
    Hypermap.extensionUColor Q.map Q.point k' e
  refine ⟨ku, Hypermap.extensionUColor_coloring hk' he,
    cpRingCycle_u hcycleQ, ?_⟩
  have hcolorsU :
      (cpmap (CpStep.u :: cpc)).map.colorsOn ku
          (cpRing (CpStep.u :: cpc)) =
        k' (Q.map.node Q.point) ::
          (e + k' (Q.map.node Q.point)) ::
            Q.map.colorsOn k' (cpRing cpc) := by
    change Q.u.map.colorsOn ku
        (ringDarts Q.u (CProg.ringSize cpc + 2)) = _
    simpa [ku] using colorsOn_extensionUColor_ringDarts
      (P := Q) (n := CProg.ringSize cpc)
      hcycleQ k' e
  have hsecondFresh :
      e + k' (Q.map.node Q.point) = k P.h.point := by
    simpa [e] using color_add_add_eq_right hheadFresh
  change (cpmap (CpStep.u :: cpc)).map.colorsOn ku
      (cpRing (CpStep.u :: cpc)) =
    P.h.map.colorsOn k
      (CfMask.select ((false :: false :: mr).map Bool.not)
        (cpRing (CpStep.h :: cp)))
  rw [hcolorsU, hboundary, hringP, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    Bool.not_true, CfMask.select, if_true]
  exact congrArg₂ List.cons hheadFresh
    (congrArg₂ List.cons hsecondFresh
      (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
        ((cpRing cp).drop 2)))

/-- `H` masks `00010` and `00001`: exactly one old head edge is selected,
and the surviving fresh colors extend the recursive coloring through `Y`. -/
theorem contractProgramCorrect_h_y
    {cp cpc : CProg} {b4 b5 : Bool} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hone : b4 ≠ b5)
    (hrec : ContractProgramCorrect (b4 :: b5 :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: false :: mr)
      (false :: b4 :: b5 :: mc) (CpStep.h :: cp)
      (CpStep.y :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    false false false b4 b5 mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have hsizeQ : 1 < CProg.ringSize cpc :=
    hcycleQ.one_lt_of_properRingHead hproperQ
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hsecondOld :=
    contractProgramCorrect_ringSecond_after_one_selected_eq
      hcfg hcycleQ hproperQ hone (by simpa [P] using hkrec) hboundary
  have hgeomP := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: (cpRing cpc).drop 1 := by
    simpa [Q] using cpRing_eq_nodePoint_cons_drop_one cpc
  have hnodeOld := h_node_color_eq_old_node P hgeomP.proper hk
  have hheadFresh :
      k' (Q.map.node Q.point) = k (P.h.map.node P.h.point) :=
    hhead.trans hnodeOld.symm
  have hnodeNot : P.h.map.node P.h.point ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: b4 :: b5 :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_not_contractClosure_old
      (mr := mr) (mc := mc) b4 b5 hcfg hgeomP.proper
  have hfreshNe := h_node_point_color_ne P hk hnodeNot
  have hpointNot : P.h.point ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: b4 :: b5 :: mc) (CpStep.h :: cp)) := by
    rw [cpContractFinset_h_eq false false false b4 b5 mr mc hcfg]
    simp only [Bool.false_eq_true, if_false, Finset.empty_union]
    rw [Hypermap.contractClosure_image_of_edge_commute P.hOld P.hOld_edge]
    intro hp
    rcases Finset.mem_image.mp hp with ⟨x, _hx, hxp⟩
    exact P.hOld_ne_point x hxp
  let faceEdge := P.map.face (P.map.edge P.point)
  have hedgePointOld := h_edge_point_color_eq_old_faceEdge
    P hgeomP.proper hgeomP.long hk
  have hpointOldNe : k P.h.point ≠ k (P.hOld faceEdge) := by
    exact h_point_color_ne_old_faceEdge P hk hpointNot hedgePointOld
  let e := k (P.h.map.node P.h.point) + k P.h.point
  have he : e ≠ Color.zero := by
    simpa [e] using color_add_ne_zero_of_ne hfreshNe
  let ku : Q.u.map.Dart → Color :=
    Hypermap.extensionUColor Q.map Q.point k' e
  have hku : Q.u.map.Coloring ku :=
    Hypermap.extensionUColor_coloring hk' he
  have hsecondFresh : ku ExtDart.new = k P.h.point := by
    simpa [ku, e] using extensionUColor_new_eq_right Q k' hheadFresh
  have hdoubleInv :
      Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new) =
        Q.uOld Q.point := by
    exact extensionU_node_symm_sq_new_eq_old_point Q hproperQ
  have hnFresh :
      ku ExtDart.new ≠
        ku (Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new)) := by
    rw [hdoubleInv, hsecondFresh]
    change k P.h.point ≠ k' Q.point
    rw [hsecondOld]
    simpa [P, faceEdge] using hpointOldNe
  let ky : Q.y.map.Dart → Color :=
    Hypermap.extensionNColor Q.u.map ExtDart.new ku
  have hky : Q.y.map.Coloring ky :=
    Hypermap.extensionNColor_coloring hku
      (Hypermap.extensionU_long_new (G := Q.map) Q.point) hnFresh
  refine ⟨ky, hky,
    cpRingCycle_y hcycleQ hproperQ hsizeQ, ?_⟩
  have hringYQ :
      cpRing (CpStep.y :: cpc) =
        Q.y.map.node Q.y.point :: Q.y.point ::
          ((cpRing cpc).drop 1).map Q.yOld := by
    simpa [Q] using cpRing_y_eq_of_ringCycle
      (cp := cpc) hcycleQ hproperQ
  have hboundaryTail :
      Q.map.colorsOn k' ((cpRing cpc).drop 1) =
        P.map.colorsOn (k ∘ P.hOld)
          (CfMask.select (mr.map Bool.not) ((cpRing cp).drop 2)) := by
    rw [hringQ, hringP] at hboundary
    cases b4 <;> cases b5
    · exact (hone rfl).elim
    · simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
        Bool.not_true, CfMask.select, if_true] at hboundary
      exact (List.cons.inj hboundary).2
    · simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
        Bool.not_true, CfMask.select, if_true] at hboundary
      exact (List.cons.inj hboundary).2
    · exact (hone rfl).elim
  have hkyNode : ky (Q.y.map.node Q.y.point) =
      k' (Q.map.node Q.point) := by
    change Hypermap.extensionNColor
        (Hypermap.extensionU Q.map Q.point) ExtDart.new ku
          ((Hypermap.extensionY Q.map Q.point).node ExtDart.new) = _
    rw [Hypermap.extensionY_node_new]
    rfl
  have hkyPoint : ky Q.y.point = ku ExtDart.new := by rfl
  have hkyOld (x : Q.map.Dart) : ky (Q.yOld x) = k' x := by rfl
  have hcolorsY :
      Q.y.map.colorsOn ky (cpRing (CpStep.y :: cpc)) =
        k' (Q.map.node Q.point) :: ku ExtDart.new ::
          Q.map.colorsOn k' ((cpRing cpc).drop 1) := by
    rw [hringYQ]
    unfold Hypermap.colorsOn
    simp only [List.map_cons, hkyNode, hkyPoint]
    apply congrArg (List.cons (k' (Q.map.node Q.point)))
    apply congrArg (List.cons (ku ExtDart.new))
    induction (cpRing cpc).drop 1 with
    | nil => rfl
    | cons x xs ih =>
        change ky (Q.yOld x) :: List.map ky (xs.map Q.yOld) =
          k' x :: List.map k' xs
        exact congrArg₂ List.cons (hkyOld x) ih
  change Q.y.map.colorsOn ky (cpRing (CpStep.y :: cpc)) =
    P.h.map.colorsOn k
      (CfMask.select ((false :: false :: mr).map Bool.not)
        (cpRing (CpStep.h :: cp)))
  rw [hcolorsY, hboundaryTail, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    CfMask.select, if_true]
  exact congrArg₂ List.cons hheadFresh
    (congrArg₂ List.cons hsecondFresh
      (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
        ((cpRing cp).drop 2)))

/-- `H` mask `00000`: all three fresh edges survive, and the recursive
coloring extends canonically through `U`, then the two `N` constructors of
`H`. -/
theorem contractProgramCorrect_h_h
    {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : (false :: false :: mr).length = CProg.ringSize cp)
    (hrec : ContractProgramCorrect (false :: false :: mr) mc cp cpc) :
    ContractProgramCorrect (false :: false :: mr)
      (false :: false :: false :: mc) (CpStep.h :: cp)
      (CpStep.h :: cpc) := by
  intro k hk
  let P := cpmap cp
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_h
    false false false false false mr mc hcfg hk
  rcases hrec (k ∘ P.hOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have honeQ : 1 < CProg.ringSize cpc :=
    hcycleQ.one_lt_of_properRingHead hproperQ
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hsecondOld := contractProgramCorrect_ringSecond_eq hcfg hcycleQ hproperQ
    (by simpa [P] using hkrec) hboundary
  have hthirdOld := contractProgramCorrect_ringThird_eq
    hcfg hcycleQ hproperQ hmr (by simpa [P] using hkrec) hboundary
  have hgeomP := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringH⟩ := cpRings_h_of_config hcfg
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: Q.point ::
        (cpRing cpc).drop 2 := by
    simpa [Q] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
        (cp := cpc) honeQ
  have hnodeOld := h_node_color_eq_old_node P hgeomP.proper hk
  have hheadFresh :
      k' (Q.map.node Q.point) = k (P.h.map.node P.h.point) :=
    hhead.trans hnodeOld.symm
  have hnodeNot : P.h.map.node P.h.point ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    simpa [P] using h_node_point_not_contractClosure_old
      (mr := mr) (mc := mc) false false hcfg hgeomP.proper
  have hpointNot : P.h.point ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    rw [cpContractFinset_h_eq false false false false false mr mc hcfg]
    simp only [Bool.false_eq_true, if_false, Finset.empty_union]
    rw [Hypermap.contractClosure_image_of_edge_commute P.hOld P.hOld_edge]
    intro hp
    rcases Finset.mem_image.mp hp with ⟨x, _hx, hxp⟩
    exact P.hOld_ne_point x hxp
  let crossbar := P.h.map.face P.h.point
  have hcrossbarNot : crossbar ∉
      P.h.map.contractClosure
        (cpContractFinset (false :: false :: mr)
          (false :: false :: false :: mc) (CpStep.h :: cp)) := by
    rw [cpContractFinset_h_eq false false false false false mr mc hcfg]
    simp only [Bool.false_eq_true, if_false, Finset.empty_union]
    rw [Hypermap.contractClosure_image_of_edge_commute P.hOld P.hOld_edge]
    intro hc
    rcases Finset.mem_image.mp hc with ⟨x, _hx, hxc⟩
    change ExtDart.old (ExtDart.old (ExtDart.old x)) =
      ExtDart.old (ExtDart.new : P.y.map.Dart) at hxc
    injection hxc with hxc'
    cases hxc'
  have hfreshNe := h_node_point_color_ne P hk hnodeNot
  have hpointOldPointNe : k P.h.point ≠ k (P.hOld P.point) := by
    have hedgeNe := Hypermap.ContractColoring.edge_ne
      (G := P.h.map) hk crossbar hcrossbarNot
    have hfacePoint := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk P.h.point
    change k crossbar = k P.h.point at hfacePoint
    have hfaceEdge := Hypermap.ContractColoring.face_eq
      (G := P.h.map) hk (P.h.map.edge crossbar)
    change k (P.h.map.face (P.h.map.edge (P.h.map.face P.h.point))) =
      k (P.h.map.edge crossbar) at hfaceEdge
    rw [h_face_edge_face_point_eq_hOld_point P hgeomP.proper] at hfaceEdge
    intro heq
    exact hedgeNe
      (hfaceEdge.symm.trans (heq.symm.trans hfacePoint.symm))
  let faceEdge := P.map.face (P.map.edge P.point)
  have hedgePointOld := h_edge_point_color_eq_old_faceEdge
    P hgeomP.proper hgeomP.long hk
  have hpointOldFaceNe : k P.h.point ≠ k (P.hOld faceEdge) := by
    exact h_point_color_ne_old_faceEdge P hk hpointNot hedgePointOld
  let e := k (P.h.map.node P.h.point) + k P.h.point
  have he : e ≠ Color.zero := by
    simpa [e] using color_add_ne_zero_of_ne hfreshNe
  let ku : Q.u.map.Dart → Color :=
    Hypermap.extensionUColor Q.map Q.point k' e
  have hku : Q.u.map.Coloring ku :=
    Hypermap.extensionUColor_coloring hk' he
  have hsecondFresh : ku ExtDart.new = k P.h.point := by
    simpa [ku, e] using extensionUColor_new_eq_right Q k' hheadFresh
  have hdoubleInvU :
      Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new) =
        Q.uOld Q.point := by
    exact extensionU_node_symm_sq_new_eq_old_point Q hproperQ
  have hnFreshY :
      ku ExtDart.new ≠
        ku (Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new)) := by
    rw [hdoubleInvU, hsecondFresh]
    change k P.h.point ≠ k' Q.point
    rw [hsecondOld]
    simpa [P] using hpointOldPointNe
  let ky : Q.y.map.Dart → Color :=
    Hypermap.extensionNColor Q.u.map ExtDart.new ku
  have hky : Q.y.map.Coloring ky :=
    Hypermap.extensionNColor_coloring hku
      (Hypermap.extensionU_long_new (G := Q.map) Q.point) hnFreshY
  have hkyNode : ky (Q.y.map.node Q.y.point) =
      k' (Q.map.node Q.point) := by
    change Hypermap.extensionNColor
        (Hypermap.extensionU Q.map Q.point) ExtDart.new ku
          ((Hypermap.extensionY Q.map Q.point).node ExtDart.new) = _
    rw [Hypermap.extensionY_node_new]
    rfl
  have hkyPoint : ky Q.y.point = ku ExtDart.new := by rfl
  have hnFreshH :
      ky Q.y.point ≠
        ky (Q.y.map.node.symm (Q.y.map.node.symm Q.y.point)) := by
    by_cases hsizeQ : 2 < CProg.ringSize cpc
    · have hlongQ : Q.LongRingHead :=
        ringCycle_longRingHead_of_two_lt hcycleQ hsizeQ
      have hdoubleInvY :
          Q.y.map.node.symm (Q.y.map.node.symm Q.y.point) =
            Q.yOld (Q.map.face (Q.map.edge Q.point)) := by
        have hnn : Q.point ≠ Q.map.node (Q.map.node Q.point) := by
          intro heq
          apply hlongQ
          apply Q.map.node.injective
          rw [Hypermap.node_face_edge]
          exact heq
        rw [Q.y_node_symm_point_eq_yOld_point hproperQ]
        rw [Q.yOld_node_symm_of_ne_node_node_point_of_ne_node_point
          hnn hproperQ]
        rw [Hypermap.face_edge_eq_node_symm]
      rw [hdoubleInvY, hkyPoint, hsecondFresh]
      change k P.h.point ≠ k' (Q.map.face (Q.map.edge Q.point))
      rw [hthirdOld]
      simpa [P, faceEdge] using hpointOldFaceNe
    · have htwoQ : CProg.ringSize cpc = 2 := by omega
      have hfaceQ :
          Q.map.face (Q.map.edge Q.point) = Q.map.node Q.point := by
        simpa [Q] using hcycleQ.face_edge_eq_node_of_eq_two htwoQ
      have hnodeTwo : Q.map.node (Q.map.node Q.point) = Q.point := by
        rw [← hfaceQ]
        exact Q.map.node_face_edge Q.point
      have hdoubleInvY :
          Q.y.map.node.symm (Q.y.map.node.symm Q.y.point) =
            Q.y.map.node Q.y.point := by
        rw [Q.y_node_symm_point_eq_yOld_point hproperQ]
        rw [← hnodeTwo]
        exact Q.yOld_node_symm_node_node_point hproperQ
      rw [hdoubleInvY, hkyPoint, hsecondFresh, hkyNode]
      rw [← hfaceQ, hthirdOld]
      simpa [P, faceEdge] using hpointOldFaceNe
  let kh : Q.h.map.Dart → Color :=
    Hypermap.extensionNColor Q.y.map Q.y.point ky
  have hkh : Q.h.map.Coloring kh :=
    Hypermap.extensionNColor_coloring hky
      (Q.y_longRingHead_of_proper hproperQ) hnFreshH
  have hcycleHQ : cpRingCycle (CpStep.h :: cpc) := by
    by_cases hsizeQ : 2 < CProg.ringSize cpc
    · exact cpRingCycle_h hcycleQ hproperQ
        (ringCycle_longRingHead_of_two_lt hcycleQ hsizeQ) hsizeQ
    · have htwoQ : CProg.ringSize cpc = 2 := by omega
      exact cpRingCycle_h_of_ringSize_eq_two hcycleQ hproperQ htwoQ
  refine ⟨kh, hkh, hcycleHQ, ?_⟩
  have hringHQ :
      cpRing (CpStep.h :: cpc) =
        Q.h.map.node Q.h.point :: Q.h.point ::
          ((cpRing cpc).drop 2).map Q.hOld := by
    by_cases hsizeQ : 2 < CProg.ringSize cpc
    · simpa [Q] using cpRing_h_eq_of_ringCycle
        (cp := cpc) hcycleQ hproperQ
        (ringCycle_longRingHead_of_two_lt hcycleQ hsizeQ) hsizeQ
    · have htwoQ : CProg.ringSize cpc = 2 := by omega
      have hdropQ : (cpRing cpc).drop 2 = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [length_cpRing, htwoQ]
      have hdropHQ : (cpRing (CpStep.h :: cpc)).drop 2 = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [List.length_drop, length_cpRing]
        change CProg.ringSize cpc - 2 = 0
        omega
      have hheadHQ :=
        cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
          (cp := CpStep.h :: cpc) (by simpa [CProg.ringSize] using honeQ)
      rw [hdropHQ] at hheadHQ
      rw [hdropQ]
      simpa [Q] using hheadHQ
  have hboundaryTail :
      Q.map.colorsOn k' ((cpRing cpc).drop 2) =
        P.map.colorsOn (k ∘ P.hOld)
          (CfMask.select (mr.map Bool.not) ((cpRing cp).drop 2)) := by
    rw [hringQ, hringP] at hboundary
    simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
      CfMask.select, if_true] at hboundary
    exact (List.cons.inj (List.cons.inj hboundary).2).2
  have hkhNode : kh (Q.h.map.node Q.h.point) =
      k' (Q.map.node Q.point) := by
    have hlongY :
        (Hypermap.extensionY Q.map Q.point).LongRingHead ExtDart.new :=
      Hypermap.extensionY_long_new_of_proper
        (G := Q.map) Q.point hproperQ
    change Hypermap.extensionNColor Q.y.map Q.y.point ky
      ((Hypermap.extensionH Q.map Q.point).node ExtDart.new) = _
    unfold Hypermap.extensionH Hypermap.extensionN
    rw [Hypermap.ExtensionN.node_new,
      if_pos hlongY]
    exact hkyNode
  have hkhPoint : kh Q.h.point = ku ExtDart.new := by rfl
  have hkhOld (x : Q.map.Dart) : kh (Q.hOld x) = k' x := by rfl
  have hcolorsH :
      Q.h.map.colorsOn kh (cpRing (CpStep.h :: cpc)) =
        k' (Q.map.node Q.point) :: ku ExtDart.new ::
          Q.map.colorsOn k' ((cpRing cpc).drop 2) := by
    rw [hringHQ]
    unfold Hypermap.colorsOn
    simp only [List.map_cons, hkhNode, hkhPoint]
    apply congrArg (List.cons (k' (Q.map.node Q.point)))
    apply congrArg (List.cons (ku ExtDart.new))
    induction (cpRing cpc).drop 2 with
    | nil => rfl
    | cons x xs ih =>
        change kh (Q.hOld x) :: List.map kh (xs.map Q.hOld) =
          k' x :: List.map k' xs
        exact congrArg₂ List.cons (hkhOld x) ih
  change Q.h.map.colorsOn kh (cpRing (CpStep.h :: cpc)) =
    P.h.map.colorsOn k
      (CfMask.select ((false :: false :: mr).map Bool.not)
        (cpRing (CpStep.h :: cp)))
  rw [hcolorsH, hboundaryTail, hringH]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    CfMask.select, if_true]
  exact congrArg₂ List.cons hheadFresh
    (congrArg₂ List.cons hsecondFresh
      (map_comp_select_eq_select_map k P.hOld (mr.map Bool.not)
        ((cpRing cp).drop 2)))

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
