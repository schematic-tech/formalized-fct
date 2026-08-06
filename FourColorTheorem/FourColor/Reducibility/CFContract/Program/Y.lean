import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Initial

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

open CFContract.Internal

private theorem cpRings_y_of_config
    {s : CpStep} {cp : CProg} (hcfg : CProg.config (s :: cp) = true) :
    cpRing (s :: cp) =
        (cpmap (s :: cp)).map.node (cpmap (s :: cp)).point ::
          (cpRing (s :: cp)).drop 1 ∧
      cpRing (CpStep.y :: s :: cp) =
        (cpmap (s :: cp)).y.map.node (cpmap (s :: cp)).y.point ::
          (cpmap (s :: cp)).y.point ::
            ((cpRing (s :: cp)).drop 1).map (cpmap (s :: cp)).yOld := by
  have hgeom := cpmap_configGeometry_of_config hcfg
  exact ⟨cpRing_eq_nodePoint_cons_drop_one (s :: cp),
    cpRing_y_eq_of_ringCycle (cpRingCycle_of_config hcfg) hgeom.proper⟩

private theorem y_node_color_eq_old_node
    (P : PointedHypermap) {cc : Finset P.y.map.Dart}
    {k : P.y.map.Dart → Color}
    (hk : P.y.map.ContractColoring cc k) :
    k (P.y.map.node P.y.point) = k (P.yOld (P.map.node P.point)) := by
  apply Eq.symm
  apply Hypermap.ContractColoring.eq_of_face_reachable (G := P.y.map) hk
  exact (P.y_faceReachable_node_point_old_iff).2
    (PermReachable.refl P.map.face (P.map.node P.point))

private theorem y_old_new_not_contractClosure
    {s : CpStep} {cp : CProg} {mr mc : List Bool} (b3 : Bool)
    (hcfg : CProg.config (s :: cp) = true) :
    (ExtDart.old
        (ExtDart.new : (cpmap (s :: cp)).u.map.Dart) :
          (cpmap (s :: cp)).y.map.Dart) ∉
      (cpmap (s :: cp)).y.map.contractClosure
        (cpContractFinset (false :: false :: mr) (b3 :: mc)
          (CpStep.y :: s :: cp)) := by
  let P := cpmap (s :: cp)
  rw [cpContractFinset_y_eq false false b3 mr mc hcfg]
  simp only [Bool.false_eq_true, if_false, Finset.empty_union]
  rw [Hypermap.contractClosure_image_of_edge_commute P.yOld P.yOld_edge]
  intro hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
  change ExtDart.old (ExtDart.old x) =
    ExtDart.old (ExtDart.new : P.u.map.Dart) at hzx
  injection hzx with h
  cases h

private theorem y_node_point_color_ne
    (P : PointedHypermap) {cc : Finset P.y.map.Dart}
    {k : P.y.map.Dart → Color}
    (hk : P.y.map.ContractColoring cc k)
    (hznot :
      (ExtDart.old (ExtDart.new : P.u.map.Dart) : P.y.map.Dart) ∉
        P.y.map.contractClosure cc) :
    k (P.y.map.node P.y.point) ≠ k P.y.point := by
  let z : P.y.map.Dart := ExtDart.old (ExtDart.new : P.u.map.Dart)
  have hpointZ : PermReachable P.y.map.face P.y.point z := by
    exact Hypermap.extensionN_faceReachable_new_old_x0
      (G := Hypermap.extensionU P.map P.point) ExtDart.new
  have hzPoint := Hypermap.ContractColoring.eq_of_face_reachable
    (G := P.y.map) hk hpointZ
  have hedgeNe := Hypermap.ContractColoring.edge_ne
    (G := P.y.map) hk z (by simpa [z] using hznot)
  have hedgeZ : P.y.map.edge z = P.y.map.node P.y.point := by rfl
  rw [hedgeZ] at hedgeNe
  intro heq
  exact hedgeNe (heq.trans hzPoint.symm)

/-- Recursive `Y` case in which one of the two fresh boundary edges is
contracted and the executable output is the recursive program unchanged. -/
theorem contractProgramCorrect_y_cons_unchanged
    {s : CpStep} {cp cpc : CProg} {mr mc : List Bool}
    (b1 b2 b3 : Bool)
    (hcfg : CProg.config (s :: cp) = true)
    (hnsp : CProg.nonSparse b1 b2 b3 = false)
    (hb12 : b1 || b2 = true)
    (hrec : ContractProgramCorrect (b3 :: mr) mc (s :: cp) cpc) :
    ContractProgramCorrect (b1 :: b2 :: mr) (b3 :: mc)
      (CpStep.y :: s :: cp) cpc := by
  intro k hk
  let P := cpmap (s :: cp)
  have hkrec := contractColoring_pullback_y b1 b2 b3 mr mc hcfg hk
  rcases hrec (k ∘ P.yOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  refine ⟨k', hk', hcycleQ, ?_⟩
  rw [hboundary]
  have hgeom := cpmap_configGeometry_of_config hcfg
  obtain ⟨hringP, hringY⟩ := cpRings_y_of_config hcfg
  have hnodeOld := y_node_color_eq_old_node P hk
  cases b1 <;> cases b2 <;> cases b3
  all_goals simp [CProg.nonSparse] at hnsp hb12
  · rw [hringP, hringY]
    simp only [List.map_cons, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, CfMask.select, if_true, if_false, Hypermap.colorsOn,
      Function.comp_apply]
    exact congrArg₂ List.cons hnodeOld.symm
      (map_comp_select_eq_select_map k P.yOld (mr.map Bool.not)
        ((cpRing (s :: cp)).drop 1))
  · have hfirstSelected : P.y.map.node P.y.point ∈
        P.y.map.contractClosure
          (cpContractFinset (true :: false :: mr) (false :: mc)
            (CpStep.y :: s :: cp)) := by
      apply P.y.map.mem_contractClosure_self
      unfold cpContractFinset cpContractSelection
      apply List.mem_toFinset.mpr
      apply List.mem_append.mpr
      apply Or.inl
      rw [hringY]
      exact List.mem_cons_self
    let z : P.y.map.Dart := ExtDart.old (ExtDart.new : P.u.map.Dart)
    have hedgeZ : P.y.map.edge z = P.y.map.node P.y.point := by
      rfl
    have hzcontract : z ∈ P.y.map.contractClosure
        (cpContractFinset (true :: false :: mr) (false :: mc)
          (CpStep.y :: s :: cp)) := by
      apply (P.y.map.contractClosure_edge_mem_iff_of_plain
        (P.y_plain hgeom.plain)).1
      simpa [hedgeZ] using hfirstSelected
    have hpointZ :
        PermReachable P.y.map.face P.y.point z := by
      change PermReachable
        (Hypermap.extensionN (Hypermap.extensionU P.map P.point)
          ExtDart.new).face ExtDart.new (ExtDart.old ExtDart.new)
      exact Hypermap.extensionN_faceReachable_new_old_x0
        (G := Hypermap.extensionU P.map P.point) ExtDart.new
    have hpointNode :
        k P.y.point = k (P.y.map.node P.y.point) := by
      have hzPoint :=
        Hypermap.ContractColoring.eq_of_face_reachable (G := P.y.map) hk hpointZ
      have hedgeColor :=
        Hypermap.ContractColoring.edge_eq (G := P.y.map) hk z hzcontract
      rw [hedgeZ] at hedgeColor
      exact hzPoint.symm.trans hedgeColor.symm
    rw [hringP, hringY]
    simp only [List.map_cons, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, CfMask.select, if_true, if_false, Hypermap.colorsOn,
      Function.comp_apply]
    exact congrArg₂ List.cons (hpointNode.trans hnodeOld).symm
      (map_comp_select_eq_select_map k P.yOld (mr.map Bool.not)
        ((cpRing (s :: cp)).drop 1))

/-- Recursive `Y` case `001`: the old ring head is contracted and the two
fresh surviving boundary colors are realized by a `U` extension. -/
theorem contractProgramCorrect_y_cons_u
    {s : CpStep} {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config (s :: cp) = true)
    (hrec : ContractProgramCorrect (true :: mr) mc (s :: cp) cpc) :
    ContractProgramCorrect (false :: false :: mr) (true :: mc)
      (CpStep.y :: s :: cp) (CpStep.u :: cpc) := by
  intro k hk
  let P := cpmap (s :: cp)
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_y false false true mr mc hcfg hk
  rcases hrec (k ∘ P.yOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  obtain ⟨hringP, hringY⟩ := cpRings_y_of_config hcfg
  have hnodeOld := y_node_color_eq_old_node P hk
  have hheadFresh :
      k' (Q.map.node Q.point) = k (P.y.map.node P.y.point) := by
    exact hhead.trans hnodeOld.symm
  have hfreshNe := y_node_point_color_ne P hk (by
    simpa [P] using y_old_new_not_contractClosure
      (s := s) (cp := cp) (mr := mr) (mc := mc) true hcfg)
  let e := k (P.y.map.node P.y.point) + k P.y.point
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
  rw [hcolorsU, hboundary, hringP, hringY]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    CfMask.select, if_true]
  simp only [Bool.not_true]
  have hsecond : e + k' (Q.map.node Q.point) = k P.y.point := by
    simpa [e] using color_add_add_eq_right hheadFresh
  exact congrArg₂ List.cons hheadFresh
    (congrArg₂ List.cons hsecond
      (map_comp_select_eq_select_map k P.yOld (mr.map Bool.not)
        ((cpRing (s :: cp)).drop 1)))

/-- Recursive `Y` case `000`: both fresh boundary colors survive, and the
recursive coloring extends through the canonical `U`-then-`N` construction. -/
theorem contractProgramCorrect_y_cons_y
    {s : CpStep} {cp cpc : CProg} {mr mc : List Bool}
    (hcfg : CProg.config (s :: cp) = true)
    (hrec : ContractProgramCorrect (false :: mr) mc (s :: cp) cpc) :
    ContractProgramCorrect (false :: false :: mr) (false :: mc)
      (CpStep.y :: s :: cp) (CpStep.y :: cpc) := by
  intro k hk
  let P := cpmap (s :: cp)
  let Q := cpmap cpc
  have hkrec := contractColoring_pullback_y false false false mr mc hcfg hk
  rcases hrec (k ∘ P.yOld) (by simpa [P] using hkrec) with
    ⟨k', hk', hcycleQ, hboundary⟩
  have hproperQ : Q.ProperRingHead := by
    simpa [Q, PointedHypermap.ProperRingHead] using
      hk'.properRingHead Q.point
  have hsizeQ : 1 < CProg.ringSize cpc :=
    hcycleQ.one_lt_of_properRingHead hproperQ
  have hhead := contractProgramCorrect_ringHead_eq
    (by simpa [P] using hkrec) hboundary
  have hsecondOld := contractProgramCorrect_ringSecond_eq hcfg hcycleQ hproperQ
    (by simpa [P] using hkrec) hboundary
  have hgeomP := cpmap_configGeometry_of_config hcfg
  have hringYP :
      cpRing (CpStep.y :: s :: cp) =
        P.y.map.node P.y.point :: P.y.point ::
          ((cpRing (s :: cp)).drop 1).map P.yOld := by
    simpa [P] using cpRing_y_eq_of_ringCycle
      (cp := s :: cp) (cpRingCycle_of_config hcfg) hgeomP.proper
  have hringP :
      cpRing (s :: cp) =
        P.map.node P.point :: (cpRing (s :: cp)).drop 1 := by
    simpa [P] using cpRing_eq_nodePoint_cons_drop_one (s :: cp)
  have hringQ :
      cpRing cpc = Q.map.node Q.point :: (cpRing cpc).drop 1 := by
    simpa [Q] using cpRing_eq_nodePoint_cons_drop_one cpc
  have hnodeOld :
      k (P.y.map.node P.y.point) =
        k (P.yOld (P.map.node P.point)) := by
    apply Eq.symm
    apply Hypermap.ContractColoring.eq_of_face_reachable (G := P.y.map) hk
    exact (P.y_faceReachable_node_point_old_iff).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have hheadFresh :
      k' (Q.map.node Q.point) = k (P.y.map.node P.y.point) :=
    hhead.trans hnodeOld.symm
  have hpointNot : P.y.point ∉ P.y.map.contractClosure
      (cpContractFinset (false :: false :: mr) (false :: mc)
        (CpStep.y :: s :: cp)) := by
    rw [cpContractFinset_y_eq false false false mr mc hcfg]
    simp only [Bool.false_eq_true, if_false, Finset.empty_union]
    rw [Hypermap.contractClosure_image_of_edge_commute P.yOld P.yOld_edge]
    intro hp
    rcases Finset.mem_image.mp hp with ⟨x, _hx, hxp⟩
    change ExtDart.old (ExtDart.old x) = ExtDart.new at hxp
    cases hxp
  have hpointOldNe : k P.y.point ≠ k (P.yOld P.point) := by
    have hedgeNe := Hypermap.ContractColoring.edge_ne
      (G := P.y.map) hk P.y.point hpointNot
    have hface := Hypermap.ContractColoring.face_eq
      (G := P.y.map) hk (P.y.map.edge P.y.point)
    rw [P.y_face_edge_point_eq_yOld_point hgeomP.proper] at hface
    intro heq
    exact hedgeNe (hface.symm.trans heq.symm)
  have hfreshNe := y_node_point_color_ne P hk (by
    simpa [P] using y_old_new_not_contractClosure
      (s := s) (cp := cp) (mr := mr) (mc := mc) false hcfg)
  let e := k (P.y.map.node P.y.point) + k P.y.point
  have he : e ≠ Color.zero := by
    simpa [e] using color_add_ne_zero_of_ne hfreshNe
  let ku : Q.u.map.Dart → Color :=
    Hypermap.extensionUColor Q.map Q.point k' e
  have hku : Q.u.map.Coloring ku :=
    Hypermap.extensionUColor_coloring hk' he
  have hsecondFresh : ku ExtDart.new = k P.y.point := by
    simpa [ku, e] using extensionUColor_new_eq_right Q k' hheadFresh
  have hdoubleInv :
      Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new) = Q.uOld Q.point := by
    exact extensionU_node_symm_sq_new_eq_old_point Q hproperQ
  have hnFresh :
      ku ExtDart.new ≠
        ku (Q.u.map.node.symm (Q.u.map.node.symm ExtDart.new)) := by
    rw [hdoubleInv, hsecondFresh]
    change k P.y.point ≠ k' Q.point
    rw [hsecondOld]
    exact hpointOldNe
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
        P.map.colorsOn (k ∘ P.yOld)
          (CfMask.select (mr.map Bool.not) ((cpRing (s :: cp)).drop 1)) := by
    rw [hringQ, hringP] at hboundary
    simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
      CfMask.select, if_true] at hboundary
    exact (List.cons.inj hboundary).2
  have hkyNode : ky (Q.y.map.node Q.y.point) =
      k' (Q.map.node Q.point) := by
    change Hypermap.extensionNColor
        (Hypermap.extensionU Q.map Q.point) ExtDart.new ku
          ((Hypermap.extensionY Q.map Q.point).node ExtDart.new) = _
    rw [Hypermap.extensionY_node_new]
    rfl
  have hkyPoint : ky Q.y.point = ku ExtDart.new := by
    rfl
  have hkyOld (x : Q.map.Dart) : ky (Q.yOld x) = k' x := by
    rfl
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
    P.y.map.colorsOn k
      (CfMask.select ((false :: false :: mr).map Bool.not)
        (cpRing (CpStep.y :: s :: cp)))
  rw [hcolorsY, hboundaryTail, hringYP]
  simp only [Hypermap.colorsOn, List.map_cons, Bool.not_false,
    CfMask.select, if_true]
  exact congrArg₂ List.cons hheadFresh
    (congrArg₂ List.cons hsecondFresh
      (map_comp_select_eq_select_map k P.yOld (mr.map Bool.not)
        ((cpRing (s :: cp)).drop 1)))

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
