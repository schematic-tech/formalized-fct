import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Y

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

theorem hOld_point_not_onRing
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    ¬ P.h.OnRing (P.hOld P.point) := by
  intro h
  change PermReachable
      (Hypermap.extensionN (Hypermap.extensionY P.map P.point)
        ExtDart.new).node
      ExtDart.new
      (ExtDart.old (P.yOld P.point)) at h
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := P.y.map) (x0 := P.y.point) h
  have hlong : P.y.LongRingHead :=
    P.y_longRingHead_of_proper hproper
  change P.y.map.LongRingHead P.y.point at hlong
  have hface :
      P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point :=
    P.y_face_edge_point_eq_yOld_point hproper
  have hne : P.yOld P.point ≠ P.y.point := P.yOld_ne_point P.point
  simp only [Hypermap.extensionNNodeOrbitCode] at hcode
  rw [if_pos hlong, if_pos hlong, if_neg hne,
    if_pos hface.symm] at hcode
  cases hcode

theorem hOld_node_point_nodeReachable_implies
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    {z : P.map.Dart}
    (h : PermReachable P.h.map.node
      (P.hOld (P.map.node P.point)) (P.hOld z)) :
    z = P.map.node P.point := by
  change PermReachable
      (Hypermap.extensionN (Hypermap.extensionY P.map P.point)
        ExtDart.new).node
      (ExtDart.old (P.yOld (P.map.node P.point)))
      (ExtDart.old (P.yOld z)) at h
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := P.y.map) (x0 := P.y.point) h
  have hlong : P.y.map.LongRingHead P.y.point :=
    P.y_longRingHead_of_proper hproper
  have hface :
      P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point :=
    P.y_face_edge_point_eq_yOld_point hproper
  have hsourcePoint : P.yOld (P.map.node P.point) ≠ P.y.point :=
    P.yOld_ne_point (P.map.node P.point)
  have hsourceFace :
      P.yOld (P.map.node P.point) ≠
        P.y.map.face (P.y.map.edge P.y.point) := by
    rw [hface]
    intro hEq
    have hold := P.yOld_injective hEq
    exact hproper hold.symm
  by_cases hz : z = P.point
  · subst z
    have htargetPoint : P.yOld P.point ≠ P.y.point :=
      P.yOld_ne_point P.point
    simp only [Hypermap.extensionNNodeOrbitCode] at hcode
    rw [if_pos hlong, if_neg hsourcePoint, if_neg hsourceFace,
      if_pos hlong, if_neg htargetPoint, if_pos hface.symm] at hcode
    cases hcode
  · have htargetPoint : P.yOld z ≠ P.y.point := P.yOld_ne_point z
    have htargetFace :
        P.yOld z ≠ P.y.map.face (P.y.map.edge P.y.point) := by
      rw [hface]
      intro hEq
      exact hz (P.yOld_injective hEq)
    simp only [Hypermap.extensionNNodeOrbitCode] at hcode
    rw [if_pos hlong, if_neg hsourcePoint, if_neg hsourceFace,
      if_pos hlong, if_neg htargetPoint, if_neg htargetFace] at hcode
    have horbit :
        PermOrbit.of P.y.map.node (P.yOld (P.map.node P.point)) =
          PermOrbit.of P.y.map.node (P.yOld z) := by
      exact Option.some.inj hcode
    exact yOld_node_point_nodeReachable_implies P (Quotient.exact horbit)

theorem hOld_point_nodeReachable_implies
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    {z : P.map.Dart}
    (h : PermReachable P.h.map.node (P.hOld P.point) (P.hOld z)) :
    z = P.point := by
  by_contra hz
  change PermReachable
      (Hypermap.extensionN (Hypermap.extensionY P.map P.point)
        ExtDart.new).node
      (ExtDart.old (P.yOld P.point))
      (ExtDart.old (P.yOld z)) at h
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := P.y.map) (x0 := P.y.point) h
  have hlong : P.y.map.LongRingHead P.y.point :=
    P.y_longRingHead_of_proper hproper
  have hface :
      P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point :=
    P.y_face_edge_point_eq_yOld_point hproper
  have hsourcePoint : P.yOld P.point ≠ P.y.point :=
    P.yOld_ne_point P.point
  have htargetPoint : P.yOld z ≠ P.y.point := P.yOld_ne_point z
  have htargetFace :
      P.yOld z ≠ P.y.map.face (P.y.map.edge P.y.point) := by
    rw [hface]
    intro hEq
    exact hz (P.yOld_injective hEq)
  simp only [Hypermap.extensionNNodeOrbitCode] at hcode
  rw [if_pos hlong, if_neg hsourcePoint, if_pos hface.symm,
    if_pos hlong, if_neg htargetPoint, if_neg htargetFace] at hcode
  cases hcode

theorem hOld_nodeReachable_iff_of_not_onRing
    {cp : CProg} {x y : (cpmap cp).map.Dart}
    (hx : ¬ (cpmap cp).OnRing x) :
    PermReachable (cpmap (CpStep.h :: cp)).map.node
      ((cpmap cp).hOld x) ((cpmap cp).hOld y) ↔
      PermReachable (cpmap cp).map.node x y := by
  simpa [CProg.appendRev, injcp, cpmap, oldStep, step] using
    (injcp_nodeReachable_iff_of_cubic_of_not_onRing
      [CpStep.h] cp (by rfl) hx)

theorem rootSparse_h_lift
    {cp : CProg} {p : Finset (cpmap cp).map.Dart}
    (hcfg : CProg.config cp = true)
    (h : RootSparse (cpmap cp) p) :
    RootSparse (cpmap (CpStep.h :: cp))
      (insert ((cpmap cp).hOld ((cpmap cp).map.node (cpmap cp).point))
        (insert ((cpmap cp).hOld (cpmap cp).point)
          (p.image (cpmap cp).hOld))) := by
  let P := cpmap cp
  change RootSparse P p at h
  change RootSparse P.h
    (insert (P.hOld (P.map.node P.point))
      (insert (P.hOld P.point) (p.image P.hOld)))
  have hproper : P.ProperRingHead :=
    (cpmap_configGeometry_of_config hcfg).proper
  have hoff : ∀ {x : P.map.Dart}, x ∈ p → ¬ P.OnRing x := by
    intro x hx hpx
    have heq := h.2 (by simp) (Finset.mem_insert_of_mem hx) hpx
    subst x
    exact h.1 hx
  have hnodeNot : P.map.node P.point ∉ p := by
    intro hn
    have heq := h.2 (by simp) (Finset.mem_insert_of_mem hn)
      (PermReachable.forward P.map.node P.point)
    exact hproper heq
  have hyOff : ¬ P.h.OnRing (P.hOld (P.map.node P.point)) := by
    intro hy
    exact yOld_node_point_not_onRing P
      (P.hOld_onRing_implies_yOld_onRing hy)
  have hxOff : ¬ P.h.OnRing (P.hOld P.point) :=
    hOld_point_not_onRing P hproper
  have himageOff :
      ∀ {z : P.h.map.Dart}, z ∈ p.image P.hOld → ¬ P.h.OnRing z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact P.hOld_not_onRing_of_not_onRing (hoff hx)
  have htailOff :
      ∀ {z : P.h.map.Dart},
        z ∈ insert (P.hOld (P.map.node P.point))
            (insert (P.hOld P.point) (p.image P.hOld)) →
          ¬ P.h.OnRing z := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hyOff
    · rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hxOff
      · exact himageOff hz
  constructor
  · intro hz
    exact htailOff hz (PermReachable.refl P.h.map.node P.h.point)
  · intro x y hx hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · exact (htailOff hy hxy).elim
    · rcases hy with rfl | hy
      · exact (htailOff hx
          (PermReachable.symm P.h.map.node hxy)).elim
      · rw [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · rfl
          · rw [Finset.mem_insert] at hy
            rcases hy with rfl | hy
            · have heq :=
                hOld_node_point_nodeReachable_implies P hproper hxy
              exact (hproper heq).elim
            · rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
              have heq :=
                hOld_node_point_nodeReachable_implies P hproper hxy
              exact (hnodeNot (heq ▸ hz)).elim
        · rcases hy with rfl | hy
          · rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · have heq := hOld_node_point_nodeReachable_implies
                P hproper (PermReachable.symm P.h.map.node hxy)
              exact (hproper heq).elim
            · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
              have heq := hOld_node_point_nodeReachable_implies
                P hproper (PermReachable.symm P.h.map.node hxy)
              exact (hnodeNot (heq ▸ hz)).elim
          · rw [Finset.mem_insert] at hx hy
            rcases hx with rfl | hx
            · rcases hy with rfl | hy
              · rfl
              · rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
                have heq := hOld_point_nodeReachable_implies P hproper hxy
                exact (h.1 (heq ▸ hz)).elim
            · rcases hy with rfl | hy
              · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
                have heq := hOld_point_nodeReachable_implies P hproper
                  (PermReachable.symm P.h.map.node hxy)
                exact (h.1 (heq ▸ hz)).elim
              · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
                rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
                have hzw : PermReachable P.map.node z w :=
                  (hOld_nodeReachable_iff_of_not_onRing
                    (cp := cp) (x := z) (y := w) (hoff hz)).mp hxy
                exact congrArg P.hOld
                  (h.2 (Finset.mem_insert_of_mem hz)
                    (Finset.mem_insert_of_mem hw) hzw)

theorem h_xRing_nodeReachable
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    PermReachable P.h.map.node (P.h.map.edge P.h.point)
      (P.hOld P.point) := by
  change PermReachable
      (Hypermap.extensionN P.y.map P.y.point).node
      ExtDart.newEdge (ExtDart.old (P.yOld P.point))
  have h := Hypermap.extensionN_nodeReachable_newEdge_old_face_edge
    (G := P.y.map) P.y.point
  rw [P.y_face_edge_point_eq_yOld_point hproper] at h
  exact h

theorem h_xCrossbar_nodeReachable
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    PermReachable P.h.map.node (P.h.map.face P.h.point)
      (P.hOld P.point) := by
  change PermReachable
      (Hypermap.extensionN P.y.map P.y.point).node
      (ExtDart.old P.y.point) (ExtDart.old (P.yOld P.point))
  have h := Hypermap.extensionN_nodeReachable_old_x0_old_face_edge
    (G := P.y.map) P.y.point
  rw [P.y_face_edge_point_eq_yOld_point hproper] at h
  exact h

theorem h_yRing_nodeReachable
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    PermReachable P.h.map.node
      (P.h.map.edge (P.h.map.node P.h.point))
      (P.hOld (P.map.node P.point)) := by
  have hlongY : P.y.map.LongRingHead P.y.point :=
    P.y_longRingHead_of_proper hproper
  have hsource :
      P.h.map.edge (P.h.map.node P.h.point) =
        (ExtDart.old (ExtDart.old P.u.point) : P.h.map.Dart) := by
    change ExtDart.Perm.edge P.y.map.edge
        (Hypermap.ExtensionN.node P.y.map P.y.point ExtDart.new) =
      ExtDart.old (ExtDart.old P.u.point)
    rw [Hypermap.ExtensionN.node_new, if_pos hlongY]
    have hyNode : P.y.map.node P.y.point =
        (ExtDart.old ExtDart.newEdge : P.y.map.Dart) :=
      Hypermap.extensionY_node_new (G := P.map) P.point
    rw [hyNode]
    rfl
  rw [hsource]
  have hUFace :
      P.u.map.face (P.u.map.edge P.u.point) =
        P.uOld (P.map.node P.point) := by
    rw [Hypermap.face_edge_eq_node_symm]
    rfl
  have hinner :
      PermReachable P.y.map.node (ExtDart.old P.u.point)
        (P.yOld (P.map.node P.point)) := by
    have h := Hypermap.extensionN_nodeReachable_old_x0_old_face_edge
      (G := P.u.map) P.u.point
    rw [hUFace] at h
    exact h
  have hface :
      P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point :=
    P.y_face_edge_point_eq_yOld_point hproper
  apply extensionN_old_nodeReachable_of_regular_of_long hlongY
  · intro h
    cases h
  · rw [hface]
    intro h
    cases h
  · exact P.yOld_ne_point (P.map.node P.point)
  · rw [hface]
    intro h
    exact hproper (P.yOld_injective h).symm
  · exact hinner

theorem h_yCrossbar_nodeReachable
    (P : PointedHypermap) (hproper : P.ProperRingHead) :
    PermReachable P.h.map.node
      (P.h.map.edge (P.h.map.face P.h.point))
      (P.hOld (P.map.node P.point)) := by
  have hlongY : P.y.map.LongRingHead P.y.point :=
    P.y_longRingHead_of_proper hproper
  have hsource :
      P.h.map.edge (P.h.map.face P.h.point) =
        (ExtDart.old ExtDart.newEdge : P.h.map.Dart) := by
    change ExtDart.Perm.edge P.y.map.edge (ExtDart.old P.y.point) =
      ExtDart.old ExtDart.newEdge
    rfl
  rw [hsource]
  have hUFace :
      P.u.map.face (P.u.map.edge P.u.point) =
        P.uOld (P.map.node P.point) := by
    rw [Hypermap.face_edge_eq_node_symm]
    rfl
  have hinner :
      PermReachable P.y.map.node ExtDart.newEdge
        (P.yOld (P.map.node P.point)) := by
    have h := Hypermap.extensionN_nodeReachable_newEdge_old_face_edge
      (G := P.u.map) P.u.point
    rw [hUFace] at h
    exact h
  have hface :
      P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point :=
    P.y_face_edge_point_eq_yOld_point hproper
  apply extensionN_old_nodeReachable_of_regular_of_long hlongY
  · intro h
    cases h
  · rw [hface]
    intro h
    cases h
  · exact P.yOld_ne_point (P.map.node P.point)
  · rw [hface]
    intro h
    exact hproper (P.yOld_injective h).symm
  · exact hinner

set_option maxHeartbeats 2000000 in
theorem cpSparseTail_h_eq
    {cp : CProg} (b1 b2 b3 b4 b5 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config cp = true) :
    cpSparseTail (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp) =
      (if b1 then {(cpmap (CpStep.h :: cp)).map.edge
          ((cpmap (CpStep.h :: cp)).map.node
            (cpmap (CpStep.h :: cp)).point)} else ∅) ∪
      (if b2 then {(cpmap (CpStep.h :: cp)).map.edge
          (cpmap (CpStep.h :: cp)).point} else ∅) ∪
      (if b3 then
        {(cpmap (CpStep.h :: cp)).map.face
            (cpmap (CpStep.h :: cp)).point,
          (cpmap (CpStep.h :: cp)).map.edge
            ((cpmap (CpStep.h :: cp)).map.face
              (cpmap (CpStep.h :: cp)).point)} else ∅) ∪
      (if b4 then {((cpmap cp).hOld
          ((cpmap cp).map.node (cpmap cp).point))} else ∅) ∪
      (if b5 then {((cpmap cp).hOld (cpmap cp).point)} else ∅) ∪
      (cpSparseTail (b4 :: b5 :: mr) mc cp).image
        (cpmap cp).hOld := by
  let P := cpmap cp
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
      cpRing cp = P.map.node P.point :: P.point :: (cpRing cp).drop 2 := by
    simpa [P] using
      cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
        (cp := cp) hsize
  have hOldEdgeMix (x : P.map.Dart) :
      (cpmap cp).h.map.edge (P.hOld x) = P.hOld (P.map.edge x) := by
    exact P.hOld_edge x
  have hOldEdgeFun :
      (cpmap cp).h.map.edge ∘ P.hOld = P.hOld ∘ P.map.edge := by
    funext x
    exact hOldEdgeMix x
  have hOldEdgeImage (s : Finset P.map.Dart) :
      s.image ((cpmap cp).h.map.edge ∘ P.hOld) =
        s.image (P.hOld ∘ P.map.edge) := by
    rw [hOldEdgeFun]
  have holdRingSelected :
      (CfMask.select (b4 :: b5 :: mr) (cpRing cp)).toFinset.image
          P.map.edge =
        (if b4 then {P.map.edge (P.map.node P.point)} else ∅) ∪
        (if b5 then {P.map.edge P.point} else ∅) ∪
        (CfMask.select mr ((cpRing cp).drop 2)).toFinset.image
          P.map.edge := by
    rw [holdRing]
    cases b4 <;> cases b5 <;>
      simp [CfMask.select]
  change cpSparseTail (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
      (CpStep.h :: cp) =
    (if b1 then {P.h.map.edge (P.h.map.node P.h.point)} else ∅) ∪
    (if b2 then {P.h.map.edge P.h.point} else ∅) ∪
    (if b3 then {P.h.map.face P.h.point,
      P.h.map.edge (P.h.map.face P.h.point)} else ∅) ∪
    (if b4 then {P.hOld (P.map.node P.point)} else ∅) ∪
    (if b5 then {P.hOld P.point} else ∅) ∪
    (cpSparseTail (b4 :: b5 :: mr) mc cp).image P.hOld
  dsimp only [P] at *
  unfold cpSparseTail
  change
    ((CfMask.select (b1 :: b2 :: mr) (cpRing (CpStep.h :: cp))).toFinset.image
        (cpmap cp).h.map.edge) ∪
      (cpmap cp).h.map.contractClosure
        (CfMask.select (b3 :: b4 :: b5 :: mc)
          (cpContractDarts (CpStep.h :: cp))).toFinset = _
  rw [hring, cpContractDarts_h, holdRingSelected]
  simp only [cpmap_cons, step]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5
  all_goals simp only [CfMask.select, Bool.false_eq_true, if_false, if_true,
    List.toFinset_cons, Finset.image_insert, Finset.empty_union,
    Finset.union_empty]
  all_goals rw [CfMask.toFinset_select_map]
  all_goals rw [Finset.image_image]
  all_goals rw [CfMask.toFinset_select_map]
  all_goals simp only [CfMask.select, eq_self, if_true]
  all_goals simp only [Hypermap.contractClosure, Finset.image_union,
    Finset.image_insert, Finset.image_singleton, Finset.image_image]
  all_goals simp only [Bool.false_eq_true, if_false,
    List.toFinset_cons, Finset.image_insert]
  all_goals simp only [hOldEdgeImage]
  all_goals ext x
  all_goals try simp_rw [Finset.mem_union]
  all_goals try simp_rw [Finset.mem_insert]
  all_goals try simp_rw [Finset.mem_singleton]
  all_goals tauto

set_option maxHeartbeats 1000000 in
theorem rootSparse_h_step
    {cp : CProg} {mr mc : List Bool}
    (b1 b2 b3 b4 b5 : Bool)
    (hcfg : CProg.config cp = true)
    (hnspY : CProg.nonSparse b3 b1 b4 = false)
    (hnspX : CProg.nonSparse b3 b2 b5 = false)
    (h : RootSparse (cpmap cp)
      (cpSparseTail (b4 :: b5 :: mr) mc cp)) :
    RootSparse (cpmap (CpStep.h :: cp))
      (cpSparseTail (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc)
        (CpStep.h :: cp)) := by
  let P := cpmap cp
  let p := cpSparseTail (b4 :: b5 :: mr) mc cp
  change RootSparse P p at h
  have hlift : RootSparse P.h
      (insert (P.hOld (P.map.node P.point))
        (insert (P.hOld P.point) (p.image P.hOld))) := by
    simpa [P, p] using rootSparse_h_lift hcfg h
  have hproper : P.ProperRingHead :=
    (cpmap_configGeometry_of_config hcfg).proper
  have hnodeNot : P.map.node P.point ∉ p := by
    intro hn
    have heq := h.2 (by simp) (Finset.mem_insert_of_mem hn)
      (PermReachable.forward P.map.node P.point)
    exact hproper heq
  have hxNot : P.hOld P.point ∉ p.image P.hOld := by
    intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, hEq⟩
    exact h.1 ((P.hOld_injective hEq) ▸ hz)
  have hyImageNot :
      P.hOld (P.map.node P.point) ∉ p.image P.hOld := by
    intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, hEq⟩
    exact hnodeNot ((P.hOld_injective hEq) ▸ hz)
  have hyx : P.hOld (P.map.node P.point) ≠ P.hOld P.point := by
    intro hEq
    exact hproper (P.hOld_injective hEq).symm
  have hyNot :
      P.hOld (P.map.node P.point) ∉
        insert (P.hOld P.point) (p.image P.hOld) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hyx, hyImageNot⟩
  have hpair {qx qy : P.h.map.Dart}
      (hqx : PermReachable P.h.map.node qx (P.hOld P.point))
      (hqy : PermReachable P.h.map.node qy
        (P.hOld (P.map.node P.point))) :
      RootSparse P.h (insert qy (insert qx (p.image P.hOld))) := by
    exact hlift.replaceTwoRepresentatives hyNot hxNot
      (PermReachable.symm P.h.map.node hqy)
      (PermReachable.symm P.h.map.node hqx)
  have hxonly {qx : P.h.map.Dart}
      (hqx : PermReachable P.h.map.node qx (P.hOld P.point)) :
      RootSparse P.h (insert qx (p.image P.hOld)) := by
    exact (hpair hqx
      (PermReachable.refl P.h.map.node
        (P.hOld (P.map.node P.point)))).mono
      (Finset.subset_insert _ _)
  have hyonly {qy : P.h.map.Dart}
      (hqy : PermReachable P.h.map.node qy
        (P.hOld (P.map.node P.point))) :
      RootSparse P.h (insert qy (p.image P.hOld)) := by
    apply (hpair
      (PermReachable.refl P.h.map.node (P.hOld P.point)) hqy).mono
    intro z hz
    rw [Finset.mem_insert] at hz ⊢
    exact hz.elim Or.inl (fun hs => Or.inr (Finset.mem_insert_of_mem hs))
  have hnone : RootSparse P.h (p.image P.hOld) := by
    apply hlift.mono
    intro z hz
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  have hxRing := h_xRing_nodeReachable P hproper
  have hxCross := h_xCrossbar_nodeReachable P hproper
  have hyRing := h_yRing_nodeReachable P hproper
  have hyCross := h_yCrossbar_nodeReachable P hproper
  rw [cpSparseTail_h_eq b1 b2 b3 b4 b5 mr mc hcfg]
  change RootSparse P.h
    ((if b1 then {P.h.map.edge (P.h.map.node P.h.point)} else ∅) ∪
    (if b2 then {P.h.map.edge P.h.point} else ∅) ∪
    (if b3 then {P.h.map.face P.h.point,
      P.h.map.edge (P.h.map.face P.h.point)} else ∅) ∪
    (if b4 then {P.hOld (P.map.node P.point)} else ∅) ∪
    (if b5 then {P.hOld P.point} else ∅) ∪
    p.image P.hOld)
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp [CProg.nonSparse] at hnspY hnspX
  all_goals simp only [Bool.false_eq_true, if_false, if_true,
    Finset.empty_union, Finset.union_empty, Finset.singleton_union,
    Finset.insert_union] at ⊢
  next => exact hnone
  next => exact hxonly (PermReachable.refl P.h.map.node (P.hOld P.point))
  next => exact hyonly (PermReachable.refl P.h.map.node
      (P.hOld (P.map.node P.point)))
  next => exact (hpair
      (PermReachable.refl P.h.map.node (P.hOld P.point))
      (PermReachable.refl P.h.map.node (P.hOld (P.map.node P.point))))
  next => simpa only [Finset.insert_comm] using (hpair hxCross hyCross)
  next => exact hxonly hxRing
  next => simpa only [Finset.insert_comm] using (hpair hxRing
      (PermReachable.refl P.h.map.node (P.hOld (P.map.node P.point))))
  next => exact hyonly hyRing
  next => simpa only [Finset.insert_comm] using (hpair
      (PermReachable.refl P.h.map.node (P.hOld P.point)) hyRing)
  next => simpa only [Finset.insert_comm] using (hpair hxRing hyRing)

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
