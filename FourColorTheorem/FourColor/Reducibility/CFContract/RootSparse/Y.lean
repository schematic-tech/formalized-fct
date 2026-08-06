import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Helpers

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

theorem rootSparse_rotate
    {cp : CProg} {n : Nat} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : mr.length = CProg.ringSize cp)
    (h : RootSparse (cpmap cp)
      (cpSparseTail (CProg.rotateRight n mr) mc cp)) :
    RootSparse (cpmap (CpStep.rotate n :: cp))
      (cpSparseTail mr mc (CpStep.rotate n :: cp)) := by
  rw [cpSparseTail_rotate_eq hcfg hmr]
  change
    ((cpmap cp).rotate n).point ∉
        cpSparseTail (CProg.rotateRight n mr) mc cp ∧
      (cpmap cp).map.Sparse
        (insert ((cpmap cp).rotate n).point
          (cpSparseTail (CProg.rotateRight n mr) mc cp))
  exact Hypermap.rootSparse_replace h
    (permReachable_iteratePerm (cpmap cp).map.node
      ((cpmap cp).nodeOrder - n) (cpmap cp).point)

theorem yOld_node_point_not_onRing (P : PointedHypermap) :
    ¬ P.y.OnRing (P.yOld (P.map.node P.point)) := by
  intro h
  change PermReachable (Hypermap.extensionY P.map P.point).node
      ExtDart.new
      (Hypermap.extensionYOld P.map P.point (P.map.node P.point)) at h
  unfold Hypermap.extensionY Hypermap.extensionYOld at h
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := Hypermap.extensionU P.map P.point)
      (x0 := ExtDart.new) h
  have hface :
      (Hypermap.extensionU P.map P.point).face
          ((Hypermap.extensionU P.map P.point).edge ExtDart.new) =
        ExtDart.old (P.map.node P.point) := rfl
  simp [Hypermap.extensionNNodeOrbitCode,
    Hypermap.extensionU_long_new] at hcode
  exact hcode.1 hface.symm

theorem yOld_node_point_nodeReachable_implies
    (P : PointedHypermap) {y : P.map.Dart}
    (h : PermReachable P.y.map.node
      (P.yOld (P.map.node P.point)) (P.yOld y)) :
    y = P.map.node P.point := by
  change PermReachable
      (Hypermap.extensionN (Hypermap.extensionU P.map P.point)
        ExtDart.new).node
      (ExtDart.old (ExtDart.old (P.map.node P.point)))
      (ExtDart.old (ExtDart.old y)) at h
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := Hypermap.extensionU P.map P.point)
      (x0 := ExtDart.new) h
  have hface :
      (Hypermap.extensionU P.map P.point).face
          ((Hypermap.extensionU P.map P.point).edge ExtDart.new) =
        ExtDart.old (P.map.node P.point) := rfl
  simp [Hypermap.extensionNNodeOrbitCode,
    Hypermap.extensionU_long_new, hface] at hcode
  exact ExtDart.old_injective hcode

theorem yOld_nodeReachable_iff_of_not_onRing
    {cp : CProg} {x y : (cpmap cp).map.Dart}
    (hx : ¬ (cpmap cp).OnRing x) :
    PermReachable (cpmap (CpStep.y :: cp)).map.node
      ((cpmap cp).yOld x) ((cpmap cp).yOld y) ↔
      PermReachable (cpmap cp).map.node x y := by
  simpa [CProg.appendRev, injcp, cpmap, oldStep, step] using
    (injcp_nodeReachable_iff_of_cubic_of_not_onRing
      [CpStep.y] cp (by rfl) hx)

theorem rootSparse_y_lift
    {cp : CProg} {p : Finset (cpmap cp).map.Dart}
    (hcfg : CProg.config cp = true)
    (h : RootSparse (cpmap cp) p) :
    RootSparse (cpmap (CpStep.y :: cp))
      (insert ((cpmap cp).yOld ((cpmap cp).map.node (cpmap cp).point))
        (p.image (cpmap cp).yOld)) := by
  let P := cpmap cp
  change RootSparse P p at h
  change RootSparse P.y
    (insert (P.yOld (P.map.node P.point)) (p.image P.yOld))
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
  have haNotRing :
      ¬ P.y.OnRing (P.yOld (P.map.node P.point)) :=
    yOld_node_point_not_onRing P
  have himageNotRing :
      ∀ {z : P.y.map.Dart}, z ∈ p.image P.yOld → ¬ P.y.OnRing z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact yOld_not_onRing_of_not_onRing P (hoff hx)
  have htailNotRing :
      ∀ {z : P.y.map.Dart},
        z ∈ insert (P.yOld (P.map.node P.point)) (p.image P.yOld) →
          ¬ P.y.OnRing z := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact haNotRing
    · exact himageNotRing hz
  have hrootNot :
      P.y.point ∉ insert (P.yOld (P.map.node P.point))
        (p.image P.yOld) := by
    intro hx
    exact htailNotRing hx (by simpa [hx] using onRing_point P.y)
  refine ⟨hrootNot, ?_⟩
  intro x y hx hy hxy
  rw [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exact (htailNotRing hy hxy).elim
  · rcases hy with rfl | hy
    · exact (htailNotRing hx
        (PermReachable.symm P.y.map.node hxy)).elim
    · rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
          have hzEq := yOld_node_point_nodeReachable_implies P hxy
          exact (hnodeNot (hzEq ▸ hz)).elim
      · rcases hy with rfl | hy
        · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
          have hzEq := yOld_node_point_nodeReachable_implies P
            (PermReachable.symm P.y.map.node hxy)
          exact (hnodeNot (hzEq ▸ hz)).elim
        · rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
          have hzw : PermReachable P.map.node z w :=
            (yOld_nodeReachable_iff_of_not_onRing (cp := cp)
              (x := z) (y := w) (hoff hz)).mp hxy
          exact congrArg P.yOld
            (h.2 (Finset.mem_insert_of_mem hz)
              (Finset.mem_insert_of_mem hw) hzw)

theorem cpSparseTail_y_eq
    {s : CpStep} {cp : CProg} (b1 b2 b3 : Bool)
    (mr mc : List Bool)
    (hcfg : CProg.config (s :: cp) = true) :
    cpSparseTail (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp) =
      (if b1 then {(cpmap (CpStep.y :: s :: cp)).map.edge
          ((cpmap (CpStep.y :: s :: cp)).map.node
            (cpmap (CpStep.y :: s :: cp)).point)} else ∅) ∪
      (if b2 then {(cpmap (CpStep.y :: s :: cp)).map.edge
          (cpmap (CpStep.y :: s :: cp)).point} else ∅) ∪
      (if b3 then {((cpmap (s :: cp)).yOld
          ((cpmap (s :: cp)).map.node (cpmap (s :: cp)).point))} else ∅) ∪
      (cpSparseTail (b3 :: mr) mc (s :: cp)).image
        (cpmap (s :: cp)).yOld := by
  let P := cpmap (s :: cp)
  change cpSparseTail (b1 :: b2 :: mr) (b3 :: mc)
      (CpStep.y :: s :: cp) =
    (if b1 then {P.y.map.edge (P.y.map.node P.y.point)} else ∅) ∪
    (if b2 then {P.y.map.edge P.y.point} else ∅) ∪
    (if b3 then {P.yOld (P.map.node P.point)} else ∅) ∪
    (cpSparseTail (b3 :: mr) mc (s :: cp)).image P.yOld
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
  have hringTail :
      (CfMask.select mr (((cpRing (s :: cp)).drop 1).map P.yOld)).toFinset.image
          P.y.map.edge =
        ((CfMask.select mr ((cpRing (s :: cp)).drop 1)).toFinset.image
          P.map.edge).image P.yOld := by
    rw [CfMask.toFinset_select_map]
    exact Hypermap.image_edge_image_of_edge_commute
      P.yOld P.yOld_edge _
  have hcontractFalse :
      P.y.map.contractClosure
          (CfMask.select (false :: mc)
            ((P.map.node P.point :: cpContractDarts (s :: cp)).map
              P.yOld)).toFinset =
        (P.map.contractClosure
          (CfMask.select mc (cpContractDarts (s :: cp))).toFinset).image
            P.yOld := by
    rw [CfMask.toFinset_select_map]
    simp only [CfMask.select]
    exact Hypermap.contractClosure_image_of_edge_commute
      P.yOld P.yOld_edge _
  have hcontractTrue :
      P.y.map.contractClosure
          (CfMask.select (true :: mc)
            ((P.map.node P.point :: cpContractDarts (s :: cp)).map
              P.yOld)).toFinset =
        insert (P.yOld (P.map.node P.point))
          (insert (P.y.map.edge (P.yOld (P.map.node P.point)))
            ((P.map.contractClosure
              (CfMask.select mc (cpContractDarts (s :: cp))).toFinset).image
                P.yOld)) := by
    rw [CfMask.toFinset_select_map]
    simp only [CfMask.select]
    simp only [if_true, List.toFinset_cons, Finset.image_insert]
    rw [Hypermap.contractClosure, Finset.image_insert,
      Hypermap.image_edge_image_of_edge_commute P.yOld P.yOld_edge,
      Hypermap.contractClosure, Finset.image_union]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  unfold cpSparseTail
  rw [hring, cpContractDarts_y_cons, holdRing]
  change
    (CfMask.select (b1 :: b2 :: mr)
      (P.y.map.node P.y.point :: P.y.point ::
        ((cpRing (s :: cp)).drop 1).map P.yOld)).toFinset.image
          P.y.map.edge ∪
      P.y.map.contractClosure
        (CfMask.select (b3 :: mc)
          ((P.map.node P.point :: cpContractDarts (s :: cp)).map
            P.yOld)).toFinset =
    (if b1 then {P.y.map.edge (P.y.map.node P.y.point)} else ∅) ∪
    (if b2 then {P.y.map.edge P.y.point} else ∅) ∪
    (if b3 then {P.yOld (P.map.node P.point)} else ∅) ∪
    ((CfMask.select (b3 :: mr)
        (P.map.node P.point :: (cpRing (s :: cp)).drop 1)).toFinset.image
          P.map.edge ∪
      P.map.contractClosure
        (CfMask.select mc (cpContractDarts (s :: cp))).toFinset).image
          P.yOld
  cases b1 <;> cases b2 <;> cases b3
  all_goals simp only [CfMask.select, Bool.false_eq_true, if_false, if_true,
    List.toFinset_cons, Finset.image_insert, Finset.empty_union,
    Finset.union_empty]
  all_goals rw [hringTail]
  all_goals first | rw [hcontractFalse] | rw [hcontractTrue]
  all_goals simp only [Finset.image_union, Finset.image_insert]
  all_goals try rw [P.yOld_edge]
  all_goals ext x
  all_goals simp only [Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  all_goals tauto

theorem RootSparse.replaceRepresentative
    {P : PointedHypermap} {a b : P.map.Dart} {s : Finset P.map.Dart}
    (h : RootSparse P (insert a s))
    (ha : a ∉ s)
    (hab : PermReachable P.map.node a b) :
    RootSparse P (insert b s) := by
  have hpoint : P.point ≠ a ∧ P.point ∉ s := by
    simpa only [Finset.mem_insert, not_or] using h.1
  have haRoot : a ∉ insert P.point s := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hpoint.1, ha⟩
  have hsparse : P.map.Sparse (insert a (insert P.point s)) := by
    simpa only [Finset.insert_comm] using h.2
  have hr := Hypermap.rootSparse_replace ⟨haRoot, hsparse⟩ hab
  have hb : b ≠ P.point ∧ b ∉ s := by
    simpa only [Finset.mem_insert, not_or] using hr.1
  constructor
  · simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hb.1, hpoint.2⟩
  · simpa only [Finset.insert_comm] using hr.2

theorem extensionN_old_nodeReachable_of_regular_of_long
    {G : Hypermap} {x0 x y : G.Dart}
    (hlong : G.LongRingHead x0)
    (hx0 : x ≠ x0) (hxf : x ≠ G.face (G.edge x0))
    (hy0 : y ≠ x0) (hyf : y ≠ G.face (G.edge x0))
    (hxy : PermReachable G.node x y) :
    PermReachable (G.extensionN x0).node (ExtDart.old x) (ExtDart.old y) := by
  have horbit :
      PermOrbit.of (G.extensionN x0).node (ExtDart.old x) =
        PermOrbit.of (G.extensionN x0).node (ExtDart.old y) := by
    apply (Hypermap.extensionNNodeOrbitEquivOfLong
      (G := G) x0 hlong).injective
    change Hypermap.extensionNNodeOrbitCode G x0 (ExtDart.old x) =
      Hypermap.extensionNNodeOrbitCode G x0 (ExtDart.old y)
    simp only [Hypermap.extensionNNodeOrbitCode, if_pos hlong,
      if_neg hx0, if_neg hxf, if_neg hy0, if_neg hyf,
      Option.some.injEq]
    exact PermOrbit.of_eq_of G.node hxy
  exact Quotient.exact horbit

theorem RootSparse.replaceTwoRepresentatives
    {P : PointedHypermap} {a b a' b' : P.map.Dart}
    {s : Finset P.map.Dart}
    (h : RootSparse P (insert a (insert b s)))
    (ha : a ∉ insert b s) (hb : b ∉ s)
    (haa' : PermReachable P.map.node a a')
    (hbb' : PermReachable P.map.node b b') :
    RootSparse P (insert a' (insert b' s)) := by
  have hfirst : RootSparse P (insert a' (insert b s)) :=
    h.replaceRepresentative ha haa'
  have hba' : b ≠ a' := by
    intro hEq
    have hab : PermReachable P.map.node a b := by
      simpa [hEq] using haa'
    have habEq := h.sparse (by simp) (by simp) hab
    apply ha
    simp [habEq]
  have hb' : b ∉ insert a' s := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hba', hb⟩
  have hcomm : RootSparse P (insert b (insert a' s)) := by
    simpa only [Finset.insert_comm] using hfirst
  have hsecond : RootSparse P (insert b' (insert a' s)) :=
    hcomm.replaceRepresentative hb' hbb'
  simpa only [Finset.insert_comm] using hsecond

theorem y_q1_nodeReachable (P : PointedHypermap) :
    PermReachable P.y.map.node
      (P.y.map.edge (P.y.map.node P.y.point))
      (P.yOld (P.map.node P.point)) := by
  change PermReachable
    (Hypermap.extensionN (Hypermap.extensionU P.map P.point) ExtDart.new).node
    (ExtDart.old ExtDart.new)
    (ExtDart.old (ExtDart.old (P.map.node P.point)))
  exact Hypermap.extensionN_nodeReachable_old_x0_old_face_edge
    (G := Hypermap.extensionU P.map P.point) ExtDart.new

theorem y_q2_nodeReachable (P : PointedHypermap) :
    PermReachable P.y.map.node
      (P.y.map.edge P.y.point)
      (P.yOld (P.map.node P.point)) := by
  change PermReachable
    (Hypermap.extensionN (Hypermap.extensionU P.map P.point) ExtDart.new).node
    ExtDart.newEdge
    (ExtDart.old (ExtDart.old (P.map.node P.point)))
  exact Hypermap.extensionN_nodeReachable_newEdge_old_face_edge
    (G := Hypermap.extensionU P.map P.point) ExtDart.new

/-- The noninitial `Y` branch of Coq `sparse_cfctr`. -/
theorem rootSparse_y_step
    {s : CpStep} {cp : CProg} {mr mc : List Bool}
    (b1 b2 b3 : Bool)
    (hcfg : CProg.config (s :: cp) = true)
    (hnsp : CProg.nonSparse b1 b2 b3 = false)
    (h : RootSparse (cpmap (s :: cp))
      (cpSparseTail (b3 :: mr) mc (s :: cp))) :
    RootSparse (cpmap (CpStep.y :: s :: cp))
      (cpSparseTail (b1 :: b2 :: mr) (b3 :: mc)
        (CpStep.y :: s :: cp)) := by
  let P := cpmap (s :: cp)
  let p := cpSparseTail (b3 :: mr) mc (s :: cp)
  change RootSparse P p at h
  have hlift : RootSparse P.y
      (insert (P.yOld (P.map.node P.point)) (p.image P.yOld)) := by
    simpa [P, p] using rootSparse_y_lift hcfg h
  have hproper : P.ProperRingHead :=
    (cpmap_configGeometry_of_config hcfg).proper
  have hnodeNot : P.map.node P.point ∉ p := by
    intro hn
    have heq := h.2 (by simp) (Finset.mem_insert_of_mem hn)
      (PermReachable.forward P.map.node P.point)
    exact hproper heq
  have haNot : P.yOld (P.map.node P.point) ∉ p.image P.yOld := by
    intro ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, hEq⟩
    exact hnodeNot ((P.yOld_injective hEq).symm ▸ hx)
  have hq1 : RootSparse P.y
      (insert (P.y.map.edge (P.y.map.node P.y.point))
        (p.image P.yOld)) :=
    hlift.replaceRepresentative haNot
      (PermReachable.symm P.y.map.node (y_q1_nodeReachable P))
  have hq2 : RootSparse P.y
      (insert (P.y.map.edge P.y.point) (p.image P.yOld)) :=
    hlift.replaceRepresentative haNot
      (PermReachable.symm P.y.map.node (y_q2_nodeReachable P))
  rw [cpSparseTail_y_eq b1 b2 b3 mr mc hcfg]
  change RootSparse P.y
    ((if b1 then {P.y.map.edge (P.y.map.node P.y.point)} else ∅) ∪
    (if b2 then {P.y.map.edge P.y.point} else ∅) ∪
    (if b3 then {P.yOld (P.map.node P.point)} else ∅) ∪
    p.image P.yOld)
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [CProg.nonSparse] at hnsp ⊢
  · apply hlift.mono
    intro x hx
    exact Finset.mem_insert_of_mem hx
  · simpa [Finset.singleton_union] using hlift
  · simpa [Finset.singleton_union] using hq2
  · simpa [Finset.singleton_union] using hq1


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
