import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.NoDup

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

theorem rootSparse_of_subset_opposite_ring_of_card_le_one
    {cp : CProg} {s : Finset (cpmap cp).map.Dart}
    (hcfg : CProg.config cp = true)
    (hsub : s ⊆ (cpRing cp).toFinset.image (cpmap cp).map.edge)
    (hcard : s.card ≤ 1) :
    RootSparse (cpmap cp) s := by
  let P := cpmap cp
  have hcycle := cpRingCycle_of_config hcfg
  have hsize : 0 < CProg.ringSize cp := by
    have := CProg.ringSize_gt_two_of_config hcfg
    omega
  have hpoint : P.point ∈ cpRing cp := by
    simpa [P, cpRing] using
      hcycle.mem_ringDarts_of_onRing hsize (onRing_point P)
  have hringNodup :
      (P.map.insertEdges (cpRing cp)).Nodup := by
    have hfull := nodup_insertEdges_cpRing_contractDarts hcfg
    rw [Hypermap.insertEdges_append] at hfull
    exact hfull.of_append_left
  have hdisjoint :
      (cpRing cp).Disjoint ((cpRing cp).map P.map.edge) :=
    P.map.disjoint_self_map_edge_of_nodup_insertEdges hringNodup
  have hnotOrbit :
      ∀ {y : P.map.Dart}, y ∈ s →
        ¬ PermReachable P.map.node P.point y := by
    intro y hy hreach
    have hyRing : y ∈ cpRing cp := by
      exact hcycle.mem_ringDarts_of_onRing hsize hreach
    rcases Finset.mem_image.mp (hsub hy) with ⟨x, hx, rfl⟩
    have hxList : x ∈ cpRing cp := List.mem_toFinset.mp hx
    exact hdisjoint hyRing (List.mem_map.mpr ⟨x, hxList, rfl⟩)
  have hpointNot : P.point ∉ s := by
    intro hp
    exact hnotOrbit hp (PermReachable.refl P.map.node P.point)
  refine ⟨hpointNot, ?_⟩
  intro x y hx hy hxy
  rw [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exact (hnotOrbit hy hxy).elim
  · rcases hy with rfl | hy
    · exact (hnotOrbit hx (PermReachable.symm P.map.node hxy)).elim
    · exact Finset.card_le_one_iff.mp hcard hx hy

theorem rootSparse_contractProgram_y_nil
    {mr mc : List Bool} {cpc : CProg}
    (hmr : mr.length = CProg.ringSize [CpStep.y])
    (hmc : mc.length = CProg.contractEdgeSize [CpStep.y])
    (hrun : CProg.contractProgram mr mc [CpStep.y] = some cpc) :
    RootSparse (cpmap [CpStep.y])
      (cpSparseTail mr mc [CpStep.y]) := by
  have hcount : CfMask.countTrue mr ≤ 1 := by
    have hmr3 : mr.length = 3 := by
      simpa [CProg.ringSize] using hmr
    rcases List.length_eq_three.mp hmr3 with ⟨b1, b2, b3, hmrEq⟩
    subst mr
    have hmc0 : mc.length = 0 := by
      simpa [CProg.contractEdgeSize] using hmc
    have hmcnil := List.eq_nil_of_length_eq_zero hmc0
    subst mc
    cases b1 <;> cases b2 <;> cases b3 <;>
      simp [CProg.contractProgram, CProg.nonSparse,
        CfMask.countTrue] at hrun ⊢
  apply rootSparse_of_subset_opposite_ring_of_card_le_one (by rfl)
  · intro x hx
    unfold cpSparseTail at hx
    rw [cpContractDarts_y_nil] at hx
    simp only [CfMask.select, List.toFinset_nil,
      (cpmap [CpStep.y]).map.contractClosure_empty,
      Finset.union_empty] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y,
      List.mem_toFinset.mpr (CfMask.mem_of_mem_select
        (List.mem_toFinset.mp hy)), rfl⟩
  · unfold cpSparseTail
    rw [cpContractDarts_y_nil]
    simp only [CfMask.select, List.toFinset_nil,
      (cpmap [CpStep.y]).map.contractClosure_empty,
      Finset.union_empty]
    calc
      ((CfMask.select mr (cpRing [CpStep.y])).toFinset.image
          (cpmap [CpStep.y]).map.edge).card ≤
          (CfMask.select mr (cpRing [CpStep.y])).toFinset.card :=
        Finset.card_image_le
      _ ≤ (CfMask.select mr (cpRing [CpStep.y])).length :=
        List.toFinset_card_le _
      _ = CfMask.countTrue mr := by
        exact CfMask.length_select_eq_countTrue_of_length mr
          (cpRing [CpStep.y]) (by
            rw [length_cpRing]
            simpa [CProg.ringSize] using hmr.symm)
      _ ≤ 1 := hcount


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
