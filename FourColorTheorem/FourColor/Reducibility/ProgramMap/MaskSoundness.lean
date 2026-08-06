import FourColorTheorem.FourColor.Reducibility.ProgramMap.Mask

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpMaskAdjSound_yOld_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hsize : 1 < CProg.ringSize cp)
    {b0 b1 b2 : Bool} {mr ks : List Bool}
    {a0 a2 : Bool} {mr' ks' : List Bool}
    (hsound : cpMaskAdjSound cp (⟨b0 :: b2 :: mr, ks⟩ : CfMask))
    (hinner :
      CfMask.adjMask (⟨b0 :: b2 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a2 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).y).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
            (CpStep.y :: cp))
          (CpStep.y :: cp))
        ((cpmap cp).yOld x) ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x) y := by
  rw [cpMaskAdjSound_yOld_faceBand_rewrite_of_ringCycle
    hcycle hproper hinner]
  rw [cpMaskAdjSound_yOld_exists_rewrite_of_ringCycle
    hcycle hproper b0 b1 b2 mr ks]
  rw [y_faceReachable_node_point_old_iff]
  have hnotPoint :
      ¬ PermReachable
        (Hypermap.extensionY (cpmap cp).map (cpmap cp).point).face
        ExtDart.new ((cpmap cp).yOld x) := by
    change ¬ PermReachable ((cpmap cp).y).map.face
      ((cpmap cp).y).point ((cpmap cp).yOld x)
    exact y_not_faceReachable_point_old (cpmap cp) x
  have hnodeAdj :
      (Hypermap.extensionY (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).yOld x)
          ((Hypermap.extensionY (cpmap cp).map (cpmap cp).point).node
            ExtDart.new) ↔
        (cpmap cp).map.RingAdj x
          ((cpmap cp).map.node (cpmap cp).point) := by
    change ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x)
        (((cpmap cp).y).map.node ((cpmap cp).y).point) ↔
      (cpmap cp).map.RingAdj x
        ((cpmap cp).map.node (cpmap cp).point)
    exact yOld_ringAdj_node_point_iff (cpmap cp)
  have hpointAdj :
      (Hypermap.extensionY (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).yOld x) ExtDart.new ↔
        PermReachable (cpmap cp).map.face
          ((cpmap cp).map.node (cpmap cp).point) x ∨
          PermReachable (cpmap cp).map.face (cpmap cp).point x := by
    rw [← Hypermap.FaceBand.pair]
    change ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x)
        ((cpmap cp).y).point ↔
      (cpmap cp).map.FaceBand
        [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point] x
    exact yOld_ringAdj_point_iff_faceBand_coq_of_plain (cpmap cp) hplainY
  rw [selectMask_cpRing_drop_one_eq_of_ringSize_gt_one
    (cp := cp) hsize (a2 || b1) mr' ks']
  rw [Hypermap.FaceBand.optional_prefix]
  rw [selectMask_cpRing_drop_one_eq_of_ringSize_gt_one
    (cp := cp) hsize b2 mr ks]
  rw [Hypermap.RingAdj.exists_mem_optional_prefix]
  have htail :=
    cpMaskAdjSound_cons_cons_rewrite_of_inner
      (cp := cp) (b0 := b0) (b1 := b2) (mr := mr) (ks := ks)
      (a0 := a0) (a1 := a2) (mr' := mr') (ks' := ks')
      hsize hsound hinner (x := x)
  simpa [Bool.or_eq_true, hnotPoint, or_assoc] using
    (cpMaskAdjSound_yOld_bool
      (a0 := a0) (a2 := a2) (b0 := b0) (b1 := b1) (b2 := b2)
      (N := PermReachable (cpmap cp).map.face
        ((cpmap cp).map.node (cpmap cp).point) x)
      (P := PermReachable (cpmap cp).map.face (cpmap cp).point x)
      (T := (cpmap cp).map.FaceBand
        (CfMask.selectMask (⟨mr', ks'⟩ : CfMask)
          ((cpRing cp).drop 2) (cpKernel cp)) x)
      (RN := (cpmap cp).map.RingAdj x
        ((cpmap cp).map.node (cpmap cp).point))
      (RP := (cpmap cp).map.RingAdj x (cpmap cp).point)
      (E := ∃ y : (cpmap cp).map.Dart,
        y ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
          ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.RingAdj x y)
      (RNY :=
        (Hypermap.extensionY (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).yOld x)
          ((Hypermap.extensionY (cpmap cp).map (cpmap cp).point).node
            ExtDart.new))
      (RPY :=
        (Hypermap.extensionY (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).yOld x) ExtDart.new)
      hnodeAdj hpointAdj htail)

theorem cpMaskAdjSound_hOld_faceBand_rewrite_of_ringCycle_cons
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 a2 : Bool} {mr' ks' : List Bool}
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ((a0 || b1) = true ∧
          PermReachable ((cpmap cp).h).map.face
            (((cpmap cp).h).map.node ((cpmap cp).h).point)
            ((cpmap cp).hOld x)) ∨
        ((b0 || b1' || mr.headD b0) = true ∧
          PermReachable ((cpmap cp).h).map.face
            ((cpmap cp).h).point ((cpmap cp).hOld x)) ∨
          (cpmap cp).map.FaceBand
            (CfMask.selectMask
              (⟨(a2 || b1) :: mr', (a1 || b1) :: ks'⟩ : CfMask)
              ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp)) x := by
  rw [CfMask.adjMask_h_eq_of_inner_cons hinner]
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize
    (a0 || b1) (b0 || b1' || mr.headD b0) (a1 || b1)
    ((a2 || b1) :: mr') ks']
  exact hOld_faceBand_two_prefixes_map_iff (cpmap cp)
    (a0 || b1) (b0 || b1' || mr.headD b0)
    (((cpmap cp).h).map.node ((cpmap cp).h).point)
    ((cpmap cp).h).point
    (CfMask.selectMask
      (⟨(a2 || b1) :: mr', (a1 || b1) :: ks'⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_hOld_faceBand_rewrite_of_ringCycle_nil
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 : Bool} {ks' : List Bool}
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨[a0, a1], ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ((a0 || b1) = true ∧
          PermReachable ((cpmap cp).h).map.face
            (((cpmap cp).h).map.node ((cpmap cp).h).point)
            ((cpmap cp).hOld x)) ∨
        ((b0 || b1' || mr.headD b0) = true ∧
          PermReachable ((cpmap cp).h).map.face
            ((cpmap cp).h).point ((cpmap cp).hOld x)) ∨
          (cpmap cp).map.FaceBand
            (CfMask.selectMask
              (⟨[], (a1 || b1) :: ks'⟩ : CfMask)
              ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp)) x := by
  rw [CfMask.adjMask_h_eq_of_inner_nil hinner]
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize
    (a0 || b1) (b0 || b1' || mr.headD b0) (a1 || b1)
    [] ks']
  exact hOld_faceBand_two_prefixes_map_iff (cpmap cp)
    (a0 || b1) (b0 || b1' || mr.headD b0)
    (((cpmap cp).h).map.node ((cpmap cp).h).point)
    ((cpmap cp).h).point
    (CfMask.selectMask
      (⟨[], (a1 || b1) :: ks'⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_hOld_exists_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b1' : Bool) (mr ks : List Bool)
    {x : (cpmap cp).map.Dart} :
    (∃ y : ((cpmap cp).h).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
        ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x) y) ↔
      (b0 = true ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x)
            (((cpmap cp).h).map.node ((cpmap cp).h).point)) ∨
        (b1 = true ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x)
            ((cpmap cp).h).point) ∨
          ∃ y : (cpmap cp).map.Dart,
            y ∈ CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
              ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) ∧
              (cpmap cp).map.RingAdj x y := by
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize b0 b1 b1' mr ks]
  exact hOld_exists_two_prefixes_map_ringAdj_iff (cpmap cp)
    b0 b1
    (((cpmap cp).h).map.node ((cpmap cp).h).point)
    ((cpmap cp).h).point
    (CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_h_point_faceBand_rewrite_of_ringCycle_cons
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 a2 : Bool} {mr' ks' : List Bool}
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩) :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).h).point ↔
      (b0 || b1' || mr.headD b0) = true := by
  rw [CfMask.adjMask_h_eq_of_inner_cons hinner]
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize
    (a0 || b1) (b0 || b1' || mr.headD b0) (a1 || b1)
    ((a2 || b1) :: mr') ks']
  exact h_faceBand_two_prefixes_map_point_iff (cpmap cp) hproper
    (a0 || b1) (b0 || b1' || mr.headD b0)
    (CfMask.selectMask
      (⟨(a2 || b1) :: mr', (a1 || b1) :: ks'⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_h_point_faceBand_rewrite_of_ringCycle_nil
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 : Bool} {ks' : List Bool}
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨[a0, a1], ks'⟩) :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).h).point ↔
      (b0 || b1' || mr.headD b0) = true := by
  rw [CfMask.adjMask_h_eq_of_inner_nil hinner]
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize
    (a0 || b1) (b0 || b1' || mr.headD b0) (a1 || b1)
    [] ks']
  exact h_faceBand_two_prefixes_map_point_iff (cpmap cp) hproper
    (a0 || b1) (b0 || b1' || mr.headD b0)
    (CfMask.selectMask
      (⟨[], (a1 || b1) :: ks'⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_h_point_exists_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b1' : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).h).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
        ((cpmap cp).h).map.RingAdj ((cpmap cp).h).point y) ↔
      b0 = true ∨
        (b1 = true ∧
          ((cpmap cp).h).map.RingAdj
            ((cpmap cp).h).point ((cpmap cp).h).point) ∨
          ∃ x : (cpmap cp).map.Dart,
            x ∈ CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
              ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) ∧
              (cpmap cp).map.FaceBand
                [(cpmap cp).map.face
                    ((cpmap cp).map.edge (cpmap cp).point),
                  (cpmap cp).point,
                  (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize b0 b1 b1' mr ks]
  exact h_exists_two_prefixes_map_ringAdj_point_iff
    (cpmap cp) hproper hlong b0 b1
    (CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

theorem cpMaskAdjSound_h_point_exists_rewrite_of_ringCycle_bridgeless
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b1' : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).h).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
        ((cpmap cp).h).map.RingAdj ((cpmap cp).h).point y) ↔
      b0 = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
            ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) ∧
            (cpmap cp).map.FaceBand
              [(cpmap cp).map.face
                  ((cpmap cp).map.edge (cpmap cp).point),
                (cpmap cp).point,
                (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMaskAdjSound_h_point_exists_rewrite_of_ringCycle
    hcycle hproper hlong hsize b0 b1 b1' mr ks]
  have hself :
      ¬ ((cpmap cp).h).map.RingAdj
        ((cpmap cp).h).point ((cpmap cp).h).point :=
    Hypermap.Bridgeless.not_ringAdj_self
      (G := ((cpmap cp).h).map) hbridgeH ((cpmap cp).h).point
  tauto

theorem cpMask_h_tail_faceBand_triple_exists_split_of_ringSize_gt_two
    {cp : CProg}
    (hsize : 2 < CProg.ringSize cp)
    (b2 b1' : Bool) (mr ks : List Bool) :
    (∃ x : (cpmap cp).map.Dart,
      x ∈ CfMask.selectMask (⟨b2 :: mr, b1' :: ks⟩ : CfMask)
        ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) ∧
        (cpmap cp).map.FaceBand
          [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
            (cpmap cp).point,
            (cpmap cp).map.node (cpmap cp).point] x) ↔
      b2 = true ∨ b1' = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
    (cp := cp) hsize]
  rw [CfMask.selectMask_cons_ring_cons_kernel]
  cases b2 with
  | false =>
      cases b1' with
      | false => simp [CfMask.selectMask]
      | true =>
          constructor
          · intro _h
            exact Or.inr (Or.inl rfl)
          · intro _h
            refine ⟨(cpmap cp).point, ?_, ?_⟩
            · simp
            · exact (Hypermap.FaceBand.triple (G := (cpmap cp).map)).2
                (Or.inr (Or.inl (PermReachable.refl (cpmap cp).map.face
                  (cpmap cp).point)))
  | true =>
      constructor
      · intro _h
        exact Or.inl rfl
      · intro _h
        refine ⟨(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
          ?_, ?_⟩
        · simp
        · exact (Hypermap.FaceBand.triple (G := (cpmap cp).map)).2
            (Or.inl (PermReachable.refl (cpmap cp).map.face
              ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))))

theorem cpMaskAdjSound_h_point_exists_split_of_ringCycle_bridgeless
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b2 b1' : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).h).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
        ((cpmap cp).h).map.RingAdj ((cpmap cp).h).point y) ↔
      b0 = true ∨ b2 = true ∨ b1' = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMaskAdjSound_h_point_exists_rewrite_of_ringCycle_bridgeless
    hcycle hproper hlong hbridgeH hsize b0 b1 b1' (b2 :: mr) ks]
  rw [cpMask_h_tail_faceBand_triple_exists_split_of_ringSize_gt_two
    (cp := cp) hsize b2 b1' mr ks]

theorem cpMask_h_tail_faceBand_split_of_ringSize_gt_two
    {cp : CProg}
    (hsize : 2 < CProg.ringSize cp)
    (a2 a1 b1 : Bool) (mr' ks' : List Bool)
    {x : (cpmap cp).map.Dart} :
    (cpmap cp).map.FaceBand
        (CfMask.selectMask
          (⟨(a2 || b1) :: mr', (a1 || b1) :: ks'⟩ : CfMask)
          ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp)) x ↔
      ((a2 || b1) = true ∧
          PermReachable (cpmap cp).map.face
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
            x) ∨
        ((a1 || b1) = true ∧
          PermReachable (cpmap cp).map.face (cpmap cp).point x) ∨
          (cpmap cp).map.FaceBand
            (CfMask.selectMask (⟨mr', ks'⟩ : CfMask)
              ((cpRing cp).drop 3) (cpKernel cp)) x := by
  rw [cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
    (cp := cp) hsize]
  rw [CfMask.selectMask_cons_ring_cons_kernel]
  simp only [List.append_assoc]
  rw [Hypermap.FaceBand.optional_prefix]
  rw [← List.append_assoc]
  rw [Hypermap.FaceBand.optional_middle]
  rw [CfMask.selectMask, Hypermap.FaceBand.append]
  tauto

theorem cpMask_tail_faceBand_split_of_ringSize_gt_two
    {cp : CProg}
    (hsize : 2 < CProg.ringSize cp)
    (a2 : Bool) (mr' ks' : List Bool)
    {x : (cpmap cp).map.Dart} :
    (cpmap cp).map.FaceBand
        (CfMask.selectMask (⟨a2 :: mr', ks'⟩ : CfMask)
          ((cpRing cp).drop 2) (cpKernel cp)) x ↔
      (a2 = true ∧
          PermReachable (cpmap cp).map.face
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
            x) ∨
        (cpmap cp).map.FaceBand
          (CfMask.selectMask (⟨mr', ks'⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp)) x := by
  rw [cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
    (cp := cp) hsize]
  rw [CfMask.selectMask_cons_ring]
  rw [Hypermap.FaceBand.optional_prefix]

theorem cpMask_h_tail_exists_ringAdj_split
    {cp : CProg}
    (b1' : Bool) (mr ks : List Bool)
    {x : (cpmap cp).map.Dart} :
    (∃ y : (cpmap cp).map.Dart,
      y ∈ CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
        ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) ∧
        (cpmap cp).map.RingAdj x y) ↔
      (b1' = true ∧ (cpmap cp).map.RingAdj x (cpmap cp).point) ∨
        ∃ y : (cpmap cp).map.Dart,
          y ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.RingAdj x y := by
  rw [CfMask.selectMask_cons_kernel]
  rw [Hypermap.RingAdj.exists_mem_optional_middle]
  constructor
  · rintro (hRing | hPoint | hKernel)
    · rcases hRing with ⟨y, hy, hxy⟩
      exact Or.inr ⟨y, by simp [CfMask.selectMask, hy], hxy⟩
    · exact Or.inl hPoint
    · rcases hKernel with ⟨y, hy, hxy⟩
      exact Or.inr ⟨y, by simp [CfMask.selectMask, hy], hxy⟩
  · rintro (hPoint | hTail)
    · exact Or.inr (Or.inl hPoint)
    · rcases hTail with ⟨y, hy, hxy⟩
      simp [CfMask.selectMask] at hy
      rcases hy with hy | hy
      · exact Or.inl ⟨y, hy, hxy⟩
      · exact Or.inr (Or.inr ⟨y, hy, hxy⟩)

theorem cpMaskAdjSound_hOld_bool
    (a0 a1 a2 b0 b1 b1' : Bool)
    {N P F T RN RP E RNH RPH : Prop}
    (hRNH : RNH ↔ RN)
    (hRPH : RPH ↔ N ∨ P ∨ F)
    (htail :
      ((a0 = true ∧ N) ∨
          (a1 = true ∧ P) ∨
            (a2 = true ∧ F) ∨ T) ↔
        (b0 = true ∧ RN) ∨ (b1' = true ∧ RP) ∨ E) :
    (((a0 = true ∨ b1 = true) ∧ N) ∨
        ((a2 = true ∨ b1 = true) ∧ F) ∨
          ((a1 = true ∨ b1 = true) ∧ P) ∨ T) ↔
      (b0 = true ∧ RNH) ∨
        (b1 = true ∧ RPH) ∨
          (b1' = true ∧ RP) ∨ E := by
  have tailToNew :
      ((b0 = true ∧ RN) ∨ (b1' = true ∧ RP) ∨ E) →
        (b0 = true ∧ RNH) ∨
          (b1 = true ∧ RPH) ∨
            (b1' = true ∧ RP) ∨ E := by
    intro h
    rcases h with h0 | htail'
    · exact Or.inl ⟨h0.1, hRNH.2 h0.2⟩
    · rcases htail' with h1' | hE
      · exact Or.inr (Or.inr (Or.inl h1'))
      · exact Or.inr (Or.inr (Or.inr hE))
  have tailToOld :
      ((a0 = true ∧ N) ∨
          (a1 = true ∧ P) ∨
            (a2 = true ∧ F) ∨ T) →
        (((a0 = true ∨ b1 = true) ∧ N) ∨
          ((a2 = true ∨ b1 = true) ∧ F) ∨
            ((a1 = true ∨ b1 = true) ∧ P) ∨ T) := by
    intro h
    rcases h with h0 | htail'
    · exact Or.inl ⟨Or.inl h0.1, h0.2⟩
    · rcases htail' with h1 | htail''
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inl h1.1, h1.2⟩))
      · rcases htail'' with h2 | hT
        · exact Or.inr (Or.inl ⟨Or.inl h2.1, h2.2⟩)
        · exact Or.inr (Or.inr (Or.inr hT))
  constructor
  · intro h
    rcases h with h0 | htail'
    · rcases h0 with ⟨h0, hN⟩
      rcases h0 with h0 | h1
      · exact tailToNew (htail.1 (Or.inl ⟨h0, hN⟩))
      · exact Or.inr (Or.inl ⟨h1, hRPH.2 (Or.inl hN)⟩)
    · rcases htail' with h2 | htail''
      · rcases h2 with ⟨h2, hF⟩
        rcases h2 with h2 | h1
        · exact tailToNew
            (htail.1 (Or.inr (Or.inr (Or.inl ⟨h2, hF⟩))))
        · exact Or.inr (Or.inl ⟨h1, hRPH.2 (Or.inr (Or.inr hF))⟩)
      · rcases htail'' with h1P | hT
        · rcases h1P with ⟨h1P, hP⟩
          rcases h1P with h1P | h1
          · exact tailToNew
              (htail.1 (Or.inr (Or.inl ⟨h1P, hP⟩)))
          · exact Or.inr (Or.inl ⟨h1, hRPH.2 (Or.inr (Or.inl hP))⟩)
        · exact tailToNew (htail.1 (Or.inr (Or.inr (Or.inr hT))))
  · intro h
    rcases h with h0 | htail'
    · exact tailToOld (htail.2 (Or.inl ⟨h0.1, hRNH.1 h0.2⟩))
    · rcases htail' with h1 | htail''
      · rcases h1 with ⟨h1, hRPH'⟩
        rcases hRPH.1 hRPH' with hN | hPF
        · exact Or.inl ⟨Or.inr h1, hN⟩
        · rcases hPF with hP | hF
          · exact Or.inr (Or.inr (Or.inl ⟨Or.inr h1, hP⟩))
          · exact Or.inr (Or.inl ⟨Or.inr h1, hF⟩)
      · rcases htail'' with h1' | hE
        · exact tailToOld (htail.2 (Or.inr (Or.inl h1')))
        · exact tailToOld (htail.2 (Or.inr (Or.inr hE)))

theorem cpMaskAdjSound_hOld_of_ringCycle_cons
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 a2 : Bool} {mr' ks' : List Bool}
    (hsound : cpMaskAdjSound cp (⟨b0 :: b1' :: mr, ks⟩ : CfMask))
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x) y := by
  rw [cpMaskAdjSound_hOld_faceBand_rewrite_of_ringCycle_cons
    hcycle hproper hlong hsize hinner]
  rw [cpMaskAdjSound_hOld_exists_rewrite_of_ringCycle
    hcycle hproper hlong hsize b0 b1 b1' mr ks]
  rw [h_faceReachable_node_point_old_iff (cpmap cp) hproper]
  have hnotPoint :
      ¬ PermReachable
        (Hypermap.extensionH (cpmap cp).map (cpmap cp).point).face
        ExtDart.new ((cpmap cp).hOld x) := by
    change ¬ PermReachable ((cpmap cp).h).map.face
      ((cpmap cp).h).point ((cpmap cp).hOld x)
    exact h_not_faceReachable_point_old (cpmap cp) x
  have hnodeAdj :
      (Hypermap.extensionH (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).hOld x)
          ((Hypermap.extensionH (cpmap cp).map (cpmap cp).point).node
            ExtDart.new) ↔
        (cpmap cp).map.RingAdj x
          ((cpmap cp).map.node (cpmap cp).point) := by
    change ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x)
        (((cpmap cp).h).map.node ((cpmap cp).h).point) ↔
      (cpmap cp).map.RingAdj x
        ((cpmap cp).map.node (cpmap cp).point)
    exact hOld_ringAdj_node_point_iff (cpmap cp) hproper
  have hpointAdj :
      (Hypermap.extensionH (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).hOld x) ExtDart.new ↔
        PermReachable (cpmap cp).map.face
          ((cpmap cp).map.node (cpmap cp).point) x ∨
          PermReachable (cpmap cp).map.face (cpmap cp).point x ∨
          PermReachable (cpmap cp).map.face
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
            x := by
    rw [← Hypermap.FaceBand.triple]
    change ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x)
        ((cpmap cp).h).point ↔
      (cpmap cp).map.FaceBand
        [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point,
          (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)] x
    exact hOld_ringAdj_point_iff_faceBand_coq_of_plain_proper_long
      (cpmap cp) hplainH hproper hlong
  rw [cpMask_h_tail_faceBand_split_of_ringSize_gt_two
    (cp := cp) hsize (a2 := a2) (a1 := a1) (b1 := b1)
    (mr' := mr') (ks' := ks')]
  rw [cpMask_h_tail_exists_ringAdj_split
    (cp := cp) b1' mr ks]
  have htail :=
    cpMaskAdjSound_cons_cons_rewrite_of_inner
      (cp := cp) (b0 := b0) (b1 := b1') (mr := mr) (ks := ks)
      (a0 := a0) (a1 := a1) (mr' := a2 :: mr') (ks' := ks')
      (by omega) hsound hinner (x := x)
  rw [cpMask_tail_faceBand_split_of_ringSize_gt_two
    (cp := cp) hsize a2 mr' ks'] at htail
  simpa [Bool.or_eq_true, hnotPoint, or_assoc] using
    (cpMaskAdjSound_hOld_bool
      (a0 := a0) (a1 := a1) (a2 := a2)
      (b0 := b0) (b1 := b1) (b1' := b1')
      (N := PermReachable (cpmap cp).map.face
        ((cpmap cp).map.node (cpmap cp).point) x)
      (P := PermReachable (cpmap cp).map.face (cpmap cp).point x)
      (F := PermReachable (cpmap cp).map.face
        ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) x)
      (T := (cpmap cp).map.FaceBand
        (CfMask.selectMask (⟨mr', ks'⟩ : CfMask)
          ((cpRing cp).drop 3) (cpKernel cp)) x)
      (RN := (cpmap cp).map.RingAdj x
        ((cpmap cp).map.node (cpmap cp).point))
      (RP := (cpmap cp).map.RingAdj x (cpmap cp).point)
      (E := ∃ y : (cpmap cp).map.Dart,
        y ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
          ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.RingAdj x y)
      (RNH :=
        (Hypermap.extensionH (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).hOld x)
          ((Hypermap.extensionH (cpmap cp).map (cpmap cp).point).node
            ExtDart.new))
      (RPH :=
        (Hypermap.extensionH (cpmap cp).map (cpmap cp).point).RingAdj
          ((cpmap cp).hOld x) ExtDart.new)
      hnodeAdj hpointAdj htail)

theorem cpMaskAdjSound_nil
    (m : CfMask)
    (hm : CfMask.Proper [] m) :
    cpMaskAdjSound [] m := by
  intro x
  rcases m with ⟨mr, mk⟩
  have hmr : mr.length = 2 := by
    simpa [CfMask.Proper, CProg.ringSize] using hm.1
  have hmk : mk.length = 0 := by
    simpa [CfMask.Proper, CProg.kernelSize] using hm.2
  cases mr with
  | nil =>
      simp at hmr
  | cons b0 mr₁ =>
      cases mr₁ with
      | nil =>
          simp at hmr
      | cons b1 mr₂ =>
          cases mr₂ with
          | nil =>
              cases mk with
              | nil =>
                  change cpmap0.FaceBand
                      (CfMask.cpmask
                        (CfMask.adjMask (⟨[b0, b1], []⟩ : CfMask) [])
                        [false, true] []) x ↔
                    ∃ y : Bool,
                      y ∈ CfMask.cpmask (⟨[b0, b1], []⟩ : CfMask)
                        [false, true] [] ∧ cpmap0.RingAdj x y
                  cases b0 <;> cases b1 <;> cases x <;>
                    simp [CfMask.cpmask, CfMask.selectMask, CfMask.select,
                      CfMask.adjMask]
              | cons _ mk' =>
                  simp at hmk
          | cons _ mr₃ =>
              simp at hmr

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
