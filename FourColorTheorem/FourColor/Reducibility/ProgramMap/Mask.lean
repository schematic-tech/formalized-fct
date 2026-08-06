import FourColorTheorem.FourColor.Reducibility.ProgramMap.ProgramRing

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Semantic kernel representatives of a construction program, matching Coq
`cpker`: one representative is added for each `H` step, and old representatives
are injected through `Y` and `H` constructors. -/
noncomputable def cpKernel : (cp : CProg) → List (cpmap cp).map.Dart
  | [] => []
  | CpStep.rotate _ :: cp => cpKernel cp
  | CpStep.y :: cp => (cpKernel cp).map (fun x => (cpmap cp).yOld x)
  | CpStep.h :: cp =>
      match cpRing cp with
      | _ :: x :: _ => (x :: cpKernel cp).map (fun y => (cpmap cp).hOld y)
      | _ => []
  | _ :: _ => []

@[simp]
theorem cpKernel_nil :
    cpKernel [] = [] :=
  rfl

theorem cpKernel_y_eq (cp : CProg) :
    cpKernel (CpStep.y :: cp) =
      (cpKernel cp).map (fun x => (cpmap cp).yOld x) := by
  rfl

theorem cpKernel_h_eq_of_ringSize_gt_one
    {cp : CProg}
    (hsize : 1 < CProg.ringSize cp) :
    cpKernel (CpStep.h :: cp) =
      ((cpmap cp).point :: cpKernel cp).map
        (fun x => (cpmap cp).hOld x) := by
  change
    (match cpRing cp with
      | _ :: x :: _ =>
          (x :: cpKernel cp).map (fun y => (cpmap cp).hOld y)
      | _ => []) =
      ((cpmap cp).point :: cpKernel cp).map
        (fun x => (cpmap cp).hOld x)
  have h :
      CProg.ringSize cp = (CProg.ringSize cp - 2) + 2 := by
    omega
  rw [cpRing, h, ringDarts_succ_succ]

theorem length_cpKernel_of_config :
    ∀ cp : CProg, CProg.config cp = true →
      (cpKernel cp).length = CProg.kernelSize cp
  | [], hcp => by
      simp [CProg.config] at hcp
  | CpStep.rotate n :: cp, hcp => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcp
      simpa [cpKernel, CProg.kernelSize] using
        length_cpKernel_of_config cp htail
  | CpStep.reverseRotate :: _cp, hcp => by
      simp [CProg.config] at hcp
  | CpStep.y :: cp, hcp => by
      cases cp with
      | nil =>
          simp [cpKernel, CProg.kernelSize]
      | cons s cp =>
          have htail : CProg.config (s :: cp) = true := by
            simpa [CProg.config] using hcp
          simpa [cpKernel, CProg.kernelSize] using
            length_cpKernel_of_config (s :: cp) htail
  | CpStep.h :: cp, hcp => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcp
      have hgt : 2 < CProg.ringSize cp :=
        CProg.ringSize_gt_two_of_config htail
      have hlen : (cpRing cp).length = CProg.ringSize cp :=
        length_cpRing cp
      cases hring : cpRing cp with
      | nil =>
          simp [hring] at hlen
          omega
      | cons a rest =>
          cases rest with
          | nil =>
              simp [hring] at hlen
              omega
          | cons x xs =>
              simp [cpKernel, hring, CProg.kernelSize,
                length_cpKernel_of_config cp htail]
  | CpStep.u :: _cp, hcp => by
      simp [CProg.config] at hcp
  | CpStep.k :: _cp, hcp => by
      simp [CProg.config] at hcp
  | CpStep.a :: _cp, hcp => by
      simp [CProg.config] at hcp

/-- Semantic selection of ring/kernel face representatives by a configuration
mask, matching Coq `cpmask`. -/
noncomputable def cpMask (m : CfMask) (cp : CProg) :
    List (cpmap cp).map.Dart :=
  CfMask.cpmask m (cpRing cp) (cpKernel cp)

theorem cpMask_cons_ring_eq
    (cp : CProg) (b : Bool) (mr ks : List Bool) :
    cpMask (⟨b :: mr, ks⟩ : CfMask) cp =
      (if b then [(cpmap cp).map.node (cpmap cp).point] else []) ++
        CfMask.selectMask (⟨mr, ks⟩ : CfMask)
          ((cpRing cp).drop 1) (cpKernel cp) := by
  change CfMask.selectMask (⟨b :: mr, ks⟩ : CfMask)
      (cpRing cp) (cpKernel cp) = _
  rw [cpRing_eq_nodePoint_cons_drop_one cp]
  rw [CfMask.selectMask_cons_ring]
  simp

theorem cpMask_cons_cons_ring_eq_of_ringSize_gt_one
    {cp : CProg} (hsize : 1 < CProg.ringSize cp)
    (b0 b1 : Bool) (mr ks : List Bool) :
    cpMask (⟨b0 :: b1 :: mr, ks⟩ : CfMask) cp =
      (if b0 then [(cpmap cp).map.node (cpmap cp).point] else []) ++
        (if b1 then [(cpmap cp).point] else []) ++
          CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) := by
  change CfMask.selectMask (⟨b0 :: b1 :: mr, ks⟩ : CfMask)
      (cpRing cp) (cpKernel cp) = _
  rw [cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one hsize]
  rw [CfMask.selectMask_cons_cons_ring]
  simp

theorem selectMask_cpRing_drop_one_eq_of_ringSize_gt_one
    {cp : CProg} (hsize : 1 < CProg.ringSize cp)
    (b : Bool) (mr ks : List Bool) :
    CfMask.selectMask (⟨b :: mr, ks⟩ : CfMask)
        ((cpRing cp).drop 1) (cpKernel cp) =
      (if b then [(cpmap cp).point] else []) ++
        CfMask.selectMask (⟨mr, ks⟩ : CfMask)
          ((cpRing cp).drop 2) (cpKernel cp) := by
  rw [cpRing_drop_one_eq_point_cons_drop_two_of_ringSize_gt_one
    (cp := cp) hsize]
  rw [CfMask.selectMask_cons_ring]

theorem cpMask_y_eq_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (b0 b1 b2 : Bool) (mr ks : List Bool) :
    cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask) (CpStep.y :: cp) =
      (if b0 then [((cpmap cp).y).map.node ((cpmap cp).y).point] else []) ++
        (if b1 then [((cpmap cp).y).point] else []) ++
          (CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
            ((cpRing cp).drop 1) (cpKernel cp)).map
              (fun x => (cpmap cp).yOld x) := by
  change CfMask.selectMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
      (cpRing (CpStep.y :: cp)) (cpKernel (CpStep.y :: cp)) = _
  rw [cpRing_y_eq_of_ringCycle hcycle hproper, cpKernel_y_eq]
  cases b0 <;> cases b1 <;>
    simp [CfMask.selectMask, CfMask.select, CfMask.select_map,
      CfMask.select_map_tail, List.map_append]
  all_goals rfl

theorem cpMask_h_eq_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b1' : Bool) (mr ks : List Bool) :
    cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask) (CpStep.h :: cp) =
      (if b0 then [((cpmap cp).h).map.node ((cpmap cp).h).point] else []) ++
        (if b1 then [((cpmap cp).h).point] else []) ++
          (CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
            ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp)).map
              (fun x => (cpmap cp).hOld x) := by
  change CfMask.selectMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
      (cpRing (CpStep.h :: cp)) (cpKernel (CpStep.h :: cp)) = _
  rw [cpRing_h_eq_of_ringCycle hcycle hproper hlong hsize,
    cpKernel_h_eq_of_ringSize_gt_one (cp := cp) (by omega)]
  cases b0 <;> cases b1 <;> cases b1' <;>
    simp [CfMask.selectMask, CfMask.select, CfMask.select_map,
      CfMask.select_map_drop, List.map_append]
  all_goals rfl

theorem cpMask_yOld_mem_iff_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (b0 b1 b2 : Bool) (mr ks : List Bool) {x : (cpmap cp).map.Dart} :
    (cpmap cp).yOld x ∈
        cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask) (CpStep.y :: cp) ↔
      x ∈ CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
        ((cpRing cp).drop 1) (cpKernel cp) := by
  rw [cpMask_y_eq_of_ringCycle hcycle hproper b0 b1 b2 mr ks]
  exact CfMask.mem_two_prefixes_map_iff_of_injective
    (f := fun z => (cpmap cp).yOld z)
    (x := x)
    (a := ((cpmap cp).y).map.node ((cpmap cp).y).point)
    (b := ((cpmap cp).y).point)
    (yOld_injective (cpmap cp))
    (yOld_ne_node_point (cpmap cp) x)
    (yOld_ne_point (cpmap cp) x)
    b0 b1
    (CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
      ((cpRing cp).drop 1) (cpKernel cp))

theorem cpMask_hOld_mem_iff_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    (b0 b1 b1' : Bool) (mr ks : List Bool) {x : (cpmap cp).map.Dart} :
    (cpmap cp).hOld x ∈
        cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask) (CpStep.h :: cp) ↔
      x ∈ CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
        ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp) := by
  rw [cpMask_h_eq_of_ringCycle hcycle hproper hlong hsize b0 b1 b1' mr ks]
  exact CfMask.mem_two_prefixes_map_iff_of_injective
    (f := fun z => (cpmap cp).hOld z)
    (x := x)
    (a := ((cpmap cp).h).map.node ((cpmap cp).h).point)
    (b := ((cpmap cp).h).point)
    (hOld_injective (cpmap cp))
    (hOld_ne_node_point (cpmap cp) x)
    (hOld_ne_point (cpmap cp) x)
    b0 b1
    (CfMask.selectMask (⟨mr, b1' :: ks⟩ : CfMask)
      ((cpRing cp).drop 2) ((cpmap cp).point :: cpKernel cp))

/-- Semantic correctness target for Coq `cpmask_adj`: the executable
`adjMask` selects exactly the faces adjacent to the original selected
ring/kernel mask. -/
noncomputable def cpMaskAdjSound (cp : CProg) (m : CfMask) : Prop :=
  ∀ x : (cpmap cp).map.Dart,
    (cpmap cp).map.FaceBand (cpMask (CfMask.adjMask m cp) cp) x ↔
      ∃ y : (cpmap cp).map.Dart,
        y ∈ cpMask m cp ∧ (cpmap cp).map.RingAdj x y

theorem cpMaskAdjSound_cons_cons_rewrite_of_inner
    {cp : CProg} {b0 b1 : Bool} {mr ks : List Bool}
    {a0 a1 : Bool} {mr' ks' : List Bool}
    (hsize : 1 < CProg.ringSize cp)
    (hsound : cpMaskAdjSound cp (⟨b0 :: b1 :: mr, ks⟩ : CfMask))
    (hinner :
      CfMask.adjMask (⟨b0 :: b1 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    (a0 = true ∧
        PermReachable (cpmap cp).map.face
          ((cpmap cp).map.node (cpmap cp).point) x) ∨
      (a1 = true ∧
        PermReachable (cpmap cp).map.face (cpmap cp).point x) ∨
        (cpmap cp).map.FaceBand
          (CfMask.selectMask (⟨mr', ks'⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp)) x ↔
      (b0 = true ∧
          (cpmap cp).map.RingAdj x
            ((cpmap cp).map.node (cpmap cp).point)) ∨
        (b1 = true ∧
          (cpmap cp).map.RingAdj x (cpmap cp).point) ∨
          ∃ y : (cpmap cp).map.Dart,
            y ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
              ((cpRing cp).drop 2) (cpKernel cp) ∧
              (cpmap cp).map.RingAdj x y := by
  have h := hsound x
  rw [hinner] at h
  rw [cpMask_cons_cons_ring_eq_of_ringSize_gt_one
      (cp := cp) hsize a0 a1 mr' ks'] at h
  rw [Hypermap.FaceBand.two_optional_prefixes] at h
  rw [cpMask_cons_cons_ring_eq_of_ringSize_gt_one
      (cp := cp) hsize b0 b1 mr ks] at h
  rw [Hypermap.RingAdj.exists_mem_two_optional_prefixes] at h
  exact h

theorem cpMaskAdjSound_yOld_faceBand_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    {b0 b1 b2 : Bool} {mr ks : List Bool}
    {a0 a2 : Bool} {mr' ks' : List Bool}
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
      ((a0 || b1) = true ∧
          PermReachable ((cpmap cp).y).map.face
            (((cpmap cp).y).map.node ((cpmap cp).y).point)
            ((cpmap cp).yOld x)) ∨
        ((b0 || b2) = true ∧
          PermReachable ((cpmap cp).y).map.face
            ((cpmap cp).y).point ((cpmap cp).yOld x)) ∨
          (cpmap cp).map.FaceBand
            (CfMask.selectMask (⟨(a2 || b1) :: mr', ks'⟩ : CfMask)
              ((cpRing cp).drop 1) (cpKernel cp)) x := by
  rw [CfMask.adjMask_y_eq_of_inner hinner]
  rw [cpMask_y_eq_of_ringCycle hcycle hproper
    (a0 || b1) (b0 || b2) (a2 || b1) mr' ks']
  exact yOld_faceBand_two_prefixes_map_iff (cpmap cp)
    (a0 || b1) (b0 || b2)
    (((cpmap cp).y).map.node ((cpmap cp).y).point)
    ((cpmap cp).y).point
    (CfMask.selectMask (⟨(a2 || b1) :: mr', ks'⟩ : CfMask)
      ((cpRing cp).drop 1) (cpKernel cp))

theorem cpMaskAdjSound_yOld_exists_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (b0 b1 b2 : Bool) (mr ks : List Bool)
    {x : (cpmap cp).map.Dart} :
    (∃ y : ((cpmap cp).y).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
        ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x) y) ↔
      (b0 = true ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x)
            (((cpmap cp).y).map.node ((cpmap cp).y).point)) ∨
        (b1 = true ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x)
            ((cpmap cp).y).point) ∨
          ∃ y : (cpmap cp).map.Dart,
            y ∈ CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
              ((cpRing cp).drop 1) (cpKernel cp) ∧
              (cpmap cp).map.RingAdj x y := by
  rw [cpMask_y_eq_of_ringCycle hcycle hproper b0 b1 b2 mr ks]
  exact yOld_exists_two_prefixes_map_ringAdj_iff (cpmap cp)
    b0 b1
    (((cpmap cp).y).map.node ((cpmap cp).y).point)
    ((cpmap cp).y).point
    (CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
      ((cpRing cp).drop 1) (cpKernel cp))

theorem cpMaskAdjSound_y_point_faceBand_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    {b0 b1 b2 : Bool} {mr ks : List Bool}
    {a0 a2 : Bool} {mr' ks' : List Bool}
    (hinner :
      CfMask.adjMask (⟨b0 :: b2 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a2 :: mr', ks'⟩) :
    ((cpmap cp).y).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
            (CpStep.y :: cp))
          (CpStep.y :: cp))
        ((cpmap cp).y).point ↔
      (b0 || b2) = true := by
  rw [CfMask.adjMask_y_eq_of_inner hinner]
  rw [cpMask_y_eq_of_ringCycle hcycle hproper
    (a0 || b1) (b0 || b2) (a2 || b1) mr' ks']
  exact y_faceBand_two_prefixes_map_point_iff (cpmap cp)
    (a0 || b1) (b0 || b2)
    (CfMask.selectMask (⟨(a2 || b1) :: mr', ks'⟩ : CfMask)
      ((cpRing cp).drop 1) (cpKernel cp))

theorem cpMaskAdjSound_y_point_exists_rewrite_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (b0 b1 b2 : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).y).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
        ((cpmap cp).y).map.RingAdj ((cpmap cp).y).point y) ↔
      b0 = true ∨
        (b1 = true ∧
          ((cpmap cp).y).map.RingAdj
            ((cpmap cp).y).point ((cpmap cp).y).point) ∨
          ∃ x : (cpmap cp).map.Dart,
            x ∈ CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
              ((cpRing cp).drop 1) (cpKernel cp) ∧
              (cpmap cp).map.FaceBand
                [(cpmap cp).point,
                  (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMask_y_eq_of_ringCycle hcycle hproper b0 b1 b2 mr ks]
  exact y_exists_two_prefixes_map_ringAdj_point_iff (cpmap cp)
    b0 b1
    (CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
      ((cpRing cp).drop 1) (cpKernel cp))

theorem cpMaskAdjSound_y_point_exists_rewrite_of_ringCycle_bridgeless
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (b0 b1 b2 : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).y).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
        ((cpmap cp).y).map.RingAdj ((cpmap cp).y).point y) ↔
      b0 = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
            ((cpRing cp).drop 1) (cpKernel cp) ∧
            (cpmap cp).map.FaceBand
              [(cpmap cp).point,
                (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMaskAdjSound_y_point_exists_rewrite_of_ringCycle
    hcycle hproper b0 b1 b2 mr ks]
  have hself :
      ¬ ((cpmap cp).y).map.RingAdj
        ((cpmap cp).y).point ((cpmap cp).y).point :=
    Hypermap.Bridgeless.not_ringAdj_self
      (G := ((cpmap cp).y).map) hbridgeY ((cpmap cp).y).point
  tauto

theorem cpMask_y_tail_faceBand_pair_exists_split_of_ringSize_gt_one
    {cp : CProg}
    (hsize : 1 < CProg.ringSize cp)
    (b2 : Bool) (mr ks : List Bool) :
    (∃ x : (cpmap cp).map.Dart,
      x ∈ CfMask.selectMask (⟨b2 :: mr, ks⟩ : CfMask)
        ((cpRing cp).drop 1) (cpKernel cp) ∧
        (cpmap cp).map.FaceBand
          [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x) ↔
      b2 = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x := by
  rw [selectMask_cpRing_drop_one_eq_of_ringSize_gt_one
    (cp := cp) hsize b2 mr ks]
  cases b2
  · simp
  · constructor
    · intro _h
      exact Or.inl rfl
    · intro _h
      refine ⟨(cpmap cp).point, ?_, ?_⟩
      · simp
      · exact (Hypermap.FaceBand.pair (G := (cpmap cp).map)).2
          (Or.inl (PermReachable.refl (cpmap cp).map.face
            (cpmap cp).point))

theorem cpMaskAdjSound_y_point_exists_split_of_ringCycle_bridgeless
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (b0 b1 b2 : Bool) (mr ks : List Bool) :
    (∃ y : ((cpmap cp).y).map.Dart,
      y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
        ((cpmap cp).y).map.RingAdj ((cpmap cp).y).point y) ↔
      b0 = true ∨ b2 = true ∨
        ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x := by
  rw [cpMaskAdjSound_y_point_exists_rewrite_of_ringCycle_bridgeless
    hcycle hproper hbridgeY b0 b1 b2 mr ks]
  rw [cpMask_y_tail_faceBand_pair_exists_split_of_ringSize_gt_one
    (cp := cp) hsize b2 mr ks]

theorem cpMaskAdjSound_yOld_bool
    (a0 a2 b0 b1 b2 : Bool)
    {N P T RN RP E RNY RPY : Prop}
    (hRNY : RNY ↔ RN)
    (hRPY : RPY ↔ N ∨ P)
    (htail :
      ((a0 = true ∧ N) ∨ (a2 = true ∧ P) ∨ T) ↔
        (b0 = true ∧ RN) ∨ (b2 = true ∧ RP) ∨ E) :
    (((a0 = true ∨ b1 = true) ∧ N) ∨
        ((a2 = true ∨ b1 = true) ∧ P) ∨ T) ↔
      (b0 = true ∧ RNY) ∨
        (b1 = true ∧ RPY) ∨
          (b2 = true ∧ RP) ∨ E := by
  have tailToNew :
      ((b0 = true ∧ RN) ∨ (b2 = true ∧ RP) ∨ E) →
        (b0 = true ∧ RNY) ∨
          (b1 = true ∧ RPY) ∨
            (b2 = true ∧ RP) ∨ E := by
    intro h
    rcases h with h0 | htail'
    · exact Or.inl ⟨h0.1, hRNY.2 h0.2⟩
    · rcases htail' with h2 | hE
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr hE))
  have tailToOld :
      ((a0 = true ∧ N) ∨ (a2 = true ∧ P) ∨ T) →
        (((a0 = true ∨ b1 = true) ∧ N) ∨
          ((a2 = true ∨ b1 = true) ∧ P) ∨ T) := by
    intro h
    rcases h with h0 | htail'
    · exact Or.inl ⟨Or.inl h0.1, h0.2⟩
    · rcases htail' with h2 | hT
      · exact Or.inr (Or.inl ⟨Or.inl h2.1, h2.2⟩)
      · exact Or.inr (Or.inr hT)
  constructor
  · intro h
    rcases h with h0 | htail'
    · rcases h0 with ⟨h0, hN⟩
      rcases h0 with h0 | h1
      · exact tailToNew (htail.1 (Or.inl ⟨h0, hN⟩))
      · exact Or.inr (Or.inl ⟨h1, hRPY.2 (Or.inl hN)⟩)
    · rcases htail' with h2 | hT
      · rcases h2 with ⟨h2, hP⟩
        rcases h2 with h2 | h1
        · exact tailToNew (htail.1 (Or.inr (Or.inl ⟨h2, hP⟩)))
        · exact Or.inr (Or.inl ⟨h1, hRPY.2 (Or.inr hP)⟩)
      · exact tailToNew (htail.1 (Or.inr (Or.inr hT)))
  · intro h
    rcases h with h0 | htail'
    · exact tailToOld (htail.2 (Or.inl ⟨h0.1, hRNY.1 h0.2⟩))
    · rcases htail' with h1 | htail''
      · rcases h1 with ⟨h1, hRPY'⟩
        rcases hRPY.1 hRPY' with hN | hP
        · exact Or.inl ⟨Or.inr h1, hN⟩
        · exact Or.inr (Or.inl ⟨Or.inr h1, hP⟩)
      · rcases htail'' with h2 | hE
        · exact tailToOld (htail.2 (Or.inr (Or.inl h2)))
        · exact tailToOld (htail.2 (Or.inr (Or.inr hE)))



end Schematic.Math.GraphTheory.FourColor.PointedHypermap
