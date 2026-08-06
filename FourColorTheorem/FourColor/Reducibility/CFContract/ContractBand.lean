import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Correct

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Semantic statement of Coq `ctrband_correct`: `contractBand` marks exactly
the face orbits incident with the selected contract edges. -/
def ContractBandCorrect (cm : List Bool) (cp : CProg) : Prop :=
  ∀ u : (cpmap cp).map.Dart,
    (cpmap cp).map.FaceBand
        ((cpmap cp).map.insertEdges
          (CfMask.select cm (cpContractDarts cp))) u ↔
      (cpmap cp).map.FaceBand
        (cpMask (CfMask.contractBand cm cp) cp) u

private theorem faceBand_node_edgeNode_iff
    (P : PointedHypermap) {u : P.map.Dart} :
    P.map.FaceBand
        [P.map.node P.point, P.map.edge (P.map.node P.point)] u ↔
      PermReachable P.map.face (P.map.node P.point) u ∨
        PermReachable P.map.face P.point u := by
  rw [Hypermap.FaceBand.pair]
  have hep : PermReachable P.map.face
      (P.map.edge (P.map.node P.point)) P.point := by
    simpa [face_edge_node_eq_self] using
      PermReachable.forward P.map.face
        (P.map.edge (P.map.node P.point))
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (PermReachable.trans P.map.face
        (PermReachable.symm P.map.face hep) h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (PermReachable.trans P.map.face hep h)

private theorem faceBand_point_edgePoint_iff
    (P : PointedHypermap) {u : P.map.Dart} :
    P.map.FaceBand [P.point, P.map.edge P.point] u ↔
      PermReachable P.map.face P.point u ∨
        PermReachable P.map.face
          (P.map.face (P.map.edge P.point)) u := by
  rw [Hypermap.FaceBand.pair]
  have hep : PermReachable P.map.face
      (P.map.edge P.point) (P.map.face (P.map.edge P.point)) :=
    PermReachable.forward P.map.face (P.map.edge P.point)
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (PermReachable.trans P.map.face
        (PermReachable.symm P.map.face hep) h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (PermReachable.trans P.map.face hep h)

private theorem faceBand_optional_pair_prefix
    {G : Hypermap} (b : Bool) (r s : List G.Dart) {u : G.Dart} :
    G.FaceBand ((if b then r else []) ++ s) u ↔
      (b = true ∧ G.FaceBand r u) ∨ G.FaceBand s u := by
  cases b <;> simp [Hypermap.FaceBand.append]

private theorem h_faceBand_freshContractEdge_old_iff
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    {x : P.map.Dart} :
    P.h.map.FaceBand
        [P.h.map.face P.h.point,
          P.h.map.edge (P.h.map.face P.h.point)]
        (P.hOld x) ↔
      PermReachable P.map.face P.point x := by
  rw [Hypermap.FaceBand.pair]
  have hstep : PermReachable P.h.map.face
      (P.h.map.edge (P.h.map.face P.h.point))
      (P.hOld P.point) := by
    have h := PermReachable.forward P.h.map.face
      (P.h.map.edge (P.h.map.face P.h.point))
    rw [h_face_edge_face_point_eq_hOld_point P hproper] at h
    exact h
  constructor
  · rintro (hfresh | hedge)
    · have hpoint : PermReachable P.h.map.face P.h.point
          (P.hOld x) :=
        PermReachable.trans P.h.map.face
          (PermReachable.forward P.h.map.face P.h.point) hfresh
      exact False.elim (P.h_not_faceReachable_point_old x hpoint)
    · exact (P.hOld_faceReachable_iff).1
        (PermReachable.trans P.h.map.face
          (PermReachable.symm P.h.map.face hstep) hedge)
  · intro h
    exact Or.inr (PermReachable.trans P.h.map.face hstep
      (P.hOld_faceReachable_of_faceReachable h))

private theorem h_faceBand_nodeContractEdge_old_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    P.h.map.FaceBand
        [P.hOld (P.map.node P.point),
          P.h.map.edge (P.hOld (P.map.node P.point))]
        (P.hOld x) ↔
      PermReachable P.map.face (P.map.node P.point) x ∨
        PermReachable P.map.face P.point x := by
  rw [← P.hOld_edge]
  change P.h.map.FaceBand
      ([P.map.node P.point,
        P.map.edge (P.map.node P.point)].map P.hOld) (P.hOld x) ↔ _
  rw [P.hOld_faceBand_iff]
  exact faceBand_node_edgeNode_iff P

private theorem h_faceBand_pointContractEdge_old_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    P.h.map.FaceBand
        [P.hOld P.point, P.h.map.edge (P.hOld P.point)]
        (P.hOld x) ↔
      PermReachable P.map.face P.point x ∨
        PermReachable P.map.face
          (P.map.face (P.map.edge P.point)) x := by
  rw [← P.hOld_edge]
  change P.h.map.FaceBand
      ([P.point, P.map.edge P.point].map P.hOld) (P.hOld x) ↔ _
  rw [P.hOld_faceBand_iff]
  exact faceBand_point_edgePoint_iff P

private theorem cpMask_three_ring_faceBand_iff
    {cp : CProg} (hsize : 2 < CProg.ringSize cp)
    (a0 a1 a2 : Bool) (mr ks : List Bool)
    {x : (cpmap cp).map.Dart} :
    (cpmap cp).map.FaceBand
        (cpMask (⟨a0 :: a1 :: a2 :: mr, ks⟩ : CfMask) cp) x ↔
      (a0 = true ∧ PermReachable (cpmap cp).map.face
          ((cpmap cp).map.node (cpmap cp).point) x) ∨
        (a1 = true ∧ PermReachable (cpmap cp).map.face
          (cpmap cp).point x) ∨
        (a2 = true ∧ PermReachable (cpmap cp).map.face
          ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) x) ∨
        (cpmap cp).map.FaceBand
          (CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp)) x := by
  change (cpmap cp).map.FaceBand
      (CfMask.selectMask (⟨a0 :: a1 :: a2 :: mr, ks⟩ : CfMask)
        (cpRing cp) (cpKernel cp)) x ↔ _
  rw [cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
    (cp := cp) hsize]
  rw [CfMask.selectMask_cons_ring, CfMask.selectMask_cons_ring,
    CfMask.selectMask_cons_ring]
  rw [Hypermap.FaceBand.optional_prefix,
    Hypermap.FaceBand.optional_prefix,
    Hypermap.FaceBand.optional_prefix]
  rfl

private theorem cpMask_h_tail_faceBand_iff
    {cp : CProg} (hsize : 2 < CProg.ringSize cp)
    (r2 k0 : Bool) (mr ks : List Bool)
    {x : (cpmap cp).map.Dart} :
    (cpmap cp).map.FaceBand
        (CfMask.selectMask (⟨r2 :: mr, k0 :: ks⟩ : CfMask)
          ((cpRing cp).drop 2)
          ((cpmap cp).point :: cpKernel cp)) x ↔
      (r2 = true ∧ PermReachable (cpmap cp).map.face
          ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) x) ∨
        (k0 = true ∧ PermReachable (cpmap cp).map.face
          (cpmap cp).point x) ∨
        (cpmap cp).map.FaceBand
          (CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp)) x := by
  simpa using cpMask_h_tail_faceBand_split_of_ringSize_gt_two
    (cp := cp) hsize r2 k0 false mr ks

private theorem insertEdges_h_contract_select_eq
    (P : PointedHypermap) (b1 b0 b2 : Bool)
    (cm : List Bool) (xs : List P.map.Dart) :
    P.h.map.insertEdges
        (CfMask.select (b1 :: b0 :: b2 :: cm)
          (P.h.map.face P.h.point ::
            (P.map.node P.point :: P.point :: xs).map P.hOld)) =
      (if b1 then
          [P.h.map.face P.h.point,
            P.h.map.edge (P.h.map.face P.h.point)]
        else []) ++
      (if b0 then
          [P.hOld (P.map.node P.point),
            P.h.map.edge (P.hOld (P.map.node P.point))]
        else []) ++
      (if b2 then
          [P.hOld P.point, P.h.map.edge (P.hOld P.point)]
        else []) ++
      (P.map.insertEdges (CfMask.select cm xs)).map P.hOld := by
  have hsource :
      P.map.insertEdges
          (CfMask.select (b0 :: b2 :: cm)
            (P.map.node P.point :: P.point :: xs)) =
        (if b0 then
            [P.map.node P.point,
              P.map.edge (P.map.node P.point)]
          else []) ++
        (if b2 then [P.point, P.map.edge P.point] else []) ++
        P.map.insertEdges (CfMask.select cm xs) := by
    cases b0 <;> cases b2 <;> simp [CfMask.select]
  cases b1
  · simp only [CfMask.select, Bool.false_eq_true, if_false]
    rw [CfMask.select_map]
    rw [P.map.insertEdges_map P.hOld P.hOld_edge, hsource]
    cases b0 <;> cases b2 <;> simp <;> rfl
  · simp only [CfMask.select, if_true]
    rw [CfMask.select_map]
    rw [Hypermap.insertEdges_cons,
      P.map.insertEdges_map P.hOld P.hOld_edge, hsource]
    cases b0 <;> cases b2 <;> simp <;> rfl

private theorem hOld_faceBand_point_false
    (P : PointedHypermap) (r : List P.map.Dart) :
    ¬ P.h.map.FaceBand (r.map P.hOld) P.h.point := by
  rintro ⟨z, hz, hzp⟩
  rcases List.mem_map.mp hz with ⟨x, _hx, rfl⟩
  exact P.h_not_faceReachable_point_old x
    (PermReachable.symm P.h.map.face hzp)

private theorem h_faceBand_oldContractEdge_point_false
    (P : PointedHypermap) (z : P.map.Dart) :
    ¬ P.h.map.FaceBand
      [P.hOld z, P.h.map.edge (P.hOld z)] P.h.point := by
  rw [← P.hOld_edge]
  change ¬ P.h.map.FaceBand ([z, P.map.edge z].map P.hOld) P.h.point
  exact hOld_faceBand_point_false P [z, P.map.edge z]

private theorem h_faceBand_freshContractEdge_point
    (P : PointedHypermap) :
    P.h.map.FaceBand
      [P.h.map.face P.h.point,
        P.h.map.edge (P.h.map.face P.h.point)] P.h.point := by
  exact Hypermap.FaceBand.of_mem
    (G := P.h.map) (x := P.h.map.face P.h.point)
    (List.Mem.head _)
    (PermReachable.symm P.h.map.face
      (PermReachable.forward P.h.map.face P.h.point))

private theorem contractBandCorrect_y
    {s : CpStep} {cp : CProg} {cm : List Bool} (b : Bool)
    (hcfg : CProg.config (s :: cp) = true)
    (hcm : cm.length = CProg.contractEdgeSize (s :: cp))
    (hsound : ContractBandCorrect cm (s :: cp)) :
    ContractBandCorrect (b :: cm) (CpStep.y :: s :: cp) := by
  let P := cpmap (s :: cp)
  have hcycle : cpRingCycle (s :: cp) := cpRingCycle_of_config hcfg
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 1 < CProg.ringSize (s :: cp) := by
    have := CProg.ringSize_gt_two_of_config hcfg
    omega
  have hproperBand := CfMask.proper_contractBand_of_length hcm hcfg
  cases hband : CfMask.contractBand cm (s :: cp) with
  | mk r ks =>
      have hr : r.length = CProg.ringSize (s :: cp) := by
        simpa [hband] using hproperBand.1
      cases r with
      | nil => exfalso; simp at hr; omega
      | cons a0 r1 =>
          cases r1 with
          | nil => exfalso; simp at hr; omega
          | cons a1 mr =>
              intro u
              have hselected :
                  CfMask.select (b :: cm)
                      (cpContractDarts (CpStep.y :: s :: cp)) =
                    (CfMask.select (b :: cm)
                      (P.map.node P.point :: cpContractDarts (s :: cp))).map
                        P.yOld := by
                rw [cpContractDarts_y_cons]
                exact CfMask.select_map P.yOld (b :: cm)
                  (P.map.node P.point :: cpContractDarts (s :: cp))
              have hinserted :
                  P.y.map.insertEdges
                      (CfMask.select (b :: cm)
                        (cpContractDarts (CpStep.y :: s :: cp))) =
                    (P.map.insertEdges
                      (CfMask.select (b :: cm)
                        (P.map.node P.point :: cpContractDarts (s :: cp)))).map
                          P.yOld := by
                calc
                  P.y.map.insertEdges
                      (CfMask.select (b :: cm)
                        (cpContractDarts (CpStep.y :: s :: cp))) =
                      P.y.map.insertEdges
                        ((CfMask.select (b :: cm)
                          (P.map.node P.point ::
                            cpContractDarts (s :: cp))).map P.yOld) :=
                    congrArg P.y.map.insertEdges hselected
                  _ = (P.map.insertEdges
                        (CfMask.select (b :: cm)
                          (P.map.node P.point ::
                            cpContractDarts (s :: cp)))).map P.yOld :=
                    P.map.insertEdges_map P.yOld P.yOld_edge _
              change P.y.map.FaceBand
                  (P.y.map.insertEdges
                    (CfMask.select (b :: cm)
                      (cpContractDarts (CpStep.y :: s :: cp)))) u ↔
                P.y.map.FaceBand
                  (cpMask
                    (CfMask.contractBand (b :: cm)
                      (CpStep.y :: s :: cp))
                    (CpStep.y :: s :: cp)) u
              rw [hinserted]
              have hbandOuter :
                  CfMask.contractBand (b :: cm) (CpStep.y :: s :: cp) =
                    ⟨(b || a0) :: false :: (b || a1) :: mr, ks⟩ := by
                simp [CfMask.contractBand, hband]
              rw [hbandOuter]
              rw [cpMask_y_eq_of_ringCycle hcycle hgeom.proper
                (b || a0) false (b || a1) mr ks]
              rcases y_exists_old_faceReachable_or_point P u with
                ⟨x, hux⟩ | hpoint
              · rw [Hypermap.FaceBand.congr_faceReachable
                      (G := P.y.map) hux,
                    Hypermap.FaceBand.congr_faceReachable
                      (G := P.y.map) hux]
                rw [yOld_faceBand_iff]
                rw [yOld_faceBand_two_prefixes_map_iff]
                rw [y_faceReachable_node_point_old_iff]
                rw [selectMask_cpRing_drop_one_eq_of_ringSize_gt_one
                  hsize (b || a1) mr ks]
                rw [Hypermap.FaceBand.optional_prefix]
                have hrec := hsound x
                rw [hband] at hrec
                rw [cpMask_cons_cons_ring_eq_of_ringSize_gt_one
                  hsize a0 a1 mr ks] at hrec
                rw [Hypermap.FaceBand.two_optional_prefixes] at hrec
                cases b
                · simpa [CfMask.select, Bool.or_false] using hrec
                · simp only [CfMask.select, if_true]
                  rw [Hypermap.insertEdges_cons]
                  change P.map.FaceBand
                      ([P.map.node P.point,
                        P.map.edge (P.map.node P.point)] ++
                        P.map.insertEdges
                          (CfMask.select cm
                            (cpContractDarts (s :: cp)))) x ↔ _
                  rw [Hypermap.FaceBand.append,
                    faceBand_node_edgeNode_iff]
                  simp only [Bool.true_or, true_and]
                  tauto
              · rw [← Hypermap.FaceBand.congr_faceReachable
                      (G := P.y.map) hpoint,
                    ← Hypermap.FaceBand.congr_faceReachable
                      (G := P.y.map) hpoint]
                have hleft :
                    ¬ P.y.map.FaceBand
                      ((P.map.insertEdges
                        (CfMask.select (b :: cm)
                          (P.map.node P.point ::
                            cpContractDarts (s :: cp)))).map P.yOld)
                      P.y.point := by
                  rintro ⟨z, hz, hzp⟩
                  rcases List.mem_map.mp hz with ⟨x, _hx, rfl⟩
                  exact y_not_faceReachable_point_old P x
                    (PermReachable.symm P.y.map.face hzp)
                have hright :
                    ¬ P.y.map.FaceBand
                      ((if b || a0 then [P.y.map.node P.y.point] else []) ++
                        (if false then [P.y.point] else []) ++
                          (CfMask.selectMask
                            (⟨(b || a1) :: mr, ks⟩ : CfMask)
                            ((cpRing (s :: cp)).drop 1)
                            (cpKernel (s :: cp))).map P.yOld)
                      P.y.point := by
                  intro hright
                  have := (y_faceBand_two_prefixes_map_point_iff P
                    (b || a0) false
                    (CfMask.selectMask
                      (⟨(b || a1) :: mr, ks⟩ : CfMask)
                      ((cpRing (s :: cp)).drop 1)
                      (cpKernel (s :: cp)))).1 hright
                  simp at this
                exact ⟨fun h => (hleft h).elim,
                  fun h => (hright h).elim⟩

private theorem contractBandCorrect_rotate
    {cp : CProg} {cm : List Bool} (n : Nat)
    (hcfg : CProg.config cp = true)
    (hcm : cm.length = CProg.contractEdgeSize cp)
    (hsound : ContractBandCorrect cm cp) :
    ContractBandCorrect cm (CpStep.rotate n :: cp) := by
  have hcycle : cpRingCycle cp := cpRingCycle_of_config hcfg
  have hproper := CfMask.proper_contractBand_of_length hcm hcfg
  have hring :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle (n := n) hcycle
  intro u
  simp only [cpContractDarts_rotate, CfMask.contractBand, cpMask,
    cpKernel, cpmap_cons, step_rotate, PointedHypermap.rotate_map]
  rw [hsound u]
  apply Hypermap.FaceBand.congr_mem
  intro x
  rw [hring]
  exact (CfMask.mem_selectMask_rotateLeft_ring_iff_of_length
    (n := n) (m := CfMask.contractBand cm cp)
    (ring := cpRing cp) (kernel := cpKernel cp) (x := x)
    (by rw [length_cpRing cp, hproper.1])).symm

private theorem contractBandCorrect_h
    {cp : CProg} {cm : List Bool} (b1 b0 b2 : Bool)
    (hcfg : CProg.config cp = true)
    (hcm : cm.length = CProg.contractEdgeSize cp)
    (hsound : ContractBandCorrect cm cp) :
    ContractBandCorrect (b1 :: b0 :: b2 :: cm) (CpStep.h :: cp) := by
  let P := cpmap cp
  have hcycle : cpRingCycle cp := cpRingCycle_of_config hcfg
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 2 < CProg.ringSize cp :=
    CProg.ringSize_gt_two_of_config hcfg
  have hproperBand := CfMask.proper_contractBand_of_length hcm hcfg
  cases hband : CfMask.contractBand cm cp with
  | mk r ks =>
      have hr : r.length = CProg.ringSize cp := by
        simpa [hband] using hproperBand.1
      cases r with
      | nil => exfalso; simp at hr; omega
      | cons a0 r1 =>
          cases r1 with
          | nil => exfalso; simp at hr; omega
          | cons a1 r2 =>
              cases r2 with
              | nil => exfalso; simp at hr; omega
              | cons a2 mr =>
                  intro u
                  change P.h.map.FaceBand
                      (P.h.map.insertEdges
                        (CfMask.select (b1 :: b0 :: b2 :: cm)
                          (cpContractDarts (CpStep.h :: cp)))) u ↔
                    P.h.map.FaceBand
                      (cpMask
                        (CfMask.contractBand (b1 :: b0 :: b2 :: cm)
                          (CpStep.h :: cp))
                        (CpStep.h :: cp)) u
                  rw [cpContractDarts_h]
                  simp only [cpmap_cons, step_h]
                  change P.h.map.FaceBand
                      (P.h.map.insertEdges
                        (CfMask.select (b1 :: b0 :: b2 :: cm)
                          (P.h.map.face P.h.point ::
                            (P.map.node P.point :: P.point ::
                              cpContractDarts cp).map P.hOld))) u ↔ _
                  rw [insertEdges_h_contract_select_eq P b1 b0 b2 cm
                    (cpContractDarts cp)]
                  have hbandOuter :
                      CfMask.contractBand (b1 :: b0 :: b2 :: cm)
                          (CpStep.h :: cp) =
                        ⟨(b0 || a0) :: b1 :: (b2 || a2) :: mr,
                          (b0 || b1 || b2 || a1) :: ks⟩ := by
                    simp [CfMask.contractBand, hband]
                  rw [hbandOuter]
                  rw [cpMask_h_eq_of_ringCycle hcycle hgeom.proper
                    hgeom.long hsize (b0 || a0) b1
                    (b0 || b1 || b2 || a1) ((b2 || a2) :: mr) ks]
                  rcases h_exists_old_faceReachable_or_freshFace_of_proper
                      P hgeom.proper u with ⟨x, hux⟩ | hfresh
                  · rw [Hypermap.FaceBand.congr_faceReachable
                          (G := P.h.map) hux,
                        Hypermap.FaceBand.congr_faceReachable
                          (G := P.h.map) hux]
                    rw [List.append_assoc, List.append_assoc]
                    rw [faceBand_optional_pair_prefix,
                      faceBand_optional_pair_prefix,
                      faceBand_optional_pair_prefix]
                    rw [h_faceBand_freshContractEdge_old_iff P hgeom.proper,
                      h_faceBand_nodeContractEdge_old_iff P,
                      h_faceBand_pointContractEdge_old_iff P,
                      P.hOld_faceBand_iff]
                    have hrec := hsound x
                    rw [hband] at hrec
                    rw [cpMask_three_ring_faceBand_iff hsize a0 a1 a2 mr ks]
                      at hrec
                    rw [hrec]
                    rw [P.hOld_faceBand_two_prefixes_map_iff]
                    rw [P.h_faceReachable_node_point_old_iff hgeom.proper]
                    rw [cpMask_h_tail_faceBand_iff hsize
                      (b2 || a2) (b0 || b1 || b2 || a1) mr ks]
                    have hnot : ¬ PermReachable P.h.map.face P.h.point
                        (P.hOld x) := P.h_not_faceReachable_point_old x
                    have hnot' : ¬ PermReachable (cpmap cp).h.map.face
                        (cpmap cp).h.point ((cpmap cp).hOld x) := by
                      simpa [P] using hnot
                    simp only [Bool.or_eq_true]
                    aesop
                  · have hpu : PermReachable P.h.map.face P.h.point u := by
                      change PermReachable
                        (Hypermap.extensionH P.map P.point).face ExtDart.new u
                      exact
                        (Hypermap.extensionH_faceReachable_new_iff_freshFace_of_proper
                          (G := P.map) P.point hgeom.proper).2 hfresh
                    rw [← Hypermap.FaceBand.congr_faceReachable
                          (G := P.h.map) hpu,
                        ← Hypermap.FaceBand.congr_faceReachable
                          (G := P.h.map) hpu]
                    rw [P.h_faceBand_two_prefixes_map_point_iff hgeom.proper]
                    rw [List.append_assoc, List.append_assoc]
                    rw [faceBand_optional_pair_prefix,
                      faceBand_optional_pair_prefix,
                      faceBand_optional_pair_prefix]
                    have hnew := h_faceBand_freshContractEdge_point P
                    have hnode := h_faceBand_oldContractEdge_point_false P
                      (P.map.node P.point)
                    have hpoint := h_faceBand_oldContractEdge_point_false P
                      P.point
                    have htail := hOld_faceBand_point_false P
                      (P.map.insertEdges
                        (CfMask.select cm (cpContractDarts cp)))
                    simp only [hnew, hnode, hpoint, htail,
                      and_false, or_false, and_true]

/-- Coq `ctrband_correct`: the executable contract-band mask is proper and
selects exactly the face orbits incident with the chosen contract edges.  The
properness component is `CfMask.proper_contractBand_of_length`; this theorem
is its semantic component. -/
theorem contractBand_correct :
    ∀ {cm : List Bool} {cp : CProg},
      cm.length = CProg.contractEdgeSize cp →
      CProg.config cp = true →
      ContractBandCorrect cm cp
  | cm, [], _hcm, hcfg => by
      simp [CProg.config] at hcfg
  | cm, CpStep.rotate n :: cp, hcm, hcfg => by
      have hcfg' : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      have hcm' : cm.length = CProg.contractEdgeSize cp := by
        simpa [CProg.contractEdgeSize] using hcm
      exact contractBandCorrect_rotate n hcfg' hcm'
        (contractBand_correct hcm' hcfg')
  | cm, CpStep.reverseRotate :: cp, _hcm, hcfg => by
      simp [CProg.config] at hcfg
  | cm, [CpStep.y], hcm, _hcfg => by
      have hnil : cm = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [CProg.contractEdgeSize] using hcm
      subst cm
      intro u
      simp only [CfMask.select,
        Hypermap.insertEdges_nil, CfMask.contractBand, cpMask,
        CfMask.selectMask]
      rw [CfMask.select_replicate_false]
      exact Iff.rfl
  | [], CpStep.y :: s :: cp, hcm, _hcfg => by
      simp [CProg.contractEdgeSize] at hcm
  | b :: cm, CpStep.y :: s :: cp, hcm, hcfg => by
      have hcfg' : CProg.config (s :: cp) = true := by
        simpa [CProg.config] using hcfg
      have hcm' : cm.length = CProg.contractEdgeSize (s :: cp) := by
        simp [CProg.contractEdgeSize] at hcm
        omega
      exact contractBandCorrect_y b hcfg' hcm'
        (contractBand_correct hcm' hcfg')
  | [], CpStep.h :: cp, hcm, _hcfg => by
      simp [CProg.contractEdgeSize] at hcm
  | [_], CpStep.h :: cp, hcm, _hcfg => by
      simp [CProg.contractEdgeSize] at hcm
  | [_, _], CpStep.h :: cp, hcm, _hcfg => by
      simp [CProg.contractEdgeSize] at hcm
  | b1 :: b0 :: b2 :: cm, CpStep.h :: cp, hcm, hcfg => by
      have hcfg' : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      have hcm' : cm.length = CProg.contractEdgeSize cp := by
        simp [CProg.contractEdgeSize] at hcm
        omega
      exact contractBandCorrect_h b1 b0 b2 hcfg' hcm'
        (contractBand_correct hcm' hcfg')
  | cm, CpStep.u :: cp, _hcm, hcfg => by
      simp [CProg.config] at hcfg
  | cm, CpStep.k :: cp, _hcm, hcfg => by
      simp [CProg.config] at hcfg
  | cm, CpStep.a :: cp, _hcm, hcfg => by
      simp [CProg.config] at hcfg

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
