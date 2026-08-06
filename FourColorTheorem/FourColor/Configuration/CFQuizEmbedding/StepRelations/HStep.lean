import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.StepRelations.YStep

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- Coq `en_v1`, `nv1Fu0`, and `enn_v2` in the `CpH` branch.  The two
removed old ring darts are off the H perimeter, so the outer cubic-program
injection commutes with all node steps used by the compiled questions. -/
theorem hStep_outer_relations
    {cp1 cp2 : CProg}
    (hcp1 : CProg.cubic cp1 = true)
    (hcp2 : CProg.config cp2 = true) :
    let P := PointedHypermap.cpmap cp2
    let h := PointedHypermap.injcp cp1 (CpStep.h :: cp2)
    let G0 := (PointedHypermap.cpmap
      (CProg.appendRev cp1 (CpStep.h :: cp2))).map
    let v1 := P.hOld (P.map.node P.point)
    let v2 := P.hOld P.point
    G0.edge (G0.node (h v1)) = h (P.h.map.node P.h.point) ∧
      PermReachable G0.face (G0.node (h v1)) (h P.h.point) ∧
        G0.edge (G0.node (G0.node (h v2))) = h P.h.point := by
  let P := PointedHypermap.cpmap cp2
  let h := PointedHypermap.injcp cp1 (CpStep.h :: cp2)
  let G0 := (PointedHypermap.cpmap
    (CProg.appendRev cp1 (CpStep.h :: cp2))).map
  let r := PointedHypermap.cpRing cp2
  let v1 := P.hOld (P.map.node P.point)
  let v2 := P.hOld P.point
  have hgeom := PointedHypermap.cpmap_configGeometry_of_config hcp2
  have hcycle := PointedHypermap.cpRingCycle_of_config hcp2
  have hsize : 2 < CProg.ringSize cp2 :=
    CProg.ringSize_gt_two_of_config hcp2
  have hcycleH : PointedHypermap.cpRingCycle (CpStep.h :: cp2) :=
    PointedHypermap.cpRingCycle_h hcycle hgeom.proper hgeom.long hsize
  have hringH :
      PointedHypermap.cpRing (CpStep.h :: cp2) =
        P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld := by
    simpa [P, r] using
      PointedHypermap.cpRing_h_eq_of_ringCycle
        hcycle hgeom.proper hgeom.long hsize
  have hr :
      r = P.map.node P.point :: P.point ::
        P.map.face (P.map.edge P.point) :: r.drop 3 := by
    simpa [P, r] using
      PointedHypermap.cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
        (cp := cp2) hsize
  have hdrop2 :
      r.drop 2 = P.map.face (P.map.edge P.point) :: r.drop 3 := by
    simpa [P, r] using
      PointedHypermap.cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
        (cp := cp2) hsize
  have hnodup : r.Nodup := by
    simpa [r, PointedHypermap.cpRing] using hcycle.nodup
  have hnodeNotDrop : P.map.node P.point ∉ r.drop 2 := by
    rw [hr] at hnodup
    have hnotTail := (List.nodup_cons.mp hnodup).1
    intro hx
    exact hnotTail (List.mem_cons_of_mem P.point (hdrop2 ▸ hx))
  have hpointNotDrop : P.point ∉ r.drop 2 := by
    rw [hr] at hnodup
    have htailNodup := (List.nodup_cons.mp hnodup).2
    have hnot := (List.nodup_cons.mp htailNodup).1
    intro hx
    exact hnot (hdrop2 ▸ hx)
  have hv1NotMem : v1 ∉ PointedHypermap.cpRing (CpStep.h :: cp2) := by
    intro hv1Mem
    rw [hringH] at hv1Mem
    rcases List.mem_cons.mp hv1Mem with hv | hv1Mem
    · exact PointedHypermap.hOld_ne_node_point P _ hv
    rcases List.mem_cons.mp hv1Mem with hv | hv1Mem
    · exact PointedHypermap.hOld_ne_point P _ hv
    rcases List.mem_map.mp hv1Mem with ⟨x, hx, hv⟩
    have heq := PointedHypermap.hOld_injective P (by
      simpa [v1] using hv)
    exact hnodeNotDrop (by simpa [heq] using hx)
  have hv2NotMem : v2 ∉ PointedHypermap.cpRing (CpStep.h :: cp2) := by
    intro hv2Mem
    rw [hringH] at hv2Mem
    rcases List.mem_cons.mp hv2Mem with hv | hv2Mem
    · exact PointedHypermap.hOld_ne_node_point P _ hv
    rcases List.mem_cons.mp hv2Mem with hv | hv2Mem
    · exact PointedHypermap.hOld_ne_point P _ hv
    rcases List.mem_map.mp hv2Mem with ⟨x, hx, hv⟩
    have heq := PointedHypermap.hOld_injective P (by
      simpa [v2] using hv)
    exact hpointNotDrop (by simpa [heq] using hx)
  have hv1Off : ¬ P.h.OnRing v1 := by
    intro hv1Ring
    apply hv1NotMem
    simpa [PointedHypermap.cpRing] using
      hcycleH.mem_ringDarts_of_onRing
        (CProg.ringSize_pos (CpStep.h :: cp2)) hv1Ring
  have hv2Off : ¬ P.h.OnRing v2 := by
    intro hv2Ring
    apply hv2NotMem
    simpa [PointedHypermap.cpRing] using
      hcycleH.mem_ringDarts_of_onRing
        (CProg.ringSize_pos (CpStep.h :: cp2)) hv2Ring
  have hnodeV1Off : ¬ P.h.OnRing (P.h.map.node v1) :=
    PointedHypermap.not_onRing_of_nodeReachable P.h hv1Off
      (PermReachable.forward P.h.map.node v1)
  have hnodeV2Off : ¬ P.h.OnRing (P.h.map.node v2) :=
    PointedHypermap.not_onRing_of_nodeReachable P.h hv2Off
      (PermReachable.forward P.h.map.node v2)
  have hnodeNodeV2Off :
      ¬ P.h.OnRing (P.h.map.node (P.h.map.node v2)) :=
    PointedHypermap.not_onRing_of_nodeReachable P.h hnodeV2Off
      (PermReachable.forward P.h.map.node (P.h.map.node v2))
  have hnodeV1 : h (P.h.map.node v1) = G0.node (h v1) := by
    simpa [P, h, G0] using
      PointedHypermap.node_injcp cp1 (CpStep.h :: cp2) hcp1 hv1Off
  have hnodeV2 : h (P.h.map.node v2) = G0.node (h v2) := by
    simpa [P, h, G0] using
      PointedHypermap.node_injcp cp1 (CpStep.h :: cp2) hcp1 hv2Off
  have hnodeNodeV2 :
      h (P.h.map.node (P.h.map.node v2)) =
        G0.node (h (P.h.map.node v2)) := by
    simpa [P, h, G0] using
      PointedHypermap.node_injcp cp1 (CpStep.h :: cp2) hcp1 hnodeV2Off
  have hedge (x : P.h.map.Dart) :
      h (P.h.map.edge x) = G0.edge (h x) := by
    simpa [P, h, G0] using
      PointedHypermap.edge_injcp cp1 (CpStep.h :: cp2) hcp1 x
  have hyNodeV1 :
      P.y.map.node (P.yOld (P.map.node P.point)) =
        ExtDart.old ExtDart.new := by
    have hu1 :
        (Hypermap.extensionU P.map P.point).node
            (ExtDart.old (P.map.node P.point)) = ExtDart.new := by
      change Hypermap.ExtensionU.node P.map P.point
          (ExtDart.old (P.map.node P.point)) = ExtDart.new
      rw [Hypermap.ExtensionU.node_old]
      simp
    have huNew :
        (Hypermap.extensionU P.map P.point).node ExtDart.new =
          ExtDart.newEdge := rfl
    change (Hypermap.extensionY P.map P.point).node
        (Hypermap.extensionYOld P.map P.point (P.map.node P.point)) =
      ExtDart.old ExtDart.new
    unfold Hypermap.extensionY Hypermap.extensionYOld
    change Hypermap.ExtensionN.node
        (Hypermap.extensionU P.map P.point) ExtDart.new
          (ExtDart.old (ExtDart.old (P.map.node P.point))) =
      ExtDart.old ExtDart.new
    rw [Hypermap.ExtensionN.node_old]
    rw [hu1]
    rw [huNew]
    simp
    rfl
  have hyNodeNodeV1 :
      P.y.map.node
          (P.y.map.node (P.yOld (P.map.node P.point))) =
        ExtDart.newEdge := by
    rw [hyNodeV1]
    change (Hypermap.extensionY P.map P.point).node
        (ExtDart.old ExtDart.new) = ExtDart.newEdge
    unfold Hypermap.extensionY
    change Hypermap.ExtensionN.node
        (Hypermap.extensionU P.map P.point) ExtDart.new
          (ExtDart.old ExtDart.new) = ExtDart.newEdge
    rw [Hypermap.ExtensionN.node_old]
    simp
  have hsourceNodeV1 :
      P.h.map.node v1 = ExtDart.old (ExtDart.old ExtDart.new) := by
    change (Hypermap.extensionN P.y.map P.y.point).node
        (ExtDart.old (P.yOld (P.map.node P.point))) =
      ExtDart.old (ExtDart.old ExtDart.new)
    change Hypermap.ExtensionN.node P.y.map P.y.point
        (ExtDart.old (P.yOld (P.map.node P.point))) =
      ExtDart.old (ExtDart.old ExtDart.new)
    rw [Hypermap.ExtensionN.node_old]
    rw [if_neg (PointedHypermap.yOld_ne_point P _)]
    rw [if_neg (by rw [hyNodeNodeV1]; intro hEq; cases hEq)]
    rw [hyNodeV1]
    rfl
  have hsource1 :
      P.h.map.edge (P.h.map.node v1) = P.h.map.node P.h.point := by
    rw [hsourceNodeV1]
    change (Hypermap.extensionH P.map P.point).edge
        (ExtDart.old (ExtDart.old ExtDart.new)) =
      (Hypermap.extensionH P.map P.point).node ExtDart.new
    unfold Hypermap.extensionH Hypermap.extensionN
    rw [Hypermap.ExtensionN.node_new,
      if_pos (Hypermap.extensionY_long_new_of_proper
        (G := P.map) P.point hgeom.proper),
      Hypermap.extensionY_node_new]
    rfl
  have hyNodeV2 : P.y.map.node (P.yOld P.point) = P.y.point := by
    rw [← PointedHypermap.y_node_symm_point_eq_yOld_point P hgeom.proper]
    exact P.y.map.node.apply_symm_apply P.y.point
  have hsourceNodeV2 :
      P.h.map.node v2 = P.h.map.face P.h.point := by
    change (Hypermap.extensionN P.y.map P.y.point).node
        (ExtDart.old (P.yOld P.point)) =
      (Hypermap.extensionH P.map P.point).face ExtDart.new
    change Hypermap.ExtensionN.node P.y.map P.y.point
        (ExtDart.old (P.yOld P.point)) =
      (Hypermap.extensionH P.map P.point).face ExtDart.new
    rw [Hypermap.ExtensionN.node_old]
    rw [if_neg (PointedHypermap.yOld_ne_point P _)]
    rw [if_neg (by
      rw [hyNodeV2]
      exact Ne.symm (PointedHypermap.y_properRingHead P))]
    rw [hyNodeV2, Hypermap.extensionH_face_new]
    change ExtDart.old ExtDart.new = ExtDart.old ExtDart.new
    rfl
  have hsource3 :
      P.h.map.edge (P.h.map.node (P.h.map.node v2)) = P.h.point := by
    rw [hsourceNodeV2]
    exact P.h.map.edge_node_face P.h.point
  have hfaceInj (x y : P.h.map.Dart) :
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y := by
    simpa [P, h, G0] using
      (PointedHypermap.injcp_faceReachable_iff_of_cubic
        cp1 (CpStep.h :: cp2) hcp1 (x := x) (y := y))
  have hsource2 :
      PermReachable P.h.map.face (P.h.map.node v1) P.h.point := by
    rw [hsourceNodeV1]
    exact PermReachable.symm P.h.map.face
      ((Hypermap.extensionH_faceReachable_new_iff_three_of_proper
        (G := P.map) P.point hgeom.proper).2
        (Or.inr (Or.inr rfl)))
  constructor
  · rw [← hnodeV1, ← hedge, hsource1]
  constructor
  · rw [← hnodeV1]
    exact (hfaceInj _ _).2 hsource2
  · rw [← hnodeV2, ← hnodeNodeV2, ← hedge, hsource3]

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
