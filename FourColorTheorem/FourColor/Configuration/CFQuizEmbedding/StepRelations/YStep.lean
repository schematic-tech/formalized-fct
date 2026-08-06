import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.ProperSequences

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- Coq `en_v1` and `enn_v1` in the `CpY` branch.  The first surviving old
ring dart is off the intermediate Y perimeter, so the outer cubic-program
injection commutes with the two node steps used by the compiled question. -/
theorem yStep_outer_relations
    {cp1 cp2 : CProg}
    (hcp1 : CProg.cubic cp1 = true)
    (hcp2 : cp2 = [] ∨ CProg.config cp2 = true) :
    let P := PointedHypermap.cpmap cp2
    let h := PointedHypermap.injcp cp1 (CpStep.y :: cp2)
    let G0 := (PointedHypermap.cpmap
      (CProg.appendRev cp1 (CpStep.y :: cp2))).map
    G0.edge (G0.node (h (P.yOld (P.map.node P.point)))) =
        h (P.y.map.node P.y.point) ∧
      G0.edge (G0.node (G0.node
          (h (P.yOld (P.map.node P.point))))) = h P.y.point := by
  let P := PointedHypermap.cpmap cp2
  let h := PointedHypermap.injcp cp1 (CpStep.y :: cp2)
  let G0 := (PointedHypermap.cpmap
    (CProg.appendRev cp1 (CpStep.y :: cp2))).map
  have htail :
      P.ProperRingHead ∧ PointedHypermap.cpRingCycle cp2 ∧
        1 < CProg.ringSize cp2 := by
    rcases hcp2 with rfl | hcfg
    · exact ⟨by simpa [P] using PointedHypermap.base_properRingHead,
        PointedHypermap.cpRingCycle_nil, by decide⟩
    · exact
        ⟨(PointedHypermap.cpmap_configGeometry_of_config hcfg).proper,
          PointedHypermap.cpRingCycle_of_config hcfg,
          by
            have hgt := CProg.ringSize_gt_two_of_config hcfg
            omega⟩
  have hproperHead := htail.1
  have hcycle := htail.2.1
  have hsize := htail.2.2
  have hcycleY : PointedHypermap.cpRingCycle (CpStep.y :: cp2) :=
    PointedHypermap.cpRingCycle_y hcycle hproperHead hsize
  have hringY :
      PointedHypermap.cpRing (CpStep.y :: cp2) =
        P.y.map.node P.y.point :: P.y.point ::
          ((PointedHypermap.cpRing cp2).drop 1).map P.yOld := by
    simpa [P] using
      PointedHypermap.cpRing_y_eq_of_ringCycle hcycle hproperHead
  have hhead :
      PointedHypermap.cpRing cp2 =
        P.map.node P.point :: (PointedHypermap.cpRing cp2).drop 1 := by
    simpa [P] using PointedHypermap.cpRing_eq_nodePoint_cons_drop_one cp2
  have hnodup : (PointedHypermap.cpRing cp2).Nodup := by
    simpa [PointedHypermap.cpRing] using hcycle.nodup
  have hnotDrop :
      P.map.node P.point ∉ (PointedHypermap.cpRing cp2).drop 1 := by
    rw [hhead] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  let v1 := P.yOld (P.map.node P.point)
  have hv1NotMem : v1 ∉ PointedHypermap.cpRing (CpStep.y :: cp2) := by
    intro hv1Mem
    rw [hringY]
      at hv1Mem
    rcases List.mem_cons.mp hv1Mem with hv | hv1Mem
    · exact PointedHypermap.yOld_ne_node_point P _ hv
    rcases List.mem_cons.mp hv1Mem with hv | hv1Mem
    · exact PointedHypermap.yOld_ne_point P _ hv
    rcases List.mem_map.mp hv1Mem with ⟨x, hx, hv⟩
    exact hnotDrop (by
      have heq := PointedHypermap.yOld_injective P (by
        simpa [v1] using hv)
      simpa [heq] using hx)
  have hv1Off : ¬ P.y.OnRing v1 := by
    intro hv1
    apply hv1NotMem
    simpa [PointedHypermap.cpRing] using
      hcycleY.mem_ringDarts_of_onRing
        (CProg.ringSize_pos (CpStep.y :: cp2)) hv1
  have hnodeV1 :
      h (P.y.map.node v1) = G0.node (h v1) := by
    simpa [P, h, G0] using
      PointedHypermap.node_injcp cp1 (CpStep.y :: cp2) hcp1 hv1Off
  have hnodeV1Off : ¬ P.y.OnRing (P.y.map.node v1) := by
    exact PointedHypermap.not_onRing_of_nodeReachable P.y hv1Off
      (PermReachable.forward P.y.map.node v1)
  have hnodeNodeV1 :
      h (P.y.map.node (P.y.map.node v1)) =
        G0.node (h (P.y.map.node v1)) := by
    simpa [P, h, G0] using
      PointedHypermap.node_injcp cp1 (CpStep.y :: cp2) hcp1 hnodeV1Off
  have hedge (x : P.y.map.Dart) :
      h (P.y.map.edge x) = G0.edge (h x) := by
    simpa [P, h, G0] using
      PointedHypermap.edge_injcp cp1 (CpStep.y :: cp2) hcp1 x
  have hnodeV1Source :
      P.y.map.node v1 = ExtDart.old ExtDart.new := by
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
    rw [if_neg (by intro heq; cases heq)]
    rw [if_neg (by intro heq; cases heq)]
    rfl
  have hnodeNodeV1Source :
      P.y.map.node (P.y.map.node v1) = ExtDart.newEdge := by
    rw [hnodeV1Source]
    change (Hypermap.extensionY P.map P.point).node
        (ExtDart.old ExtDart.new) = ExtDart.newEdge
    unfold Hypermap.extensionY
    change Hypermap.ExtensionN.node
        (Hypermap.extensionU P.map P.point) ExtDart.new
          (ExtDart.old ExtDart.new) = ExtDart.newEdge
    rw [Hypermap.ExtensionN.node_old]
    simp
  have hsource1 :
      P.y.map.edge (P.y.map.node v1) = P.y.map.node P.y.point := by
    rw [hnodeV1Source]
    change (Hypermap.extensionY P.map P.point).edge
        (ExtDart.old ExtDart.new) =
      (Hypermap.extensionY P.map P.point).node ExtDart.new
    rw [Hypermap.extensionY_node_new]
    rfl
  have hsource2 :
      P.y.map.edge (P.y.map.node (P.y.map.node v1)) = P.y.point := by
    rw [hnodeNodeV1Source]
    rfl
  constructor
  · rw [← hnodeV1, ← hedge, hsource1]
  · rw [← hnodeV1, ← hnodeNodeV1, ← hedge, hsource2]

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
