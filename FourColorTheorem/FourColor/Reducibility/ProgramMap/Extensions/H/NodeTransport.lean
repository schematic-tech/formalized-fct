import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.H.Basics

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
@[simp]
theorem hOld_edge (P : PointedHypermap) (x : P.map.Dart) :
    P.hOld (P.map.edge x) = P.h.map.edge (P.hOld x) := by
  change Hypermap.extensionHOld P.map P.point (P.map.edge x) =
    (Hypermap.extensionH P.map P.point).edge
      (Hypermap.extensionHOld P.map P.point x)
  rfl

theorem hOld_node_of_ne_node_point_of_ne_point_of_ne_face_edge
    (P : PointedHypermap) {x : P.map.Dart}
    (hxNode : x ≠ P.map.node P.point)
    (hxPoint : x ≠ P.point)
    (hxFaceEdge : x ≠ P.map.face (P.map.edge P.point)) :
    P.hOld (P.map.node x) = P.h.map.node (P.hOld x) := by
  change Hypermap.extensionHOld P.map P.point (P.map.node x) =
    (Hypermap.extensionH P.map P.point).node
      (Hypermap.extensionHOld P.map P.point x)
  unfold Hypermap.extensionH Hypermap.extensionHOld
  change ExtDart.old (Hypermap.extensionYOld P.map P.point (P.map.node x)) =
    Hypermap.ExtensionN.node (Hypermap.extensionY P.map P.point) ExtDart.new
      (ExtDart.old (Hypermap.extensionYOld P.map P.point x))
  rw [Hypermap.ExtensionN.node_old]
  have hnode1 :
      (Hypermap.extensionY P.map P.point).node
          (Hypermap.extensionYOld P.map P.point x) =
        Hypermap.extensionYOld P.map P.point (P.map.node x) := by
    exact (yOld_node_of_ne_node_point_of_ne_point P hxNode hxPoint).symm
  have hxNodeNode : P.map.node x ≠ P.map.node P.point := by
    intro h
    exact hxPoint (P.map.node.injective h)
  have hxNodePoint : P.map.node x ≠ P.point := by
    intro h
    apply hxFaceEdge
    calc
      x = P.map.node.symm (P.map.node x) := by simp
      _ = P.map.node.symm P.point := by rw [h]
      _ = P.map.face (P.map.edge P.point) := by
        rw [← Hypermap.face_edge_eq_node_symm]
  have hnode2 :
      (Hypermap.extensionY P.map P.point).node
          ((Hypermap.extensionY P.map P.point).node
            (Hypermap.extensionYOld P.map P.point x)) ≠
        ExtDart.new := by
    rw [hnode1]
    have hnode1b :
        (Hypermap.extensionY P.map P.point).node
            (Hypermap.extensionYOld P.map P.point (P.map.node x)) =
          Hypermap.extensionYOld P.map P.point
            (P.map.node (P.map.node x)) := by
      exact (yOld_node_of_ne_node_point_of_ne_point P
        (x := P.map.node x) hxNodeNode hxNodePoint).symm
    rw [hnode1b]
    unfold Hypermap.extensionYOld
    simp
  have hyOldNe : Hypermap.extensionYOld P.map P.point x ≠ ExtDart.new := by
    unfold Hypermap.extensionYOld
    simp
  rw [if_neg hnode2, hnode1]
  simp [hyOldNe]

theorem hOld_node_symm_of_ne_node_node_point_of_ne_node_point_of_ne_point
    (P : PointedHypermap) {x : P.map.Dart}
    (hxNodeNode : x ≠ P.map.node (P.map.node P.point))
    (hxNode : x ≠ P.map.node P.point)
    (hxPoint : x ≠ P.point) :
    P.h.map.node.symm (P.hOld x) = P.hOld (P.map.node.symm x) := by
  have hcomm :=
    hOld_node_of_ne_node_point_of_ne_point_of_ne_face_edge P
      (x := P.map.node.symm x)
      (by
        intro h
        exact hxNodeNode (by
          calc
            x = P.map.node (P.map.node.symm x) := by simp
            _ = P.map.node (P.map.node P.point) := by rw [h]))
      (by
        intro h
        exact hxNode (by
          calc
            x = P.map.node (P.map.node.symm x) := by simp
            _ = P.map.node P.point := by rw [h]))
      (by
        intro h
        exact hxPoint (by
          calc
            x = P.map.node (P.map.node.symm x) := by simp
            _ = P.map.node (P.map.face (P.map.edge P.point)) := by rw [h]
            _ = P.point := P.map.node_face_edge P.point))
  have hcomm' :
      P.hOld x =
        P.h.map.node (P.hOld (P.map.node.symm x)) := by
    simpa using hcomm
  rw [hcomm']
  exact P.h.map.node.symm_apply_apply (P.hOld (P.map.node.symm x))

theorem h_iterate_node_symm_succ_point_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead) :
    ∀ i : Nat,
      (∀ k : Nat, 0 < k → k < i + 1 →
        iteratePerm P.map.node.symm k P.point ≠ P.point) →
      (∀ k : Nat, 0 < k → k < i + 1 →
        iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point) →
      (∀ k : Nat, 0 < k → k < i + 1 →
        iteratePerm P.map.node.symm k P.point ≠
          P.map.node (P.map.node P.point)) →
      iteratePerm P.h.map.node.symm (i + 1) P.h.point =
        P.hOld (iteratePerm P.map.node.symm (i + 1) P.point)
  | 0, _hpoint, _hnode, _hnodeNode => by
      simpa using h_node_symm_point_eq_hOld_node_symm_point P hproper hlong
  | i + 1, hpoint, hnode, hnodeNode => by
      rw [iteratePerm_succ_right]
      rw [h_iterate_node_symm_succ_point_of_avoids_heads P hproper hlong i
        (fun k hkpos hk => hpoint k hkpos
          (Nat.lt_trans hk (Nat.lt_succ_self (i + 1))))
        (fun k hkpos hk => hnode k hkpos
          (Nat.lt_trans hk (Nat.lt_succ_self (i + 1))))
        (fun k hkpos hk => hnodeNode k hkpos
          (Nat.lt_trans hk (Nat.lt_succ_self (i + 1))))]
      rw [hOld_node_symm_of_ne_node_node_point_of_ne_node_point_of_ne_point P
        (hnodeNode (i + 1) (by omega) (Nat.lt_succ_self (i + 1)))
        (hnode (i + 1) (by omega) (Nat.lt_succ_self (i + 1)))
        (hpoint (i + 1) (by omega) (Nat.lt_succ_self (i + 1)))]
      simpa [iteratePerm_succ] using
        congrArg (fun z => P.hOld z)
          (iteratePerm_apply_comm P.map.node.symm i
            (P.map.node.symm P.point))

theorem hOld_node_symm_node_node_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead) :
    P.h.map.node.symm
        (P.hOld (P.map.node (P.map.node P.point))) =
      P.h.map.node P.h.point := by
  change (Hypermap.extensionH P.map P.point).node.symm
      (Hypermap.extensionHOld P.map P.point
        (P.map.node (P.map.node P.point))) =
    (Hypermap.extensionH P.map P.point).node ExtDart.new
  unfold Hypermap.extensionH Hypermap.extensionHOld
  change Hypermap.ExtensionN.nodeInvFun
      (Hypermap.extensionY P.map P.point) ExtDart.new
      (ExtDart.old
        (Hypermap.extensionYOld P.map P.point
          (P.map.node (P.map.node P.point)))) =
    Hypermap.ExtensionN.node (Hypermap.extensionY P.map P.point)
      ExtDart.new ExtDart.new
  have hlongY :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper (G := P.map) P.point hproper
  have hnodeY :
      (Hypermap.extensionY P.map P.point).node ExtDart.new =
        ExtDart.old ExtDart.newEdge :=
    Hypermap.extensionY_node_new (G := P.map) P.point
  have hnotFace :
      Hypermap.extensionYOld P.map P.point
          (P.map.node (P.map.node P.point)) ≠
        (Hypermap.extensionY P.map P.point).face
          ((Hypermap.extensionY P.map P.point).edge ExtDart.new) := by
    rw [show (Hypermap.extensionY P.map P.point).edge ExtDart.new =
        ExtDart.newEdge by rfl]
    rw [Hypermap.extensionY_face_newEdge_of_proper
      (G := P.map) P.point hproper]
    unfold Hypermap.extensionYOld
    intro h
    injection h with h'
    injection h' with h''
    apply hlong
    rw [Hypermap.face_edge_eq_node_symm]
    apply P.map.node.injective
    simpa using h''.symm
  have hnotNode :
      Hypermap.extensionYOld P.map P.point
          (P.map.node (P.map.node P.point)) ≠
        (Hypermap.extensionY P.map P.point).node ExtDart.new := by
    rw [hnodeY]
    unfold Hypermap.extensionYOld
    intro h
    injection h with h'
    cases h'
  have hnodeSymm :
      (Hypermap.extensionY P.map P.point).node.symm
          (Hypermap.extensionYOld P.map P.point
            (P.map.node (P.map.node P.point))) =
        (Hypermap.extensionY P.map P.point).node ExtDart.new :=
    yOld_node_symm_node_node_point P hproper
  simp [Hypermap.ExtensionN.nodeInvFun, hlongY, hnotFace, hnotNode,
    hnodeSymm]

end Schematic.Math.GraphTheory.FourColor.PointedHypermap
