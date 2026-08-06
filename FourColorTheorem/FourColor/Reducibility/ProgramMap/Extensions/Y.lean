import FourColorTheorem.FourColor.Reducibility.ProgramMap.Pointed
import FourColorTheorem.FourColor.Reducibility.ProgramMap.OldDartTransport

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Coq `ecpY`, using the checked composite `U` then `N` constructor. -/
def y (P : PointedHypermap) : PointedHypermap where
  map := Hypermap.extensionY P.map P.point
  point := ExtDart.new

@[simp]
theorem y_map (P : PointedHypermap) :
    P.y.map = Hypermap.extensionY P.map P.point :=
  rfl

@[simp]
theorem y_point (P : PointedHypermap) :
    P.y.point = ExtDart.new :=
  rfl

theorem y_properRingHead (P : PointedHypermap) :
    P.y.ProperRingHead := by
  intro h
  change ExtDart.new =
      (Hypermap.extensionY P.map P.point).node ExtDart.new at h
  rw [Hypermap.extensionY_node_new] at h
  cases h

theorem y_longRingHead_of_proper
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.y.LongRingHead :=
  Hypermap.extensionY_long_new_of_proper (G := P.map) P.point hproper

theorem y_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.y.Plain :=
  Hypermap.extensionY_plain (G := P.map) P.point hP

theorem y_bridgeless_of_proper
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hP : P.Bridgeless) :
    P.y.Bridgeless :=
  Hypermap.extensionY_bridgeless_of_proper (G := P.map) P.point hproper hP

theorem y_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.y.Connected :=
  Hypermap.extensionY_connected (G := P.map) P.point hP

/-- Old-dart embedding into the semantic `Y` construction, matching Coq's
`icpY`. -/
def yOld (P : PointedHypermap) (x : P.map.Dart) : P.y.map.Dart := by
  change (Hypermap.extensionY P.map P.point).Dart
  exact Hypermap.extensionYOld P.map P.point x

theorem yOld_ne_point
    (P : PointedHypermap) (x : P.map.Dart) :
    P.yOld x ≠ P.y.point := by
  change Hypermap.extensionYOld P.map P.point x ≠ ExtDart.new
  simp [Hypermap.extensionYOld]

theorem yOld_ne_node_point
    (P : PointedHypermap) (x : P.map.Dart) :
    P.yOld x ≠ P.y.map.node P.y.point := by
  change Hypermap.extensionYOld P.map P.point x ≠
    (Hypermap.extensionY P.map P.point).node ExtDart.new
  rw [Hypermap.extensionY_node_new]
  change ExtDart.old (ExtDart.old x) ≠ ExtDart.old ExtDart.newEdge
  intro h
  injection h with h'
  cases h'

theorem y_node_symm_point_eq_yOld_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.y.map.node.symm P.y.point = P.yOld P.point := by
  change (Hypermap.extensionY P.map P.point).node.symm ExtDart.new =
    Hypermap.extensionYOld P.map P.point P.point
  unfold Hypermap.extensionY Hypermap.extensionN Hypermap.extensionYOld
  change Hypermap.ExtensionN.nodeInvFun
      (Hypermap.extensionU P.map P.point) ExtDart.new ExtDart.new =
    ExtDart.old (ExtDart.old P.point)
  have hne : P.map.node P.point ≠ P.map.node (P.map.node P.point) := by
    intro h
    exact hproper (P.map.node.injective h)
  simp [Hypermap.ExtensionN.nodeInvFun, Hypermap.extensionU_long_new]
  change ExtDart.old
      (Hypermap.ExtensionU.nodeInvFun P.map P.point
        (Hypermap.ExtensionU.nodeInvFun P.map P.point ExtDart.new)) =
    ExtDart.old (ExtDart.old P.point)
  simp [Hypermap.ExtensionU.nodeInvFun, hne]

theorem y_face_edge_point_eq_yOld_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.y.map.face (P.y.map.edge P.y.point) = P.yOld P.point := by
  rw [Hypermap.face_edge_eq_node_symm,
    y_node_symm_point_eq_yOld_point P hproper]

theorem yOld_faceReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.y.map.face (P.yOld x) (P.yOld y) ↔
      PermReachable P.map.face x y := by
  change PermReachable
      (Hypermap.extensionY P.map P.point).face
      (Hypermap.extensionYOld P.map P.point x)
      (Hypermap.extensionYOld P.map P.point y) ↔
    PermReachable P.map.face x y
  exact Hypermap.extensionYOld_faceReachable_iff
    (G := P.map) (x0 := P.point)

theorem yOld_faceReachable_of_faceReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.y.map.face (P.yOld x) (P.yOld y) :=
  (yOld_faceReachable_iff P).2 hxy

theorem yOld_faceBand_iff
    (P : PointedHypermap) {r : List P.map.Dart} {x : P.map.Dart} :
    P.y.map.FaceBand (r.map P.yOld) (P.yOld x) ↔
      P.map.FaceBand r x := by
  exact OldDartTransport.faceBand_map_iff
    P.yOld (yOld_faceReachable_iff P) r x

theorem yOld_faceBand_of_faceBand
    (P : PointedHypermap) {r : List P.map.Dart} {x : P.map.Dart}
    (hx : P.map.FaceBand r x) :
    P.y.map.FaceBand (r.map P.yOld) (P.yOld x) :=
  (yOld_faceBand_iff P).2 hx

theorem yOld_faceBand_selectMask_iff
    (P : PointedHypermap) (m : CfMask)
    (ring kernel : List P.map.Dart) {x : P.map.Dart} :
    P.y.map.FaceBand
        (CfMask.selectMask m (ring.map P.yOld) (kernel.map P.yOld))
        (P.yOld x) ↔
      P.map.FaceBand (CfMask.selectMask m ring kernel) x := by
  rw [CfMask.selectMask_map]
  exact yOld_faceBand_iff P

theorem yOld_edgeReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.y.map.edge (P.yOld x) (P.yOld y) ↔
      PermReachable P.map.edge x y := by
  change PermReachable
      (Hypermap.extensionY P.map P.point).edge
      (Hypermap.extensionYOld P.map P.point x)
      (Hypermap.extensionYOld P.map P.point y) ↔
    PermReachable P.map.edge x y
  exact Hypermap.extensionYOld_edgeReachable_iff
    (G := P.map) (x0 := P.point)

theorem yOld_edgeReachable_of_edgeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.edge x y) :
    PermReachable P.y.map.edge (P.yOld x) (P.yOld y) :=
  (yOld_edgeReachable_iff P).2 hxy

@[simp]
theorem yOld_edge (P : PointedHypermap) (x : P.map.Dart) :
    P.yOld (P.map.edge x) = P.y.map.edge (P.yOld x) := by
  change Hypermap.extensionYOld P.map P.point (P.map.edge x) =
    (Hypermap.extensionY P.map P.point).edge
      (Hypermap.extensionYOld P.map P.point x)
  rfl

theorem yOld_node_of_ne_node_point_of_ne_point
    (P : PointedHypermap) {x : P.map.Dart}
    (hxNode : x ≠ P.map.node P.point)
    (hxPoint : x ≠ P.point) :
    P.yOld (P.map.node x) = P.y.map.node (P.yOld x) := by
  change Hypermap.extensionYOld P.map P.point (P.map.node x) =
    (Hypermap.extensionY P.map P.point).node
      (Hypermap.extensionYOld P.map P.point x)
  unfold Hypermap.extensionY Hypermap.extensionYOld
  change ExtDart.old (ExtDart.old (P.map.node x)) =
    Hypermap.ExtensionN.node (Hypermap.extensionU P.map P.point) ExtDart.new
      (ExtDart.old (ExtDart.old x))
  rw [Hypermap.ExtensionN.node_old]
  have hnode1 :
      (Hypermap.extensionU P.map P.point).node (ExtDart.old x) =
        ExtDart.old (P.map.node x) := by
    change Hypermap.ExtensionU.node P.map P.point (ExtDart.old x) =
      ExtDart.old (P.map.node x)
    rw [Hypermap.ExtensionU.node_old]
    simp [hxNode]
  have hnode2 :
      (Hypermap.extensionU P.map P.point).node
          ((Hypermap.extensionU P.map P.point).node (ExtDart.old x)) ≠
        ExtDart.new := by
    rw [hnode1]
    change Hypermap.ExtensionU.node P.map P.point
        (ExtDart.old (P.map.node x)) ≠ ExtDart.new
    rw [Hypermap.ExtensionU.node_old]
    have hne : P.map.node x ≠ P.map.node P.point := by
      intro h
      exact hxPoint (P.map.node.injective h)
    simp [hne]
  rw [if_neg hnode2, hnode1]
  simp
  rfl

theorem yOld_node_symm_of_ne_node_node_point_of_ne_node_point
    (P : PointedHypermap) {x : P.map.Dart}
    (hxNodeNode : x ≠ P.map.node (P.map.node P.point))
    (hxNode : x ≠ P.map.node P.point) :
    P.y.map.node.symm (P.yOld x) = P.yOld (P.map.node.symm x) := by
  have hcomm :=
    yOld_node_of_ne_node_point_of_ne_point P
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
  have hcomm' :
      P.yOld x =
        P.y.map.node (P.yOld (P.map.node.symm x)) := by
    simpa using hcomm
  rw [hcomm']
  exact P.y.map.node.symm_apply_apply (P.yOld (P.map.node.symm x))

theorem yOld_node_symm_node_node_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.y.map.node.symm
        (P.yOld (P.map.node (P.map.node P.point))) =
      P.y.map.node P.y.point := by
  have hnode :
      P.y.map.node (P.y.map.node P.y.point) =
        P.yOld (P.map.node (P.map.node P.point)) := by
    change (Hypermap.extensionY P.map P.point).node
        ((Hypermap.extensionY P.map P.point).node ExtDart.new) =
      Hypermap.extensionYOld P.map P.point
        (P.map.node (P.map.node P.point))
    rw [Hypermap.extensionY_node_new]
    unfold Hypermap.extensionY Hypermap.extensionYOld
    change Hypermap.ExtensionN.node
        (Hypermap.extensionU P.map P.point) ExtDart.new
        (ExtDart.old ExtDart.newEdge) =
      ExtDart.old (ExtDart.old (P.map.node (P.map.node P.point)))
    rw [Hypermap.ExtensionN.node_old]
    have hnotNew :
        ¬ (Hypermap.extensionU P.map P.point).node
            ((Hypermap.extensionU P.map P.point).node ExtDart.newEdge) =
          ExtDart.new := by
      change ¬ Hypermap.ExtensionU.node P.map P.point
          (Hypermap.ExtensionU.node P.map P.point ExtDart.newEdge) =
        ExtDart.new
      have hne : P.map.node (P.map.node P.point) ≠
          P.map.node P.point := by
        intro h
        exact hproper (P.map.node.injective h).symm
      simp [Hypermap.ExtensionU.node, Hypermap.ExtensionU.nodeToFun, hne]
    have hnodeNewEdge :
        (Hypermap.extensionU P.map P.point).node ExtDart.newEdge =
          ExtDart.old (P.map.node (P.map.node P.point)) :=
      rfl
    have hnotNewEdge :
        ¬ ExtDart.newEdge =
          (ExtDart.new : (Hypermap.extensionU P.map P.point).Dart) := by
      intro h
      cases h
    have hnotNew' :
        ¬ (Hypermap.extensionU P.map P.point).node
            (ExtDart.old (P.map.node (P.map.node P.point))) =
          ExtDart.new := by
      simpa [hnodeNewEdge] using hnotNew
    simp [hnotNew', hnodeNewEdge]
    rfl
  apply P.y.map.node.injective
  calc
    P.y.map.node
        (P.y.map.node.symm
          (P.yOld (P.map.node (P.map.node P.point)))) =
        P.yOld (P.map.node (P.map.node P.point)) :=
          P.y.map.node.apply_symm_apply _
    _ = P.y.map.node (P.y.map.node P.y.point) := hnode.symm

theorem y_iterate_node_symm_succ_point_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    ∀ i : Nat,
      (∀ k : Nat, k < i →
        iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point) →
      (∀ k : Nat, k < i →
        iteratePerm P.map.node.symm k P.point ≠
          P.map.node (P.map.node P.point)) →
      iteratePerm P.y.map.node.symm (i + 1) P.y.point =
        P.yOld (iteratePerm P.map.node.symm i P.point)
  | 0, _hnode, _hnodeNode => by
      simpa using y_node_symm_point_eq_yOld_point P hproper
  | i + 1, hnode, hnodeNode => by
      rw [iteratePerm_succ_right]
      rw [y_iterate_node_symm_succ_point_of_avoids_heads P hproper i
        (fun k hk => hnode k (Nat.lt_trans hk (Nat.lt_succ_self i)))
        (fun k hk => hnodeNode k (Nat.lt_trans hk (Nat.lt_succ_self i)))]
      rw [yOld_node_symm_of_ne_node_node_point_of_ne_node_point P
        (hnodeNode i (Nat.lt_succ_self i))
        (hnode i (Nat.lt_succ_self i))]
      rw [iteratePerm_succ_right]

theorem yOld_onRing_implies_onRing
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : P.y.OnRing (P.yOld x)) :
    P.OnRing x := by
  by_cases hnode : x = P.map.node P.point
  · rw [hnode]
    exact onRing_node_point P
  change PermReachable (Hypermap.extensionY P.map P.point).node
      ExtDart.new (Hypermap.extensionYOld P.map P.point x) at hx
  unfold Hypermap.extensionY Hypermap.extensionYOld at hx
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := Hypermap.extensionU P.map P.point)
      (x0 := ExtDart.new) hx
  have hlongU :
      (Hypermap.extensionU P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionU_long_new (G := P.map) P.point
  have hnodeU :
      (Hypermap.extensionU P.map P.point).node ExtDart.new =
        ExtDart.newEdge :=
    rfl
  have hfaceU :
      (Hypermap.extensionU P.map P.point).face
          ((Hypermap.extensionU P.map P.point).edge ExtDart.new) =
        ExtDart.old (P.map.node P.point) :=
    rfl
  have hold_ne_new :
      ExtDart.old x ≠
        (ExtDart.new :
          (Hypermap.extensionU P.map P.point).Dart) :=
    ExtDart.old_ne_new x
  have hold_ne_face :
      ExtDart.old x ≠
        (Hypermap.extensionU P.map P.point).face
          ((Hypermap.extensionU P.map P.point).edge ExtDart.new) := by
    rw [hfaceU]
    intro h
    exact hnode (ExtDart.old_injective h)
  have horbit :
      PermOrbit.of (Hypermap.extensionU P.map P.point).node ExtDart.newEdge =
        PermOrbit.of (Hypermap.extensionU P.map P.point).node
          (ExtDart.old x) := by
    have hpair := by
      simpa [Hypermap.extensionNNodeOrbitCode, hlongU, hnodeU, hold_ne_new,
        hfaceU] using hcode
    exact hpair.2
  have hU :
      PermReachable (Hypermap.extensionU P.map P.point).node
        ExtDart.newEdge (ExtDart.old x) :=
    Quotient.exact horbit
  have hproj :
      PermReachable P.map.node (P.map.node (P.map.node P.point)) x := by
    have hproj' :=
      (Hypermap.extensionU_nodeReachable_newEdge_iff_proj
        (G := P.map) P.point (y := ExtDart.old x)).1 hU
    simpa [Hypermap.extensionUNodeOrbitProj] using hproj'
  exact PermReachable.trans P.map.node
    (Hypermap.nodeReachable_two (G := P.map) P.point) hproj

theorem yOld_not_onRing_of_not_onRing
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.OnRing x) :
    ¬ P.y.OnRing (P.yOld x) := by
  intro hy
  exact hx (yOld_onRing_implies_onRing P hy)

theorem yOld_injective (P : PointedHypermap) :
    Function.Injective P.yOld := by
  intro x y hxy
  change Hypermap.extensionYOld P.map P.point x =
      Hypermap.extensionYOld P.map P.point y at hxy
  simp only [Hypermap.extensionYOld] at hxy
  injection hxy with hxy'
  injection hxy' with hxy''

theorem yOld_ringAdj_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    P.y.map.RingAdj (P.yOld x) (P.yOld y) ↔
      P.map.RingAdj x y := by
  change (Hypermap.extensionY P.map P.point).RingAdj
      (Hypermap.extensionYOld P.map P.point x)
      (Hypermap.extensionYOld P.map P.point y) ↔
    P.map.RingAdj x y
  exact Hypermap.extensionYOld_ringAdj_iff
    (G := P.map) (x0 := P.point)

theorem yOld_ringAdj_of_ringAdj
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.y.map.RingAdj (P.yOld x) (P.yOld y) :=
  (yOld_ringAdj_iff P).2 hxy

theorem y_ringAdj_point_old_iff_faceBand
    (P : PointedHypermap) {y : P.map.Dart} :
    P.y.map.RingAdj P.y.point (P.yOld y) ↔
      P.map.FaceBand [P.point, P.map.node P.point] y := by
  change (Hypermap.extensionY P.map P.point).RingAdj
      ExtDart.new (Hypermap.extensionYOld P.map P.point y) ↔
    P.map.FaceBand [P.point, P.map.node P.point] y
  exact Hypermap.extensionY_ringAdj_new_old_iff_faceBand
    (G := P.map) P.point

theorem y_ringAdj_point_old_iff_faceBand_coq
    (P : PointedHypermap) {y : P.map.Dart} :
    P.y.map.RingAdj P.y.point (P.yOld y) ↔
      P.map.FaceBand [P.map.node P.point, P.point] y := by
  change (Hypermap.extensionY P.map P.point).RingAdj
      ExtDart.new (Hypermap.extensionYOld P.map P.point y) ↔
    P.map.FaceBand [P.map.node P.point, P.point] y
  exact Hypermap.extensionY_ringAdj_new_old_iff_faceBand_coq
    (G := P.map) P.point

theorem yOld_ringAdj_point_iff_faceBand_coq_of_plain
    (P : PointedHypermap)
    (hplain : P.y.map.Plain) {x : P.map.Dart} :
    P.y.map.RingAdj (P.yOld x) P.y.point ↔
      P.map.FaceBand [P.map.node P.point, P.point] x := by
  constructor
  · intro h
    exact (y_ringAdj_point_old_iff_faceBand_coq P).1
      (Hypermap.RingAdj.symm_of_plain (G := P.y.map) hplain h)
  · intro h
    exact Hypermap.RingAdj.symm_of_plain (G := P.y.map) hplain
      ((y_ringAdj_point_old_iff_faceBand_coq P).2 h)

theorem y_not_faceReachable_point_old
    (P : PointedHypermap) (x : P.map.Dart) :
    ¬ PermReachable P.y.map.face P.y.point (P.yOld x) := by
  change ¬ PermReachable (Hypermap.extensionY P.map P.point).face
    ExtDart.new (Hypermap.extensionYOld P.map P.point x)
  exact Hypermap.extensionY_not_faceReachable_new_old
    (G := P.map) (x0 := P.point) x

theorem y_faceReachable_node_point_old_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    PermReachable P.y.map.face (P.y.map.node P.y.point) (P.yOld x) ↔
      PermReachable P.map.face (P.map.node P.point) x := by
  change PermReachable (Hypermap.extensionY P.map P.point).face
      ((Hypermap.extensionY P.map P.point).node ExtDart.new)
      (Hypermap.extensionYOld P.map P.point x) ↔
    PermReachable P.map.face (P.map.node P.point) x
  rw [Hypermap.extensionY_node_new]
  exact Hypermap.extensionY_faceReachable_old_newEdge_old_iff
    (G := P.map) (x0 := P.point)

theorem y_faceBand_point_node_point_old_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    P.y.map.FaceBand [P.y.point, P.y.map.node P.y.point] (P.yOld x) ↔
      PermReachable P.map.face (P.map.node P.point) x := by
  rw [Hypermap.FaceBand.pair]
  constructor
  · rintro (hpoint | hnode)
    · exact False.elim (y_not_faceReachable_point_old P x hpoint)
    · exact (y_faceReachable_node_point_old_iff P).1 hnode
  · intro hnode
    exact Or.inr ((y_faceReachable_node_point_old_iff P).2 hnode)

theorem yOld_forall_mem_not_faceBand_point_node_iff
    (P : PointedHypermap) (r : List P.map.Dart) :
    (∀ z : P.y.map.Dart,
      z ∈ r.map P.yOld →
        ¬ P.y.map.FaceBand [P.y.point, P.y.map.node P.y.point] z) ↔
      ∀ x : P.map.Dart,
        x ∈ r → ¬ PermReachable P.map.face (P.map.node P.point) x := by
  constructor
  · intro h x hx hface
    exact h (P.yOld x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      ((y_faceBand_point_node_point_old_iff P).2 hface)
  · intro h z hz hband
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact h x hx ((y_faceBand_point_node_point_old_iff P).1 hband)

theorem y_not_faceReachable_point_node_point
    (P : PointedHypermap) :
    ¬ PermReachable P.y.map.face P.y.point
      (P.y.map.node P.y.point) := by
  change ¬ PermReachable (Hypermap.extensionY P.map P.point).face
    ExtDart.new ((Hypermap.extensionY P.map P.point).node ExtDart.new)
  rw [Hypermap.extensionY_node_new]
  intro h
  have hproj :=
    (Hypermap.extensionY_faceReachable_new_iff_proj_eq_new
      (G := P.map) P.point (u := ExtDart.old ExtDart.newEdge)).1 h
  change Hypermap.extensionNFaceProj
      (Hypermap.extensionU P.map P.point) ExtDart.new
      (ExtDart.old ExtDart.newEdge) = ExtDart.new at hproj
  simp [Hypermap.extensionNFaceProj] at hproj

theorem y_ringAdj_point_node_point
    (P : PointedHypermap) :
    P.y.map.RingAdj P.y.point (P.y.map.node P.y.point) := by
  change (Hypermap.extensionY P.map P.point).RingAdj
    ExtDart.new ((Hypermap.extensionY P.map P.point).node ExtDart.new)
  rw [Hypermap.extensionY_node_new]
  refine ⟨ExtDart.old ExtDart.new, ?_, ?_⟩
  · unfold Hypermap.extensionY
    exact Hypermap.extensionN_faceReachable_new_old_x0
      (G := Hypermap.extensionU P.map P.point) ExtDart.new
  · exact PermReachable.refl (Hypermap.extensionY P.map P.point).face
      (ExtDart.old ExtDart.newEdge)

theorem y_faceBand_two_prefixes_map_point_iff
    (P : PointedHypermap) (b0 b1 : Bool) (r : List P.map.Dart) :
    P.y.map.FaceBand
        ((if b0 then [P.y.map.node P.y.point] else []) ++
          (if b1 then [P.y.point] else []) ++ r.map P.yOld)
        P.y.point ↔
      b1 = true := by
  rw [Hypermap.FaceBand.two_optional_prefixes]
  have hnode :
      ¬ PermReachable P.y.map.face (P.y.map.node P.y.point)
        P.y.point := by
    intro h
    exact y_not_faceReachable_point_node_point P
      (PermReachable.symm P.y.map.face h)
  have hold : ¬ P.y.map.FaceBand (r.map P.yOld) P.y.point := by
    rintro ⟨z, hz, hzp⟩
    rcases List.mem_map.mp hz with ⟨x, _hx, rfl⟩
    exact y_not_faceReachable_point_old P x
      (PermReachable.symm P.y.map.face hzp)
  change
      (b0 = true ∧
            PermReachable P.y.map.face (P.y.map.node P.y.point) P.y.point) ∨
        (b1 = true ∧
            PermReachable P.y.map.face P.y.point P.y.point) ∨
          P.y.map.FaceBand (r.map P.yOld) P.y.point ↔
        b1 = true
  constructor
  · rintro (h0 | htail)
    · exact False.elim (hnode h0.2)
    · rcases htail with h1 | htail
      · exact h1.1
      · exact False.elim (hold htail)
  · intro hb1
    exact Or.inr (Or.inl
      ⟨hb1, PermReachable.refl P.y.map.face P.y.point⟩)

theorem y_exists_map_ringAdj_point_iff
    (P : PointedHypermap) (r : List P.map.Dart) :
    (∃ y : P.y.map.Dart,
      y ∈ r.map P.yOld ∧ P.y.map.RingAdj P.y.point y) ↔
      ∃ x : P.map.Dart,
        x ∈ r ∧ P.map.FaceBand [P.point, P.map.node P.point] x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (y_ringAdj_point_old_iff_faceBand P).1 hxy⟩
  · rintro ⟨x, hx, hband⟩
    exact ⟨P.yOld x, List.mem_map.mpr ⟨x, hx, rfl⟩,
      (y_ringAdj_point_old_iff_faceBand P).2 hband⟩

theorem y_exists_two_prefixes_map_ringAdj_point_iff
    (P : PointedHypermap) (b0 b1 : Bool) (r : List P.map.Dart) :
    (∃ y : P.y.map.Dart,
      y ∈ (if b0 then [P.y.map.node P.y.point] else []) ++
          (if b1 then [P.y.point] else []) ++ r.map P.yOld ∧
        P.y.map.RingAdj P.y.point y) ↔
      b0 = true ∨
        (b1 = true ∧ P.y.map.RingAdj P.y.point P.y.point) ∨
          ∃ x : P.map.Dart,
            x ∈ r ∧ P.map.FaceBand [P.point, P.map.node P.point] x := by
  rw [Hypermap.RingAdj.exists_mem_two_optional_prefixes,
    y_exists_map_ringAdj_point_iff]
  constructor
  · rintro (h0 | htail)
    · exact Or.inl h0.1
    · rcases htail with h1 | hold
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hold)
  · rintro (h0 | htail)
    · exact Or.inl ⟨h0, y_ringAdj_point_node_point P⟩
    · rcases htail with h1 | hold
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hold)

theorem yOld_ringAdj_node_point_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    P.y.map.RingAdj (P.yOld x) (P.y.map.node P.y.point) ↔
      P.map.RingAdj x (P.map.node P.point) := by
  have hface :
      PermReachable P.y.map.face (P.y.map.node P.y.point)
        (P.yOld (P.map.node P.point)) :=
    (y_faceReachable_node_point_old_iff P).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  constructor
  · intro h
    have h' :=
      Hypermap.RingAdj.of_faceReachable_right (G := P.y.map) h hface
    exact (yOld_ringAdj_iff P).1 h'
  · intro h
    have h' : P.y.map.RingAdj (P.yOld x)
        (P.yOld (P.map.node P.point)) :=
      (yOld_ringAdj_iff P).2 h
    exact Hypermap.RingAdj.of_faceReachable_right (G := P.y.map) h'
      (PermReachable.symm P.y.map.face hface)

theorem y_exists_old_faceReachable_or_point
    (P : PointedHypermap) (u : P.y.map.Dart) :
    (∃ x : P.map.Dart,
      PermReachable P.y.map.face u (P.yOld x)) ∨
      PermReachable P.y.map.face P.y.point u := by
  change (∃ x : P.map.Dart,
      PermReachable (Hypermap.extensionY P.map P.point).face
        u (Hypermap.extensionYOld P.map P.point x)) ∨
    PermReachable (Hypermap.extensionY P.map P.point).face ExtDart.new u
  exact Hypermap.extensionY_exists_old_faceReachable_or_new
    (G := P.map) P.point u

theorem yOld_faceReachable_newEdge_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    PermReachable P.y.map.face (P.yOld x) ExtDart.newEdge ↔
      PermReachable P.map.face x P.point := by
  constructor
  · intro h
    exact PermReachable.symm P.map.face
      ((Hypermap.extensionY_faceReachable_newEdge_old_iff
        (G := P.map) P.point (y := x)).1
        (PermReachable.symm P.y.map.face h))
  · intro h
    exact PermReachable.symm P.y.map.face
      ((Hypermap.extensionY_faceReachable_newEdge_old_iff
        (G := P.map) P.point (y := x)).2
        (PermReachable.symm P.map.face h))

theorem yOld_faceReachable_node_point_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    PermReachable P.y.map.face (P.yOld x)
        (P.y.map.node P.y.point) ↔
      PermReachable P.map.face x (P.map.node P.point) := by
  constructor
  · intro h
    exact PermReachable.symm P.map.face
      ((y_faceReachable_node_point_old_iff P).1
        (PermReachable.symm P.y.map.face h))
  · intro h
    exact PermReachable.symm P.y.map.face
      ((y_faceReachable_node_point_old_iff P).2
        (PermReachable.symm P.map.face h))

theorem yOld_not_faceReachable_point
    (P : PointedHypermap) (x : P.map.Dart) :
    ¬ PermReachable P.y.map.face (P.yOld x) P.y.point := by
  intro h
  exact y_not_faceReachable_point_old P x
    (PermReachable.symm P.y.map.face h)

theorem yOld_not_faceReachable_old_new
    (P : PointedHypermap) (x : P.map.Dart) :
    ¬ PermReachable P.y.map.face (P.yOld x)
      (ExtDart.old ExtDart.new) := by
  intro h
  have hpointInner :
      PermReachable P.y.map.face P.y.point
        (ExtDart.old ExtDart.new) := by
    change PermReachable
      (Hypermap.extensionN (Hypermap.extensionU P.map P.point)
        ExtDart.new).face ExtDart.new (ExtDart.old ExtDart.new)
    exact Hypermap.extensionN_faceReachable_new_old_x0
      (G := Hypermap.extensionU P.map P.point) ExtDart.new
  exact yOld_not_faceReachable_point P x
    (PermReachable.trans P.y.map.face h
      (PermReachable.symm P.y.map.face hpointInner))

theorem yOld_exists_selectMask_ringAdj_iff
    (P : PointedHypermap) (m : CfMask)
    (ring kernel : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.y.map.Dart,
      y ∈ CfMask.selectMask m (ring.map P.yOld) (kernel.map P.yOld) ∧
        P.y.map.RingAdj (P.yOld x) y) ↔
      ∃ y : P.map.Dart,
        y ∈ CfMask.selectMask m ring kernel ∧ P.map.RingAdj x y := by
  exact OldDartTransport.exists_selectMask_map_iff
    P.yOld (yOld_ringAdj_iff P) m ring kernel x

theorem yOld_exists_map_ringAdj_iff
    (P : PointedHypermap) (r : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.y.map.Dart,
      y ∈ r.map P.yOld ∧ P.y.map.RingAdj (P.yOld x) y) ↔
      ∃ y : P.map.Dart, y ∈ r ∧ P.map.RingAdj x y := by
  exact OldDartTransport.exists_mem_map_iff
    P.yOld (yOld_ringAdj_iff P) r x

theorem yOld_faceBand_two_prefixes_map_iff
    (P : PointedHypermap) (b0 b1 : Bool)
    (a b : P.y.map.Dart) (r : List P.map.Dart) {x : P.map.Dart} :
    P.y.map.FaceBand
        ((if b0 then [a] else []) ++ (if b1 then [b] else []) ++
          r.map P.yOld)
        (P.yOld x) ↔
      (b0 = true ∧ PermReachable P.y.map.face a (P.yOld x)) ∨
        (b1 = true ∧ PermReachable P.y.map.face b (P.yOld x)) ∨
          P.map.FaceBand r x := by
  rw [Hypermap.FaceBand.two_optional_prefixes,
    yOld_faceBand_iff P]

theorem yOld_exists_two_prefixes_map_ringAdj_iff
    (P : PointedHypermap) (b0 b1 : Bool)
    (a b : P.y.map.Dart) (r : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.y.map.Dart,
      y ∈ (if b0 then [a] else []) ++ (if b1 then [b] else []) ++
          r.map P.yOld ∧
        P.y.map.RingAdj (P.yOld x) y) ↔
      (b0 = true ∧ P.y.map.RingAdj (P.yOld x) a) ∨
        (b1 = true ∧ P.y.map.RingAdj (P.yOld x) b) ∨
          ∃ y : P.map.Dart, y ∈ r ∧ P.map.RingAdj x y := by
  rw [Hypermap.RingAdj.exists_mem_two_optional_prefixes,
    yOld_exists_map_ringAdj_iff P r]

theorem yOld_lift_maskAdjSound
    (P : PointedHypermap) {adj orig : List P.map.Dart}
    (hsound :
      ∀ x : P.map.Dart,
        P.map.FaceBand adj x ↔
          ∃ y : P.map.Dart, y ∈ orig ∧ P.map.RingAdj x y)
    {x : P.map.Dart} :
    P.y.map.FaceBand (adj.map P.yOld) (P.yOld x) ↔
      ∃ y : P.y.map.Dart,
        y ∈ orig.map P.yOld ∧ P.y.map.RingAdj (P.yOld x) y := by
  exact OldDartTransport.liftFaceBandRingAdj P.yOld
    (fun r => yOld_faceBand_iff P) (yOld_ringAdj_iff P) hsound


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
