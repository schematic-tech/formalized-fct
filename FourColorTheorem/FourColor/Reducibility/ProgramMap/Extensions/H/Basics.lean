import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.Y
import Schematic.Math.GraphTheory.Embedding.DartExtension.H.RingAdjacency

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Coq `ecpH`, using the checked composite `Y` then `N` constructor. -/
def h (P : PointedHypermap) : PointedHypermap where
  map := Hypermap.extensionH P.map P.point
  point := ExtDart.new

@[simp]
theorem h_map (P : PointedHypermap) :
    P.h.map = Hypermap.extensionH P.map P.point :=
  rfl

@[simp]
theorem h_point (P : PointedHypermap) :
    P.h.point = ExtDart.new :=
  rfl

theorem h_properRingHead_of_proper
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.h.ProperRingHead := by
  intro hEq
  have hyLong :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper (G := P.map) P.point hproper
  change ExtDart.new =
      (Hypermap.extensionH P.map P.point).node ExtDart.new at hEq
  unfold Hypermap.extensionH Hypermap.extensionN at hEq
  change ExtDart.new =
      Hypermap.ExtensionN.node (Hypermap.extensionY P.map P.point)
        ExtDart.new ExtDart.new at hEq
  rw [Hypermap.ExtensionN.node_new, if_pos hyLong] at hEq
  cases hEq

theorem h_longRingHead_of_proper_long
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead) :
    P.h.LongRingHead :=
  Hypermap.extensionH_long_new_of_proper_long
    (G := P.map) P.point hproper hlong

theorem h_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.h.Plain :=
  Hypermap.extensionH_plain (G := P.map) P.point hP

/-- Exact Coq `bridgeless_ecpH`: properness alone suffices. -/
theorem h_bridgeless_of_proper
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hP : P.Bridgeless) :
    P.h.Bridgeless :=
  Hypermap.extensionH_bridgeless_of_proper
    (G := P.map) P.point hproper hP

theorem h_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.h.Connected :=
  Hypermap.extensionH_connected (G := P.map) P.point hP

/-- Old-dart embedding into the semantic `H` construction, matching Coq's
`icpH`. -/
def hOld (P : PointedHypermap) (x : P.map.Dart) : P.h.map.Dart := by
  change (Hypermap.extensionH P.map P.point).Dart
  exact Hypermap.extensionHOld P.map P.point x

theorem hOld_ne_point
    (P : PointedHypermap) (x : P.map.Dart) :
    P.hOld x ≠ P.h.point := by
  change Hypermap.extensionHOld P.map P.point x ≠ ExtDart.new
  simp [Hypermap.extensionHOld]

theorem hOld_ne_node_point
    (P : PointedHypermap) (x : P.map.Dart) :
    P.hOld x ≠ P.h.map.node P.h.point := by
  change Hypermap.extensionHOld P.map P.point x ≠
    (Hypermap.extensionH P.map P.point).node ExtDart.new
  unfold Hypermap.extensionH Hypermap.extensionN Hypermap.extensionHOld
  change ExtDart.old (Hypermap.extensionYOld P.map P.point x) ≠
    Hypermap.ExtensionN.node (Hypermap.extensionY P.map P.point)
      ExtDart.new ExtDart.new
  by_cases hlong :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new
  · rw [Hypermap.ExtensionN.node_new, if_pos hlong]
    intro h
    cases h
  · rw [Hypermap.ExtensionN.node_new, if_neg hlong]
    intro h
    cases h

theorem h_node_symm_point_eq_hOld_node_symm_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead) :
    P.h.map.node.symm P.h.point = P.hOld (P.map.node.symm P.point) := by
  change (Hypermap.extensionH P.map P.point).node.symm ExtDart.new =
    Hypermap.extensionHOld P.map P.point (P.map.node.symm P.point)
  unfold Hypermap.extensionH Hypermap.extensionN Hypermap.extensionHOld
  change Hypermap.ExtensionN.nodeInvFun
      (Hypermap.extensionY P.map P.point) ExtDart.new ExtDart.new =
    ExtDart.old (Hypermap.extensionYOld P.map P.point
      (P.map.node.symm P.point))
  have hlongY :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper (G := P.map) P.point hproper
  have hnodeY :
      (Hypermap.extensionY P.map P.point).node ExtDart.new =
        ExtDart.old ExtDart.newEdge :=
    Hypermap.extensionY_node_new (G := P.map) P.point
  have hnodeSymmY :
      (Hypermap.extensionY P.map P.point).node.symm ExtDart.new =
        Hypermap.extensionYOld P.map P.point P.point := by
    exact y_node_symm_point_eq_yOld_point P hproper
  have hpoint_ne_node_node :
      P.point ≠ P.map.node (P.map.node P.point) := by
    intro h
    apply hlong
    calc
      P.map.face (P.map.edge P.point) = P.map.node.symm P.point := by
        rw [Hypermap.face_edge_eq_node_symm]
      _ = P.map.node P.point := by
        apply P.map.node.injective
        simpa using h
  have hnodeSymmYOld :
      (Hypermap.extensionY P.map P.point).node.symm
          (Hypermap.extensionYOld P.map P.point P.point) =
        Hypermap.extensionYOld P.map P.point
          (P.map.node.symm P.point) := by
    exact yOld_node_symm_of_ne_node_node_point_of_ne_node_point
      P hpoint_ne_node_node hproper
  simp [Hypermap.ExtensionN.nodeInvFun, hlongY, hnodeSymmY,
    hnodeSymmYOld]

theorem hOld_faceReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.h.map.face (P.hOld x) (P.hOld y) ↔
      PermReachable P.map.face x y := by
  change PermReachable
      (Hypermap.extensionH P.map P.point).face
      (Hypermap.extensionHOld P.map P.point x)
      (Hypermap.extensionHOld P.map P.point y) ↔
    PermReachable P.map.face x y
  exact Hypermap.extensionHOld_faceReachable_iff
    (G := P.map) (x0 := P.point)

theorem hOld_faceReachable_of_faceReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.h.map.face (P.hOld x) (P.hOld y) :=
  (hOld_faceReachable_iff P).2 hxy

theorem h_faceReachable_face_edge_point_old_iff
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    {x : P.map.Dart} :
    PermReachable P.h.map.face
      (P.h.map.face (P.h.map.edge P.h.point)) (P.hOld x) ↔
      PermReachable P.map.face (P.map.face (P.map.edge P.point)) x := by
  let H := Hypermap.extensionH P.map P.point
  change PermReachable H.face (H.face (H.edge ExtDart.new))
        (Hypermap.extensionHOld P.map P.point x) ↔
      PermReachable P.map.face (P.map.face (P.map.edge P.point)) x
  constructor
  · intro h
    have hstep :
        PermReachable H.face ExtDart.newEdge (H.face (H.edge ExtDart.new)) := by
      simpa [H] using PermReachable.forward H.face ExtDart.newEdge
    exact
      (Hypermap.extensionH_faceReachable_newEdge_old_iff_face_edge_of_proper_long
        (G := P.map) P.point hproper hlong).1
        (PermReachable.trans H.face hstep h)
  · intro h
    have hnew :
        PermReachable H.face ExtDart.newEdge
          (Hypermap.extensionHOld P.map P.point x) :=
      (Hypermap.extensionH_faceReachable_newEdge_old_iff_face_edge_of_proper_long
        (G := P.map) P.point hproper hlong).2 h
    have hback :
        PermReachable H.face (H.face (H.edge ExtDart.new)) ExtDart.newEdge := by
      simpa [H] using
        PermReachable.symm H.face
          (PermReachable.forward H.face ExtDart.newEdge)
    exact PermReachable.trans H.face hback hnew

theorem hOld_faceBand_iff
    (P : PointedHypermap) {r : List P.map.Dart} {x : P.map.Dart} :
    P.h.map.FaceBand (r.map P.hOld) (P.hOld x) ↔
      P.map.FaceBand r x := by
  exact OldDartTransport.faceBand_map_iff
    P.hOld (hOld_faceReachable_iff P) r x

theorem hOld_faceBand_of_faceBand
    (P : PointedHypermap) {r : List P.map.Dart} {x : P.map.Dart}
    (hx : P.map.FaceBand r x) :
    P.h.map.FaceBand (r.map P.hOld) (P.hOld x) :=
  (hOld_faceBand_iff P).2 hx

theorem hOld_faceBand_selectMask_iff
    (P : PointedHypermap) (m : CfMask)
    (ring kernel : List P.map.Dart) {x : P.map.Dart} :
    P.h.map.FaceBand
        (CfMask.selectMask m (ring.map P.hOld) (kernel.map P.hOld))
        (P.hOld x) ↔
      P.map.FaceBand (CfMask.selectMask m ring kernel) x := by
  rw [CfMask.selectMask_map]
  exact hOld_faceBand_iff P

theorem hOld_edgeReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.h.map.edge (P.hOld x) (P.hOld y) ↔
      PermReachable P.map.edge x y := by
  change PermReachable
      (Hypermap.extensionH P.map P.point).edge
      (Hypermap.extensionHOld P.map P.point x)
      (Hypermap.extensionHOld P.map P.point y) ↔
    PermReachable P.map.edge x y
  exact Hypermap.extensionHOld_edgeReachable_iff
    (G := P.map) (x0 := P.point)

theorem hOld_edgeReachable_of_edgeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.edge x y) :
    PermReachable P.h.map.edge (P.hOld x) (P.hOld y) :=
  (hOld_edgeReachable_iff P).2 hxy

end Schematic.Math.GraphTheory.FourColor.PointedHypermap
