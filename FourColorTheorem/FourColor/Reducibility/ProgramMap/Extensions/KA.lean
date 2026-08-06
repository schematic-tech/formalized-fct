import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.N

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Coq `ecpK`: `ecpR 1 (ecpN ecpR')`.  This semantic object is kept
separate from `step?` until the remaining `ecpN` bridgeless/contraction facts
are available. -/
noncomputable def k (P : PointedHypermap) : PointedHypermap :=
  (P.reverseRotate.n).rotate 1

@[simp]
theorem k_map (P : PointedHypermap) :
    P.k.map = Hypermap.extensionN P.map (P.map.node P.point) :=
  rfl

theorem k_properRingHead_of_long
    (P : PointedHypermap)
    (hlong : P.LongRingHead) :
    P.k.ProperRingHead := by
  have hrevLong : P.reverseRotate.LongRingHead :=
    reverseRotate_longRingHead P hlong
  have hnProper : P.reverseRotate.n.ProperRingHead :=
    n_properRingHead_of_long P.reverseRotate hrevLong
  exact rotate_properRingHead 1 P.reverseRotate.n hnProper

theorem k_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.k.Plain := by
  exact rotate_plain 1 P.reverseRotate.n
    (n_plain P.reverseRotate (reverseRotate_plain P hP))

theorem k_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.k.Connected := by
  exact rotate_connected 1 P.reverseRotate.n
    (n_connected P.reverseRotate (reverseRotate_connected P hP))

/-- Old-dart embedding into the semantic `K` construction, matching Coq's
`icpK` after the definitional `ecpR 1` rotation is erased from the map. -/
def kOld (P : PointedHypermap) (x : P.map.Dart) : P.k.map.Dart := by
  change (Hypermap.extensionN P.map (P.map.node P.point)).Dart
  exact Hypermap.extensionNOld P.map (P.map.node P.point) x

theorem kOld_edgeReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.k.map.edge (P.kOld x) (P.kOld y) ↔
      PermReachable P.map.edge x y := by
  change PermReachable
      (Hypermap.extensionN P.map (P.map.node P.point)).edge
      (Hypermap.extensionNOld P.map (P.map.node P.point) x)
      (Hypermap.extensionNOld P.map (P.map.node P.point) y) ↔
    PermReachable P.map.edge x y
  exact Hypermap.extensionNOld_edgeReachable_iff
    (G := P.map) (x0 := P.map.node P.point)

theorem kOld_edgeReachable_of_edgeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.edge x y) :
    PermReachable P.k.map.edge (P.kOld x) (P.kOld y) :=
  (kOld_edgeReachable_iff P).2 hxy

theorem kOld_faceReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.k.map.face (P.kOld x) (P.kOld y) ↔
      PermReachable P.map.face x y := by
  change PermReachable
      (Hypermap.extensionN P.map (P.map.node P.point)).face
      (Hypermap.extensionNOld P.map (P.map.node P.point) x)
      (Hypermap.extensionNOld P.map (P.map.node P.point) y) ↔
    PermReachable P.map.face x y
  exact Hypermap.extensionNOld_faceReachable_iff
    (G := P.map) (x0 := P.map.node P.point)

theorem kOld_faceReachable_of_faceReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.k.map.face (P.kOld x) (P.kOld y) :=
  (kOld_faceReachable_iff P).2 hxy

theorem kOld_ringAdj_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    P.k.map.RingAdj (P.kOld x) (P.kOld y) ↔
      P.map.RingAdj x y ∨
        (PermReachable P.map.face (P.map.edge P.point) x ∧
          PermReachable P.map.face (P.map.node P.point) y) ∨
        (PermReachable P.map.face (P.map.edge P.point) y ∧
          PermReachable P.map.face (P.map.node P.point) x) := by
  simpa [kOld, k, reverseRotate, n, rotate,
    Hypermap.face_edge_eq_node_symm] using
    (Hypermap.extensionNOld_ringAdj_iff
      (G := P.map) (x0 := P.map.node P.point) (x := x) (y := y))

theorem kOld_ringAdj_of_ringAdj
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.k.map.RingAdj (P.kOld x) (P.kOld y) :=
  (kOld_ringAdj_iff P).2 (Or.inl hxy)

theorem kOld_reachable_of_reachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.Reachable x y) :
    P.k.map.Reachable (P.kOld x) (P.kOld y) := by
  change (Hypermap.extensionN P.map (P.map.node P.point)).Reachable
    (Hypermap.extensionNOld P.map (P.map.node P.point) x)
    (Hypermap.extensionNOld P.map (P.map.node P.point) y)
  exact Hypermap.extensionN_old_reachable_of_reachable
    (G := P.map) (x0 := P.map.node P.point) hxy

/-- Coq `ecpA`: merge the two neighboring ring nodes around the current
pointer.  As with `K`, this semantic object is kept separate from `step?`
until its face/adjacency preservation interface is fully ported. -/
noncomputable def a (P : PointedHypermap) : PointedHypermap where
  map := Hypermap.extensionA P.map P.point
  point :=
    (Hypermap.extensionA P.map P.point).face
      ((Hypermap.extensionA P.map P.point).edge
        (P.map.face (P.map.edge P.point)))

@[simp]
theorem a_map (P : PointedHypermap) :
    P.a.map = Hypermap.extensionA P.map P.point :=
  rfl

@[simp]
theorem a_point (P : PointedHypermap) :
    P.a.point =
      (Hypermap.extensionA P.map P.point).face
        ((Hypermap.extensionA P.map P.point).edge
          (P.map.face (P.map.edge P.point))) :=
  rfl

/-- The ring of `ecpA` starts at the third dart of the source ring. -/
theorem a_node_point_eq_face_edge (P : PointedHypermap) :
    P.a.map.node P.a.point = P.map.face (P.map.edge P.point) := by
  change (Hypermap.extensionA P.map P.point).node
    ((Hypermap.extensionA P.map P.point).face
      ((Hypermap.extensionA P.map P.point).edge
        (P.map.face (P.map.edge P.point)))) = _
  rw [Hypermap.node_face_edge]

theorem a_node_symm_apply_of_ne
    (P : PointedHypermap) {x : P.map.Dart}
    (hx0 : x ≠ P.point)
    (hxnn : x ≠ P.map.node (P.map.node P.point)) :
    P.a.map.node.symm x = P.map.node.symm x := by
  change (Hypermap.extensionA P.map P.point).node.symm x = _
  exact Hypermap.extensionA_node_symm_apply_of_ne P.map P.point hx0 hxnn

/-- Identity embedding into the semantic `A` construction, matching Coq's
`icpA`. -/
noncomputable def aOld (P : PointedHypermap) (x : P.map.Dart) : P.a.map.Dart := by
  change (Hypermap.extensionA P.map P.point).Dart
  exact Hypermap.extensionAOld P.map P.point x

@[simp]
theorem aOld_apply (P : PointedHypermap) (x : P.map.Dart) :
    P.aOld x = x :=
  rfl

theorem aOld_faceReachable_of_faceReachable_of_faceReachable_edge_node
    (P : PointedHypermap)
    (h : PermReachable P.map.face (P.map.edge P.point) (P.map.node P.point))
    {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.a.map.face (P.aOld x) (P.aOld y) := by
  exact Hypermap.extensionA_faceReachable_of_faceReachable_of_faceReachable_edge_node
    (G := P.map) P.point h hxy

theorem aOld_ringAdj_of_ringAdj_of_faceReachable_edge_node
    (P : PointedHypermap)
    (h : PermReachable P.map.face (P.map.edge P.point) (P.map.node P.point))
    {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.a.map.RingAdj (P.aOld x) (P.aOld y) := by
  exact Hypermap.extensionA_ringAdj_of_ringAdj_of_faceReachable_edge_node
    (G := P.map) P.point h hxy

theorem aOld_faceReachable_of_faceReachable
    (P : PointedHypermap)
    {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.a.map.face (P.aOld x) (P.aOld y) := by
  exact Hypermap.extensionA_faceReachable_of_faceReachable
    (G := P.map) P.point hxy

theorem aOld_ringAdj_of_ringAdj
    (P : PointedHypermap)
    {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.a.map.RingAdj (P.aOld x) (P.aOld y) := by
  exact Hypermap.extensionA_ringAdj_of_ringAdj
    (G := P.map) P.point hxy

theorem aOld_edge_faceReachable_edge
    (P : PointedHypermap) (x : P.map.Dart) :
    PermReachable P.a.map.face (P.a.map.edge (P.aOld x))
      (P.map.edge x) := by
  exact Hypermap.extensionA_edge_faceReachable_edge
    (G := P.map) P.point x

theorem aOld_faceReachable_iff_old_or_faceBand_pair
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.a.map.face (P.aOld x) (P.aOld y) ↔
      PermReachable P.map.face x y ∨
        (P.map.FaceBand
            [P.map.face (P.map.edge P.point), P.map.node P.point] x ∧
          P.map.FaceBand
            [P.map.face (P.map.edge P.point), P.map.node P.point] y) := by
  exact Hypermap.extensionA_faceReachable_iff_old_or_faceBand_pair
    (G := P.map) (x0 := P.point)

theorem aOld_node_step_oldReachable
    (P : PointedHypermap) (x : P.map.Dart) :
    PermReachable P.map.node x (P.a.map.node (P.aOld x)) := by
  exact Hypermap.extensionA_node_step_oldReachable
    (G := P.map) P.point x

theorem aOld_nodeReachable_implies_nodeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.a.map.node (P.aOld x) (P.aOld y)) :
    PermReachable P.map.node x y := by
  exact Hypermap.extensionA_nodeReachable_implies_nodeReachable
    (G := P.map) (x0 := P.point) hxy

theorem aOld_nodeReachable_of_iterate_regular
    (P : PointedHypermap) {x y : P.map.Dart} {n : ℕ}
    (hiter : (P.map.node : P.map.Dart → P.map.Dart)^[n] x = y)
    (hxnode : ∀ k : ℕ, k < n →
      (P.map.node : P.map.Dart → P.map.Dart)^[k] x ≠ P.map.node P.point)
    (hxface : ∀ k : ℕ, k < n →
      (P.map.node : P.map.Dart → P.map.Dart)^[k] x ≠
        P.map.face (P.map.edge P.point)) :
    PermReachable P.a.map.node (P.aOld x) (P.aOld y) := by
  exact Hypermap.extensionA_nodeReachable_of_iterate_regular
    (G := P.map) (x0 := P.point) hiter hxnode hxface


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
