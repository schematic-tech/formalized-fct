import FourColorTheorem.FourColor.Reducibility.ProgramMap.Pointed

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Coq `ecpU`, the primitive constructor that adds a new singleton face. -/
def u (P : PointedHypermap) : PointedHypermap where
  map := Hypermap.extensionU P.map P.point
  point := ExtDart.new

@[simp]
theorem u_map (P : PointedHypermap) :
    P.u.map = Hypermap.extensionU P.map P.point :=
  rfl

@[simp]
theorem u_point (P : PointedHypermap) :
    P.u.point = ExtDart.new :=
  rfl

theorem u_properRingHead (P : PointedHypermap) :
    P.u.ProperRingHead := by
  intro h
  change ExtDart.new =
      (Hypermap.extensionU P.map P.point).node ExtDart.new at h
  unfold Hypermap.extensionU at h
  change ExtDart.new =
      Hypermap.ExtensionU.node P.map P.point ExtDart.new at h
  rw [Hypermap.ExtensionU.node_new] at h
  cases h

theorem u_longRingHead (P : PointedHypermap) :
    P.u.LongRingHead :=
  Hypermap.extensionU_long_new (G := P.map) P.point

theorem u_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.u.Plain :=
  Hypermap.extensionU_plain (G := P.map) P.point hP

theorem u_bridgeless
    (P : PointedHypermap)
    (hP : P.Bridgeless) :
    P.u.Bridgeless :=
  Hypermap.extensionU_bridgeless (G := P.map) P.point hP

theorem u_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.u.Connected :=
  Hypermap.extensionU_connected (G := P.map) P.point hP

/-- Old-dart embedding into the semantic `U` construction, matching Coq's
`icpU`. -/
def uOld (P : PointedHypermap) (x : P.map.Dart) : P.u.map.Dart :=
  ExtDart.old x

@[simp]
theorem uOld_apply (P : PointedHypermap) (x : P.map.Dart) :
    P.uOld x = ExtDart.old x :=
  rfl

theorem uOld_faceReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.u.map.face (P.uOld x) (P.uOld y) ↔
      PermReachable P.map.face x y := by
  change PermReachable
      (Hypermap.extensionU P.map P.point).face
      (ExtDart.old x) (ExtDart.old y) ↔
    PermReachable P.map.face x y
  exact Hypermap.extensionU_old_faceReachable_iff
    (G := P.map) (x0 := P.point)

theorem uOld_faceReachable_of_faceReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable P.u.map.face (P.uOld x) (P.uOld y) :=
  (uOld_faceReachable_iff P).2 hxy

theorem uOld_edgeReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.u.map.edge (P.uOld x) (P.uOld y) ↔
      PermReachable P.map.edge x y := by
  change PermReachable
      (Hypermap.extensionU P.map P.point).edge
      (ExtDart.old x) (ExtDart.old y) ↔
    PermReachable P.map.edge x y
  exact Hypermap.extensionU_old_edgeReachable_iff
    (G := P.map) (x0 := P.point)

theorem uOld_edgeReachable_of_edgeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.edge x y) :
    PermReachable P.u.map.edge (P.uOld x) (P.uOld y) :=
  (uOld_edgeReachable_iff P).2 hxy

@[simp]
theorem uOld_edge (P : PointedHypermap) (x : P.map.Dart) :
    P.uOld (P.map.edge x) = P.u.map.edge (P.uOld x) := by
  rfl

theorem uOld_injective (P : PointedHypermap) :
    Function.Injective P.uOld := by
  intro x y hxy
  simp only [uOld] at hxy
  injection hxy with hxy'

theorem uOld_nodeReachable_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable P.u.map.node (P.uOld x) (P.uOld y) ↔
      PermReachable P.map.node x y := by
  change PermReachable
      (Hypermap.extensionU P.map P.point).node
      (ExtDart.old x) (ExtDart.old y) ↔
    PermReachable P.map.node x y
  exact Hypermap.extensionU_old_nodeReachable_iff
    (G := P.map) (x0 := P.point)

theorem uOld_nodeReachable_of_nodeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.node x y) :
    PermReachable P.u.map.node (P.uOld x) (P.uOld y) :=
  (uOld_nodeReachable_iff P).2 hxy

theorem uOld_onRing_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    P.u.OnRing (P.uOld x) ↔ P.OnRing x := by
  change PermReachable (Hypermap.extensionU P.map P.point).node
      ExtDart.new (ExtDart.old x) ↔
    PermReachable P.map.node P.point x
  rw [Hypermap.extensionU_nodeReachable_new_iff_proj]
  change PermReachable P.map.node (P.map.node P.point) x ↔
    PermReachable P.map.node P.point x
  constructor
  · intro h
    exact PermReachable.trans P.map.node
      (PermReachable.forward P.map.node P.point) h
  · intro h
    exact PermReachable.trans P.map.node
      (PermReachable.symm P.map.node
        (PermReachable.forward P.map.node P.point)) h

theorem uOld_not_onRing_iff
    (P : PointedHypermap) {x : P.map.Dart} :
    ¬ P.u.OnRing (P.uOld x) ↔ ¬ P.OnRing x := by
  rw [uOld_onRing_iff]

theorem uOld_node_of_ne_node_point
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : x ≠ P.map.node P.point) :
    P.uOld (P.map.node x) = P.u.map.node (P.uOld x) := by
  change ExtDart.old (P.map.node x) =
    Hypermap.ExtensionU.node P.map P.point (ExtDart.old x)
  rw [Hypermap.ExtensionU.node_old]
  simp [hx]

theorem u_quasicubic
    (P : PointedHypermap)
    (hP : P.Quasicubic) :
    P.u.Quasicubic := by
  intro z hz
  cases z with
  | new =>
      exact (hz (onRing_point P.u)).elim
  | newEdge =>
      have hring : P.u.OnRing ExtDart.newEdge :=
        PermReachable.forward P.u.map.node P.u.point
      exact (hz hring).elim
  | old x =>
      have hx : ¬ P.OnRing x :=
        (uOld_not_onRing_iff P).mp hz
      have hnx : ¬ P.OnRing (P.map.node x) :=
        not_onRing_of_nodeReachable P hx
          (PermReachable.forward P.map.node x)
      have hnnx : ¬ P.OnRing (P.map.node (P.map.node x)) :=
        not_onRing_of_nodeReachable P hnx
          (PermReachable.forward P.map.node (P.map.node x))
      have hxRegular : x ≠ P.map.node P.point := by
        intro h
        exact hx (h ▸ onRing_node_point P)
      have hnxRegular : P.map.node x ≠ P.map.node P.point := by
        intro h
        exact hnx (h ▸ onRing_node_point P)
      have hnnxRegular :
          P.map.node (P.map.node x) ≠ P.map.node P.point := by
        intro h
        exact hnnx (h ▸ onRing_node_point P)
      have hxCubic := hP x hx
      constructor
      · change P.u.map.node
            (P.u.map.node (P.u.map.node (P.uOld x))) = P.uOld x
        rw [← uOld_node_of_ne_node_point P hxRegular,
          ← uOld_node_of_ne_node_point P hnxRegular,
          ← uOld_node_of_ne_node_point P hnnxRegular,
          hxCubic.1]
      · intro hfixed
        apply hxCubic.2
        apply uOld_injective P
        rw [uOld_node_of_ne_node_point P hxRegular]
        exact hfixed


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
