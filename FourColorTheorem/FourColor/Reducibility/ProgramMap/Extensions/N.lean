import FourColorTheorem.FourColor.Reducibility.ProgramMap.Pointed

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Coq `ecpN`: close the next outer ring corner. -/
def n (P : PointedHypermap) : PointedHypermap where
  map := Hypermap.extensionN P.map P.point
  point := ExtDart.new

@[simp]
theorem n_map (P : PointedHypermap) :
    P.n.map = Hypermap.extensionN P.map P.point :=
  rfl

@[simp]
theorem n_point (P : PointedHypermap) :
    P.n.point = ExtDart.new :=
  rfl

theorem n_properRingHead_of_long
    (P : PointedHypermap)
    (hlong : P.LongRingHead) :
    P.n.ProperRingHead := by
  have hlong' : P.map.LongRingHead P.point := hlong
  intro hEq
  change ExtDart.new =
      (Hypermap.extensionN P.map P.point).node ExtDart.new at hEq
  unfold Hypermap.extensionN at hEq
  change ExtDart.new =
      Hypermap.ExtensionN.node P.map P.point ExtDart.new at hEq
  rw [Hypermap.ExtensionN.node_new, if_pos hlong'] at hEq
  cases hEq

theorem n_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.n.Plain :=
  Hypermap.extensionN_plain (G := P.map) P.point hP

theorem n_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.n.Connected :=
  Hypermap.extensionN_connected (G := P.map) P.point hP

/-- Old-dart inclusion for the primitive `N` constructor. -/
def nOld (P : PointedHypermap) (x : P.map.Dart) : P.n.map.Dart :=
  ExtDart.old x

theorem nOld_injective (P : PointedHypermap) :
    Function.Injective P.nOld := by
  intro x y h
  exact ExtDart.old_injective h

theorem nOld_node_of_regular
    (P : PointedHypermap) {x : P.map.Dart}
    (hxPoint : x ≠ P.point)
    (hxTwo : P.map.node (P.map.node x) ≠ P.point) :
    P.nOld (P.map.node x) = P.n.map.node (P.nOld x) := by
  change ExtDart.old (P.map.node x) =
    Hypermap.ExtensionN.node P.map P.point (ExtDart.old x)
  simp [Hypermap.ExtensionN.node, Hypermap.ExtensionN.nodeToFun,
    hxPoint, hxTwo]

private theorem n_onRing_nOld_of_long_of_onRing
    (P : PointedHypermap)
    (hlong : P.LongRingHead)
    {x : P.map.Dart}
    (hxPoint : x ≠ P.point)
    (hxFace : x ≠ P.map.face (P.map.edge P.point))
    (hx : P.OnRing x) :
    P.n.OnRing (P.nOld x) := by
  change PermReachable (Hypermap.extensionN P.map P.point).node
    ExtDart.new (ExtDart.old x)
  have horbit :
      PermOrbit.of P.map.node (P.map.node P.point) =
        PermOrbit.of P.map.node x := by
    apply PermOrbit.of_eq_of
    have hback :
        PermReachable P.map.node (P.map.node P.point) P.point := by
      simpa using
        (PermReachable.backward P.map.node (P.map.node P.point))
    exact PermReachable.trans P.map.node
      hback hx
  have heq :
      PermOrbit.of (Hypermap.extensionN P.map P.point).node ExtDart.new =
        PermOrbit.of (Hypermap.extensionN P.map P.point).node
          (ExtDart.old x) := by
    have hlong' : P.map.LongRingHead P.point := hlong
    let e := Hypermap.extensionNNodeOrbitEquivOfLong
      (G := P.map) P.point hlong'
    apply e.injective
    change Hypermap.extensionNNodeOrbitCode P.map P.point ExtDart.new =
      Hypermap.extensionNNodeOrbitCode P.map P.point (ExtDart.old x)
    simp [Hypermap.extensionNNodeOrbitCode, hlong', hxPoint, hxFace,
      horbit]
  exact Quotient.exact heq

private theorem nOld_not_onRing_source_or_exception
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.n.OnRing (P.nOld x)) :
    ¬ P.OnRing x ∨ x = P.point ∨
      x = P.map.face (P.map.edge P.point) := by
  by_cases hxRing : P.OnRing x
  · right
    by_cases hlong : P.LongRingHead
    · by_cases hxPoint : x = P.point
      · exact Or.inl hxPoint
      · by_cases hxFace : x = P.map.face (P.map.edge P.point)
        · exact Or.inr hxFace
        · exact (hx (n_onRing_nOld_of_long_of_onRing
            P hlong hxPoint hxFace hxRing)).elim
    · have hperiod : P.map.node (P.map.node P.point) = P.point :=
        Hypermap.node_node_eq_self_of_not_long
          (G := P.map) P.point hlong
      rcases onRing_eq_point_or_node_point_of_period_two
          P hperiod hxRing with hxPoint | hxNode
      · exact Or.inl hxPoint
      · right
        have hface :
            P.map.face (P.map.edge P.point) = P.map.node P.point :=
          not_not.mp hlong
        exact hxNode.trans hface.symm
  · exact Or.inl hxRing

private theorem n_exceptional_node_cycle
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    let a : P.n.map.Dart := ExtDart.newEdge
    let b : P.n.map.Dart :=
      ExtDart.old (P.map.face (P.map.edge P.point))
    let c : P.n.map.Dart := ExtDart.old P.point
    P.n.map.node a = b ∧ P.n.map.node b = c ∧
      P.n.map.node c = a := by
  dsimp
  have hfaceNode :
      P.map.node (P.map.face (P.map.edge P.point)) = P.point :=
    P.map.node_face_edge P.point
  have hfaceNe : P.map.face (P.map.edge P.point) ≠ P.point := by
    intro h
    apply hproper
    calc
      P.point = P.map.node (P.map.face (P.map.edge P.point)) :=
        hfaceNode.symm
      _ = P.map.node P.point := by rw [h]
  have hnodeNe : P.map.node P.point ≠ P.point :=
    fun h => hproper h.symm
  change
    Hypermap.ExtensionN.node P.map P.point ExtDart.newEdge =
        ExtDart.old (P.map.face (P.map.edge P.point)) ∧
      Hypermap.ExtensionN.node P.map P.point
          (ExtDart.old (P.map.face (P.map.edge P.point))) =
        ExtDart.old P.point ∧
      Hypermap.ExtensionN.node P.map P.point (ExtDart.old P.point) =
        ExtDart.newEdge
  simp [Hypermap.ExtensionN.node, Hypermap.ExtensionN.nodeToFun,
    hfaceNe, hfaceNode, hnodeNe]

private theorem n_exceptional_cubic
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    {x : P.n.map.Dart}
    (hx : x = ExtDart.newEdge ∨
      x = ExtDart.old (P.map.face (P.map.edge P.point)) ∨
        x = ExtDart.old P.point) :
    P.n.map.node (P.n.map.node (P.n.map.node x)) = x ∧
      P.n.map.node x ≠ x := by
  rcases n_exceptional_node_cycle P hproper with ⟨hab, hbc, hca⟩
  rcases hx with rfl | rfl | rfl
  · simp only [hab, hbc, hca]
    exact ⟨trivial, by simp⟩
  · simp only [hbc, hca, hab]
    constructor
    · trivial
    · intro h
      have h' : P.point = P.map.face (P.map.edge P.point) :=
        ExtDart.old_injective h
      apply hproper
      calc
        P.point = P.map.node (P.map.face (P.map.edge P.point)) :=
          (P.map.node_face_edge P.point).symm
        _ = P.map.node P.point := (congrArg P.map.node h').symm
  · simp only [hca, hab, hbc]
    exact ⟨trivial, by simp⟩

theorem n_quasicubic
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hP : P.Quasicubic) :
    P.n.Quasicubic := by
  intro z hz
  cases z with
  | new =>
      exact (hz (onRing_point P.n)).elim
  | newEdge =>
      exact n_exceptional_cubic P hproper (Or.inl rfl)
  | old x =>
      rcases nOld_not_onRing_source_or_exception P hz with
        hx | hxPoint | hxFace
      · have hnx : ¬ P.OnRing (P.map.node x) :=
          not_onRing_of_nodeReachable P hx
            (PermReachable.forward P.map.node x)
        have hnnx : ¬ P.OnRing (P.map.node (P.map.node x)) :=
          not_onRing_of_nodeReachable P hnx
            (PermReachable.forward P.map.node (P.map.node x))
        have hxPointNe : x ≠ P.point := by
          intro h
          exact hx (h ▸ onRing_point P)
        have hnxPointNe : P.map.node x ≠ P.point := by
          intro h
          exact hnx (h ▸ onRing_point P)
        have hnnxPointNe :
            P.map.node (P.map.node x) ≠ P.point := by
          intro h
          exact hnnx (h ▸ onRing_point P)
        have hxCubic := hP x hx
        have hn3PointNe :
            P.map.node (P.map.node (P.map.node x)) ≠ P.point := by
          rw [hxCubic.1]
          exact hxPointNe
        have hn4PointNe :
            P.map.node
                (P.map.node (P.map.node (P.map.node x))) ≠
              P.point := by
          rw [congrArg P.map.node hxCubic.1]
          exact hnxPointNe
        constructor
        · change P.n.map.node
              (P.n.map.node (P.n.map.node (P.nOld x))) = P.nOld x
          rw [← nOld_node_of_regular P hxPointNe hnnxPointNe,
            ← nOld_node_of_regular P hnxPointNe hn3PointNe,
            ← nOld_node_of_regular P hnnxPointNe hn4PointNe,
            hxCubic.1]
        · intro hfixed
          apply hxCubic.2
          apply nOld_injective P
          rw [nOld_node_of_regular P hxPointNe hnnxPointNe]
          exact hfixed
      · subst x
        exact n_exceptional_cubic P hproper (Or.inr (Or.inr rfl))
      · subst x
        exact n_exceptional_cubic P hproper (Or.inr (Or.inl rfl))


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
