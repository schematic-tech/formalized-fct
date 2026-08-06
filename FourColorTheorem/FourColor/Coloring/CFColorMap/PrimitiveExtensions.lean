import FourColorTheorem.FourColor.Coloring.CFColorMap.TraceBasics

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

/-- Reading colors commutes with boundary rotation. -/
theorem colorsOn_rotate_boundary
    (G : Hypermap) (k : G.Dart → Color) (r : List G.Dart) (n : Nat) :
    G.colorsOn k (r.rotate n) = (G.colorsOn k r).rotate n := by
  change (r.rotate n).map k = (r.map k).rotate n
  exact List.map_rotate _ _ _

theorem colorsOn_rotateLeft
    (G : Hypermap) (k : G.Dart → Color) (r : List G.Dart) (n : Nat) :
    G.colorsOn k (CProg.rotateLeft n r) =
      CProg.rotateLeft n (G.colorsOn k r) := by
  change (CProg.rotateLeft n r).map k =
    CProg.rotateLeft n (r.map k)
  exact CProg.map_rotateLeft k n r

/-- Ring traces rotate together with their boundary representatives. -/
theorem RingTrace.rotate_boundary
    {G : Hypermap} {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) (n : Nat) :
    G.RingTrace (r.rotate n) (et.rotate n) := by
  rcases htrace with ⟨k, hk, het⟩
  refine ⟨k, hk, ?_⟩
  rw [het, colorsOn_rotate_boundary, ColSeq.trace_rotate]

/-- Coq's coloring used in the `CpU` case of `cpcolor1U_correct`.  Old faces
retain their source color, while the fresh singleton face differs from the
boundary face by the prescribed nonzero edge color `e`. -/
def extensionUColor
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) (e : Color) :
    (G.extensionU x0).Dart → Color
  | ExtDart.new => e + k (G.node x0)
  | ExtDart.newEdge => k (G.node x0)
  | ExtDart.old x => k x

@[simp]
theorem extensionUColor_new
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) (e : Color) :
    extensionUColor G x0 k e ExtDart.new = e + k (G.node x0) :=
  rfl

@[simp]
theorem extensionUColor_newEdge
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) (e : Color) :
    extensionUColor G x0 k e ExtDart.newEdge = k (G.node x0) :=
  rfl

@[simp]
theorem extensionUColor_old
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color)
    (e : Color) (x : G.Dart) :
    extensionUColor G x0 k e (ExtDart.old x) = k x :=
  rfl

/-- The primitive `U` coloring extension used by Coq `cpcolor1U_correct`. -/
theorem extensionUColor_coloring
    {G : Hypermap} {x0 : G.Dart} {k : G.Dart → Color} {e : Color}
    (hk : G.Coloring k) (he : e ≠ Color.zero) :
    (G.extensionU x0).Coloring (extensionUColor G x0 k e) := by
  constructor
  · intro x
    cases x with
    | new =>
        change k (G.node x0) ≠ e + k (G.node x0)
        intro h
        apply he
        have h' := congrArg (fun c => c + k (G.node x0)) h
        simpa [Color.add_assoc] using h'.symm
    | newEdge =>
        change e + k (G.node x0) ≠ k (G.node x0)
        intro h
        apply he
        have h' := congrArg (fun c => c + k (G.node x0)) h
        simpa [Color.add_assoc] using h'
    | old x =>
        exact Coloring.edge_ne (G := G) hk x
  · intro x
    cases x with
    | new =>
        rfl
    | newEdge =>
        rfl
    | old x =>
        have hface :
            (G.extensionU x0).face (ExtDart.old x) =
              if G.face x = G.node x0 then ExtDart.newEdge
              else ExtDart.old (G.face x) :=
          rfl
        by_cases hx : G.face x = G.node x0
        · rw [hface, if_pos hx]
          change k (G.node x0) = k x
          rw [← hx]
          exact Coloring.face_eq (G := G) hk x
        · rw [hface, if_neg hx]
          exact Coloring.face_eq (G := G) hk x

/-- Coq's coloring used in `cpcolor1K_correct`, expressed for the underlying
primitive `N` extension.  The two fresh darts inherit the colors of the two
old face orbits to which `N` splices them. -/
def extensionNColor
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) :
    (G.extensionN x0).Dart → Color
  | ExtDart.new => k x0
  | ExtDart.newEdge => k (G.node.symm (G.node.symm x0))
  | ExtDart.old x => k x

@[simp]
theorem extensionNColor_new
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) :
    extensionNColor G x0 k ExtDart.new = k x0 :=
  rfl

@[simp]
theorem extensionNColor_newEdge
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) :
    extensionNColor G x0 k ExtDart.newEdge =
      k (G.node.symm (G.node.symm x0)) :=
  rfl

@[simp]
theorem extensionNColor_old
    (G : Hypermap) (x0 : G.Dart) (k : G.Dart → Color) (x : G.Dart) :
    extensionNColor G x0 k (ExtDart.old x) = k x :=
  rfl

/-- The primitive `N` coloring extension.  `LongRingHead` identifies both
fresh face splices with old faces; `hne` is precisely the new-edge coloring
condition. -/
theorem extensionNColor_coloring
    {G : Hypermap} {x0 : G.Dart} {k : G.Dart → Color}
    (hk : G.Coloring k) (hlong : G.LongRingHead x0)
    (hne : k x0 ≠ k (G.node.symm (G.node.symm x0))) :
    (G.extensionN x0).Coloring (extensionNColor G x0 k) := by
  constructor
  · intro x
    cases x with
    | new =>
        exact hne.symm
    | newEdge =>
        exact hne
    | old x =>
        exact Coloring.edge_ne (G := G) hk x
  · intro x
    cases x with
    | new =>
        rfl
    | newEdge =>
        have hface :
            (G.extensionN x0).face ExtDart.newEdge =
              if G.LongRingHead x0 then
                ExtDart.old (G.face (G.edge (G.face (G.edge x0))))
              else ExtDart.new :=
          ExtensionN.face_newEdge G x0
        rw [hface, if_pos hlong]
        change k (G.face (G.edge (G.face (G.edge x0)))) =
          k (G.node.symm (G.node.symm x0))
        rw [face_edge_eq_node_symm, face_edge_eq_node_symm]
    | old x =>
        have hface :
            (G.extensionN x0).face (ExtDart.old x) =
              if x = G.edge (G.face (G.edge x0)) then ExtDart.newEdge
              else if x = G.edge (G.node x0) then ExtDart.new
              else ExtDart.old (G.face x) :=
          ExtensionN.face_old G x0 x
        by_cases hxFace : x = G.edge (G.face (G.edge x0))
        · rw [hface, if_pos hxFace]
          change k (G.node.symm (G.node.symm x0)) = k x
          have hfx : G.face x = G.node.symm (G.node.symm x0) := by
            rw [hxFace, face_edge_eq_node_symm,
              face_edge_eq_node_symm]
          rw [← hfx]
          exact Coloring.face_eq (G := G) hk x
        · by_cases hxNode : x = G.edge (G.node x0)
          · rw [hface, if_neg hxFace, if_pos hxNode]
            change k x0 = k x
            have hfx : G.face x = x0 := by
              rw [hxNode, face_edge_eq_node_symm]
              simp
            rw [← hfx]
            exact Coloring.face_eq (G := G) hk x
          · rw [hface, if_neg hxFace, if_neg hxNode]
            exact Coloring.face_eq (G := G) hk x

/-- Coq's coloring argument for `ecpA`: identifying the two distinguished
source face colors makes the node-merge rewiring preserve a proper map
coloring. -/
theorem extensionAColoring
    {G : Hypermap} {x0 : G.Dart} {k : G.Dart → Color}
    (hk : G.Coloring k)
    (hlong : G.LongRingHead x0)
    (heq : k (G.node x0) = k (G.face (G.edge x0))) :
    (Hypermap.extensionA G x0).Coloring k := by
  classical
  have hnn0 : G.node (G.node x0) ≠ x0 := by
    intro h
    apply hlong
    apply G.node.injective
    simpa using h.symm
  constructor
  · intro x
    change G.Dart at x
    change k (Hypermap.extensionAEdge G x0 x) ≠ k x
    by_cases hreach : PermReachable G.face (G.edge x0) (G.node x0)
    · have hconn : k (G.node x0) = k (G.edge x0) :=
        Hypermap.Coloring.eq_of_face_reachable (G := G) hk hreach
      have hnnFace :
          k (G.node x0) = k (G.edge (G.node (G.node x0))) := by
        have hface := Hypermap.Coloring.face_eq
          (G := G) hk (G.edge (G.node (G.node x0)))
        rw [Hypermap.face_edge_eq_node_symm] at hface
        simpa using hface
      rw [Hypermap.extensionAEdge_apply_coq, if_pos hreach]
      by_cases hx : x = x0
      · subst x
        simp only [if_pos]
        intro hbad
        exact hk.1 x0 (hconn.symm.trans (hnnFace.trans hbad))
      · by_cases hnn : x = G.node (G.node x0)
        · subst x
          have hedge :
              (if G.node (G.node x0) = x0 then
                  G.edge (G.node (G.node x0))
                else if G.node (G.node x0) = G.node (G.node x0) then
                  G.edge x0
                else G.edge (G.node (G.node x0))) = G.edge x0 := by
            rw [if_neg hnn0, if_pos rfl]
          rw [hedge]
          intro hbad
          exact hk.1 (G.node (G.node x0))
            (hnnFace.symm.trans (hconn.trans hbad))
        · have hedge :
              (if x = x0 then G.edge (G.node (G.node x0))
                else if x = G.node (G.node x0) then G.edge x0
                else G.edge x) = G.edge x := by
            rw [if_neg hx, if_neg hnn]
          rw [hedge]
          exact hk.1 x
    · rw [Hypermap.extensionAEdge_apply_coq, if_neg hreach]
      exact hk.1 x
  · intro x
    change G.Dart at x
    change k (Hypermap.extensionAFace G x0 x) = k x
    by_cases hreach : PermReachable G.face (G.edge x0) (G.node x0)
    · rw [Hypermap.extensionAFace_of_faceReachable (G := G) x0 hreach]
      exact hk.2 x
    · rw [Hypermap.extensionAFace_of_not_faceReachable
        (G := G) x0 hreach]
      by_cases hx : x = G.edge x0
      · simp only [hx, if_true]
        subst x
        exact heq.trans (hk.2 (G.edge x0))
      · by_cases hfx : G.face x = G.node x0
        · have hface :
              (if x = G.edge x0 then G.node x0
                else if G.face x = G.node x0 then G.face (G.edge x0)
                else G.face x) = G.face (G.edge x0) := by
            rw [if_neg hx, if_pos hfx]
          rw [hface]
          exact heq.symm.trans (hfx ▸ hk.2 x)
        · have hface :
              (if x = G.edge x0 then G.node x0
                else if G.face x = G.node x0 then G.face (G.edge x0)
                else G.face x) = G.face x := by
            rw [if_neg hx, if_neg hfx]
          rw [hface]
          exact hk.2 x

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
