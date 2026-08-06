import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.KA
import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.Quasicubic

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Total semantic interpretation of one construction step, matching Coq's
`cpmap` step semantics.  The checked geometry-preservation API below still
uses `step?`, because the `K` and `A` geometry needed there is being ported
separately. -/
noncomputable def step : CpStep → PointedHypermap → PointedHypermap
  | CpStep.rotate n, P => P.rotate n
  | CpStep.reverseRotate, P => P.reverseRotate
  | CpStep.y, P => P.y
  | CpStep.h, P => P.h
  | CpStep.u, P => P.u
  | CpStep.k, P => P.k
  | CpStep.a, P => P.a

/-- Total right-to-left construction-program interpretation, matching Coq
`cpmap` on all constructors. -/
noncomputable def cpmap : CProg → PointedHypermap
  | [] => base
  | s :: cp => step s (cpmap cp)

@[simp]
theorem step_rotate (n : Nat) (P : PointedHypermap) :
    step (CpStep.rotate n) P = P.rotate n :=
  rfl

@[simp]
theorem step_reverseRotate (P : PointedHypermap) :
    step CpStep.reverseRotate P = P.reverseRotate :=
  rfl

@[simp]
theorem step_y (P : PointedHypermap) :
    step CpStep.y P = P.y :=
  rfl

@[simp]
theorem step_h (P : PointedHypermap) :
    step CpStep.h P = P.h :=
  rfl

@[simp]
theorem step_u (P : PointedHypermap) :
    step CpStep.u P = P.u :=
  rfl

@[simp]
theorem step_k (P : PointedHypermap) :
    step CpStep.k P = P.k :=
  rfl

@[simp]
theorem step_a (P : PointedHypermap) :
    step CpStep.a P = P.a :=
  rfl

/-- Inject an old dart through one semantic construction step.  This is the
one-step ingredient of Coq's `injcp`. -/
noncomputable def oldStep (s : CpStep) (P : PointedHypermap)
    (x : P.map.Dart) : (step s P).map.Dart :=
  match s with
  | CpStep.rotate _ => x
  | CpStep.reverseRotate => x
  | CpStep.y => P.yOld x
  | CpStep.h => P.hOld x
  | CpStep.u => P.uOld x
  | CpStep.k => P.kOld x
  | CpStep.a => P.aOld x

/-- Old darts on which a construction step commutes pointwise with `node`.
These are exactly the finite exceptional lists appearing in Coq's
`icpU_node`, `icpY_node`, and `icpH_node` lemmas. -/
def oldStepNodeRegular (s : CpStep) (P : PointedHypermap)
    (x : P.map.Dart) : Prop :=
  match s with
  | CpStep.rotate _ => True
  | CpStep.reverseRotate => False
  | CpStep.y => x ≠ P.map.node P.point ∧ x ≠ P.point
  | CpStep.h =>
      x ≠ P.map.node P.point ∧ x ≠ P.point ∧
        x ≠ P.map.face (P.map.edge P.point)
  | CpStep.u => x ≠ P.map.node P.point
  | CpStep.k => False
  | CpStep.a => False

theorem oldStepNodeRegular_of_not_onRing
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.OnRing x) :
    oldStepNodeRegular s P x := by
  cases s with
  | rotate n =>
      trivial
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      constructor
      · intro h
        apply hx
        rw [h]
        exact onRing_node_point P
      · intro h
        apply hx
        rw [h]
        exact onRing_point P
  | h =>
      constructor
      · intro h
        apply hx
        rw [h]
        exact onRing_node_point P
      constructor
      · intro h
        apply hx
        rw [h]
        exact onRing_point P
      · intro h
        apply hx
        rw [h]
        exact onRing_face_edge_point P
  | u =>
      intro h
      apply hx
      rw [h]
      exact onRing_node_point P
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_faceReachable_of_faceReachable
    (s : CpStep) (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : PermReachable P.map.face x y) :
    PermReachable (step s P).map.face (oldStep s P x) (oldStep s P y) := by
  cases s with
  | rotate n =>
      simpa [oldStep, step, rotate] using hxy
  | reverseRotate =>
      simpa [oldStep, step, reverseRotate] using hxy
  | y =>
      exact yOld_faceReachable_of_faceReachable P hxy
  | h =>
      exact hOld_faceReachable_of_faceReachable P hxy
  | u =>
      exact uOld_faceReachable_of_faceReachable P hxy
  | k =>
      exact kOld_faceReachable_of_faceReachable P hxy
  | a =>
      exact aOld_faceReachable_of_faceReachable P hxy

theorem oldStep_faceReachable_iff_of_cubicStep
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x y : P.map.Dart} :
    PermReachable (step s P).map.face (oldStep s P x) (oldStep s P y) ↔
      PermReachable P.map.face x y := by
  cases s with
  | rotate n =>
      rfl
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      exact yOld_faceReachable_iff P
  | h =>
      exact hOld_faceReachable_iff P
  | u =>
      exact uOld_faceReachable_iff P
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_ringAdj_of_ringAdj
    (s : CpStep) (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    (step s P).map.RingAdj (oldStep s P x) (oldStep s P y) := by
  cases s with
  | rotate n =>
      simpa [oldStep, step, rotate] using hxy
  | reverseRotate =>
      simpa [oldStep, step, reverseRotate] using hxy
  | y =>
      exact yOld_ringAdj_of_ringAdj P hxy
  | h =>
      exact hOld_ringAdj_of_ringAdj P hxy
  | u =>
      exact uOld_ringAdj_of_ringAdj P hxy
  | k =>
      exact kOld_ringAdj_of_ringAdj P hxy
  | a =>
      exact aOld_ringAdj_of_ringAdj P hxy

theorem oldStep_ringAdj_iff_of_cubicStep
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x y : P.map.Dart} :
    (step s P).map.RingAdj (oldStep s P x) (oldStep s P y) ↔
      P.map.RingAdj x y := by
  cases s with
  | rotate n =>
      simp [oldStep, rotate]
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      exact yOld_ringAdj_iff P
  | h =>
      exact hOld_ringAdj_iff P
  | u =>
      exact uOld_ringAdj_iff P
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_edge_of_cubicStep
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) (x : P.map.Dart) :
    oldStep s P (P.map.edge x) = (step s P).map.edge (oldStep s P x) := by
  cases s with
  | rotate n =>
      exact rfl
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      exact yOld_edge P x
  | h =>
      exact hOld_edge P x
  | u =>
      exact uOld_edge P x
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_node_of_cubicStep_of_nodeRegular
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : oldStepNodeRegular s P x) :
    oldStep s P (P.map.node x) =
      (step s P).map.node (oldStep s P x) := by
  cases s with
  | rotate n =>
      rfl
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      exact yOld_node_of_ne_node_point_of_ne_point P hx.1 hx.2
  | h =>
      exact hOld_node_of_ne_node_point_of_ne_point_of_ne_face_edge
        P hx.1 hx.2.1 hx.2.2
  | u =>
      exact uOld_node_of_ne_node_point P hx
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_node_of_cubicStep_of_not_onRing
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.OnRing x) :
    oldStep s P (P.map.node x) =
      (step s P).map.node (oldStep s P x) :=
  oldStep_node_of_cubicStep_of_nodeRegular hs P
    (oldStepNodeRegular_of_not_onRing hs P hx)

theorem oldStep_not_onRing_of_cubicStep
    {s : CpStep}
    (hs : CProg.cubic [s] = true)
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.OnRing x) :
    ¬ (step s P).OnRing (oldStep s P x) := by
  cases s with
  | rotate n =>
      simpa [oldStep, step] using
        ((rotate_onRing_iff n P (x := x)).not.mpr hx)
  | reverseRotate =>
      simp [CProg.cubic] at hs
  | y =>
      simpa [oldStep, step] using yOld_not_onRing_of_not_onRing P hx
  | h =>
      simpa [oldStep, step] using hOld_not_onRing_of_not_onRing P hx
  | u =>
      simpa [oldStep, step] using (uOld_not_onRing_iff P (x := x)).2 hx
  | k =>
      simp [CProg.cubic] at hs
  | a =>
      simp [CProg.cubic] at hs

theorem oldStep_injective
    (s : CpStep) (P : PointedHypermap) :
    Function.Injective (oldStep s P) := by
  cases s with
  | rotate n =>
      intro x y hxy
      simpa [oldStep] using hxy
  | reverseRotate =>
      intro x y hxy
      simpa [oldStep] using hxy
  | y =>
      exact yOld_injective P
  | h =>
      exact hOld_injective P
  | u =>
      exact uOld_injective P
  | k =>
      intro x y hxy
      change Hypermap.extensionNOld P.map (P.map.node P.point) x =
          Hypermap.extensionNOld P.map (P.map.node P.point) y at hxy
      simp only [Hypermap.extensionNOld] at hxy
      injection hxy with hxy'
  | a =>
      intro x y hxy
      simpa [oldStep, aOld] using hxy

@[simp]
theorem cpmap_nil :
    cpmap [] = base :=
  rfl

@[simp]
theorem cpmap_cons (s : CpStep) (cp : CProg) :
    cpmap (s :: cp) = step s (cpmap cp) :=
  rfl


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
