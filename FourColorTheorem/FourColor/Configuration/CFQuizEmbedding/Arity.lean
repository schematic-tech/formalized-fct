import FourColorTheorem.FourColor.Configuration.CFQuiz
import FourColorTheorem.FourColor.Reducibility.ProgramMap
import FourColorTheorem.FourColor.Configuration.QuizEmbedding
import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations

/-!
Semantic helpers for configuration quizzes.

This file starts the bridge from the executable guards in `CFQuiz` to the
Prop-valued embedding hypotheses from `Embedding`.  It ports the arithmetic
content of Coq `not_bad_ring_arity` and gives `cpradius2` a witness theorem
that later becomes the source of the semantic `RadiusTwo` proof.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CFQuiz

open Hypermap

theorem yOld_arity_eq_add_one_of_faceReachable_point
    (P : PointedHypermap)
    (hsep : ¬ PermReachable P.map.face P.point (P.map.node P.point))
    {x : P.map.Dart}
    (hx : PermReachable P.map.face x P.point) :
    P.y.map.arity (P.yOld x) = P.map.arity x + 1 := by
  have hxNode :
      ¬ PermReachable P.map.face x (P.map.node P.point) := by
    intro h
    exact hsep (PermReachable.trans P.map.face
      (PermReachable.symm P.map.face hx) h)
  let e : P.y.map.FaceClass (P.yOld x) ≃ Option (P.map.FaceClass x) :=
    { toFun := fun ⟨z, hz⟩ =>
        match z with
        | ExtDart.new =>
            False.elim (PointedHypermap.yOld_not_faceReachable_point P x (by
              simpa [PointedHypermap.y] using hz))
        | ExtDart.newEdge => none
        | ExtDart.old u =>
            match u with
            | ExtDart.new =>
                False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | ExtDart.newEdge =>
                False.elim (hxNode
                  ((PointedHypermap.yOld_faceReachable_node_point_iff P).1
                    (by
                      simpa [PointedHypermap.y,
                        Hypermap.extensionY_node_new] using hz)))
            | ExtDart.old y =>
                some ⟨y, (PointedHypermap.yOld_faceReachable_iff P).1 (by
                  simpa [PointedHypermap.y, PointedHypermap.yOld] using hz)⟩
      invFun := fun z =>
        match z with
        | none =>
            ⟨ExtDart.newEdge,
              (PointedHypermap.yOld_faceReachable_newEdge_iff P).2 hx⟩
        | some y =>
            ⟨P.yOld y.1,
              (PointedHypermap.yOld_faceReachable_iff P).2 y.2⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new =>
            exact False.elim
              (PointedHypermap.yOld_not_faceReachable_point P x (by
                simpa [PointedHypermap.y] using hz))
        | newEdge => rfl
        | old u =>
            cases u with
            | new =>
                exact False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | newEdge =>
                exact False.elim (hxNode
                  ((PointedHypermap.yOld_faceReachable_node_point_iff P).1
                    (by
                      simpa [PointedHypermap.y,
                        Hypermap.extensionY_node_new] using hz)))
            | old y => rfl
      right_inv := by
        intro z
        cases z with
        | none => rfl
        | some y => rfl }
  calc
    P.y.map.arity (P.yOld x) =
        Nat.card (P.y.map.FaceClass (P.yOld x)) := rfl
    _ = Nat.card (Option (P.map.FaceClass x)) := Nat.card_congr e
    _ = Nat.card (P.map.FaceClass x) + 1 := by
      simp [Nat.card_eq_fintype_card]
    _ = P.map.arity x + 1 := rfl

theorem yOld_arity_eq_add_one_of_faceReachable_node_point
    (P : PointedHypermap)
    (hsep : ¬ PermReachable P.map.face P.point (P.map.node P.point))
    {x : P.map.Dart}
    (hx : PermReachable P.map.face x (P.map.node P.point)) :
    P.y.map.arity (P.yOld x) = P.map.arity x + 1 := by
  have hxPoint : ¬ PermReachable P.map.face x P.point := by
    intro h
    exact hsep (PermReachable.trans P.map.face
      (PermReachable.symm P.map.face h) hx)
  let e : P.y.map.FaceClass (P.yOld x) ≃ Option (P.map.FaceClass x) :=
    { toFun := fun ⟨z, hz⟩ =>
        match z with
        | ExtDart.new =>
            False.elim (PointedHypermap.yOld_not_faceReachable_point P x (by
              simpa [PointedHypermap.y] using hz))
        | ExtDart.newEdge =>
            False.elim (hxPoint
              ((PointedHypermap.yOld_faceReachable_newEdge_iff P).1 (by
                simpa [PointedHypermap.y] using hz)))
        | ExtDart.old u =>
            match u with
            | ExtDart.new =>
                False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | ExtDart.newEdge => none
            | ExtDart.old y =>
                some ⟨y, (PointedHypermap.yOld_faceReachable_iff P).1 (by
                  simpa [PointedHypermap.y, PointedHypermap.yOld] using hz)⟩
      invFun := fun z =>
        match z with
        | none =>
            ⟨ExtDart.old ExtDart.newEdge, by
              simpa [PointedHypermap.y,
                Hypermap.extensionY_node_new] using
                (PointedHypermap.yOld_faceReachable_node_point_iff P).2 hx⟩
        | some y =>
            ⟨P.yOld y.1,
              (PointedHypermap.yOld_faceReachable_iff P).2 y.2⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new =>
            exact False.elim
              (PointedHypermap.yOld_not_faceReachable_point P x (by
                simpa [PointedHypermap.y] using hz))
        | newEdge =>
            exact False.elim (hxPoint
              ((PointedHypermap.yOld_faceReachable_newEdge_iff P).1 (by
                simpa [PointedHypermap.y] using hz)))
        | old u =>
            cases u with
            | new =>
                exact False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | newEdge => rfl
            | old y => rfl
      right_inv := by
        intro z
        cases z with
        | none => rfl
        | some y => rfl }
  calc
    P.y.map.arity (P.yOld x) =
        Nat.card (P.y.map.FaceClass (P.yOld x)) := rfl
    _ = Nat.card (Option (P.map.FaceClass x)) := Nat.card_congr e
    _ = Nat.card (P.map.FaceClass x) + 1 := by
      simp [Nat.card_eq_fintype_card]
    _ = P.map.arity x + 1 := rfl

theorem yOld_arity_eq_of_not_faceBand_point_node
    (P : PointedHypermap) {x : P.map.Dart}
    (hxPoint : ¬ PermReachable P.map.face x P.point)
    (hxNode : ¬ PermReachable P.map.face x (P.map.node P.point)) :
    P.y.map.arity (P.yOld x) = P.map.arity x := by
  let e : P.y.map.FaceClass (P.yOld x) ≃ P.map.FaceClass x :=
    { toFun := fun ⟨z, hz⟩ =>
        match z with
        | ExtDart.new =>
            False.elim (PointedHypermap.yOld_not_faceReachable_point P x (by
              simpa [PointedHypermap.y] using hz))
        | ExtDart.newEdge =>
            False.elim (hxPoint
              ((PointedHypermap.yOld_faceReachable_newEdge_iff P).1 (by
                simpa [PointedHypermap.y] using hz)))
        | ExtDart.old u =>
            match u with
            | ExtDart.new =>
                False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | ExtDart.newEdge =>
                False.elim (hxNode
                  ((PointedHypermap.yOld_faceReachable_node_point_iff P).1
                    (by
                      simpa [PointedHypermap.y,
                        Hypermap.extensionY_node_new] using hz)))
            | ExtDart.old y =>
                ⟨y, (PointedHypermap.yOld_faceReachable_iff P).1 (by
                  simpa [PointedHypermap.y, PointedHypermap.yOld] using hz)⟩
      invFun := fun y =>
        ⟨P.yOld y.1,
          (PointedHypermap.yOld_faceReachable_iff P).2 y.2⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new =>
            exact False.elim
              (PointedHypermap.yOld_not_faceReachable_point P x (by
                simpa [PointedHypermap.y] using hz))
        | newEdge =>
            exact False.elim (hxPoint
              ((PointedHypermap.yOld_faceReachable_newEdge_iff P).1 (by
                simpa [PointedHypermap.y] using hz)))
        | old u =>
            cases u with
            | new =>
                exact False.elim
                  (PointedHypermap.yOld_not_faceReachable_old_new P x (by
                    simpa [PointedHypermap.y] using hz))
            | newEdge =>
                exact False.elim (hxNode
                  ((PointedHypermap.yOld_faceReachable_node_point_iff P).1
                    (by
                      simpa [PointedHypermap.y,
                        Hypermap.extensionY_node_new] using hz)))
            | old y => rfl
      right_inv := by
        intro y
        rfl }
  calc
    P.y.map.arity (P.yOld x) =
        Nat.card (P.y.map.FaceClass (P.yOld x)) := rfl
    _ = Nat.card (P.map.FaceClass x) := Nat.card_congr e
    _ = P.map.arity x := rfl

/-- Coq `nFiG` in the `CpY` branch, on one of the two detached perimeter
faces. -/
theorem yOld_arity_of_faceBand
    (P : PointedHypermap)
    (hsep : ¬ PermReachable P.map.face P.point (P.map.node P.point))
    {x : P.map.Dart}
    (hband : P.map.FaceBand [P.map.node P.point, P.point] x) :
    P.y.map.arity (P.yOld x) = P.map.arity x + 1 := by
  rcases (Hypermap.FaceBand.pair (G := P.map)).1 hband with hn | hp
  · exact yOld_arity_eq_add_one_of_faceReachable_node_point P hsep
      (PermReachable.symm P.map.face hn)
  · exact yOld_arity_eq_add_one_of_faceReachable_point P hsep
      (PermReachable.symm P.map.face hp)

/-- Coq `nFiG` in the `CpY` branch, off the two detached perimeter faces. -/
theorem yOld_arity_of_not_faceBand
    (P : PointedHypermap) {x : P.map.Dart}
    (hband : ¬ P.map.FaceBand [P.map.node P.point, P.point] x) :
    P.y.map.arity (P.yOld x) = P.map.arity x := by
  apply yOld_arity_eq_of_not_faceBand_point_node
  · intro hp
    exact hband ((Hypermap.FaceBand.pair (G := P.map)).2
      (Or.inr (PermReachable.symm P.map.face hp)))
  · intro hn
    exact hband ((Hypermap.FaceBand.pair (G := P.map)).2
      (Or.inl (PermReachable.symm P.map.face hn)))

/-- Coq's local fact `nFu0`: the fresh perimeter face introduced by `ecpY`
has exactly the two darts created by the outer `ecpN` extension. -/
theorem y_point_arity_of_proper
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point) :
    P.y.map.arity P.y.point = 2 := by
  let e : P.y.map.FaceClass P.y.point ≃ Bool :=
    { toFun := fun z => by
        rcases z with ⟨z, hz⟩
        cases z with
        | new => exact false
        | newEdge =>
            exact False.elim
              (Hypermap.extensionY_not_faceReachable_new_edge_of_proper
                (G := P.map) P.point hproper (by
                  simpa [PointedHypermap.y, ExtDart.Perm.edge] using hz))
        | old u =>
            by_cases hu : u = ExtDart.new
            · exact true
            · exact False.elim (hu
                (Hypermap.extensionU_faceReachable_from_new
                  (G := P.map) P.point
                  (by
                    have hproj :=
                      (Hypermap.extensionN_faceReachable_new_iff_proj
                        (G := Hypermap.extensionU P.map P.point)
                        ExtDart.new (y := ExtDart.old u)).1 (by
                          simpa [PointedHypermap.y] using hz)
                    simpa [Hypermap.extensionNFaceProj] using hproj)))
      invFun := fun b =>
        if b then
          ⟨ExtDart.old ExtDart.new,
            Hypermap.extensionN_faceReachable_new_old_x0
              (G := Hypermap.extensionU P.map P.point) ExtDart.new⟩
        else
          ⟨ExtDart.new,
            PermReachable.refl P.y.map.face P.y.point⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new => rfl
        | newEdge =>
            exact False.elim
              (Hypermap.extensionY_not_faceReachable_new_edge_of_proper
                (G := P.map) P.point hproper hz)
        | old u =>
            have hu : u = ExtDart.new :=
              Hypermap.extensionU_faceReachable_from_new
                (G := P.map) P.point (by
                  have hproj :=
                    (Hypermap.extensionN_faceReachable_new_iff_proj
                      (G := Hypermap.extensionU P.map P.point)
                      ExtDart.new (y := ExtDart.old u)).1 hz
                  simpa [Hypermap.extensionNFaceProj] using hproj)
            subst u
            rfl
      right_inv := by
        intro b
        cases b <;> rfl }
  calc
    P.y.map.arity P.y.point = Nat.card (P.y.map.FaceClass P.y.point) := rfl
    _ = Nat.card Bool := Nat.card_congr e
    _ = 2 := by simp [Nat.card_eq_fintype_card]

/-- An old face orbit in `extensionN` gains exactly the fresh `newEdge` dart
when it avoids the extension point's face and meets the `newEdge` projection. -/
theorem extensionN_old_arity_eq_add_one
    (G : Hypermap) (x0 y : G.Dart)
    (hnotPoint : ¬ PermReachable G.face y x0)
    (hproj : PermReachable G.face y
      (Hypermap.extensionNFaceProj G x0 ExtDart.newEdge)) :
    (Hypermap.extensionN G x0).arity
        (Hypermap.extensionNOld G x0 y) = G.arity y + 1 := by
  let e :
      (Hypermap.extensionN G x0).FaceClass
          (Hypermap.extensionNOld G x0 y) ≃
        Option (G.FaceClass y) :=
    { toFun := fun ⟨z, hz⟩ =>
        match z with
        | ExtDart.new =>
            False.elim (hnotPoint (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | ExtDart.newEdge => none
        | ExtDart.old u =>
            some ⟨u, by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp⟩
      invFun := fun z =>
        match z with
        | none =>
            ⟨ExtDart.newEdge,
              (Hypermap.extensionN_faceReachable_iff_proj
                (G := G) x0).2 (by
                  simpa [Hypermap.extensionNOld,
                    Hypermap.extensionNFaceProj] using hproj)⟩
        | some u =>
            ⟨Hypermap.extensionNOld G x0 u.1,
              (Hypermap.extensionN_old_faceReachable_iff
                (G := G) x0).2 u.2⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new =>
            exact False.elim (hnotPoint (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | newEdge => rfl
        | old u => rfl
      right_inv := by
        intro z
        cases z with
        | none => rfl
        | some u => rfl }
  calc
    (Hypermap.extensionN G x0).arity
          (Hypermap.extensionNOld G x0 y) =
        Nat.card ((Hypermap.extensionN G x0).FaceClass
          (Hypermap.extensionNOld G x0 y)) := rfl
    _ = Nat.card (Option (G.FaceClass y)) := Nat.card_congr e
    _ = Nat.card (G.FaceClass y) + 1 := by
      simp [Nat.card_eq_fintype_card]
    _ = G.arity y + 1 := rfl

/-- Off both fresh projections, `extensionN` preserves an old face arity. -/
theorem extensionN_old_arity_eq
    (G : Hypermap) (x0 y : G.Dart)
    (hnotPoint : ¬ PermReachable G.face y x0)
    (hnotProj : ¬ PermReachable G.face y
      (Hypermap.extensionNFaceProj G x0 ExtDart.newEdge)) :
    (Hypermap.extensionN G x0).arity
        (Hypermap.extensionNOld G x0 y) = G.arity y := by
  let e :
      (Hypermap.extensionN G x0).FaceClass
          (Hypermap.extensionNOld G x0 y) ≃ G.FaceClass y :=
    { toFun := fun ⟨z, hz⟩ =>
        match z with
        | ExtDart.new =>
            False.elim (hnotPoint (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | ExtDart.newEdge =>
            False.elim (hnotProj (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | ExtDart.old u =>
            ⟨u, by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp⟩
      invFun := fun u =>
        ⟨Hypermap.extensionNOld G x0 u.1,
          (Hypermap.extensionN_old_faceReachable_iff
            (G := G) x0).2 u.2⟩
      left_inv := by
        intro z
        rcases z with ⟨z, hz⟩
        cases z with
        | new =>
            exact False.elim (hnotPoint (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | newEdge =>
            exact False.elim (hnotProj (by
              have hp :=
                (Hypermap.extensionN_faceReachable_iff_proj
                  (G := G) x0).1 hz
              simpa [Hypermap.extensionNOld,
                Hypermap.extensionNFaceProj] using hp))
        | old u => rfl
      right_inv := by
        intro u
        rfl }
  calc
    (Hypermap.extensionN G x0).arity
          (Hypermap.extensionNOld G x0 y) =
        Nat.card ((Hypermap.extensionN G x0).FaceClass
          (Hypermap.extensionNOld G x0 y)) := rfl
    _ = Nat.card (G.FaceClass y) := Nat.card_congr e
    _ = G.arity y := rfl

private theorem hNewEdge_faceProj
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point) :
    Hypermap.extensionNFaceProj P.y.map P.y.point ExtDart.newEdge =
      P.yOld (P.map.face (P.map.edge P.point)) := by
  change Hypermap.extensionNFaceProj
      (Hypermap.extensionY P.map P.point) ExtDart.new ExtDart.newEdge =
    Hypermap.extensionYOld P.map P.point
      (P.map.face (P.map.edge P.point))
  exact Hypermap.extensionH_newEdgeProj_eq_old_face_edge
    (G := P.map) P.point hproper hlong

theorem hOld_outer_arity_eq_add_one_of_faceReachable_face_edge
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point)
    {x : P.map.Dart}
    (hx : PermReachable P.map.face x
      (P.map.face (P.map.edge P.point))) :
    P.h.map.arity (P.hOld x) = P.y.map.arity (P.yOld x) + 1 := by
  change (Hypermap.extensionN P.y.map P.y.point).arity
      (Hypermap.extensionNOld P.y.map P.y.point (P.yOld x)) =
    P.y.map.arity (P.yOld x) + 1
  apply extensionN_old_arity_eq_add_one
  · intro hreach
    exact PointedHypermap.y_not_faceReachable_point_old P x
      (PermReachable.symm P.y.map.face hreach)
  · rw [hNewEdge_faceProj P hproper hlong]
    exact (PointedHypermap.yOld_faceReachable_iff P).2 hx

theorem hOld_outer_arity_eq_of_not_faceReachable_face_edge
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point)
    {x : P.map.Dart}
    (hx : ¬ PermReachable P.map.face x
      (P.map.face (P.map.edge P.point))) :
    P.h.map.arity (P.hOld x) = P.y.map.arity (P.yOld x) := by
  change (Hypermap.extensionN P.y.map P.y.point).arity
      (Hypermap.extensionNOld P.y.map P.y.point (P.yOld x)) =
    P.y.map.arity (P.yOld x)
  apply extensionN_old_arity_eq
  · intro hreach
    exact PointedHypermap.y_not_faceReachable_point_old P x
      (PermReachable.symm P.y.map.face hreach)
  · rw [hNewEdge_faceProj P hproper hlong]
    intro hreach
    exact hx ((PointedHypermap.yOld_faceReachable_iff P).1 hreach)

/-- Coq `nFiG` in the `CpH` branch on the three detached perimeter faces. -/
theorem hOld_arity_of_faceBand
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point)
    (hsimple : P.map.FaceSimple
      [P.map.node P.point, P.point,
        P.map.face (P.map.edge P.point)])
    {x : P.map.Dart}
    (hband : P.map.FaceBand
      [P.map.node P.point, P.point,
        P.map.face (P.map.edge P.point)] x) :
    P.h.map.arity (P.hOld x) = P.map.arity x + 1 := by
  have hnodePoint :
      ¬ PermReachable P.map.face (P.map.node P.point) P.point :=
    Hypermap.FaceSimple.not_faceReachable_head
      (G := P.map) hsimple (List.Mem.head _)
  have hsep :
      ¬ PermReachable P.map.face P.point (P.map.node P.point) :=
    fun hreach => hnodePoint (PermReachable.symm P.map.face hreach)
  rcases (Hypermap.FaceBand.triple (G := P.map)).1 hband with
      hnode | hpoint | hedge
  · have hnotEdge :
        ¬ PermReachable P.map.face x
          (P.map.face (P.map.edge P.point)) := by
      intro hxedge
      have hnodeEdge := PermReachable.trans P.map.face hnode hxedge
      exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple
        (List.Mem.tail P.point (List.Mem.head []))) hnodeEdge
    rw [hOld_outer_arity_eq_of_not_faceReachable_face_edge
      P hproper hlong hnotEdge]
    exact yOld_arity_eq_add_one_of_faceReachable_node_point
      P hsep (PermReachable.symm P.map.face hnode)
  · have hnotEdge :
        ¬ PermReachable P.map.face x
          (P.map.face (P.map.edge P.point)) := by
      intro hxedge
      have hpointEdge := PermReachable.trans P.map.face hpoint hxedge
      exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple.tail (List.Mem.head [])) hpointEdge
    rw [hOld_outer_arity_eq_of_not_faceReachable_face_edge
      P hproper hlong hnotEdge]
    exact yOld_arity_eq_add_one_of_faceReachable_point
      P hsep (PermReachable.symm P.map.face hpoint)
  · rw [hOld_outer_arity_eq_add_one_of_faceReachable_face_edge
      P hproper hlong (PermReachable.symm P.map.face hedge)]
    congr 1
    apply yOld_arity_of_not_faceBand P
    intro hpair
    rcases (Hypermap.FaceBand.pair (G := P.map)).1 hpair with
        hnode | hpoint
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple
        (List.Mem.tail P.point (List.Mem.head [])))
        (PermReachable.trans P.map.face hnode
          (PermReachable.symm P.map.face hedge))
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple.tail (List.Mem.head []))
        (PermReachable.trans P.map.face hpoint
          (PermReachable.symm P.map.face hedge))

/-- Coq `nFiG` in the `CpH` branch off the detached perimeter faces. -/
theorem hOld_arity_of_not_faceBand
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point)
    {x : P.map.Dart}
    (hband : ¬ P.map.FaceBand
      [P.map.node P.point, P.point,
        P.map.face (P.map.edge P.point)] x) :
    P.h.map.arity (P.hOld x) = P.map.arity x := by
  have hnot := (Hypermap.not_FaceBand_triple (G := P.map)).1 hband
  rw [hOld_outer_arity_eq_of_not_faceReachable_face_edge
    P hproper hlong (fun hreach =>
      hnot.2.2 (PermReachable.symm P.map.face hreach))]
  apply yOld_arity_of_not_faceBand P
  rw [Hypermap.not_FaceBand_pair]
  exact ⟨hnot.1, hnot.2.1⟩

/-- Coq's local fact `nFu0` in the `CpH` branch: the fresh perimeter face
introduced by `ecpH` consists of exactly three darts. -/
theorem h_point_arity_of_proper
    (P : PointedHypermap)
    (hproper : P.map.ProperRingHead P.point) :
    P.h.map.arity P.h.point = 3 := by
  classical
  let d0 : P.h.map.Dart := ExtDart.new
  let d1 : P.h.map.Dart := ExtDart.old ExtDart.new
  let d2 : P.h.map.Dart := ExtDart.old (ExtDart.old ExtDart.new)
  have hd0 : PermReachable P.h.map.face P.h.point d0 :=
    (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
      (G := P.map) P.point hproper).2 (Or.inl rfl)
  have hd1 : PermReachable P.h.map.face P.h.point d1 :=
    (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
      (G := P.map) P.point hproper).2 (Or.inr (Or.inl rfl))
  have hd2 : PermReachable P.h.map.face P.h.point d2 :=
    (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
      (G := P.map) P.point hproper).2 (Or.inr (Or.inr rfl))
  let z0 : P.h.map.FaceClass P.h.point := ⟨d0, hd0⟩
  let z1 : P.h.map.FaceClass P.h.point := ⟨d1, hd1⟩
  let z2 : P.h.map.FaceClass P.h.point := ⟨d2, hd2⟩
  have hzAll (z : P.h.map.FaceClass P.h.point) :
      z = z0 ∨ z = z1 ∨ z = z2 := by
    have hz :=
      (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
        (G := P.map) P.point hproper).1 z.2
    rcases hz with hz | hz | hz
    · exact Or.inl (Subtype.ext hz)
    · exact Or.inr (Or.inl (Subtype.ext hz))
    · exact Or.inr (Or.inr (Subtype.ext hz))
  have huniv :
      (Finset.univ : Finset (P.h.map.FaceClass P.h.point)) =
        {z0, z1, z2} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hzAll z
  calc
    P.h.map.arity P.h.point =
        Nat.card (P.h.map.FaceClass P.h.point) := rfl
    _ = Fintype.card (P.h.map.FaceClass P.h.point) := by
      rw [Nat.card_eq_fintype_card]
    _ = ({z0, z1, z2} :
        Finset (P.h.map.FaceClass P.h.point)).card := by
      rw [← huniv, Finset.card_univ]
    _ = 3 := by
      have hz01 : z0 ≠ z1 := by
        intro h
        have h' := congrArg Subtype.val h
        simp [z0, z1, d0, d1] at h'
      have hz02 : z0 ≠ z2 := by
        intro h
        have h' := congrArg Subtype.val h
        simp [z0, z2, d0, d2] at h'
      have hz12 : z1 ≠ z2 := by
        intro h
        have h' := congrArg Subtype.val h
        change ExtDart.old ExtDart.new =
          ExtDart.old (ExtDart.old ExtDart.new) at h'
        injection h' with h''
        cases h''
      have hz0mem : z0 ∉ ({z1, z2} :
          Finset (P.h.map.FaceClass P.h.point)) := by
        intro hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact hmem.elim hz01 hz02
      have hz1mem : z1 ∉ ({z2} :
          Finset (P.h.map.FaceClass P.h.point)) := by
        intro hmem
        rw [Finset.mem_singleton] at hmem
        exact hz12 hmem
      rw [Finset.card_insert_of_notMem hz0mem,
        Finset.card_insert_of_notMem hz1mem, Finset.card_singleton]

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
