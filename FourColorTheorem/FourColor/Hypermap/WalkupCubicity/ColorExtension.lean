import FourColorTheorem.FourColor.Hypermap.WalkupCubicity.Geometry

/-!
Color extension across the twice-deleted Walkup map.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

universe u

open Hypermap

/-- Coloring-extension target for the twice-deleted Walkup map in the
period-two node case.  This is the Lean-side boundary for the constructive
part of Coq `minimal_counter_example_is_cubic` after minimality has supplied a
colouring of the smaller map. -/
def WalkupTwoNodeColorExtension : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).FourColorable →
        G.FourColorable

/-- Function-level form of `WalkupTwoNodeColorExtension`.  This is the
constructive target matching the later Coq proof term: build the colouring of
`G` from an arbitrary colouring function on the twice-deleted map. -/
def WalkupTwoNodeColoringExtension : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∃ kG : G.Dart → Color, G.Coloring kG

/-- Local-obligation form of the two-node colouring extension.  The chosen
colours for `z` and `node z` must make the extended function satisfy the two
fields of `Hypermap.Coloring`. -/
def WalkupTwoNodeColoringLocalCases : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∃ cz cnode : Color,
          (∀ x : G.Dart,
            G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode
                (G.edge x) ≠
              G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x) ∧
          (∀ x : G.Dart,
            G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode
                (G.face x) =
              G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode x)

/-- Reduced local obligation using the face-class extension.  The face
equations are automatic from `Coloring.faceClassColor_face_eq`; only edge
inequalities remain. -/
def WalkupTwoNodeFaceClassEdgeCases : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∃ fallback : G.Dart → Color,
          ∀ x : G.Dart,
            G.walkupE_walkupE_faceClassColor hz_ne k fallback
                (G.edge x) ≠
              G.walkupE_walkupE_faceClassColor hz_ne k fallback x

/-- Exceptional edge positions left after the generic two-node Walkup edge
transport.  Away from these equalities, `faceClassColor_edge_ne_of_plain_of_ne`
discharges the edge inequality automatically. -/
def WalkupTwoNodeFaceClassEdgeExceptional
    (G : Hypermap.{u}) (z x : G.Dart) : Prop :=
  x = z ∨
    x = G.node z ∨
      x = G.edge z ∨
        G.edge x = z ∨
          G.edge x = G.node z ∨
            G.edge z = G.node z ∨
              G.face (G.edge x) = G.node z

/-- Smaller exceptional set after using plainness and the period-two node
hypothesis. -/
def WalkupTwoNodeFaceClassEdgeCoreExceptional
    (G : Hypermap.{u}) (z x : G.Dart) : Prop :=
  x = z ∨
    x = G.node z ∨
      x = G.edge z ∨
        x = G.edge (G.node z) ∨
          G.edge z = G.node z

theorem walkupTwoNodeFaceClassEdgeExceptional_core_of_plain
    {G : Hypermap.{u}} (hplain : G.Plain)
    {z x : G.Dart}
    (hzz : G.node (G.node z) = z)
    (hex : WalkupTwoNodeFaceClassEdgeExceptional G z x) :
    WalkupTwoNodeFaceClassEdgeCoreExceptional G z x := by
  rcases hex with hx | hx | hx | hx | hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (Or.inl hx))
  · exact Or.inr (Or.inr (Or.inl
      (Plain.eq_edge_of_edge_eq (G := G) hplain hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (Plain.eq_edge_of_edge_eq (G := G) hplain hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  · have hxz : x = z := by
      simpa [hzz] using congrArg G.node hx
    exact Or.inl hxz

/-- The finite exceptional edge obligation for the face-class extension. -/
def WalkupTwoNodeFaceClassExceptionalEdgeCases : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∃ fallback : G.Dart → Color,
          ∀ x : G.Dart,
            WalkupTwoNodeFaceClassEdgeExceptional G z x →
              G.walkupE_walkupE_faceClassColor hz_ne k fallback
                  (G.edge x) ≠
                G.walkupE_walkupE_faceClassColor hz_ne k fallback x

/-- The reduced finite exceptional edge obligation after shrinking the
exceptional set to the core cases. -/
def WalkupTwoNodeFaceClassCoreExceptionalEdgeCases : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∃ fallback : G.Dart → Color,
          ∀ x : G.Dart,
            WalkupTwoNodeFaceClassEdgeCoreExceptional G z x →
              G.walkupE_walkupE_faceClassColor hz_ne k fallback
                  (G.edge x) ≠
                G.walkupE_walkupE_faceClassColor hz_ne k fallback x

/-- Core exceptional edge obligation with the fixed Coq-style fallback. -/
def WalkupTwoNodeFaceClassCoreDefaultEdgeCases : Prop :=
  ∀ (G : Hypermap.{u}) (_hG : G.MinimalCounterexample) (z : G.Dart)
    (hz_ne : G.node z ≠ z)
    (_hzz : G.node (G.node z) = z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color),
      ((G.walkupE z).walkupE
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Coloring k →
        ∀ x : G.Dart,
          WalkupTwoNodeFaceClassEdgeCoreExceptional G z x →
            G.walkupE_walkupE_faceClassColor hz_ne k
                (G.walkupE_walkupE_twoNodeFallback z) (G.edge x) ≠
              G.walkupE_walkupE_faceClassColor hz_ne k
                (G.walkupE_walkupE_twoNodeFallback z) x

theorem walkupTwoNodeColoringExtension_of_localCases
    (hlocal : WalkupTwoNodeColoringLocalCases.{u}) :
    WalkupTwoNodeColoringExtension.{u} := by
  intro G hG z hz_ne hzz k hk
  rcases hlocal G hG z hz_ne hzz k hk with ⟨cz, cnode, hedge, hface⟩
  exact ⟨G.walkupE_walkupE_extendColorTwoNode hz_ne k cz cnode,
    ⟨hedge, hface⟩⟩

theorem walkupTwoNodeColoringExtension_of_faceClassEdgeCases
    (hedges : WalkupTwoNodeFaceClassEdgeCases.{u}) :
    WalkupTwoNodeColoringExtension.{u} := by
  intro G hG z hz_ne hzz k hk
  rcases hedges G hG z hz_ne hzz k hk with ⟨fallback, hedge⟩
  exact ⟨G.walkupE_walkupE_faceClassColor hz_ne k fallback,
    ⟨hedge, fun x =>
      Coloring.faceClassColor_face_eq (G := G)
        hG.bridgeless hz_ne hzz hk fallback x⟩⟩

theorem walkupTwoNodeFaceClassEdgeCases_of_exceptional
    (hexceptional : WalkupTwoNodeFaceClassExceptionalEdgeCases.{u}) :
    WalkupTwoNodeFaceClassEdgeCases.{u} := by
  intro G hG z hz_ne hzz k hk
  rcases hexceptional G hG z hz_ne hzz k hk with ⟨fallback, hfallback⟩
  refine ⟨fallback, ?_⟩
  intro x
  classical
  by_cases hex : WalkupTwoNodeFaceClassEdgeExceptional G z x
  · exact hfallback x hex
  · have hnot := hex
    simp [WalkupTwoNodeFaceClassEdgeExceptional] at hnot
    rcases hnot with
      ⟨hxz, hxnode, hxedgez, hexz, hexnode, hedgeNode,
        hfaceEdgeNode⟩
    exact Coloring.faceClassColor_edge_ne_of_plain_of_ne
      (G := G) hz_ne hG.plain hk fallback
      hxz hxnode hxedgez hexz hexnode hedgeNode hfaceEdgeNode

theorem walkupTwoNodeFaceClassExceptionalEdgeCases_of_core
    (hcore : WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u}) :
    WalkupTwoNodeFaceClassExceptionalEdgeCases.{u} := by
  intro G hG z hz_ne hzz k hk
  rcases hcore G hG z hz_ne hzz k hk with ⟨fallback, hfallback⟩
  refine ⟨fallback, ?_⟩
  intro x hex
  exact hfallback x
    (walkupTwoNodeFaceClassEdgeExceptional_core_of_plain
      hG.plain hzz hex)

theorem walkupTwoNodeFaceClassCoreExceptionalEdgeCases_of_default
    (hdefault : WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u}) :
    WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u} := by
  intro G hG z hz_ne hzz k hk
  exact ⟨G.walkupE_walkupE_twoNodeFallback z,
    hdefault G hG z hz_ne hzz k hk⟩

theorem walkupTwoNodeFaceClassCoreDefaultEdgeCases :
    WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u} := by
  intro G hG z hz_ne hzz k hk x hcore
  have hz_edge :
      G.walkupE_walkupE_faceClassColor hz_ne k
          (G.walkupE_walkupE_twoNodeFallback z) (G.edge z) ≠
        G.walkupE_walkupE_faceClassColor hz_ne k
          (G.walkupE_walkupE_twoNodeFallback z) z :=
    Coloring.faceClassColor_edge_ne_z
      (G := G) hG.plain hG.bridgeless hz_ne hzz hk
  have hnode_edge :
      G.walkupE_walkupE_faceClassColor hz_ne k
          (G.walkupE_walkupE_twoNodeFallback z) (G.edge (G.node z)) ≠
        G.walkupE_walkupE_faceClassColor hz_ne k
          (G.walkupE_walkupE_twoNodeFallback z) (G.node z) :=
    Coloring.faceClassColor_edge_ne_node
      (G := G) hG.plain hG.bridgeless hz_ne hzz hk
  rcases hcore with hx | hx | hx | hx | hedgeNode
  · subst x
    exact hz_edge
  · subst x
    exact hnode_edge
  · subst x
    simpa [Plain.edge_edge (G := G) hG.plain z] using hz_edge.symm
  · subst x
    simpa [Plain.edge_edge (G := G) hG.plain (G.node z)]
      using hnode_edge.symm
  · by_cases hxz : x = z
    · subst x
      exact hz_edge
    · by_cases hxnode : x = G.node z
      · subst x
        exact hnode_edge
      · exact Coloring.faceClassColor_edge_ne_of_outside
          (G := G) hG.bridgeless hz_ne hzz hk
          (G.walkupE_walkupE_twoNodeFallback z) hxz hxnode

theorem walkupTwoNodeColorExtension_of_coloringExtension
    (hext : WalkupTwoNodeColoringExtension.{u}) :
    WalkupTwoNodeColorExtension.{u} := by
  intro G hG z hz_ne hzz hcolor
  rcases hcolor with ⟨k, hk⟩
  rcases hext G hG z hz_ne hzz k hk with ⟨kG, hkG⟩
  exact ⟨kG, hkG⟩

theorem walkupTwoNodeColorExtension_of_localCases
    (hlocal : WalkupTwoNodeColoringLocalCases.{u}) :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    (walkupTwoNodeColoringExtension_of_localCases hlocal)

theorem walkupTwoNodeColorExtension_of_faceClassEdgeCases
    (hedges : WalkupTwoNodeFaceClassEdgeCases.{u}) :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    (walkupTwoNodeColoringExtension_of_faceClassEdgeCases hedges)

theorem walkupTwoNodeColoringExtension_of_faceClassExceptionalEdges
    (hexceptional : WalkupTwoNodeFaceClassExceptionalEdgeCases.{u}) :
    WalkupTwoNodeColoringExtension.{u} :=
  walkupTwoNodeColoringExtension_of_faceClassEdgeCases
    (walkupTwoNodeFaceClassEdgeCases_of_exceptional hexceptional)

theorem walkupTwoNodeColorExtension_of_faceClassExceptionalEdges
    (hexceptional : WalkupTwoNodeFaceClassExceptionalEdgeCases.{u}) :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    (walkupTwoNodeColoringExtension_of_faceClassExceptionalEdges
      hexceptional)

theorem walkupTwoNodeColoringExtension_of_faceClassCoreExceptionalEdges
    (hcore : WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u}) :
    WalkupTwoNodeColoringExtension.{u} :=
  walkupTwoNodeColoringExtension_of_faceClassExceptionalEdges
    (walkupTwoNodeFaceClassExceptionalEdgeCases_of_core hcore)

theorem walkupTwoNodeColorExtension_of_faceClassCoreExceptionalEdges
    (hcore : WalkupTwoNodeFaceClassCoreExceptionalEdgeCases.{u}) :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    (walkupTwoNodeColoringExtension_of_faceClassCoreExceptionalEdges hcore)

theorem walkupTwoNodeColoringExtension_of_faceClassCoreDefaultEdges
    (hdefault : WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u}) :
    WalkupTwoNodeColoringExtension.{u} :=
  walkupTwoNodeColoringExtension_of_faceClassCoreExceptionalEdges
    (walkupTwoNodeFaceClassCoreExceptionalEdgeCases_of_default hdefault)

theorem walkupTwoNodeColorExtension_of_faceClassCoreDefaultEdges
    (hdefault : WalkupTwoNodeFaceClassCoreDefaultEdgeCases.{u}) :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    (walkupTwoNodeColoringExtension_of_faceClassCoreDefaultEdges
      hdefault)

theorem walkupTwoNodeColoringExtension :
    WalkupTwoNodeColoringExtension.{u} :=
  walkupTwoNodeColoringExtension_of_faceClassCoreDefaultEdges
    walkupTwoNodeFaceClassCoreDefaultEdgeCases

theorem walkupTwoNodeColorExtension :
    WalkupTwoNodeColorExtension.{u} :=
  walkupTwoNodeColorExtension_of_coloringExtension
    walkupTwoNodeColoringExtension

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
