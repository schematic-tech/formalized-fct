import FourColorTheorem.FourColor.Reducibility.ContractMinimal.RingObstructions

/-! Geometry of deleting a selected contract edge. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}} {cc : Finset G.Dart}
/-! ### Deleting a selected contract edge

Coq `contract_coloring` removes a selected dart `x` and its edge mate by two
successive `WalkupF` operations.  Unfolding the cyclic permutations, this is
exactly two `WalkupE` operations on `G.permFace`, followed by `permNode`.  The
latter presentation lets us reuse the generic two-skip orbit API.
-/

/-- The surviving copy of `edge x` after the first face deletion. -/
def contractDeleteEdgeDart
    (hplain : G.Plain) (x : G.Dart) :
    (G.permFace.walkupE x).Dart :=
  ⟨G.edge x, Plain.edge_ne (G := G) hplain x⟩

/-- Coq's `G2`: delete both darts of the selected plain edge by two
successive `WalkupF` operations. -/
def contractDeleteMap
    (hplain : G.Plain) (x : G.Dart) : Hypermap.{u} :=
  ((G.permFace.walkupE x).walkupE
    (G.contractDeleteEdgeDart hplain x)).permNode

/-- Inclusion of a surviving dart of `contractDeleteMap` into the original
hypermap. -/
def contractDeleteInclusion
    (hplain : G.Plain) (x : G.Dart) :
    (G.contractDeleteMap hplain x).Dart → G.Dart :=
  fun w => w.1.1

/-- The two-`WalkupE` presentation is definitionally the two-`WalkupF`
presentation used in Coq `contract_coloring`. -/
theorem contractDeleteMap_eq_walkupF_walkupF
    (hplain : G.Plain) (x : G.Dart) :
    G.contractDeleteMap hplain x =
      (G.walkupF x).walkupF
        (⟨G.edge x, Plain.edge_ne (G := G) hplain x⟩ :
          (G.walkupF x).Dart) := by
  rfl

theorem contractDeleteInclusion_injective
    (hplain : G.Plain) (x : G.Dart) :
    Function.Injective (G.contractDeleteInclusion hplain x) := by
  intro w w' hww'
  apply Subtype.ext
  apply Subtype.ext
  exact hww'

/-- The composed inclusion has image exactly the complement of the selected
plain edge orbit.  This is Coq `Eh`. -/
theorem mem_range_contractDeleteInclusion_iff
    (hplain : G.Plain) (x y : G.Dart) :
    y ∈ Set.range (G.contractDeleteInclusion hplain x) ↔
      y ≠ x ∧ y ≠ G.edge x := by
  exact G.permFace.walkupE_walkupE_val_mem_range_iff
    (G.contractDeleteEdgeDart hplain x) y

theorem contractDeleteInclusion_ne
    (hplain : G.Plain) (x : G.Dart)
    (w : (G.contractDeleteMap hplain x).Dart) :
    G.contractDeleteInclusion hplain x w ≠ x ∧
      G.contractDeleteInclusion hplain x w ≠ G.edge x := by
  exact (G.mem_range_contractDeleteInclusion_iff hplain x
    (G.contractDeleteInclusion hplain x w)).1 ⟨w, rfl⟩

/-- Edge orbits of the deleted map are precisely the surviving original edge
orbits.  This is Coq `hE`. -/
theorem contractDelete_edgePermReachable_iff
    (hplain : G.Plain) (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart} :
    PermReachable (G.contractDeleteMap hplain x).edge w w' ↔
      PermReachable G.edge
        (G.contractDeleteInclusion hplain x w)
        (G.contractDeleteInclusion hplain x w') := by
  exact G.permFace.walkupE_walkupE_nodePermReachable_iff

/-- Node orbits of the deleted map are precisely the surviving original node
orbits.  This is Coq `hN`. -/
theorem contractDelete_nodePermReachable_iff
    (hplain : G.Plain) (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart} :
    PermReachable (G.contractDeleteMap hplain x).node w w' ↔
      PermReachable G.node
        (G.contractDeleteInclusion hplain x w)
        (G.contractDeleteInclusion hplain x w') := by
  exact G.permFace.walkupE_walkupE_facePermReachable_iff

/-- The inclusion commutes pointwise with edge reversal.  This is Coq
`h_e`. -/
theorem contractDeleteInclusion_edge
    (hplain : G.Plain) (x : G.Dart)
    (w : (G.contractDeleteMap hplain x).Dart) :
    G.contractDeleteInclusion hplain x
        ((G.contractDeleteMap hplain x).edge w) =
      G.edge (G.contractDeleteInclusion hplain x w) := by
  exact G.permFace.walkupE_walkupE_node_apply_coe_of_node_node_eq
    (Plain.edge_ne (G := G) hplain x)
    (Plain.edge_edge (G := G) hplain x) w

/-- Deleting both darts of an edge preserves plainness. -/
theorem contractDelete_plain
    (hplain : G.Plain) (x : G.Dart) :
    (G.contractDeleteMap hplain x).Plain := by
  intro w
  constructor
  · apply G.contractDeleteInclusion_injective hplain x
    rw [G.contractDeleteInclusion_edge hplain x,
      G.contractDeleteInclusion_edge hplain x,
      hplain.edge_edge]
  · intro hedge
    have hproj := congrArg (G.contractDeleteInclusion hplain x) hedge
    rw [G.contractDeleteInclusion_edge hplain x] at hproj
    exact Plain.edge_ne (G := G) hplain _ hproj

/-- The two original face orbits incident with `x` are the affected edge
domain of `WalkupE` on `permFace`. -/
theorem faceBand_pair_iff_permFace_edgeDomain
    (x y : G.Dart) :
    G.FaceBand [x, G.edge x] y ↔ G.permFace.EdgeDomain x y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl (PermReachable.symm G.face hzy)
    · exact Or.inr (PermReachable.symm G.face hzy)
  · rintro (hyx | hyex)
    · exact ⟨x, by simp, PermReachable.symm G.face hyx⟩
    · exact ⟨G.edge x, by simp, PermReachable.symm G.face hyex⟩

/-- After the first deletion, the surviving copy of `edge x` is a self-link.
Consequently the second `WalkupF` deletion does not change face orbits. -/
theorem contractDeleteEdgeDart_link_self
    (hplain : G.Plain) (x : G.Dart) :
    (G.permFace.walkupE x).Link
      (G.contractDeleteEdgeDart hplain x)
      (G.contractDeleteEdgeDart hplain x) := by
  right
  left
  apply Subtype.ext
  symm
  exact G.permFace.walkupE_node_apply_coe_of_eq
    (G.contractDeleteEdgeDart hplain x)
    (Plain.edge_edge (G := G) hplain x)

/-- The second deletion preserves the face orbits left by the first
deletion. -/
theorem contractDelete_facePermReachable_first_iff
    (hplain : G.Plain) (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart} :
    PermReachable (G.contractDeleteMap hplain x).face w w' ↔
      PermReachable (G.permFace.walkupE x).edge w.1 w'.1 := by
  let H := G.permFace.walkupE x
  let u := G.contractDeleteEdgeDart hplain x
  change PermReachable (H.walkupE u).edge w w' ↔
    PermReachable H.edge w.1 w'.1
  rw [H.walkupE_edge_eq_skip_edge_of_link_self
    (G.contractDeleteEdgeDart_link_self hplain x)]
  exact PermSkip.skip_permReachable_iff H.edge

/-- Coq `hF`: deleting a plain edge merges precisely its two incident
original face orbits and leaves every other face orbit unchanged. -/
theorem contractDelete_facePermReachable_iff
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart} :
    PermReachable (G.contractDeleteMap hplain x).face w w' ↔
      (G.FaceBand [x, G.edge x]
          (G.contractDeleteInclusion hplain x w) ∧
        G.FaceBand [x, G.edge x]
          (G.contractDeleteInclusion hplain x w')) ∨
      (¬ G.FaceBand [x, G.edge x]
          (G.contractDeleteInclusion hplain x w) ∧
        PermReachable G.face
          (G.contractDeleteInclusion hplain x w)
          (G.contractDeleteInclusion hplain x w')) := by
  rw [G.contractDelete_facePermReachable_first_iff hplain x]
  have hncross : ¬ G.permFace.CrossEdge x := by
    intro hcross
    exact hbridgeless x hcross
  by_cases hlink : G.permFace.Link x x
  · have hfaceFixed : G.face x = x := by
      change x = G.face x ∨ x = G.edge x ∨ x = G.node x at hlink
      rcases hlink with hface | hedge | hnode
      · exact hface.symm
      · exact False.elim
          (Plain.edge_ne (G := G) hplain x hedge.symm)
      · exfalso
        apply hbridgeless x
        have hfaceEdge : G.face (G.edge x) = x := by
          apply G.node.injective
          rw [G.node_face_edge]
          exact hnode
        exact PermReachable.symm G.face
          (by simpa [hfaceEdge] using
            PermReachable.forward G.face (G.edge x))
    have hskip :
        PermReachable (G.permFace.walkupE x).edge w.1 w'.1 ↔
          PermReachable G.face w.1.1 w'.1.1 := by
      rw [G.permFace.walkupE_edge_eq_skip_edge_of_link_self hlink]
      exact PermSkip.skip_permReachable_iff G.face
    have band_reaches_edge : ∀ {y : G.Dart}, y ≠ x →
        G.FaceBand [x, G.edge x] y →
          PermReachable G.face y (G.edge x) := by
      intro y hyx hyBand
      rcases (G.faceBand_pair_iff_permFace_edgeDomain x y).1 hyBand with
        hyFaceX | hyFaceEdge
      · exact False.elim (hyx
          (PermSkip.eq_of_permReachable_fixed G.face hfaceFixed hyFaceX))
      · exact hyFaceEdge
    constructor
    · intro hww'
      have hface := hskip.1 hww'
      by_cases hwBand : G.FaceBand [x, G.edge x] w.1.1
      · exact Or.inl ⟨hwBand,
          FaceBand.of_faceReachable (G := G) hwBand hface⟩
      · exact Or.inr ⟨hwBand, hface⟩
    · rintro (hbands | ⟨_, hface⟩)
      · apply hskip.2
        exact PermReachable.trans G.face
          (band_reaches_edge
            (G.contractDeleteInclusion_ne hplain x w).1 hbands.1)
          (PermReachable.symm G.face
            (band_reaches_edge
              (G.contractDeleteInclusion_ne hplain x w').1 hbands.2))
      · exact hskip.2 hface
  · classical
    have hmerge :=
      G.permFace.walkupE_edgePermReachable_iff_of_not_link_self_of_not_cross
        hlink hncross (x := w.1) (y := w'.1)
    constructor
    · intro hww'
      have hm := hmerge.1 hww'
      by_cases hwBand : G.FaceBand [x, G.edge x] w.1.1
      · have hwDom :=
          (G.faceBand_pair_iff_permFace_edgeDomain x w.1.1).1 hwBand
        rw [if_pos hwDom] at hm
        exact Or.inl ⟨hwBand,
          (G.faceBand_pair_iff_permFace_edgeDomain x w'.1.1).2 hm⟩
      · have hwDom : ¬ G.permFace.EdgeDomain x w.1.1 := by
          intro hdom
          exact hwBand
            ((G.faceBand_pair_iff_permFace_edgeDomain x w.1.1).2 hdom)
        rw [if_neg hwDom] at hm
        exact Or.inr ⟨hwBand, hm⟩
    · rintro (hbands | ⟨hwBand, hface⟩)
      · apply hmerge.2
        have hwDom :=
          (G.faceBand_pair_iff_permFace_edgeDomain x w.1.1).1 hbands.1
        rw [if_pos hwDom]
        exact (G.faceBand_pair_iff_permFace_edgeDomain x w'.1.1).1 hbands.2
      · apply hmerge.2
        have hwDom : ¬ G.permFace.EdgeDomain x w.1.1 := by
          intro hdom
          exact hwBand
            ((G.faceBand_pair_iff_permFace_edgeDomain x w.1.1).2 hdom)
        rw [if_neg hwDom]
        exact hface

/-- Coq's `bridgeless G2` argument: a bridge after deleting a selected edge
would be a forbidden two-dart contract ring in the original map. -/
theorem contractDelete_bridgeless_of_no_contractRing
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    {cc : Finset G.Dart} {x : G.Dart}
    (hx : x ∈ cc)
    (hnoRing : ∀ p : List G.Dart, ¬ G.ContractRing cc p) :
    (G.contractDeleteMap hplain x).Bridgeless := by
  intro w hw
  let a := G.contractDeleteInclusion hplain x w
  have hface :=
    (G.contractDelete_facePermReachable_iff
      hplain hbridgeless x).1 hw
  rw [G.contractDeleteInclusion_edge hplain x] at hface
  rcases hface with hbands | hordinary
  · rcases hbands.1 with ⟨s₀, hs₀mem, hs₀a⟩
    rcases hbands.2 with ⟨s₁, hs₁mem, hs₁edge⟩
    have hs₀s₁ : s₀ ≠ s₁ := by
      intro hs
      subst s₁
      apply hbridgeless a
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hs₀a) hs₁edge
    have hedgeS₁ : G.edge s₁ = s₀ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs₀mem hs₁mem
      rcases hs₀mem with hs₀ | hs₀ <;> rcases hs₁mem with hs₁ | hs₁
      · exact False.elim (hs₀s₁ (hs₀.trans hs₁.symm))
      · calc
          G.edge s₁ = G.edge (G.edge x) := by rw [hs₁]
          _ = x := Plain.edge_edge (G := G) hplain x
          _ = s₀ := hs₀.symm
      · calc
          G.edge s₁ = G.edge x := by rw [hs₁]
          _ = s₀ := hs₀.symm
      · exact False.elim (hs₀s₁ (hs₀.trans hs₁.symm))
    have hrlinkAS₁ : G.RLink a s₁ := by
      exact PermReachable.symm G.face hs₁edge
    have hrlinkS₁A : G.RLink s₁ a := by
      unfold RLink
      rw [hedgeS₁]
      exact hs₀a
    have hnotFace : ¬ PermReachable G.face a s₁ := by
      intro haS₁
      apply hbridgeless a
      exact PermReachable.trans G.face haS₁ hs₁edge
    have hcycle : G.SimpleRLinkCycle [a, s₁] := by
      constructor
      · exact ⟨⟨hrlinkAS₁, by simp⟩, hrlinkS₁A⟩
      · simp [FaceSimple, hnotFace]
    have hedgeANeS₁ : G.edge a ≠ s₁ := by
      have hsurvive :=
        G.contractDeleteInclusion_ne hplain x
          ((G.contractDeleteMap hplain x).edge w)
      rw [G.contractDeleteInclusion_edge hplain x] at hsurvive
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs₁mem
      rcases hs₁mem with rfl | rfl
      · exact hsurvive.1
      · exact hsurvive.2
    have hproper : G.ProperRing [a, s₁] := by
      left
      simpa [EdgePath] using hedgeANeS₁
    apply hnoRing [a, s₁]
    refine ⟨hcycle, hproper, ?_⟩
    intro y hy
    simp only [List.tail_cons, List.mem_singleton] at hy
    subst y
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs₁mem
    rcases hs₁mem with rfl | rfl
    · exact G.mem_contractClosure_self hx
    · exact G.mem_contractClosure_edge hx
  · exact hbridgeless
      (G.contractDeleteInclusion hplain x w) hordinary.2

/-- Two face deletions preserve Euler-planarity. -/
theorem contractDelete_eulerPlanar
    (hplain : G.Plain) (hplanar : G.EulerPlanar) (x : G.Dart) :
    (G.contractDeleteMap hplain x).EulerPlanar := by
  let A := G.permFace
  let H₁ := A.walkupE x
  let u := G.contractDeleteEdgeDart hplain x
  change (H₁.walkupE u).permNode.EulerPlanar
  apply ((H₁.walkupE u).permNode_eulerPlanar_iff).2
  apply Unavoidability.walkupE_eulerPlanar_of_eulerPlanar
  apply Unavoidability.walkupE_eulerPlanar_of_eulerPlanar
  exact (G.permFace_eulerPlanar_iff).2 hplanar

/-- Deleting both darts of an edge cannot increase any surviving node-orbit
period, so precubicity is preserved. -/
theorem contractDelete_precubic
    (hplain : G.Plain) (hprecubic : G.Precubic) (x : G.Dart) :
    (G.contractDeleteMap hplain x).Precubic := by
  let A := G.permFace
  let H₁ := A.walkupE x
  let u := G.contractDeleteEdgeDart hplain x
  have hfaceA : ∀ y : A.Dart,
      A.face y = y ∨ A.face (A.face y) = y ∨
        A.face (A.face (A.face y)) = y := hprecubic
  have hfaceH₁ : ∀ y : H₁.Dart,
      H₁.face y = y ∨ H₁.face (H₁.face y) = y ∨
        H₁.face (H₁.face (H₁.face y)) = y := by
    intro y
    exact PermSkip.skip_periodAtMostThree A.face hfaceA y
  intro w
  change (H₁.walkupE u).face w = w ∨
    (H₁.walkupE u).face ((H₁.walkupE u).face w) = w ∨
      (H₁.walkupE u).face
        ((H₁.walkupE u).face ((H₁.walkupE u).face w)) = w
  exact PermSkip.skip_periodAtMostThree H₁.face hfaceH₁ w

/-- Geometry package for the recursive deleted map in Coq
`contract_coloring`. -/
theorem contractDelete_planarBridgelessPlainPrecubic
    (hgeom : G.PlanarBridgelessPlainPrecubic)
    {cc : Finset G.Dart} {x : G.Dart} (hx : x ∈ cc)
    (hnoRing : ∀ p : List G.Dart, ¬ G.ContractRing cc p) :
    (G.contractDeleteMap hgeom.base.plain x).PlanarBridgelessPlainPrecubic where
  base := {
    base := {
      planar := G.contractDelete_eulerPlanar hgeom.base.plain
        hgeom.base.base.planar x
      bridgeless := G.contractDelete_bridgeless_of_no_contractRing
        hgeom.base.plain hgeom.base.base.bridgeless hx hnoRing }
    plain := G.contractDelete_plain hgeom.base.plain x }
  precubic := G.contractDelete_precubic hgeom.base.plain hgeom.precubic x


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
