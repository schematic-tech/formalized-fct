import FourColorTheorem.FourColor.Reducibility.ContractMinimal.RestrictedContract

/-! Lifting contract colorings through selected-edge deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}} {cc : Finset G.Dart}

private theorem permReachable_eq_of_fixed
    {alpha : Type _} {sigma : Equiv.Perm alpha} {a b : alpha}
    (hfix : sigma a = a) (hab : PermReachable sigma a b) :
    b = a := by
  induction hab with
  | refl => rfl
  | @tail c d _ hcd ih =>
      subst c
      cases hcd with
      | forward => exact hfix
      | backward =>
          have hsymm : sigma.symm a = a := by
            apply sigma.injective
            simp [hfix]
          simp [hsymm]

/-- A face of the original map has a representative surviving selected-edge
deletion.  This is Coq's predicate `a y`. -/
def ContractDeleteHasFace
    (hplain : G.Plain) (x y : G.Dart) : Prop :=
  exists w : (G.contractDeleteMap hplain x).Dart,
    PermReachable G.face y (G.contractDeleteInclusion hplain x w)

/-- Pull a coloring of the deleted map back by selecting one surviving dart
in each original face.  Coq uses `Color0` when a face has no representative. -/
noncomputable def contractDeleteLiftColor
    (hplain : G.Plain) (x : G.Dart)
    (k : (G.contractDeleteMap hplain x).Dart -> Color) :
    G.Dart -> Color := by
  classical
  exact fun y => if h : G.ContractDeleteHasFace hplain x y then
    k (Classical.choose h) else Color.zero

theorem contractDeleteLiftColor_eq_of_reachable
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {k : (G.contractDeleteMap hplain x).Dart -> Color}
    (hk : (G.contractDeleteMap hplain x).ContractColoring
      (G.contractDeleteContract hplain x cc) k)
    {y : G.Dart} {w : (G.contractDeleteMap hplain x).Dart}
    (hyw : PermReachable G.face y
      (G.contractDeleteInclusion hplain x w)) :
    G.contractDeleteLiftColor hplain x k y = k w := by
  classical
  unfold contractDeleteLiftColor
  split
  next h =>
    have hchosen := Classical.choose_spec h
    have hwu : PermReachable G.face
        (G.contractDeleteInclusion hplain x w)
        (G.contractDeleteInclusion hplain x (Classical.choose h)) :=
      PermReachable.trans G.face
        (PermReachable.symm G.face hyw) hchosen
    exact ContractColoring.eq_of_face_reachable
      (G := G.contractDeleteMap hplain x) hk
      (G.contractDelete_facePermReachable_of_original
        hplain hbridgeless x hwu)
  next h => exact False.elim (h ⟨w, hyw⟩)

@[simp]
theorem contractDeleteLiftColor_inclusion
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {k : (G.contractDeleteMap hplain x).Dart -> Color}
    (hk : (G.contractDeleteMap hplain x).ContractColoring
      (G.contractDeleteContract hplain x cc) k)
    (w : (G.contractDeleteMap hplain x).Dart) :
    G.contractDeleteLiftColor hplain x k
        (G.contractDeleteInclusion hplain x w) = k w :=
  G.contractDeleteLiftColor_eq_of_reachable hplain hbridgeless x hk
    (PermReachable.refl G.face _)

theorem contractDeleteLiftColor_eq_zero_of_no_face
    (hplain : G.Plain) (x : G.Dart)
    (k : (G.contractDeleteMap hplain x).Dart -> Color)
    {y : G.Dart} (hy : ¬ G.ContractDeleteHasFace hplain x y) :
    G.contractDeleteLiftColor hplain x k y = Color.zero := by
  classical
  simp [contractDeleteLiftColor, hy]

/-- Coq `ae0`: if an original face has no surviving representative, neither
does the face across its edge. -/
theorem contractDeleteHasFace_edge_of_self
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    (hprecubic : G.Precubic) (x y : G.Dart)
    (hy : ¬ G.ContractDeleteHasFace hplain x y) :
    ¬ G.ContractDeleteHasFace hplain x (G.edge y) := by
  intro hedge
  rcases hedge with ⟨w, hew⟩
  have hyRange : y ∉ Set.range (G.contractDeleteInclusion hplain x) := by
    rintro ⟨u, rfl⟩
    exact hy ⟨u, PermReachable.refl G.face _⟩
  have hfyRange : G.face y ∉
      Set.range (G.contractDeleteInclusion hplain x) := by
    rintro ⟨u, hu⟩
    apply hy
    refine ⟨u, PermReachable.trans G.face
      (PermReachable.forward G.face y) ?_⟩
    simpa [hu] using PermReachable.refl G.face (G.face y)
  have hyDeleted : y = x ∨ y = G.edge x := by
    rw [G.mem_range_contractDeleteInclusion_iff hplain x y] at hyRange
    tauto
  have hfyDeleted : G.face y = x ∨ G.face y = G.edge x := by
    rw [G.mem_range_contractDeleteInclusion_iff hplain x (G.face y)] at hfyRange
    tauto
  have hedgeDeleted : G.edge y = x ∨ G.edge y = G.edge x := by
    rcases hyDeleted with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (Plain.edge_edge (G := G) hplain x)
  have hfaceCases : G.face y = y ∨ G.face y = G.edge y := by
    rcases hyDeleted with hyx | hyex <;>
        rcases hfyDeleted with hfyx | hfyex
    · exact Or.inl (hfyx.trans hyx.symm)
    · exact Or.inr (by simpa [hyx] using hfyex)
    · exact Or.inr (hfyx.trans (by
          calc
            x = G.edge (G.edge x) :=
              (Plain.edge_edge (G := G) hplain x).symm
            _ = G.edge y := by rw [hyex]))
    · exact Or.inl (hfyex.trans hyex.symm)
  rcases hfaceCases with hfaceSelf | hfaceEdge
  · have hnodeEdge : G.node y = G.edge y := by
      apply G.edge.injective
      rw [Plain.edge_edge (G := G) hplain y]
      simpa [hfaceSelf] using G.edge_node_face y
    rcases hprecubic y with hnodeSelf | hnodeTwo | hnodeThree
    · exact Plain.edge_ne (G := G) hplain y (hnodeEdge.symm.trans hnodeSelf)
    · have hfaceEdgeFixed : G.face (G.edge y) = G.edge y := by
        apply G.node.injective
        rw [G.node_face_edge]
        simpa [hnodeEdge] using hnodeTwo.symm
      have hwEq : G.contractDeleteInclusion hplain x w = G.edge y :=
        permReachable_eq_of_fixed hfaceEdgeFixed hew
      rcases hedgeDeleted with hedgeX | hedgeEX
      · exact (G.contractDeleteInclusion_ne hplain x w).1
          (hwEq.trans hedgeX)
      · exact (G.contractDeleteInclusion_ne hplain x w).2
          (hwEq.trans hedgeEX)
    · let z := G.face (G.edge y)
      have hnodeEdgeZ : G.node (G.edge y) = z := by
        apply G.node.injective
        dsimp [z]
        rw [G.node_face_edge]
        simpa [hnodeEdge] using hnodeThree
      have hedgeZ : G.edge z = G.face.symm (G.edge y) := by
        simpa [z, hnodeEdgeZ] using G.edge_node_eq_face_symm (G.edge y)
      apply hbridgeless z
      have hbackOne : PermReachable G.face z (G.edge y) := by
        simpa [z] using PermReachable.backward G.face z
      have hbackTwo : PermReachable G.face (G.edge y) (G.edge z) := by
        simpa [hedgeZ] using PermReachable.backward G.face (G.edge y)
      exact PermReachable.trans G.face hbackOne hbackTwo
  · apply hbridgeless y
    simpa [hfaceEdge] using PermReachable.forward G.face y

theorem contractDeleteLiftColor_face
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {k : (G.contractDeleteMap hplain x).Dart -> Color}
    (hk : (G.contractDeleteMap hplain x).ContractColoring
      (G.contractDeleteContract hplain x cc) k)
    (y : G.Dart) :
    G.contractDeleteLiftColor hplain x k (G.face y) =
      G.contractDeleteLiftColor hplain x k y := by
  classical
  by_cases hy : G.ContractDeleteHasFace hplain x y
  · rcases hy with ⟨w, hyw⟩
    have hfyw : PermReachable G.face (G.face y)
        (G.contractDeleteInclusion hplain x w) :=
      PermReachable.trans G.face
        (by simpa using PermReachable.backward G.face (G.face y)) hyw
    exact (G.contractDeleteLiftColor_eq_of_reachable
      hplain hbridgeless x hk hfyw).trans
        (G.contractDeleteLiftColor_eq_of_reachable
          hplain hbridgeless x hk hyw).symm
  · have hfy : ¬ G.ContractDeleteHasFace hplain x (G.face y) := by
      rintro ⟨w, hfyw⟩
      apply hy
      exact ⟨w, PermReachable.trans G.face
        (PermReachable.forward G.face y) hfyw⟩
    rw [G.contractDeleteLiftColor_eq_zero_of_no_face hplain x k hfy,
      G.contractDeleteLiftColor_eq_zero_of_no_face hplain x k hy]

/-- The two original faces merged by deletion receive the same lifted color.
This is Coq `k0ex`. -/
theorem contractDeleteLiftColor_edge_selected
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    (hprecubic : G.Precubic) (x : G.Dart)
    {k : (G.contractDeleteMap hplain x).Dart -> Color}
    (hk : (G.contractDeleteMap hplain x).ContractColoring
      (G.contractDeleteContract hplain x cc) k) :
    G.contractDeleteLiftColor hplain x k (G.edge x) =
      G.contractDeleteLiftColor hplain x k x := by
  classical
  by_cases hxFace : G.ContractDeleteHasFace hplain x x
  · have hexFace : G.ContractDeleteHasFace hplain x (G.edge x) := by
      by_contra hexFace
      have hxx := G.contractDeleteHasFace_edge_of_self
        hplain hbridgeless hprecubic x (G.edge x) hexFace
      apply hxx
      simpa [Plain.edge_edge (G := G) hplain x] using hxFace
    rcases hxFace with ⟨w, hw⟩
    rcases hexFace with ⟨u, hu⟩
    have hwBand : G.FaceBand [x, G.edge x]
        (G.contractDeleteInclusion hplain x w) :=
      ⟨x, by simp, hw⟩
    have huBand : G.FaceBand [x, G.edge x]
        (G.contractDeleteInclusion hplain x u) :=
      ⟨G.edge x, by simp, hu⟩
    have hwu : PermReachable (G.contractDeleteMap hplain x).face w u :=
      (G.contractDelete_facePermReachable_iff hplain hbridgeless x).2
        (Or.inl ⟨hwBand, huBand⟩)
    calc
      G.contractDeleteLiftColor hplain x k (G.edge x) = k u :=
        G.contractDeleteLiftColor_eq_of_reachable
          hplain hbridgeless x hk hu
      _ = k w := ContractColoring.eq_of_face_reachable
        (G := G.contractDeleteMap hplain x) hk
        hwu
      _ = G.contractDeleteLiftColor hplain x k x :=
        (G.contractDeleteLiftColor_eq_of_reachable
          hplain hbridgeless x hk hw).symm
  · have hexFace := G.contractDeleteHasFace_edge_of_self
      hplain hbridgeless hprecubic x x hxFace
    rw [G.contractDeleteLiftColor_eq_zero_of_no_face hplain x k hexFace,
      G.contractDeleteLiftColor_eq_zero_of_no_face hplain x k hxFace]

/-- Extend a contract coloring across the selected edge deleted for the
recursive call.  This is the final `k0` block of Coq `contract_coloring`. -/
theorem contractDelete_contractColoring_lift
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    (hprecubic : G.Precubic)
    {cc : Finset G.Dart} {x : G.Dart} (hx : x ∈ cc)
    {k : (G.contractDeleteMap hplain x).Dart -> Color}
    (hk : (G.contractDeleteMap hplain x).ContractColoring
      (G.contractDeleteContract hplain x cc) k) :
    G.ContractColoring cc (G.contractDeleteLiftColor hplain x k) := by
  classical
  let H := G.contractDeleteMap hplain x
  let f := G.contractDeleteInclusion hplain x
  have hsurvive {y : G.Dart} (hyx : y ≠ x)
      (hyex : y ≠ G.edge x) :
      exists w : H.Dart, f w = y := by
    exact (G.mem_range_contractDeleteInclusion_iff hplain x y).2
      ⟨hyx, hyex⟩
  have hselected := G.contractDeleteLiftColor_edge_selected
    hplain hbridgeless hprecubic x hk
  constructor
  · intro y hyContract
    by_cases hyx : y = x
    · subst y
      exact hselected
    by_cases hyex : y = G.edge x
    · subst y
      simpa [Plain.edge_edge (G := G) hplain x] using hselected.symm
    rcases hsurvive hyx hyex with ⟨w, hw⟩
    have hwEdge : f (H.edge w) = G.edge y := by
      change G.contractDeleteInclusion hplain x
        ((G.contractDeleteMap hplain x).edge w) = G.edge y
      rw [G.contractDeleteInclusion_edge hplain x]
      exact congrArg G.edge hw
    have hwContract : w ∈ H.contractClosure
        (G.contractDeleteContract hplain x cc) := by
      apply (G.mem_contractDeleteClosure_iff hplain x cc w).2
      simpa [f, hw] using hyContract
    calc
      G.contractDeleteLiftColor hplain x k (G.edge y) =
          G.contractDeleteLiftColor hplain x k (f (H.edge w)) := by
        rw [hwEdge]
      _ = k (H.edge w) := G.contractDeleteLiftColor_inclusion
        hplain hbridgeless x hk (H.edge w)
      _ = k w := hk.1 w hwContract
      _ = G.contractDeleteLiftColor hplain x k (f w) :=
        (G.contractDeleteLiftColor_inclusion
          hplain hbridgeless x hk w).symm
      _ = G.contractDeleteLiftColor hplain x k y := by rw [hw]
  · constructor
    · intro y hyContract hsame
      have hyx : y ≠ x := by
        rintro rfl
        exact hyContract (G.mem_contractClosure_self hx)
      have hyex : y ≠ G.edge x := by
        rintro rfl
        exact hyContract (G.mem_contractClosure_edge hx)
      rcases hsurvive hyx hyex with ⟨w, hw⟩
      have hwEdge : f (H.edge w) = G.edge y := by
        change G.contractDeleteInclusion hplain x
          ((G.contractDeleteMap hplain x).edge w) = G.edge y
        rw [G.contractDeleteInclusion_edge hplain x]
        exact congrArg G.edge hw
      have hwContract : w ∉ H.contractClosure
          (G.contractDeleteContract hplain x cc) := by
        intro hwContract
        apply hyContract
        have := (G.mem_contractDeleteClosure_iff hplain x cc w).1
          hwContract
        simpa [f, hw] using this
      apply hk.2.1 w hwContract
      calc
        k (H.edge w) =
            G.contractDeleteLiftColor hplain x k (f (H.edge w)) :=
          (G.contractDeleteLiftColor_inclusion
            hplain hbridgeless x hk (H.edge w)).symm
        _ = G.contractDeleteLiftColor hplain x k (G.edge y) := by
          rw [hwEdge]
        _ = G.contractDeleteLiftColor hplain x k y := hsame
        _ = G.contractDeleteLiftColor hplain x k (f w) := by rw [hw]
        _ = k w := G.contractDeleteLiftColor_inclusion
          hplain hbridgeless x hk w
    · exact G.contractDeleteLiftColor_face hplain hbridgeless x hk

/-- Nested contract-size induction on maps already strictly smaller than the
fixed minimal counterexample. -/
private theorem contractColorable_of_noContractRing_of_smaller
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample) :
    forall n : Nat, forall H : Hypermap.{u},
      H.PlanarBridgelessPlainPrecubic ->
      Fintype.card H.Dart < Fintype.card G.Dart ->
      forall cc : Finset H.Dart, cc.card <= n ->
        (forall p : List H.Dart, ¬ H.ContractRing cc p) ->
          H.ContractColorable cc := by
  intro n
  induction n with
  | zero =>
      intro H hgeom hcard cc hcc _hnoRing
      have hcardZero : cc.card = 0 := Nat.eq_zero_of_le_zero hcc
      have hccEmpty : cc = ∅ := Finset.card_eq_zero.mp hcardZero
      subst cc
      exact (H.contractColorable_empty_iff).2
        (hG.colorable_of_smaller H hgeom hcard)
  | succ n ih =>
      intro H hgeom hcard cc hcc hnoRing
      by_cases hccEmpty : cc = ∅
      · subst cc
        exact (H.contractColorable_empty_iff).2
          (hG.colorable_of_smaller H hgeom hcard)
      · rcases Finset.nonempty_iff_ne_empty.mpr hccEmpty with ⟨x, hx⟩
        let H2 := H.contractDeleteMap hgeom.base.plain x
        let cc2 := H.contractDeleteContract hgeom.base.plain x cc
        have hgeom2 : H2.PlanarBridgelessPlainPrecubic :=
          H.contractDelete_planarBridgelessPlainPrecubic
            hgeom hx hnoRing
        have hcard2 : Fintype.card H2.Dart < Fintype.card G.Dart :=
          (H.contractDelete_dart_card_lt hgeom.base.plain x).trans hcard
        have hcc2 : cc2.card <= n := by
          have hlt := H.card_contractDeleteContract_lt
            hgeom.base.plain hx
          dsimp [cc2]
          omega
        have hnoRing2 : forall p : List H2.Dart,
            ¬ H2.ContractRing cc2 p := by
          exact H.contractDelete_noContractRing
            hgeom.base.plain hgeom.base.base.bridgeless hx hnoRing
        rcases ih H2 hgeom2 hcard2 cc2 hcc2 hnoRing2 with ⟨k, hk⟩
        exact ⟨H.contractDeleteLiftColor hgeom.base.plain x k,
          H.contractDelete_contractColoring_lift
            hgeom.base.plain hgeom.base.base.bridgeless
            hgeom.precubic hx hk⟩

/-- Coq `contract_coloring`, separated from the valid-contract ring
exclusions: any nonempty ring-free contract in a minimal counterexample is
contract-colourable. -/
theorem contractColorable_of_noContractRing
    (hG : G.MinimalCounterexample)
    {cc : Finset G.Dart} (hcc : cc.Nonempty)
    (hnoRing : forall p : List G.Dart, ¬ G.ContractRing cc p) :
    G.ContractColorable cc := by
  rcases hcc with ⟨x, hx⟩
  let G2 := G.contractDeleteMap hG.plain x
  let cc2 := G.contractDeleteContract hG.plain x cc
  have hgeom2 : G2.PlanarBridgelessPlainPrecubic :=
    G.contractDelete_planarBridgelessPlainPrecubic
      hG.geometry hx hnoRing
  have hcard2 : Fintype.card G2.Dart < Fintype.card G.Dart :=
    G.contractDelete_dart_card_lt hG.plain x
  have hnoRing2 : forall p : List G2.Dart,
      ¬ G2.ContractRing cc2 p := by
    exact G.contractDelete_noContractRing
      hG.plain hG.bridgeless hx hnoRing
  rcases contractColorable_of_noContractRing_of_smaller hG cc2.card G2
      hgeom2 hcard2 cc2 (Nat.le_refl _) hnoRing2 with ⟨k, hk⟩
  exact ⟨G.contractDeleteLiftColor hG.plain x k,
    G.contractDelete_contractColoring_lift
      hG.plain hG.bridgeless hG.precubic hx hk⟩

theorem noContractRing_of_validContract
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected) (hcubic : G.Cubic)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc) :
    forall p : List G.Dart, ¬ G.ContractRing cc p := by
  intro p hp
  rcases hvalid.size_eq_four_or_le_three with hfour | hthree
  · rcases hvalid.triad_of_card_four hfour with
      ⟨center, _hcenterKernel, htriad⟩
    exact G.no_contractRing_of_card_four_of_triad
      hG hconnected hcubic hvalid.sparse hfour htriad hp
  · exact G.no_contractRing_of_card_le_three
      hG hconnected hcubic hvalid.sparse hthree hp

/-- Coq `contract.v::contract_coloring`: every valid contract in a minimal
counterexample has a contract coloring. -/
theorem contract_coloring
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected) (hcubic : G.Cubic)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc) :
    G.ContractColorable cc := by
  apply G.contractColorable_of_noContractRing hG
  · exact Finset.card_pos.mp hvalid.size_pos
  · exact G.noContractRing_of_validContract
      hG hconnected hcubic hvalid

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
