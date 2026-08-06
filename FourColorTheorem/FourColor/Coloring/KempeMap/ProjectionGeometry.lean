import FourColorTheorem.FourColor.Coloring.KempeMap.ReductionCycle

/-!
Projection, lifting, node compatibility, and quasicubic geometry of the reduction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

theorem kempeProjection_injective
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    Function.Injective (G.kempeProjection z hplain) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

theorem kempeProjection_ne_deleted
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : (G.kempeReduction z hplain).Dart) :
    G.kempeProjection z hplain x ≠ z ∧
      G.kempeProjection z hplain x ≠ G.edge z := by
  constructor
  · exact x.1.2
  · intro hx
    apply x.2
    apply Subtype.ext
    exact hx

theorem exists_kempeReduction_dart
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    {x : G.Dart} (hxz : x ≠ z) (hxe : x ≠ G.edge z) :
    ∃ u : (G.kempeReduction z hplain).Dart,
      G.kempeProjection z hplain u = x := by
  let xN : (G.walkupN z).Dart := ⟨x, hxz⟩
  have hxN : xN ≠ G.kempeEdgeDart z hplain := by
    intro h
    exact hxe (congrArg Subtype.val h)
  exact ⟨⟨xN, hxN⟩, rfl⟩

theorem kempeEdgeDart_edge_fixed
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    (G.walkupN z).edge (G.kempeEdgeDart z hplain) =
      G.kempeEdgeDart z hplain := by
  apply Subtype.ext
  change
    (((G.permNode.walkupE z).face
      (G.kempeEdgeDart z hplain)).1 : G.Dart) = G.edge z
  exact (G.permNode.walkupE_face_apply_coe_of_eq
    (G.kempeEdgeDart z hplain)
    (Plain.edge_edge (G := G) hplain z))

/-- Coq `hE`: the reduction projection is an edge morphism. -/
theorem kempeProjection_edge
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : (G.kempeReduction z hplain).Dart) :
    G.kempeProjection z hplain
        ((G.kempeReduction z hplain).edge x) =
      G.edge (G.kempeProjection z hplain x) := by
  let M := G.walkupN z
  let ez : M.Dart := G.kempeEdgeDart z hplain
  have hez : M.edge ez = ez :=
    G.kempeEdgeDart_edge_fixed z hplain
  have houter :
      ((M.walkupE ez).edge x).1 = M.edge x.1 :=
    M.walkupE_edge_apply_coe_of_edge_fixed hez x
  have hxedge : G.edge x.1.1 ≠ z := by
    intro h
    have hx : x.1.1 = G.edge z :=
      Plain.eq_edge_of_edge_eq (G := G) hplain h
    exact x.2 (Subtype.ext hx)
  have hinner : (M.edge x.1).1 = G.edge x.1.1 := by
    exact G.permNode.walkupE_face_apply_coe_of_ne x.1 hxedge
  change (((M.walkupE ez).edge x).1).1 = G.edge x.1.1
  exact (congrArg Subtype.val houter).trans hinner

/-- Node action after the first `WalkupN` deletion, before deleting
`edge z`.  This is the inner calculation in Coq `hN`. -/
theorem walkupN_node_val
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (x : (G.walkupN z).Dart) :
    ((G.walkupN z).node x).1 =
      if G.node x.1 = G.edge z then G.node z
      else if G.node x.1 = z then G.edge z
      else G.node x.1 := by
  have hedgeCond :
      G.edge (G.node x.1) = z ↔ G.node x.1 = G.edge z := by
    constructor
    · exact Plain.eq_edge_of_edge_eq (G := G) hplain
    · intro h
      rw [h, Plain.edge_edge (G := G) hplain z]
  change
    ((G.permNode.walkupE z).edge x).1 =
      if G.node x.1 = G.edge z then G.node z
      else if G.node x.1 = z then G.edge z
      else G.node x.1
  rw [G.permNode.walkupE_edge_apply_coe]
  simp only [walkupSkipEdgeAux]
  change
    (if G.node z = z then G.node x.1
      else if G.edge (G.node x.1) = z then G.node z
      else if G.node x.1 = z then G.node (G.face z)
      else G.node x.1) =
      if G.node x.1 = G.edge z then G.node z
      else if G.node x.1 = z then G.edge z
      else G.node x.1
  rw [if_neg (hnode z)]
  by_cases hfirst : G.node x.1 = G.edge z
  · rw [if_pos hfirst, if_pos (hedgeCond.mpr hfirst)]
  · rw [if_neg hfirst, if_neg (fun h => hfirst (hedgeCond.mp h))]
    by_cases hsecond : G.node x.1 = z
    · rw [if_pos hsecond, if_pos hsecond]
      exact Plain.node_face_eq_edge (G := G) hplain z
    · rw [if_neg hsecond, if_neg hsecond]

/-- Coq `hN`: the reduction node projection is the original node action with
the two deleted targets spliced in the indicated order. -/
theorem kempeProjection_node
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (x : (G.kempeReduction z hplain).Dart) :
    G.kempeProjection z hplain
        ((G.kempeReduction z hplain).node x) =
      if G.node (G.kempeProjection z hplain x) = z then
        G.node (G.edge z)
      else if G.node (G.kempeProjection z hplain x) = G.edge z then
        G.node z
      else G.node (G.kempeProjection z hplain x) := by
  let M := G.walkupN z
  let ez : M.Dart := G.kempeEdgeDart z hplain
  let y : G.Dart := G.kempeProjection z hplain x
  have hyz : y ≠ z := (G.kempeProjection_ne_deleted z hplain x).1
  have hyez : y ≠ G.edge z :=
    (G.kempeProjection_ne_deleted z hplain x).2
  have hMnode (a : M.Dart) :
      (M.node a).1 =
        if G.node a.1 = G.edge z then G.node z
        else if G.node a.1 = z then G.edge z
        else G.node a.1 :=
    G.walkupN_node_val z hplain hnode a
  by_cases hyNodeZ : G.node y = z
  · have hnodeEdgeNotZ : G.node (G.edge z) ≠ z := by
      intro h
      exact hyez (G.node.injective (hyNodeZ.trans h.symm))
    have hyNodeNotE : G.node y ≠ G.edge z := by
      intro h
      exact Plain.edge_ne (G := G) hplain z (h.symm.trans hyNodeZ)
    have hze : z ≠ G.edge z :=
      (Plain.edge_ne (G := G) hplain z).symm
    have hMxe : M.node x.1 = ez := by
      apply Subtype.ext
      rw [hMnode x.1]
      change
        (if G.node y = G.edge z then G.node z
          else if G.node y = z then G.edge z else G.node y) = G.edge z
      simp [hyNodeZ, hze]
    have hMez : (M.node ez).1 = G.node (G.edge z) := by
      rw [hMnode ez]
      change
        (if G.node (G.edge z) = G.edge z then G.node z
          else if G.node (G.edge z) = z then G.edge z
          else G.node (G.edge z)) = G.node (G.edge z)
      simp [hnode (G.edge z), hnodeEdgeNotZ]
    change
      (PermSkip.skipAux M.node ez x.1).1 =
        if G.node y = z then G.node (G.edge z)
        else if G.node y = G.edge z then G.node z else G.node y
    rw [if_pos hyNodeZ]
    simp only [PermSkip.skipAux, hMxe, if_pos]
    exact hMez
  · by_cases hyNodeE : G.node y = G.edge z
    · have hMval : (M.node x.1).1 = G.node z := by
        rw [hMnode x.1]
        change
          (if G.node y = G.edge z then G.node z
            else if G.node y = z then G.edge z else G.node y) = G.node z
        simp [hyNodeE]
      have hMne : M.node x.1 ≠ ez := by
        intro h
        have hnzedge : G.node z = G.edge z := by
          exact hMval.symm.trans (congrArg Subtype.val h)
        exact hyz (G.node.injective (hyNodeE.trans hnzedge.symm))
      change
        (PermSkip.skipAux M.node ez x.1).1 =
          if G.node y = z then G.node (G.edge z)
          else if G.node y = G.edge z then G.node z else G.node y
      rw [if_neg hyNodeZ, if_pos hyNodeE]
      simp only [PermSkip.skipAux, if_neg hMne]
      exact hMval
    · have hMval : (M.node x.1).1 = G.node y := by
        rw [hMnode x.1]
        change
          (if G.node y = G.edge z then G.node z
            else if G.node y = z then G.edge z else G.node y) = G.node y
        simp [hyNodeE, hyNodeZ]
      have hMne : M.node x.1 ≠ ez := by
        intro h
        exact hyNodeE (hMval.symm.trans (congrArg Subtype.val h))
      change
        (PermSkip.skipAux M.node ez x.1).1 =
          if G.node y = z then G.node (G.edge z)
          else if G.node y = G.edge z then G.node z else G.node y
      rw [if_neg hyNodeZ, if_neg hyNodeE]
      simp only [PermSkip.skipAux, if_neg hMne]
      exact hMval

theorem kempeProjection_node_eq_splice
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (x : (G.kempeReduction z hplain).Dart) :
    G.kempeProjection z hplain
        ((G.kempeReduction z hplain).node x) =
      G.kempeSpliceNode z (G.kempeProjection z hplain x) := by
  exact G.kempeProjection_node z hplain hnode x

/-- Lift a projected spliced cycle to the actual Walkup reduction. -/
theorem kempeLiftList_cycle
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (q : List G.Dart)
    (hq : forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z)
    (hqn : q.Nodup)
    (hqcycle : FunctionCycle (G.kempeSpliceNode z) q) :
    FunctionCycle (G.kempeReduction z hplain).node
      (G.kempeLiftList z hplain q hq) := by
  apply functionCycle_of_map_injective
    (G.kempeProjection_injective z hplain)
    (G.kempeLiftList_nodup z hplain q hq hqn)
  · simpa [G.kempeLiftList_projection z hplain q hq] using hqcycle
  · intro x _
    exact G.kempeProjection_node_eq_splice z hplain hnode x

/-- Quasicubicity transport in the exact situation of Coq `cubHs`.  The
projected reduced boundary contains every surviving old boundary dart and,
in the non-fixed-face case, also contains `face z`; hence no splice is visible
on a node orbit outside that boundary. -/
theorem kempeLiftList_quasicubic
    (G : Hypermap.{u})
    (z : G.Dart) (hplain : G.Plain)
    (hnode : forall y : G.Dart, G.node y ≠ y)
    (r q : List G.Dart)
    (hrcycle : FunctionCycle G.node r)
    (hzr : z ∈ r)
    (hrquasi : G.Quasicubic r)
    (hq : forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z)
    (hqn : q.Nodup)
    (hqcycle : FunctionCycle (G.kempeSpliceNode z) q)
    (hcover : forall x, x ∈ r -> x ≠ z -> x ≠ G.edge z -> x ∈ q)
    (hface : G.face z = z ∨ G.face z ∈ q) :
    (G.kempeReduction z hplain).Quasicubic
      (G.kempeLiftList z hplain q hq) := by
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  let s := G.kempeLiftList z hplain q hq
  have hsCycle : FunctionCycle H.node s :=
    G.kempeLiftList_cycle z hplain hnode q hq hqn hqcycle
  have hsNodup : s.Nodup :=
    G.kempeLiftList_nodup z hplain q hq hqn
  have hprojInj : Function.Injective proj :=
    G.kempeProjection_injective z hplain
  have hprojMap : s.map proj = q :=
    G.kempeLiftList_projection z hplain q hq
  have houtsideNode (x : H.Dart) (hx : x ∉ s) : H.node x ∉ s := by
    intro hmem
    exact hx ((FunctionCycle.image_mem_iff hsCycle H.node.injective x).1 hmem)
  have hnotQ (x : H.Dart) (hx : x ∉ s) : proj x ∉ q := by
    intro hmem
    have hmemMap : proj x ∈ s.map proj := by
      rw [hprojMap]
      exact hmem
    rcases List.mem_map.mp hmemMap with ⟨y, hy, hyx⟩
    exact hx (by simpa [hprojInj hyx] using hy)
  have hnotR (x : H.Dart) (hx : x ∉ s) : proj x ∉ r := by
    intro hmem
    exact hnotQ x hx
      (hcover (proj x) hmem
        (G.kempeProjection_ne_deleted z hplain x).1
        (G.kempeProjection_ne_deleted z hplain x).2)
  have hcomm (x : H.Dart) (hx : x ∉ s) :
      proj (H.node x) = G.node (proj x) := by
    have hnodeZ : G.node (proj x) ≠ z := by
      intro h
      have hnodeMem : G.node (proj x) ∈ r := by simpa [h] using hzr
      have hxMem : proj x ∈ r :=
        (FunctionCycle.image_mem_iff hrcycle G.node.injective (proj x)).1
          hnodeMem
      exact hnotR x hx hxMem
    have hnodeEdge : G.node (proj x) ≠ G.edge z := by
      intro h
      have hxFace : proj x = G.face z := by
        apply G.node.injective
        rw [h, Plain.node_face_eq_edge (G := G) hplain z]
      rcases hface with hfixed | hfaceQ
      · exact (G.kempeProjection_ne_deleted z hplain x).1
          (hxFace.trans hfixed)
      · exact hnotQ x hx (by simpa [hxFace] using hfaceQ)
    change
      G.kempeProjection z hplain
          ((G.kempeReduction z hplain).node x) =
        G.node (G.kempeProjection z hplain x)
    rw [G.kempeProjection_node_eq_splice z hplain hnode]
    rw [kempeSpliceNode,
      if_neg (by simpa [proj] using hnodeZ),
      if_neg (by simpa [proj] using hnodeEdge)]
  intro x hx
  have hx1 : H.node x ∉ s := houtsideNode x hx
  have hx2 : H.node (H.node x) ∉ s :=
    houtsideNode (H.node x) hx1
  have hcubic := hrquasi (proj x) (hnotR x hx)
  constructor
  · apply hprojInj
    calc
      proj (H.node (H.node (H.node x))) =
          G.node (proj (H.node (H.node x))) := hcomm _ hx2
      _ = G.node (G.node (proj (H.node x))) := by rw [hcomm _ hx1]
      _ = G.node (G.node (G.node (proj x))) := by rw [hcomm _ hx]
      _ = proj x := hcubic.1
  · intro hfixed
    have hp := congrArg proj hfixed
    rw [hcomm x hx] at hp
    exact hcubic.2 hp


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
