import FourColorTheorem.FourColor.Reducibility.Embedding.Contract

/-! Cotrace transfer through a configuration embedding. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `embed_cotrace`: traces of the embedded remainder, read from the
one-place right rotation of its patch boundary. -/
def EmbedCotrace
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) (et : ColSeq) : Prop :=
  (embeddedRemainder hG hH hembed).RingTrace
    (rotateRightOne (embeddedRemainderBoundary hG hH hembed)) et

/-- Coq `embed_closure`: the embedded-remainder cotrace predicate is
Kempe-closed. -/
theorem embed_closure
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    Chromogram.KempeClosed (hG.EmbedCotrace hH hembed) := by
  let R := embeddedRemainder hG hH hembed
  let b := embeddedRemainderBoundary hG hH hembed
  have geo : CyclePlanarPlainQuasicubic R b := {
    cycle := embeddedRemainderBoundary_nodeCycle hG hH hembed
    nodup := embeddedRemainderBoundary_nodup hG hH hembed
    eulerPlanar := embeddedRemainder_eulerPlanar hG hH hembed
    plain := embeddedRemainder_plain hG hH hembed
    quasicubic := embeddedRemainder_quasicubic hG hH hembed
  }
  change Chromogram.KempeClosed
    (R.RingTrace (b.rotate (b.length - 1)))
  exact Kempe_map R (b.rotate (b.length - 1))
    (CyclePlanarPlainQuasicubic.rotate R geo (b.length - 1))

theorem mem_contractClosure_embeddedContract_iff_of_offRing
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc)
    {x : G.Dart} (hxOff : x ∉ r) :
    extendEmbedding r h x ∈ H.contractClosure (embeddedContract h r cc) <->
      x ∈ G.contractClosure cc := by
  rw [hG.contractClosure_embeddedContract hH hembed cc]
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨z, hz, hzx⟩
    have hzOff : z ∉ r := by
      intro hzr
      exact hvalid.offRing hzr hz
    have hzxSource : z = x :=
      hG.extendEmbedding_injective hH hembed hzOff hxOff hzx
    simpa [hzxSource] using hz
  · intro hx
    exact Finset.mem_image.2 ⟨x, hx, rfl⟩

/-- Pull a target contract coloring back through Coq's total embedding. -/
theorem contractColoring_pullback
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc)
    {k : H.Dart -> Color}
    (hk : H.ContractColoring (embeddedContract h r cc) k) :
    G.ContractColoring cc (k ∘ extendEmbedding r h) := by
  have edgeNeOff : ∀ {x : G.Dart}, x ∉ r →
      x ∉ G.contractClosure cc →
        (k ∘ extendEmbedding r h) (G.edge x) ≠
          (k ∘ extendEmbedding r h) x := by
    intro x hxOff hxClosure
    rw [Function.comp_apply, Function.comp_apply,
      hG.extendEmbedding_edge hH hembed x]
    apply hk.2.1
    intro hxTarget
    exact hxClosure
      ((hG.mem_contractClosure_embeddedContract_iff_of_offRing
        hH hembed hvalid hxOff).1 hxTarget)
  constructor
  · intro x hx
    have hxOff : x ∉ r := by
      intro hxr
      exact hvalid.offRing hxr hx
    rw [Function.comp_apply, Function.comp_apply,
      hG.extendEmbedding_edge hH hembed x]
    exact hk.1 _
      ((hG.mem_contractClosure_embeddedContract_iff_of_offRing
        hH hembed hvalid hxOff).2 hx)
  · constructor
    · intro x hx
      by_cases hxOff : x ∉ r
      · exact edgeNeOff hxOff hx
      · have hxOn : x ∈ r := Classical.not_not.mp hxOff
        have hedgeOff : G.edge x ∉ r :=
          (hG.edgePerimeter x).resolve_left hxOff
        have hedgeClosure : G.edge x ∉ G.contractClosure cc := by
          intro hedgeMem
          exact hx ((G.contractClosure_edge_mem_iff_of_plain hG.plain).1
            hedgeMem)
        have hne := edgeNeOff hedgeOff hedgeClosure
        simpa [Function.comp_apply,
          Hypermap.Plain.edge_edge (G := G) hG.plain] using hne.symm
    · intro x
      exact ContractColoring.eq_of_face_reachable (G := H) hk
        (hG.extendEmbedding_faceReachable hH hembed
          (PermReachable.forward G.face x))

/-- Restrict a target contract coloring to the complementary remainder. -/
theorem embeddedRemainder_coloring_of_contractColoring
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc)
    {k : H.Dart -> Color}
    (hk : H.ContractColoring (embeddedContract h r cc) k) :
    (embeddedRemainder hG hH hembed).Coloring
      (k ∘ embeddedRemainderVal) := by
  let R := embeddedRemainder hG hH hembed
  let P := hG.embeddingPatch hH hembed
  have outsideClosure : ∀ w : R.Dart,
      embeddedRemainderVal w ∉
        H.contractClosure (embeddedContract h r cc) := by
    intro w hwClosure
    rw [hG.contractClosure_embeddedContract hH hembed cc] at hwClosure
    rcases Finset.mem_image.1 hwClosure with ⟨x, hx, hxMap⟩
    have hxOff : x ∉ r := by
      intro hxr
      exact hvalid.offRing hxr hx
    let xd : (embeddedDisk hG).Dart := ⟨x, hxOff⟩
    have hedgeXMem : G.edge x ∈ G.contractClosure cc :=
      G.contractClosure_edge_mem_of_plain hG.plain hx
    have hedgeXOff : G.edge x ∉ r := by
      intro hedgeOn
      exact hvalid.offRing hedgeOn hedgeXMem
    have hxdOffBoundary : xd ∉ embeddedDiskBoundary hG := by
      intro hxdBoundary
      have hxCrossed := (mem_embeddedDiskBoundary_iff hG xd).1 hxdBoundary
      exact hedgeXOff ((hG.mem_edgePerimeter_iff x).1 hxCrossed)
    apply w.property
    exact ⟨xd, hxdOffBoundary, hxMap⟩
  constructor
  · intro w
    rw [Function.comp_apply, Function.comp_apply,
      embeddedRemainder_edge_val]
    exact hk.2.1 _ (outsideClosure w)
  · intro w
    exact ContractColoring.eq_of_face_reachable (G := H) hk
      (P.map_faceR_reachable w)

/-- Coq `embed_contract`: one target contract coloring induces the same trace
on the source reversed perimeter and on the rotated remainder boundary. -/
theorem embed_contract
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc) :
    ∃ et : ColSeq,
      G.ContractRingTrace cc r.reverse et ∧
        hG.EmbedCotrace hH hembed et := by
  classical
  rcases H.contract_coloring hH
      (Unavoidability.connectedMinimalCounterexamples_proved H hH)
      (Unavoidability.cubicMinimalCounterexamples_proved H hH)
      (hG.embed_valid_contract hH hembed hvalid) with ⟨k, hk⟩
  let kG : G.Dart -> Color := k ∘ extendEmbedding r h
  let R := embeddedRemainder hG hH hembed
  let b := embeddedRemainderBoundary hG hH hembed
  let kR : R.Dart -> Color := k ∘ embeddedRemainderVal
  let f : G.Dart -> Color := fun x => k (H.edge (extendEmbedding r h x))
  have hfg : ∀ x : G.Dart, f (G.node x) = kG x := by
    intro x
    have hsource : PermReachable G.face (G.edge (G.node x)) x := by
      rw [Hypermap.edge_node_eq_face_symm]
      simpa using PermReachable.forward G.face (G.face.symm x)
    have htarget := hG.extendEmbedding_faceReachable hH hembed hsource
    rw [hG.extendEmbedding_edge hH hembed (G.node x)] at htarget
    exact (ContractColoring.eq_of_face_reachable (G := H) hk htarget).symm
  have hrotateColors : (r.map f).rotate 1 = r.map kG := by
    calc
      (r.map f).rotate 1 = (r.rotate 1).map f := by
        rw [List.map_rotate]
      _ = (r.map G.node).map f := by
        rw [functionCycleMap_eq_rotate_one hG.cycle]
      _ = r.map kG := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro x hx
        exact hfg x
  have hdiskColors :
      (embeddedDiskBoundary hG).map (k ∘ embeddedDiskMap hG h) =
        r.map f := by
    have hmap := congrArg (List.map k)
      (map_embeddedDiskBoundary_target (h := h) hG)
    simpa [List.map_map, Function.comp_def, RevRing,
      hG.extendEmbedding_edge hH hembed] using hmap
  have hremColors : b.map kR = (r.map f).reverse := by
    have hremDisk : b.map kR =
        ((embeddedDiskBoundary hG).map
          (k ∘ embeddedDiskMap hG h)).reverse := by
      have hmap :
          ((embeddedRemainderBoundary hG hH hembed).map
              embeddedRemainderVal).map k =
            (((embeddedDiskBoundary hG).map
              (embeddedDiskMap hG h)).reverse).map k :=
        congrArg (List.map k)
          (map_embeddedRemainderBoundary hG hH hembed)
      simpa only [b, kR, List.map_map, List.map_reverse] using hmap
    rw [hremDisk, hdiskColors]
  have hboundaryColors :
      R.colorsOn kR (rotateRightOne b) = G.colorsOn kG r.reverse := by
    change (rotateRightOne b).map kR = r.reverse.map kG
    rw [map_rotateRightOne, hremColors, rotateRightOne_reverse,
      hrotateColors, List.map_reverse]
  let et := ColSeq.trace (G.colorsOn kG r.reverse)
  refine ⟨et, ?_, ?_⟩
  · exact ⟨kG, hG.contractColoring_pullback hH hembed hvalid hk, rfl⟩
  · unfold EmbedCotrace
    refine ⟨kR,
      hG.embeddedRemainder_coloring_of_contractColoring hH hembed hvalid hk,
      ?_⟩
    exact congrArg ColSeq.trace hboundaryColors.symm

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
