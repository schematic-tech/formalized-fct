import FourColorTheorem.FourColor.Reducibility.Embedding.FaceTransport

/-! Embedded contracts and their validity. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Off the perimeter, node-orbit reachability between two images reflects
through the total embedding. -/
theorem extendEmbedding_nodeReachable_reflect
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hx : x ∉ r) (hy : y ∉ r)
    (hxy : PermReachable H.node
      (extendEmbedding r h x) (extendEmbedding r h y)) :
    PermReachable G.node x y := by
  rcases permReachable_exists_iterate H.node hxy with ⟨n, hn⟩
  have hoffIter : forall m : Nat,
      ((G.node : G.Dart -> G.Dart)^[m]) x ∉ r := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
        intro hmem
        rw [Function.iterate_succ_apply'] at hmem
        exact ih ((hG.cycle.image_mem_iff G.node.injective _).mp hmem)
  have hmapIter : forall m : Nat,
      extendEmbedding r h (((G.node : G.Dart -> G.Dart)^[m]) x) =
        ((H.node : H.Dart -> H.Dart)^[m]) (extendEmbedding r h x) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hG.extendEmbedding_node hH hembed (hoffIter m), ih]
  have hsourceEq :
      ((G.node : G.Dart -> G.Dart)^[n]) x = y := by
    apply hG.extendEmbedding_injective hH hembed (hoffIter n) hy
    exact (hmapIter n).trans hn
  exact permReachable_of_iterate_eq G.node hsourceEq

/-- The selected contract transported by the total configuration embedding. -/
noncomputable def embeddedContract
    {H : Hypermap.{u}} (h : G.Dart -> H.Dart) (r : List G.Dart)
    (cc : Finset G.Dart) : Finset H.Dart :=
  cc.image (extendEmbedding r h)

theorem contractClosure_embeddedContract
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (cc : Finset G.Dart) :
    H.contractClosure (embeddedContract h r cc) =
      (G.contractClosure cc).image (extendEmbedding r h) := by
  classical
  ext y
  constructor
  · intro hy
    rcases (H.mem_contractClosure_iff).1 hy with
      hy | ⟨z, hz, hzy⟩
    · rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
      exact Finset.mem_image.2
        ⟨x, G.mem_contractClosure_self hx, rfl⟩
    · rcases Finset.mem_image.1 hz with ⟨x, hx, rfl⟩
      exact Finset.mem_image.2
        ⟨G.edge x, G.mem_contractClosure_edge hx, by
          rw [hG.extendEmbedding_edge hH hembed x]
          exact hzy⟩
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    rcases (G.mem_contractClosure_iff).1 hx with hx | ⟨z, hz, hzx⟩
    · exact H.mem_contractClosure_self (Finset.mem_image.2 ⟨x, hx, rfl⟩)
    · rw [← hzx, hG.extendEmbedding_edge hH hembed z]
      exact H.mem_contractClosure_edge
        (Finset.mem_image.2 ⟨z, hz, rfl⟩)

theorem card_embeddedContract
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hoff : G.ContractOffRing r cc) :
    (embeddedContract h r cc).card = cc.card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  apply hG.extendEmbedding_injective hH hembed
  · intro hxr
    exact hoff hxr (G.mem_contractClosure_self hx)
  · intro hyr
    exact hoff hyr (G.mem_contractClosure_self hy)
  · exact hxy

theorem sparse_embeddedContract
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc) :
    H.Sparse (H.contractClosure (embeddedContract h r cc)) := by
  intro a b ha hb hab
  rw [hG.contractClosure_embeddedContract hH hembed cc] at ha hb
  rcases Finset.mem_image.1 ha with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.1 hb with ⟨y, hy, rfl⟩
  have hxOff : x ∉ r := by
    intro hxr
    exact hvalid.offRing hxr hx
  have hyOff : y ∉ r := by
    intro hyr
    exact hvalid.offRing hyr hy
  have hxy : PermReachable G.node x y :=
    hG.extendEmbedding_nodeReachable_reflect hH hembed hxOff hyOff hab
  exact congrArg (extendEmbedding r h) (hvalid.sparse hx hy hxy)

/-- Coq `embed_valid_contract`: a valid configuration contract becomes a
valid contract with empty perimeter in the minimal counterexample. -/
theorem embed_valid_contract
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hvalid : G.ValidContract r cc) :
    H.ValidContract [] (embeddedContract h r cc) := by
  classical
  have hcard : (embeddedContract h r cc).card = cc.card :=
    hG.card_embeddedContract hH hembed hvalid.offRing
  have hclosure : H.contractClosure (embeddedContract h r cc) =
      (G.contractClosure cc).image (extendEmbedding r h) :=
    hG.contractClosure_embeddedContract hH hembed cc
  refine {
    offRing := ?_
    sparse := hG.sparse_embeddedContract hH hembed hvalid
    size_pos := by simpa [hcard] using hvalid.size_pos
    size_le_four := by simpa [hcard] using hvalid.size_le_four
    triad_of_card_four := ?_
  }
  · intro x hx
    simp at hx
  · intro hfour
    have hfourSource : cc.card = 4 := by
      rw [hcard] at hfour
      exact hfour
    rcases hvalid.triad_of_card_four hfourSource with
      ⟨center, hcenterKernel, htriad⟩
    rcases htriad.1 with
      ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hca, hcb, hcc⟩
    have off_of_mem : ∀ {z : G.Dart}, z ∈ G.contractClosure cc → z ∉ r := by
      intro z hz hzr
      exact hvalid.offRing hzr hz
    have image_mem : ∀ {z : G.Dart}, z ∈ G.contractClosure cc →
        extendEmbedding r h z ∈
          H.contractClosure (embeddedContract h r cc) := by
      intro z hz
      rw [hclosure]
      exact Finset.mem_image.2 ⟨z, hz, rfl⟩
    have haOff := off_of_mem ha
    have hbOff := off_of_mem hb
    have hcOff := off_of_mem hc
    refine ⟨extendEmbedding r h center, ?_, ?_⟩
    · simp [Kernel, FaceBand]
    · constructor
      · refine ⟨extendEmbedding r h a, image_mem ha,
          extendEmbedding r h b, image_mem hb,
          extendEmbedding r h c, image_mem hc,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hG.extendEmbedding_not_faceReachable_of_kernel_ringAdj
            hH hembed hcenterKernel haOff hbOff hca hcb hab
        · exact hG.extendEmbedding_not_faceReachable_of_kernel_ringAdj
            hH hembed hcenterKernel haOff hcOff hca hcc hac
        · exact hG.extendEmbedding_not_faceReachable_of_kernel_ringAdj
            hH hembed hcenterKernel hbOff hcOff hcb hcc hbc
        · exact hG.extendEmbedding_ringAdj_map_of_kernel hH hembed
            hcenterKernel haOff hca
        · exact hG.extendEmbedding_ringAdj_map_of_kernel hH hembed
            hcenterKernel hbOff hcb
        · exact hG.extendEmbedding_ringAdj_map_of_kernel hH hembed
            hcenterKernel hcOff hcc
      · by_contra hnoMissing
        push Not at hnoMissing
        rcases htriad.2 with ⟨y, hy, hcenterY⟩
        have hyOff : y ∉ r := off_of_mem hy
        have hedgeYMem : G.edge y ∈ G.contractClosure cc :=
          G.contractClosure_edge_mem_of_plain hG.plain hy
        have hedgeYOff : G.edge y ∉ r := off_of_mem hedgeYMem
        have htargetY : H.RingAdj (extendEmbedding r h center)
            (extendEmbedding r h y) :=
          hnoMissing (extendEmbedding r h y) (image_mem hy)
        have htargetEdgeY : H.RingAdj (extendEmbedding r h center)
            (H.edge (extendEmbedding r h y)) := by
          rw [← hG.extendEmbedding_edge hH hembed y]
          exact hnoMissing (extendEmbedding r h (G.edge y))
            (image_mem hedgeYMem)
        rcases Birkhoff.ringAdj_or_edge_mem_spokeRing hH
            (Unavoidability.connectedMinimalCounterexamples_proved H hH)
            (Unavoidability.cubicMinimalCounterexamples_proved H hH)
            (extendEmbedding r h center) (extendEmbedding r h y)
            htargetY htargetEdgeY with hySpoke | hedgeYSpoke
        · have htargetFace : PermReachable H.face
              (extendEmbedding r h center)
              (extendEmbedding r h (G.node y)) := by
            have hmem :=
              (Birkhoff.mem_spokeRing_iff H
                (extendEmbedding r h center) (extendEmbedding r h y)).1
                hySpoke
            rw [hG.extendEmbedding_node hH hembed hyOff]
            exact hmem
          have hnodeYOff : G.node y ∉ r := by
            intro hnodeOn
            exact hyOff
              ((hG.cycle.image_mem_iff G.node.injective y).mp hnodeOn)
          have hsourceFace : PermReachable G.face center (G.node y) :=
            (hG.extendEmbedding_faceReachable_iff_of_kernel hH hembed
              hcenterKernel hnodeYOff).1 htargetFace
          apply hcenterY
          refine ⟨G.node y, hsourceFace, ?_⟩
          rw [Hypermap.edge_node_eq_face_symm]
          simpa using PermReachable.forward G.face (G.face.symm y)
        · have htargetFace : PermReachable H.face
              (extendEmbedding r h center)
              (extendEmbedding r h (G.node (G.edge y))) := by
            have hmem :=
              (Birkhoff.mem_spokeRing_iff H
                (extendEmbedding r h center)
                (H.edge (extendEmbedding r h y))).1 hedgeYSpoke
            rw [← hG.extendEmbedding_edge hH hembed y] at hmem
            rw [hG.extendEmbedding_node hH hembed hedgeYOff]
            exact hmem
          have hnodeEdgeYOff : G.node (G.edge y) ∉ r := by
            intro hnodeOn
            exact hedgeYOff
              ((hG.cycle.image_mem_iff G.node.injective (G.edge y)).mp
                hnodeOn)
          have hsourceFace :
              PermReachable G.face center (G.node (G.edge y)) :=
            (hG.extendEmbedding_faceReachable_iff_of_kernel hH hembed
              hcenterKernel hnodeEdgeYOff).1 htargetFace
          have hperiod := (hG.quasicubic (G.edge y) hedgeYOff).1
          have hnodeNode : G.node (G.node (G.edge y)) = G.face y := by
            have hlocal :=
              Hypermap.node_node_eq_face_edge_of_period_three
                (G := G) hperiod
            simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hlocal
          have hfaceWitness :
              G.face (G.edge (G.face y)) = G.node (G.edge y) := by
            rw [Hypermap.face_edge_eq_node_symm, ← hnodeNode]
            simp
          have hnodeToWitness : PermReachable G.face
              (G.node (G.edge y)) (G.edge (G.face y)) := by
            apply PermReachable.symm G.face
            simpa [hfaceWitness] using
              PermReachable.forward G.face (G.edge (G.face y))
          apply hcenterY
          refine ⟨G.edge (G.face y),
            PermReachable.trans G.face hsourceFace hnodeToWitness, ?_⟩
          have hback := PermReachable.backward G.face (G.face y)
          simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hback

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
