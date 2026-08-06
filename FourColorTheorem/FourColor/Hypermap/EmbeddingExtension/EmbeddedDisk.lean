import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.Extension

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `ddart`: darts of the embedded configuration disk are precisely the
source darts off the literal perimeter. -/
def EmbeddedDiskDart (G : Hypermap.{u}) (r : List G.Dart) :=
  {x : G.Dart // x ∉ r}

noncomputable instance embeddedDiskDartFintype :
    Fintype (EmbeddedDiskDart G r) := by
  letI : Finite (EmbeddedDiskDart G r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (EmbeddedDiskDart G r)

noncomputable instance embeddedDiskDartDecidableEq :
    DecidableEq (EmbeddedDiskDart G r) :=
  Classical.decEq _

private noncomputable def embeddedDiskEdgeFn
    (hG : G.Embeddable r) :
    EmbeddedDiskDart G r → EmbeddedDiskDart G r := by
  classical
  intro x
  by_cases hedgeOff : G.edge x.1 ∉ r
  · exact ⟨G.edge x.1, hedgeOff⟩
  · refine ⟨G.edge (G.node (G.edge x.1)), ?_⟩
    have hedgeOn : G.edge x.1 ∈ r := Classical.not_not.mp hedgeOff
    rcases hG.edgePerimeter (G.node (G.edge x.1)) with hnodeOff | hresult
    · exact False.elim (hnodeOff (hG.cycle.image_mem hedgeOn))
    · exact hresult

private def embeddedDiskNodeFn
    (hG : G.Embeddable r) :
    EmbeddedDiskDart G r → EmbeddedDiskDart G r := fun x =>
  ⟨G.node x.1, by
    intro hnodeOn
    exact x.2 ((hG.cycle.image_mem_iff G.node.injective x.1).mp hnodeOn)⟩

private noncomputable def embeddedDiskFaceFn
    (hG : G.Embeddable r) :
    EmbeddedDiskDart G r → EmbeddedDiskDart G r := by
  classical
  intro x
  by_cases hfaceOff : G.face x.1 ∉ r
  · exact ⟨G.face x.1, hfaceOff⟩
  · refine ⟨G.face (G.face x.1), ?_⟩
    have hfaceOn : G.face x.1 ∈ r := Classical.not_not.mp hfaceOff
    have hedgeFaceOff : G.edge (G.face x.1) ∉ r :=
      (hG.edgePerimeter (G.face x.1)).resolve_left hfaceOff
    intro hfaceFaceOn
    have hnodeFaceFaceOn : G.node (G.face (G.face x.1)) ∈ r :=
      hG.cycle.image_mem hfaceFaceOn
    apply hedgeFaceOff
    simpa [Hypermap.Plain.node_face_eq_edge (G := G) hG.plain] using
      hnodeFaceFaceOn

private theorem embeddedDisk_cancel3
    (hG : G.Embeddable r) :
    ∀ x : EmbeddedDiskDart G r,
      embeddedDiskNodeFn hG
        (embeddedDiskFaceFn hG (embeddedDiskEdgeFn hG x)) = x := by
  classical
  intro x
  apply Subtype.ext
  by_cases hedgeOff : G.edge x.1 ∉ r
  · have hfaceEdgeOff : G.face (G.edge x.1) ∉ r := by
      rw [Hypermap.face_edge_eq_node_symm]
      intro hnodeSymmOn
      have hnodeOn : G.node (G.node.symm x.1) ∈ r :=
        hG.cycle.image_mem hnodeSymmOn
      exact x.2 (by simpa using hnodeOn)
    simp [embeddedDiskEdgeFn, embeddedDiskFaceFn,
      embeddedDiskNodeFn, hedgeOff, hfaceEdgeOff]
  · have hfaceRerouted :
        G.face (G.edge (G.node (G.edge x.1))) = G.edge x.1 := by
      rw [Hypermap.edge_node_eq_face_symm]
      simp
    simp [embeddedDiskEdgeFn, embeddedDiskFaceFn,
      embeddedDiskNodeFn, hedgeOff, hfaceRerouted]

/-- Coq `embed_disk`: the finite hypermap induced on darts off the literal
perimeter, with its boundary-crossing edge and face steps rerouted. -/
noncomputable def embeddedDisk
    (hG : G.Embeddable r) : Hypermap.{u} :=
  Hypermap.ofCancel3
    (embeddedDiskEdgeFn hG)
    (embeddedDiskNodeFn hG)
    (embeddedDiskFaceFn hG)
    (embeddedDisk_cancel3 hG)

/-- Coq projection `embd`. -/
def embeddedDiskVal
    (hG : G.Embeddable r)
    (x : (embeddedDisk hG).Dart) : G.Dart :=
  x.1

theorem embeddedDiskVal_injective
    (hG : G.Embeddable r) :
    Function.Injective (embeddedDiskVal hG) := by
  intro x y hxy
  exact Subtype.ext hxy

@[simp]
theorem embeddedDisk_node_val
    (hG : G.Embeddable r)
    (x : (embeddedDisk hG).Dart) :
    embeddedDiskVal hG ((embeddedDisk hG).node x) =
      G.node (embeddedDiskVal hG x) :=
  rfl

set_option linter.unusedVariables false in
@[simp]
theorem embeddedDisk_edge_val
    (hG : G.Embeddable r)
    (x : (embeddedDisk hG).Dart) :
    embeddedDiskVal hG ((embeddedDisk hG).edge x) =
      if hedgeOff : G.edge (embeddedDiskVal hG x) ∉ r then
        G.edge (embeddedDiskVal hG x)
      else G.edge (G.node (G.edge (embeddedDiskVal hG x))) := by
  classical
  unfold embeddedDiskVal embeddedDisk
  rw [ofCancel3_edge_apply]
  unfold embeddedDiskEdgeFn
  split <;> rfl

set_option linter.unusedVariables false in
@[simp]
theorem embeddedDisk_face_val
    (hG : G.Embeddable r)
    (x : (embeddedDisk hG).Dart) :
    embeddedDiskVal hG ((embeddedDisk hG).face x) =
      if hfaceOff : G.face (embeddedDiskVal hG x) ∉ r then
        G.face (embeddedDiskVal hG x)
      else G.face (G.face (embeddedDiskVal hG x)) := by
  classical
  unfold embeddedDiskVal embeddedDisk
  rw [ofCancel3_face_apply]
  unfold embeddedDiskFaceFn
  split <;> rfl

private theorem crossedPerimeter_off
    (hG : G.Embeddable r) {x : G.Dart}
    (hx : x ∈ G.RevRing r.reverse) :
    x ∉ r := by
  have hedgeMem : G.edge x ∈ r :=
    (hG.mem_edgePerimeter_iff x).1 hx
  exact (hG.edgePerimeter x).resolve_right (fun hedgeOff => hedgeOff hedgeMem)

/-- Coq `embd_ring`: the crossed perimeter lifted to the embedded-disk
subtype. -/
def embeddedDiskBoundary
    (hG : G.Embeddable r) : List (embeddedDisk hG).Dart :=
  (G.RevRing r.reverse).attach.map fun x =>
    ⟨x.1, crossedPerimeter_off hG x.2⟩

@[simp]
theorem map_embeddedDiskBoundary
    (hG : G.Embeddable r) :
    (embeddedDiskBoundary hG).map (embeddedDiskVal hG) =
      G.RevRing r.reverse := by
  simp [embeddedDiskBoundary, embeddedDiskVal]

theorem embeddedDiskBoundary_nodup
    (hG : G.Embeddable r) :
    (embeddedDiskBoundary hG).Nodup := by
  have hqNodup : (G.RevRing r.reverse).Nodup := by
    simpa [RevRing, List.map_reverse] using hG.nodup.map G.edge.injective
  unfold embeddedDiskBoundary
  apply hqNodup.attach.map
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : EmbeddedDiskDart G r => z.1) hxy

private theorem crossedPerimeter_functionCycle
    (hG : G.Embeddable r) :
    FunctionCycle (fun x : G.Dart => G.edge (G.node (G.edge x)))
      (G.RevRing r.reverse) := by
  have hmap : FunctionCycle (fun x : G.Dart => G.edge (G.node (G.edge x)))
      (r.map G.edge) :=
    hG.cycle.map (by
      intro x hx
      simp [Hypermap.Plain.edge_edge (G := G) hG.plain])
  simpa [RevRing, List.map_reverse] using hmap

theorem embeddedDiskBoundary_edgeCycle
    (hG : G.Embeddable r) :
    FunctionCycle (embeddedDisk hG).edge (embeddedDiskBoundary hG) := by
  classical
  apply FunctionCycle.of_eq_next (embeddedDiskBoundary_nodup hG)
  intro x hx
  apply Subtype.ext
  change embeddedDiskVal hG ((embeddedDisk hG).edge x) =
    embeddedDiskVal hG ((embeddedDiskBoundary hG).next x hx)
  rw [embeddedDisk_edge_val]
  have hxQ : embeddedDiskVal hG x ∈ G.RevRing r.reverse := by
    rw [← map_embeddedDiskBoundary hG]
    exact List.mem_map_of_mem hx
  have hedgeOn : G.edge (embeddedDiskVal hG x) ∈ r :=
    (hG.mem_edgePerimeter_iff _).1 hxQ
  rw [dif_neg (not_not_intro hedgeOn)]
  have hqNodup : (G.RevRing r.reverse).Nodup := by
    rw [← map_embeddedDiskBoundary hG]
    exact (embeddedDiskBoundary_nodup hG).map
      (embeddedDiskVal_injective hG)
  have hsourceNext :=
    (crossedPerimeter_functionCycle hG).eq_next
      hqNodup (embeddedDiskVal hG x) hxQ
  have hmapNext := List.next_map_injective
    (embeddedDiskVal hG) (embeddedDiskVal_injective hG)
    (embeddedDiskBoundary hG) (embeddedDiskBoundary_nodup hG) x hx
  have hmapNext' :
      (G.RevRing r.reverse).next (embeddedDiskVal hG x) hxQ =
        embeddedDiskVal hG ((embeddedDiskBoundary hG).next x hx) := by
    simpa only [map_embeddedDiskBoundary] using hmapNext
  exact hsourceNext.trans hmapNext'

theorem embeddedDisk_faceReachable_map
    (hG : G.Embeddable r)
    {x y : (embeddedDisk hG).Dart}
    (hxy : PermReachable (embeddedDisk hG).face x y) :
    PermReachable G.face (embeddedDiskVal hG x) (embeddedDiskVal hG y) := by
  rcases permReachable_exists_iterate (embeddedDisk hG).face hxy with ⟨n, hn⟩
  have hiter : ∀ m : Nat, ∀ z : (embeddedDisk hG).Dart,
      PermReachable G.face (embeddedDiskVal hG z)
        (embeddedDiskVal hG (((embeddedDisk hG).face : _ → _)^[m] z)) := by
    intro m z
    induction m generalizing z with
    | zero => exact PermReachable.refl G.face _
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        apply PermReachable.trans G.face (ih z)
        rw [embeddedDisk_face_val]
        split
        · exact PermReachable.forward G.face _
        · exact PermReachable.trans G.face
            (PermReachable.forward G.face _)
            (PermReachable.forward G.face _)
  simpa [hn] using hiter n x

theorem embeddedDiskBoundary_faceSimple
    (hG : G.Embeddable r) :
    (embeddedDisk hG).FaceSimple (embeddedDiskBoundary hG) := by
  have hsource : G.FaceSimple (G.RevRing r.reverse) := by
    by_cases hr : r = []
    · subst r
      simp [RevRing, FaceSimple]
    · exact (hG.edgePerimeterSimpleRLinkCycle hr).2
  rw [← map_embeddedDiskBoundary hG, FaceSimple,
    List.pairwise_map] at hsource
  rw [FaceSimple]
  exact hsource.imp (by
    intro x y hnot hreach
    exact hnot (embeddedDisk_faceReachable_map hG hreach))

theorem mem_embeddedDiskBoundary_iff
    (hG : G.Embeddable r)
    (x : (embeddedDisk hG).Dart) :
    x ∈ embeddedDiskBoundary hG ↔
      embeddedDiskVal hG x ∈ G.RevRing r.reverse := by
  constructor
  · intro hx
    rw [← map_embeddedDiskBoundary hG]
    exact List.mem_map_of_mem hx
  · intro hx
    have hxMap : embeddedDiskVal hG x ∈
        (embeddedDiskBoundary hG).map (embeddedDiskVal hG) := by
      simpa only [map_embeddedDiskBoundary] using hx
    rcases List.mem_map.mp hxMap with ⟨y, hy, hyx⟩
    have hxy : x = y := embeddedDiskVal_injective hG hyx.symm
    simpa [hxy] using hy

/-- Coq `embdd`: the embedded-disk injection into the minimal
counterexample. -/
noncomputable def embeddedDiskMap
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart)
    (x : (embeddedDisk hG).Dart) : H.Dart :=
  extendEmbedding r h (embeddedDiskVal hG x)

theorem embeddedDiskMap_injective
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    Function.Injective (embeddedDiskMap hG h) := by
  intro x y hxy
  apply embeddedDiskVal_injective hG
  exact hG.extendEmbedding_injective hH hembed x.2 y.2 hxy

theorem embeddedDiskMap_node
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (x : (embeddedDisk hG).Dart) :
    embeddedDiskMap hG h ((embeddedDisk hG).node x) =
      H.node (embeddedDiskMap hG h x) := by
  unfold embeddedDiskMap
  rw [embeddedDisk_node_val]
  exact hG.extendEmbedding_node hH hembed x.2

theorem embeddedDiskMap_edge_off_boundary
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : (embeddedDisk hG).Dart}
    (hx : x ∉ embeddedDiskBoundary hG) :
    embeddedDiskMap hG h ((embeddedDisk hG).edge x) =
      H.edge (embeddedDiskMap hG h x) := by
  have hedgeOff : G.edge (embeddedDiskVal hG x) ∉ r := by
    intro hedgeOn
    apply hx
    apply (mem_embeddedDiskBoundary_iff hG x).2
    exact (hG.mem_edgePerimeter_iff _).2 hedgeOn
  unfold embeddedDiskMap
  rw [embeddedDisk_edge_val, dif_pos hedgeOff]
  exact hG.extendEmbedding_edge hH hembed _

theorem map_embeddedDiskBoundary_target
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r) :
    (embeddedDiskBoundary hG).map (embeddedDiskMap hG h) =
      (G.RevRing r.reverse).map (extendEmbedding r h) := by
  calc
    (embeddedDiskBoundary hG).map (embeddedDiskMap hG h) =
        ((embeddedDiskBoundary hG).map (embeddedDiskVal hG)).map
          (extendEmbedding r h) := by
      change
        (embeddedDiskBoundary hG).map
            (fun x => extendEmbedding r h (embeddedDiskVal hG x)) =
          ((embeddedDiskBoundary hG).map (embeddedDiskVal hG)).map
            (extendEmbedding r h)
      rw [List.map_map]
      rfl
    _ = (G.RevRing r.reverse).map (extendEmbedding r h) := by
      rw [map_embeddedDiskBoundary]

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
