import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.EmbeddedDisk

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `rdom'`: the image of the strict interior of the embedded disk. -/
def EmbeddedDiskInteriorImage
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart)
    (z : H.Dart) : Prop :=
  ∃ x : (embeddedDisk hG).Dart,
    x ∉ embeddedDiskBoundary hG ∧ embeddedDiskMap hG h x = z

/-- Coq `rdart`: target darts outside the strict disk interior.  Boundary
darts occur in both halves of the eventual patch. -/
def EmbeddedRemainderDart
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart) :=
  {z : H.Dart // ¬ EmbeddedDiskInteriorImage hG h z}

noncomputable instance embeddedRemainderDartFintype
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart) :
    Fintype (EmbeddedRemainderDart hG h) := by
  letI : Finite (EmbeddedRemainderDart hG h) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (EmbeddedRemainderDart hG h)

noncomputable instance embeddedRemainderDartDecidableEq
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart) :
    DecidableEq (EmbeddedRemainderDart hG h) :=
  Classical.decEq _

private theorem embeddedDiskBoundary_edge_mem_iff
    (hG : G.Embeddable r) (x : (embeddedDisk hG).Dart) :
    (embeddedDisk hG).edge x ∈ embeddedDiskBoundary hG ↔
      x ∈ embeddedDiskBoundary hG := by
  exact (embeddedDiskBoundary_edgeCycle hG).image_mem_iff
    (embeddedDisk hG).edge.injective x

private theorem embeddedDiskBoundary_edge_symm_mem_iff
    (hG : G.Embeddable r) (x : (embeddedDisk hG).Dart) :
    (embeddedDisk hG).edge.symm x ∈ embeddedDiskBoundary hG ↔
      x ∈ embeddedDiskBoundary hG := by
  simpa using
    (embeddedDiskBoundary_edge_mem_iff hG
      ((embeddedDisk hG).edge.symm x)).symm

private theorem embeddedRemainder_edge_closed
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : EmbeddedRemainderDart hG h) :
    ¬ EmbeddedDiskInteriorImage hG h (H.edge w.1) := by
  intro hedgeInterior
  rcases hedgeInterior with ⟨x, hxOff, hxMap⟩
  have hedgeXOff :
      (embeddedDisk hG).edge x ∉ embeddedDiskBoundary hG := by
    intro hedgeOn
    exact hxOff ((embeddedDiskBoundary_edge_mem_iff hG x).1 hedgeOn)
  apply w.2
  refine ⟨(embeddedDisk hG).edge x, hedgeXOff, ?_⟩
  calc
    embeddedDiskMap hG h ((embeddedDisk hG).edge x) =
        H.edge (embeddedDiskMap hG h x) :=
      embeddedDiskMap_edge_off_boundary hG hH hembed hxOff
    _ = H.edge (H.edge w.1) := by rw [hxMap]
    _ = w.1 := Hypermap.Plain.edge_edge (G := H) hH.plain w.1

private def EmbeddedDiskBoundaryPreimage
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart)
    (z : H.Dart) : Prop :=
  ∃ x : (embeddedDisk hG).Dart,
    x ∈ embeddedDiskBoundary hG ∧ embeddedDiskMap hG h x = z

private noncomputable def embeddedDiskBoundaryPreimageChoice
    {H : Hypermap.{u}} {hG : G.Embeddable r} {h : G.Dart → H.Dart}
    {z : H.Dart} (hz : EmbeddedDiskBoundaryPreimage hG h z) :
    (embeddedDisk hG).Dart :=
  Classical.choose hz

private theorem embeddedDiskBoundaryPreimageChoice_spec
    {H : Hypermap.{u}} {hG : G.Embeddable r} {h : G.Dart → H.Dart}
    {z : H.Dart} (hz : EmbeddedDiskBoundaryPreimage hG h z) :
    embeddedDiskBoundaryPreimageChoice hz ∈ embeddedDiskBoundary hG ∧
      embeddedDiskMap hG h (embeddedDiskBoundaryPreimageChoice hz) = z :=
  Classical.choose_spec hz

private noncomputable def embeddedRemainderNodeVal
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart)
    (z : H.Dart) : H.Dart := by
  classical
  exact
    if hz : EmbeddedDiskBoundaryPreimage hG h z then
      embeddedDiskMap hG h
        ((embeddedDisk hG).node
          ((embeddedDisk hG).face
            (embeddedDiskBoundaryPreimageChoice hz)))
    else
      H.node z

private noncomputable def embeddedRemainderFaceVal
    {H : Hypermap.{u}} (hG : G.Embeddable r) (h : G.Dart → H.Dart)
    (z : H.Dart) : H.Dart := by
  classical
  exact
    if hz : EmbeddedDiskBoundaryPreimage hG h (H.edge z) then
      embeddedDiskMap hG h
        ((embeddedDisk hG).edge
          (embeddedDiskBoundaryPreimageChoice hz))
    else
      H.face z

private theorem embeddedRemainder_node_closed
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : EmbeddedRemainderDart hG h) :
    ¬ EmbeddedDiskInteriorImage hG h
      (embeddedRemainderNodeVal hG h w.1) := by
  classical
  unfold embeddedRemainderNodeVal
  split
  next hz =>
    let x := embeddedDiskBoundaryPreimageChoice hz
    have hxOn : x ∈ embeddedDiskBoundary hG :=
      (embeddedDiskBoundaryPreimageChoice_spec hz).1
    have hspliceOn :
        (embeddedDisk hG).node ((embeddedDisk hG).face x) ∈
          embeddedDiskBoundary hG := by
      have hnf :
          (embeddedDisk hG).node ((embeddedDisk hG).face x) =
            (embeddedDisk hG).edge.symm x := by
        simpa using (embeddedDisk hG).node_face_edge
          ((embeddedDisk hG).edge.symm x)
      rw [hnf]
      exact (embeddedDiskBoundary_edge_symm_mem_iff hG x).2 hxOn
    rintro ⟨y, hyOff, hyMap⟩
    have hyEq :
        y = (embeddedDisk hG).node ((embeddedDisk hG).face x) :=
      embeddedDiskMap_injective hG hH hembed hyMap
    exact hyOff (hyEq ▸ hspliceOn)
  next hz =>
    rintro ⟨x, hxOff, hxMap⟩
    let y := (embeddedDisk hG).node ((embeddedDisk hG).node x)
    have hyMap : embeddedDiskMap hG h y = w.1 := by
      have hcubic : H.Cubic :=
        Unavoidability.cubicMinimalCounterexamples_proved H hH
      calc
        embeddedDiskMap hG h y =
            H.node (embeddedDiskMap hG h ((embeddedDisk hG).node x)) :=
          embeddedDiskMap_node hG hH hembed _
        _ = H.node (H.node (embeddedDiskMap hG h x)) := by
          rw [embeddedDiskMap_node hG hH hembed]
        _ = H.node (H.node (H.node w.1)) := by rw [hxMap]
        _ = w.1 := (hcubic w.1).1
    have hyOff : y ∉ embeddedDiskBoundary hG := by
      intro hyOn
      exact hz ⟨y, hyOn, hyMap⟩
    exact w.2 ⟨y, hyOff, hyMap⟩

private theorem embeddedRemainder_face_closed
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : EmbeddedRemainderDart hG h) :
    ¬ EmbeddedDiskInteriorImage hG h
      (embeddedRemainderFaceVal hG h w.1) := by
  classical
  unfold embeddedRemainderFaceVal
  split
  next hz =>
    let x := embeddedDiskBoundaryPreimageChoice hz
    have hxOn : x ∈ embeddedDiskBoundary hG :=
      (embeddedDiskBoundaryPreimageChoice_spec hz).1
    have hedgeOn : (embeddedDisk hG).edge x ∈
        embeddedDiskBoundary hG :=
      (embeddedDiskBoundary_edge_mem_iff hG x).2 hxOn
    rintro ⟨y, hyOff, hyMap⟩
    have hyEq : y = (embeddedDisk hG).edge x :=
      embeddedDiskMap_injective hG hH hembed hyMap
    exact hyOff (hyEq ▸ hedgeOn)
  next hz =>
    rintro ⟨x, hxOff, hxMap⟩
    have hnodeMap :
        embeddedDiskMap hG h ((embeddedDisk hG).node x) = H.edge w.1 := by
      apply H.edge.injective
      calc
        H.edge (embeddedDiskMap hG h ((embeddedDisk hG).node x)) =
            H.edge (H.node (embeddedDiskMap hG h x)) := by
          rw [embeddedDiskMap_node hG hH hembed]
        _ = H.edge (H.node (H.face w.1)) := by rw [hxMap]
        _ = w.1 := H.edge_node_face w.1
        _ = H.edge (H.edge w.1) :=
          (Hypermap.Plain.edge_edge (G := H) hH.plain w.1).symm
    have hnodeOff :
        (embeddedDisk hG).node x ∉ embeddedDiskBoundary hG := by
      intro hnodeOn
      exact hz ⟨(embeddedDisk hG).node x, hnodeOn, hnodeMap⟩
    exact embeddedRemainder_edge_closed hG hH hembed w
      ⟨(embeddedDisk hG).node x, hnodeOff, hnodeMap⟩

private noncomputable def embeddedRemainderEdgeFn
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    EmbeddedRemainderDart hG h → EmbeddedRemainderDart hG h :=
  fun w => ⟨H.edge w.1, embeddedRemainder_edge_closed hG hH hembed w⟩

private noncomputable def embeddedRemainderNodeFn
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    EmbeddedRemainderDart hG h → EmbeddedRemainderDart hG h :=
  fun w => ⟨embeddedRemainderNodeVal hG h w.1,
    embeddedRemainder_node_closed hG hH hembed w⟩

private noncomputable def embeddedRemainderFaceFn
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    EmbeddedRemainderDart hG h → EmbeddedRemainderDart hG h :=
  fun w => ⟨embeddedRemainderFaceVal hG h w.1,
    embeddedRemainder_face_closed hG hH hembed w⟩

private theorem embeddedRemainder_cancel3
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    ∀ w : EmbeddedRemainderDart hG h,
      embeddedRemainderNodeFn hG hH hembed
        (embeddedRemainderFaceFn hG hH hembed
          (embeddedRemainderEdgeFn hG hH hembed w)) = w := by
  classical
  intro w
  apply Subtype.ext
  change embeddedRemainderNodeVal hG h
      (embeddedRemainderFaceVal hG h (H.edge w.1)) = w.1
  unfold embeddedRemainderFaceVal
  rw [Hypermap.Plain.edge_edge (G := H) hH.plain w.1]
  split
  next hwBoundary =>
    let x := embeddedDiskBoundaryPreimageChoice hwBoundary
    have hxOn : x ∈ embeddedDiskBoundary hG :=
      (embeddedDiskBoundaryPreimageChoice_spec hwBoundary).1
    have hxMap : embeddedDiskMap hG h x = w.1 :=
      (embeddedDiskBoundaryPreimageChoice_spec hwBoundary).2
    change embeddedRemainderNodeVal hG h
      (embeddedDiskMap hG h ((embeddedDisk hG).edge x)) = w.1
    unfold embeddedRemainderNodeVal
    split
    next hedgeBoundary =>
      let y := embeddedDiskBoundaryPreimageChoice hedgeBoundary
      have hyMap : embeddedDiskMap hG h y =
          embeddedDiskMap hG h ((embeddedDisk hG).edge x) :=
        (embeddedDiskBoundaryPreimageChoice_spec hedgeBoundary).2
      have hyEq : y = (embeddedDisk hG).edge x :=
        embeddedDiskMap_injective hG hH hembed hyMap
      calc
        embeddedDiskMap hG h
            ((embeddedDisk hG).node ((embeddedDisk hG).face y)) =
            embeddedDiskMap hG h x := by
          congr 1
          rw [hyEq]
          exact (embeddedDisk hG).node_face_edge x
        _ = w.1 := hxMap
    next hedgeNot =>
      exact False.elim (hedgeNot ⟨(embeddedDisk hG).edge x,
        (embeddedDiskBoundary_edge_mem_iff hG x).2 hxOn, rfl⟩)
  next hwNotBoundary =>
    have hfaceNotBoundary :
        ¬ EmbeddedDiskBoundaryPreimage hG h (H.face (H.edge w.1)) := by
      rintro ⟨x, hxOn, hxMap⟩
      have hnodeMap :
          embeddedDiskMap hG h ((embeddedDisk hG).node x) = w.1 := by
        calc
          embeddedDiskMap hG h ((embeddedDisk hG).node x) =
              H.node (embeddedDiskMap hG h x) :=
            embeddedDiskMap_node hG hH hembed x
          _ = H.node (H.face (H.edge w.1)) := by rw [hxMap]
          _ = w.1 := H.node_face_edge w.1
      have hnodeOff :
          (embeddedDisk hG).node x ∉ embeddedDiskBoundary hG := by
        intro hnodeOn
        exact hwNotBoundary
          ⟨(embeddedDisk hG).node x, hnodeOn, hnodeMap⟩
      exact w.2 ⟨(embeddedDisk hG).node x, hnodeOff, hnodeMap⟩
    unfold embeddedRemainderNodeVal
    rw [dif_neg hfaceNotBoundary]
    exact H.node_face_edge w.1

/-- Coq `embed_rem`: the target hypermap with the strict disk interior
removed and the common boundary spliced into node orbits. -/
noncomputable def embeddedRemainder
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) : Hypermap.{u} :=
  Hypermap.ofCancel3
    (embeddedRemainderEdgeFn hG hH hembed)
    (embeddedRemainderNodeFn hG hH hembed)
    (embeddedRemainderFaceFn hG hH hembed)
    (embeddedRemainder_cancel3 hG hH hembed)

/-- Coq projection `embr`. -/
def embeddedRemainderVal
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {hG : G.Embeddable r} {hH : H.MinimalCounterexample}
    {hembed : Preembedding G H (G.Kernel r) h}
    (w : (embeddedRemainder hG hH hembed).Dart) : H.Dart :=
  w.1

theorem embeddedRemainderVal_injective
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    Function.Injective
      (embeddedRemainderVal (hG := hG) (hH := hH) (hembed := hembed)) := by
  intro x y hxy
  exact Subtype.ext hxy

@[simp]
theorem embeddedRemainder_edge_val
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : (embeddedRemainder hG hH hembed).Dart) :
    embeddedRemainderVal ((embeddedRemainder hG hH hembed).edge w) =
      H.edge (embeddedRemainderVal w) :=
  rfl

@[simp]
theorem embeddedRemainder_node_val
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : (embeddedRemainder hG hH hembed).Dart) :
    embeddedRemainderVal ((embeddedRemainder hG hH hembed).node w) =
      embeddedRemainderNodeVal hG h (embeddedRemainderVal w) := by
  rfl

private theorem embeddedDiskBoundary_not_interior
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : (embeddedDisk hG).Dart}
    (hx : x ∈ embeddedDiskBoundary hG) :
    ¬ EmbeddedDiskInteriorImage hG h (embeddedDiskMap hG h x) := by
  rintro ⟨y, hyOff, hyMap⟩
  have hyx : y = x := embeddedDiskMap_injective hG hH hembed hyMap
  exact hyOff (hyx ▸ hx)

private noncomputable def embeddedRemainderBoundaryLift
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (x : {x : (embeddedDisk hG).Dart // x ∈ embeddedDiskBoundary hG}) :
    (embeddedRemainder hG hH hembed).Dart :=
  ⟨embeddedDiskMap hG h x.1,
    embeddedDiskBoundary_not_interior hG hH hembed x.2⟩

private theorem embeddedRemainderBoundaryLift_injective
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    Function.Injective (embeddedRemainderBoundaryLift hG hH hembed) := by
  intro x y hxy
  apply Subtype.ext
  apply embeddedDiskMap_injective hG hH hembed
  exact congrArg Subtype.val hxy

/-- Coq `embr_ring`: the target image of the disk boundary, in reverse
orientation, lifted to the remainder subtype. -/
noncomputable def embeddedRemainderBoundary
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    List (embeddedRemainder hG hH hembed).Dart :=
  (embeddedDiskBoundary hG).attach.reverse.map
    (embeddedRemainderBoundaryLift hG hH hembed)

@[simp]
theorem map_embeddedRemainderBoundary
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    (embeddedRemainderBoundary hG hH hembed).map
        embeddedRemainderVal =
      ((embeddedDiskBoundary hG).map (embeddedDiskMap hG h)).reverse := by
  simp [embeddedRemainderBoundary, embeddedRemainderBoundaryLift,
    embeddedRemainderVal, List.map_reverse]

theorem embeddedRemainderBoundary_nodup
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    (embeddedRemainderBoundary hG hH hembed).Nodup := by
  unfold embeddedRemainderBoundary
  apply (embeddedDiskBoundary_nodup hG).attach.reverse.map
  intro a b hba hab
  exact hba ((embeddedRemainderBoundaryLift_injective hG hH hembed hab).symm)

theorem embeddedRemainderBoundary_nodeCycle
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    FunctionCycle (embeddedRemainder hG hH hembed).node
      (embeddedRemainderBoundary hG hH hembed) := by
  classical
  apply FunctionCycle.of_eq_next
    (embeddedRemainderBoundary_nodup hG hH hembed)
  intro w hw
  rcases List.mem_map.mp hw with ⟨x, hxRev, hxw⟩
  subst w
  apply Subtype.ext
  change embeddedRemainderNodeVal hG h (embeddedDiskMap hG h x.1) =
    embeddedRemainderVal
      ((embeddedRemainderBoundary hG hH hembed).next
        (embeddedRemainderBoundaryLift hG hH hembed x) hw)
  unfold embeddedRemainderNodeVal
  split
  next hxBoundary =>
    let y := embeddedDiskBoundaryPreimageChoice hxBoundary
    have hyMap : embeddedDiskMap hG h y = embeddedDiskMap hG h x.1 :=
      (embeddedDiskBoundaryPreimageChoice_spec hxBoundary).2
    have hyEq : y = x.1 := embeddedDiskMap_injective hG hH hembed hyMap
    have hxAttach : x ∈ (embeddedDiskBoundary hG).attach :=
      List.mem_reverse.mp hxRev
    have hattachNodup : (embeddedDiskBoundary hG).attach.Nodup :=
      (embeddedDiskBoundary_nodup hG).attach
    have hreverse := List.next_reverse_eq_prev
      (embeddedDiskBoundary hG).attach hattachNodup x hxAttach
    have hprevMap := List.prev_map_injective
      (fun z : {z // z ∈ embeddedDiskBoundary hG} => z.1)
      Subtype.val_injective (embeddedDiskBoundary hG).attach
      hattachNodup x hxAttach
    have hprevVal :
        ((embeddedDiskBoundary hG).attach.prev x hxAttach).1 =
          (embeddedDiskBoundary hG).prev x.1 x.2 := by
      simpa using hprevMap.symm
    have hprevEdge :
        (embeddedDiskBoundary hG).prev x.1 x.2 =
          (embeddedDisk hG).edge.symm x.1 := by
      apply (embeddedDisk hG).edge.injective
      calc
        (embeddedDisk hG).edge
            ((embeddedDiskBoundary hG).prev x.1 x.2) =
            (embeddedDiskBoundary hG).next
              ((embeddedDiskBoundary hG).prev x.1 x.2)
              (List.prev_mem _ _ x.2) :=
          (embeddedDiskBoundary_edgeCycle hG).eq_next
            (embeddedDiskBoundary_nodup hG) _ (List.prev_mem _ _ x.2)
        _ = x.1 := List.next_prev _ (embeddedDiskBoundary_nodup hG) _ x.2
        _ = (embeddedDisk hG).edge
            ((embeddedDisk hG).edge.symm x.1) := by simp
    have hnextVal :
        (((embeddedDiskBoundary hG).attach.reverse.next x hxRev).1) =
          (embeddedDisk hG).edge.symm x.1 := by
      calc
        (((embeddedDiskBoundary hG).attach.reverse.next x hxRev).1) =
            ((embeddedDiskBoundary hG).attach.prev x hxAttach).1 :=
          congrArg Subtype.val hreverse
        _ = (embeddedDiskBoundary hG).prev x.1 x.2 := hprevVal
        _ = (embeddedDisk hG).edge.symm x.1 := hprevEdge
    have hnextMap := List.next_map_injective
      (embeddedRemainderBoundaryLift hG hH hembed)
      (embeddedRemainderBoundaryLift_injective hG hH hembed)
      (embeddedDiskBoundary hG).attach.reverse
      (List.nodup_reverse.mpr hattachNodup) x hxRev
    calc
      embeddedDiskMap hG h
          ((embeddedDisk hG).node ((embeddedDisk hG).face y)) =
          embeddedDiskMap hG h ((embeddedDisk hG).edge.symm x.1) := by
        congr 1
        rw [hyEq]
        simpa using (embeddedDisk hG).node_face_edge
          ((embeddedDisk hG).edge.symm x.1)
      _ = embeddedDiskMap hG h
          (((embeddedDiskBoundary hG).attach.reverse.next x hxRev).1) := by
        rw [hnextVal]
      _ = embeddedRemainderVal
          (embeddedRemainderBoundaryLift hG hH hembed
            ((embeddedDiskBoundary hG).attach.reverse.next x hxRev)) := rfl
      _ = embeddedRemainderVal
          ((embeddedRemainderBoundary hG hH hembed).next
            (embeddedRemainderBoundaryLift hG hH hembed x) hw) := by
        congr 1
        exact hnextMap.symm
  next hxNotBoundary =>
    exact False.elim (hxNotBoundary ⟨x.1, x.2, rfl⟩)

theorem mem_embeddedRemainderBoundary_iff
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (w : (embeddedRemainder hG hH hembed).Dart) :
    w ∈ embeddedRemainderBoundary hG hH hembed ↔
      EmbeddedDiskBoundaryPreimage hG h (embeddedRemainderVal w) := by
  constructor
  · intro hw
    have hwMap : embeddedRemainderVal w ∈
        (embeddedRemainderBoundary hG hH hembed).map
          embeddedRemainderVal :=
      List.mem_map_of_mem hw
    rw [map_embeddedRemainderBoundary] at hwMap
    have hwTarget : embeddedRemainderVal w ∈
        (embeddedDiskBoundary hG).map (embeddedDiskMap hG h) :=
      List.mem_reverse.mp hwMap
    rcases List.mem_map.mp hwTarget with ⟨x, hx, hxMap⟩
    exact ⟨x, hx, hxMap⟩
  · rintro ⟨x, hx, hxMap⟩
    let xa : {x : (embeddedDisk hG).Dart //
        x ∈ embeddedDiskBoundary hG} := ⟨x, hx⟩
    have hxa : xa ∈ (embeddedDiskBoundary hG).attach := by
      simp [xa]
    have hxaRev : xa ∈ (embeddedDiskBoundary hG).attach.reverse :=
      List.mem_reverse.mpr hxa
    have hliftMem : embeddedRemainderBoundaryLift hG hH hembed xa ∈
        embeddedRemainderBoundary hG hH hembed := by
      exact List.mem_map_of_mem hxaRev
    have hwEq : w = embeddedRemainderBoundaryLift hG hH hembed xa := by
      apply Subtype.ext
      exact hxMap.symm
    exact hwEq ▸ hliftMem

/-- Coq `embed_patch`: the extended configuration disk and the spliced
remainder form a semantic patch of the minimal counterexample. -/
theorem embeddingPatch
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    Patch H (embeddedDisk hG) (embeddedRemainder hG hH hembed)
      (embeddedDiskMap hG h) embeddedRemainderVal
      (embeddedDiskBoundary hG)
      (embeddedRemainderBoundary hG hH hembed) := by
  classical
  refine {
    injd := embeddedDiskMap_injective hG hH hembed
    injr := embeddedRemainderVal_injective hG hH hembed
    cycleD := embeddedDiskBoundary_edgeCycle hG
    boundaryD_faceSimple := embeddedDiskBoundary_faceSimple hG
    cycleR := embeddedRemainderBoundary_nodeCycle hG hH hembed
    boundaryR_nodup := embeddedRemainderBoundary_nodup hG hH hembed
    map_boundaryR := map_embeddedRemainderBoundary hG hH hembed
    coverR := ?_
    map_edgeD := ?_
    map_nodeD := ?_
    map_edgeR := ?_
    map_nodeR := ?_
  }
  · intro z
    constructor
    · rintro ⟨w, hw⟩
      have hzOutside : ¬ EmbeddedDiskInteriorImage hG h z := by
        rw [← hw]
        exact w.2
      by_cases hzDisk : ∃ x : (embeddedDisk hG).Dart,
          embeddedDiskMap hG h x = z
      · right
        rcases hzDisk with ⟨x, hxMap⟩
        have hxOn : x ∈ embeddedDiskBoundary hG := by
          by_contra hxOff
          exact hzOutside ⟨x, hxOff, hxMap⟩
        exact List.mem_map.mpr ⟨x, hxOn, hxMap⟩
      · exact Or.inl hzDisk
    · intro hz
      have hzOutside : ¬ EmbeddedDiskInteriorImage hG h z := by
        rcases hz with hzNoDisk | hzBoundary
        · rintro ⟨x, _, hxMap⟩
          exact hzNoDisk ⟨x, hxMap⟩
        · rcases List.mem_map.mp hzBoundary with ⟨x, hxOn, hxMap⟩
          rw [← hxMap]
          exact embeddedDiskBoundary_not_interior hG hH hembed hxOn
      exact ⟨⟨z, hzOutside⟩, rfl⟩
  · intro x hxOff
    exact embeddedDiskMap_edge_off_boundary hG hH hembed hxOff
  · intro x
    exact embeddedDiskMap_node hG hH hembed x
  · intro w
    exact embeddedRemainder_edge_val hG hH hembed w
  · intro w hwOff
    rw [embeddedRemainder_node_val]
    unfold embeddedRemainderNodeVal
    rw [dif_neg (fun hz => hwOff
      ((mem_embeddedRemainderBoundary_iff hG hH hembed w).2 hz))]

theorem embeddedRemainder_eulerPlanar
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    (embeddedRemainder hG hH hembed).EulerPlanar := by
  exact ((embeddingPatch hG hH hembed).eulerPlanar_iff.mp hH.planar).2

theorem embeddedRemainder_plain
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    (embeddedRemainder hG hH hembed).Plain := by
  exact ((embeddingPatch hG hH hembed).plain_iff.mp hH.plain).2

theorem embeddedRemainder_quasicubic
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    (embeddedRemainder hG hH hembed).Quasicubic
      (embeddedRemainderBoundary hG hH hembed) := by
  have hcubic : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  exact ((embeddingPatch hG hH hembed).cubic_iff.mp hcubic).2

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
