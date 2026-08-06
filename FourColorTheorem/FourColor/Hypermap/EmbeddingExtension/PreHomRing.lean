import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.KernelReduction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `embed_functor`: a preembedding commutes with edge reversal throughout
the configuration kernel. -/
theorem embedFunctor
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart}
    (hx : G.Kernel r x)
    (hex : G.Kernel r (G.edge x)) :
    h (G.edge x) = H.edge (h x) := by
  by_contra hxNot
  exact hG.noKernelBadCycle hH hembed
    (hG.exists_kernelBadCycle_of_not_edgeCentral hH.plain hembed
      hx hex hxNot)

/-- Coq `pre_hom_ring x p`: a kernel-contained source `rlink` path whose image
is already a simple closed `rlink` cycle. -/
structure PreHomRing
    {H : Hypermap.{u}} (r : List G.Dart) (h : G.Dart → H.Dart)
    (x : G.Dart) (p : List G.Dart) : Prop where
  path : G.RLinkPath x p
  kernel : ∀ z : G.Dart, z ∈ x :: p → G.Kernel r z
  imageCycle : H.SimpleRLinkCycle ((x :: p).map h)

/-- The closing `rlink` of the mapped simple cycle, transported back through
`List.getLastD_map` to the source endpoint. -/
theorem PreHomRing.imageClosing
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p) :
    H.RLink (h ((x :: p).getLastD x)) (h x) := by
  have hclose := hpre.imageCycle.cycle.closing
  rw [← List.getLastD_map (f := h) (l := x :: p) (a := x)]
  exact hclose

/-- A kernel-contained source `rlink` path maps to an `rlink` path.  This is
the path induction used implicitly by Coq's `intro_pre_hom_ring`. -/
theorem rLinkPath_map_of_kernel
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpath : G.RLinkPath x p)
    (hkernel : ∀ z : G.Dart, z ∈ x :: p → G.Kernel r z) :
    H.RLinkPath (h x) (p.map h) := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
      have hpath' : G.RLink x y ∧ G.RLinkPath y p := by
        simpa [RLinkPath] using hpath
      have hxKernel : G.Kernel r x := hkernel x (by simp)
      have hyKernel : G.Kernel r y := hkernel y (by simp)
      have hedgeKernel : G.Kernel r (G.edge x) :=
        G.kernel_faceClosed r hyKernel
          (PermReachable.symm G.face hpath'.1)
      have hmapLink : H.RLink (h x) (h y) := by
        unfold RLink
        rw [← hG.embedFunctor hH hembed hxKernel hedgeKernel]
        exact hembed.faceReachable_map (G.kernel_faceClosed r)
          hedgeKernel hpath'.1
      have htailKernel :
          ∀ z : G.Dart, z ∈ y :: p → G.Kernel r z := by
        intro z hz
        exact hkernel z (by simp [hz])
      exact ⟨hmapLink, ih hpath'.2 htailKernel⟩

/-- Coq `intro_pre_hom_ring`.  Kernel edge commutation turns every source
`rlink` step into a target `rlink` step; the supplied target closing link and
face-simplicity then package the image cycle. -/
theorem introPreHomRing
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpath : G.RLinkPath x p)
    (hclose : H.RLink (h ((x :: p).getLastD x)) (h x))
    (hkernel : ∀ z : G.Dart, z ∈ x :: p → G.Kernel r z)
    (hsimple : H.FaceSimple ((x :: p).map h)) :
    PreHomRing r h x p := by
  have hmapPath : H.RLinkPath (h x) (p.map h) :=
    hG.rLinkPath_map_of_kernel hH hembed hpath hkernel
  have hlastMap :
      ((h x :: p.map h).getLastD (h x)) =
        h ((x :: p).getLastD x) := by
    simpa using
      (List.getLastD_map (f := h) (l := x :: p) (a := x))
  refine ⟨hpath, hkernel, ?_⟩
  constructor
  · constructor
    · simpa using hmapPath
    · rw [hlastMap]
      exact hclose
  · simpa using hsimple

/-- A zero Coq `fcard face` is pointwise emptiness of the corresponding
face-closed predicate. -/
theorem no_diskF_of_faceOrbitCount_le_zero
    {H : Hypermap.{u}} {q : List H.Dart}
    (hzero : H.FaceOrbitCountOf (H.DiskF q) ≤ 0) :
    ∀ u : H.Dart, ¬ H.DiskF q u := by
  intro u hu
  have hpos : 0 < H.FaceOrbitCountOf (H.DiskF q) :=
    (H.faceOrbitCountOf_pos_iff_exists).2 ⟨u, hu⟩
  omega

/-- First geometric step of Coq `trivial_hom_ring`: since the last image dart
lies on the image ring, its next node dart lies in `DiskN`; an empty `DiskF`
therefore forces that node dart back into the ring's face band. -/
theorem PreHomRing.lastNode_faceBand_of_no_diskF
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {x : G.Dart} {p : List G.Dart}
    (hnoDisk : ∀ u : H.Dart,
      ¬ H.DiskF ((x :: p).map h) u) :
    H.FaceBand ((x :: p).map h)
      (H.node (h ((x :: p).getLastD x))) := by
  let y := (x :: p).getLastD x
  have hyMem : y ∈ x :: p := by
    have hne : x :: p ≠ [] := List.cons_ne_nil x p
    dsimp [y, List.getLastD]
    exact List.getLast_mem (List.cons_ne_nil x p)
  have hhyMem : h y ∈ (x :: p).map h := List.mem_map.mpr ⟨y, hyMem, rfl⟩
  have hhyDisk : H.DiskN ((x :: p).map h) (h y) :=
    H.diskN_of_mem hhyMem
  have hnodeDisk : H.DiskN ((x :: p).map h) (H.node (h y)) :=
    (H.diskN_node_iff (r := (x :: p).map h)).2 hhyDisk
  by_contra hnotBand
  exact hnoDisk (H.node (h y)) ⟨hnodeDisk, hnotBand⟩

/-- Pull the face-band witness in `lastNode_faceBand_of_no_diskF` back to a
listed source dart. -/
theorem PreHomRing.exists_source_face_of_lastNode
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {x : G.Dart} {p : List G.Dart}
    (hnoDisk : ∀ u : H.Dart,
      ¬ H.DiskF ((x :: p).map h) u) :
    ∃ z : G.Dart, z ∈ x :: p ∧
      PermReachable H.face (h z)
        (H.node (h ((x :: p).getLastD x))) := by
  rcases PreHomRing.lastNode_faceBand_of_no_diskF (G := G) hnoDisk with
    ⟨hz, hzMap, hzFace⟩
  rcases List.mem_map.mp hzMap with ⟨z, hzMem, rfl⟩
  exact ⟨z, hzMem, hzFace⟩

/-- Coq `splitPl` in the form used by `trivial_hom_ring`: split the path tail
after an arbitrary member of the head-cons list, recording that member as the
last dart of the left prefix. -/
private theorem exists_append_getLastD_eq_of_mem_cons
    {x z : G.Dart} {p : List G.Dart}
    (hz : z ∈ x :: p) :
    ∃ p₁ p₂ : List G.Dart,
      p = p₁ ++ p₂ ∧ (x :: p₁).getLastD x = z := by
  rcases List.mem_cons.mp hz with rfl | hzTail
  · exact ⟨[], p, by simp [List.getLastD]⟩
  · rcases (List.mem_iff_append).1 hzTail with ⟨pre, post, hp⟩
    refine ⟨pre ++ [z], post, ?_, ?_⟩
    · simpa [List.append_assoc] using hp
    · simp [List.getLastD]

/-- In a bridgeless cubic map, the face of an edge cannot contain the next
dart at its source node.  This is Coq's `bridge'Gm` rewrite in the initial
endpoint case of `trivial_hom_ring`. -/
theorem minimalCounterexample_not_faceReachable_edge_node
    {H : Hypermap.{u}}
    (hH : H.MinimalCounterexample) (x : H.Dart) :
    ¬ PermReachable H.face (H.edge x) (H.node x) := by
  intro hedgeNode
  have hcubic : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hnodeNodeEdge :
      PermReachable H.face (H.node (H.node x)) (H.edge x) := by
    rw [Hypermap.Cubic.node_node_eq_face_edge (G := H) hcubic x]
    simpa using PermReachable.backward H.face (H.face (H.edge x))
  have hnodeEdge :
      PermReachable H.face (H.node x)
        (H.edge (H.node (H.node x))) := by
    rw [Hypermap.edge_node_eq_face_symm]
    exact PermReachable.backward H.face (H.node x)
  exact hH.bridgeless (H.node (H.node x))
    (PermReachable.trans H.face hnodeNodeEdge
      (PermReachable.trans H.face hedgeNode hnodeEdge))

/-- Coq's `splitPl` setup through the two endpoint exclusions.  The face of
`node (h last)` meets an interior source dart, so both path arcs around that
dart are nonempty and hence available for strict length descent. -/
theorem PreHomRing.exists_interior_split_face_of_no_diskF
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hH : H.MinimalCounterexample)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hnoDisk : ∀ u : H.Dart,
      ¬ H.DiskF ((x :: p).map h) u) :
    ∃ z : G.Dart, ∃ p₁ p₂ : List G.Dart,
      p = p₁ ++ p₂ ∧
        (x :: p₁).getLastD x = z ∧
          p₁ ≠ [] ∧ p₂ ≠ [] ∧
            PermReachable H.face (h z)
              (H.node (h ((x :: p).getLastD x))) := by
  rcases PreHomRing.exists_source_face_of_lastNode (G := G) hnoDisk with
    ⟨z, hzMem, hzFace⟩
  rcases exists_append_getLastD_eq_of_mem_cons (G := G) hzMem with
    ⟨p₁, p₂, hp, hlast⟩
  let y := (x :: p).getLastD x
  change PermReachable H.face (h z) (H.node (h y)) at hzFace
  have hclose : H.RLink (h y) (h x) := by
    simpa [y] using hpre.imageClosing
  have hp₂Ne : p₂ ≠ [] := by
    intro hp₂
    have hyz : y = z := by
      dsimp [y]
      rw [hp, hp₂]
      simpa using hlast
    exact Hypermap.Bridgeless.not_faceReachable_node
      (G := H) hH.bridgeless (h y) (by simpa [hyz] using hzFace)
  have hp₁Ne : p₁ ≠ [] := by
    intro hp₁
    have hzx : z = x := by
      simpa [hp₁, List.getLastD] using hlast.symm
    apply minimalCounterexample_not_faceReachable_edge_node hH (h y)
    exact PermReachable.trans H.face hclose (by simpa [hzx] using hzFace)
  exact ⟨z, p₁, p₂, hp, hlast, hp₁Ne, hp₂Ne, hzFace⟩


end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
