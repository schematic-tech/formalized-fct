import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRing

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

namespace PreHomRingShortening

theorem getLastD_cons_append_eq_getLast
    {x : G.Dart} (p q : List G.Dart) (hq : q ≠ []) :
    (x :: (p ++ q)).getLastD x = q.getLast hq := by
  induction p generalizing x with
  | nil =>
      cases q with
      | nil => contradiction
      | cons y q => simp [List.getLastD]
  | cons y p ih =>
      simpa [List.getLastD] using ih (x := y)

theorem eq_dropLast_append_singleton_of_getLastD_append
    {x y : G.Dart} (p q : List G.Dart) (hq : q ≠ [])
    (hlast : (x :: (p ++ q)).getLastD x = y) :
    q = q.dropLast ++ [y] := by
  have hlast' : q.getLast hq = y :=
    (getLastD_cons_append_eq_getLast (G := G) (x := x) p q hq).symm.trans hlast
  rw [← hlast', List.dropLast_append_getLast hq]

/-- Decompose both nonempty pieces of a split at their displayed final
darts.  This packages the list bookkeeping shared by the two shortening
branches. -/
theorem split_dropLast_shapes_of_getLastD
    {x z : G.Dart} {p p₁ p₂ : List G.Dart}
    (hp : p = p₁ ++ p₂)
    (hlast : (x :: p₁).getLastD x = z)
    (hp₁Ne : p₁ ≠ []) (hp₂Ne : p₂ ≠ []) :
    p₁ = p₁.dropLast ++ [z] ∧
      p₂ = p₂.dropLast ++ [(x :: p).getLastD x] := by
  constructor
  · exact eq_dropLast_append_singleton_of_getLastD_append
      (G := G) [] p₁ hp₁Ne hlast
  · apply eq_dropLast_append_singleton_of_getLastD_append
      (G := G) p₁ p₂ hp₂Ne
    rw [← hp]

theorem nodeNode_faceReachable_of_rLink
    {H : Hypermap.{u}} (hCubic : H.Cubic) {a b : H.Dart}
    (hab : H.RLink a b) :
    PermReachable H.face (H.node (H.node a)) b := by
  have hedgeNN :
      PermReachable H.face (H.edge a) (H.node (H.node a)) := by
    rw [Hypermap.Cubic.node_node_eq_face_edge (G := H) hCubic]
    exact PermReachable.forward H.face (H.edge a)
  exact PermReachable.trans H.face
    (PermReachable.symm H.face hedgeNN) hab

end PreHomRingShortening

open PreHomRingShortening

/-- Replace the displayed last dart of an `rlink` path by a dart in the same
face orbit.  Coq uses this twice when replacing `y` by `edge (node y)` and by
`edge (node (node y))`. -/
theorem RLinkPath.replace_last_of_faceReachable
    {x y t : G.Dart} {q : List G.Dart}
    (hpath : G.RLinkPath x (q ++ [y]))
    (hyt : PermReachable G.face y t) :
    G.RLinkPath x (q ++ [t]) := by
  have hprefix : G.RLinkPath x q :=
    RLinkPath.prefix_of_append (G := G) hpath
  have hlast : G.RLink ((x :: q).getLastD x) y :=
    RLinkPath.last_link_of_append_cons (G := G)
      (p := q) (q := []) (by simpa using hpath)
  exact RLinkPath.snoc_last (G := G) hprefix
    (RLink.of_faceReachable_right (G := G) hlast hyt)

namespace PreHomRingShortening

/-- A duplicate-free mapped list makes the map injective on the source darts
that occur in that list. -/
theorem eq_of_map_nodup_of_mem
    {α β : Type*} {f : α → β} {l : List α} {a b : α}
    (hnodup : (l.map f).Nodup)
    (ha : a ∈ l) (hb : b ∈ l)
    (hab : f a = f b) :
    a = b := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons c l ih =>
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp ha with haHead | haTail
      · rcases List.mem_cons.mp hb with hbHead | hbTail
        · exact haHead.trans hbHead.symm
        · apply False.elim
          apply hparts.1
          exact List.mem_map.mpr
            ⟨b, hbTail, hab.symm.trans (congrArg f haHead)⟩
      · rcases List.mem_cons.mp hb with hbHead | hbTail
        · apply False.elim
          apply hparts.1
          exact List.mem_map.mpr
            ⟨a, haTail, hab.trans (congrArg f hbHead)⟩
        · exact ih hparts.2 haTail hbTail hab

end PreHomRingShortening

/-- Single-step form of `rLinkPath_map_of_kernel`. -/
theorem rLink_map_of_kernel
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart}
    (hxy : G.RLink x y)
    (hx : G.Kernel r x) (hy : G.Kernel r y) :
    H.RLink (h x) (h y) := by
  have hedgeKernel : G.Kernel r (G.edge x) :=
    G.kernel_faceClosed r hy (PermReachable.symm G.face hxy)
  unfold RLink
  rw [← hG.embedFunctor hH hembed hx hedgeKernel]
  exact hembed.faceReachable_map (G.kernel_faceClosed r)
    hedgeKernel hxy

/-- Occurrence branch in Coq `trivial_hom_ring`.  If `node (h last)` already
occurs on the image ring, face-simplicity and the following mapped `rlink`
force the source contact to be exactly `node last`. -/
theorem PreHomRing.edge_node_last_rLink_of_mem
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    {z : G.Dart} {p₁ p₂ : List G.Dart}
    (hp : p = p₁ ++ p₂)
    (hlast : (x :: p₁).getLastD x = z)
    (hp₁Ne : p₁ ≠ []) (hp₂Ne : p₂ ≠ [])
    (hzFace : PermReachable H.face (h z)
      (H.node (h ((x :: p).getLastD x))))
    (hnodeMem :
      H.node (h ((x :: p).getLastD x)) ∈ (x :: p).map h) :
    G.RLink (G.edge (G.node ((x :: p).getLastD x))) z := by
  let y := (x :: p).getLastD x
  let q₁ := p₁.dropLast
  change PermReachable H.face (h z) (H.node (h y)) at hzFace
  change H.node (h y) ∈ (x :: p).map h at hnodeMem
  have hp₁Shape : p₁ = q₁ ++ [z] := by
    exact eq_dropLast_append_singleton_of_getLastD_append
      (G := G) [] p₁ hp₁Ne hlast
  cases hp₂Shape : p₂ with
  | nil => exact False.elim (hp₂Ne hp₂Shape)
  | cons w ws =>
      have hpathSplit : G.RLinkPath x (q₁ ++ z :: w :: ws) := by
        simpa [hp, hp₁Shape, hp₂Shape, List.append_assoc] using hpre.path
      have hpathTail : G.RLinkPath z (w :: ws) :=
        RLinkPath.suffix_of_append_cons (G := G) hpathSplit
      have hzw : G.RLink z w := hpathTail.1
      have hzMem : z ∈ x :: p := by
        rw [hp, hp₁Shape]
        simp
      have hwMem : w ∈ x :: p := by
        rw [hp, hp₂Shape]
        simp
      have hyMem : y ∈ x :: p := by
        have hne : x :: p ≠ [] := List.cons_ne_nil x p
        dsimp [y, List.getLastD]
        exact List.getLast_mem hne
      have hhzMem : h z ∈ (x :: p).map h :=
        List.mem_map.mpr ⟨z, hzMem, rfl⟩
      have hhyMem : h y ∈ (x :: p).map h :=
        List.mem_map.mpr ⟨y, hyMem, rfl⟩
      have hzMapNode : h z = H.node (h y) :=
        FaceSimple.eq_of_faceReachable_of_mem
          (G := H) hpre.imageCycle.faceSimple hhzMem hnodeMem hzFace
      have hzKernel : G.Kernel r z := hpre.kernel z hzMem
      have hwKernel : G.Kernel r w := hpre.kernel w hwMem
      have hmapZW : H.RLink (h z) (h w) :=
        hG.rLink_map_of_kernel hH hembed hzw hzKernel hwKernel
      have hyHw : PermReachable H.face (h y) (h w) := by
        have hfaceSymmHw : PermReachable H.face (H.face.symm (h y)) (h w) := by
          simpa [RLink, hzMapNode, Hypermap.edge_node_eq_face_symm] using hmapZW
        exact PermReachable.trans H.face
          (PermReachable.backward H.face (h y)) hfaceSymmHw
      have hyMapW : h y = h w :=
        FaceSimple.eq_of_faceReachable_of_mem
          (G := H) hpre.imageCycle.faceSimple hhyMem
          (List.mem_map.mpr ⟨w, hwMem, rfl⟩) hyHw
      have hyw : y = w :=
        eq_of_map_nodup_of_mem hpre.imageCycle.faceSimple.nodup
          hyMem hwMem hyMapW
      have hzy : G.RLink z y := by simpa [hyw] using hzw
      have hyKernel : G.Kernel r y := hpre.kernel y hyMem
      have hedgeZKernel : G.Kernel r (G.edge z) :=
        G.kernel_faceClosed r hyKernel (PermReachable.symm G.face hzy)
      have hfaceSymmYKernel : G.Kernel r (G.face.symm y) :=
        G.kernel_faceClosed r hyKernel (PermReachable.backward G.face y)
      have hfaceSymmMap :
          h (G.face.symm y) = H.face.symm (h y) := by
        apply H.face.injective
        calc
          H.face (h (G.face.symm y)) = h (G.face (G.face.symm y)) :=
            (hembed.face hfaceSymmYKernel).symm
          _ = h y := by simp
          _ = H.face (H.face.symm (h y)) := by simp
      have hedgeZMap : h (G.edge z) = H.edge (h z) :=
        hG.embedFunctor hH hembed hzKernel hedgeZKernel
      have hmapsEqual : h (G.edge z) = h (G.face.symm y) := by
        calc
          h (G.edge z) = H.edge (h z) := hedgeZMap
          _ = H.edge (H.node (h y)) := by rw [hzMapNode]
          _ = H.face.symm (h y) := Hypermap.edge_node_eq_face_symm (G := H) (h y)
          _ = h (G.face.symm y) := hfaceSymmMap.symm
      have hedgeZFaceSymm :
          PermReachable G.face (G.edge z) (G.face.symm y) :=
        PermReachable.trans G.face hzy
          (PermReachable.backward G.face y)
      have hedgeEq : G.edge z = G.face.symm y :=
        hembed.injective_of_faceReachable (G.kernel_faceClosed r)
          hedgeZKernel hedgeZFaceSymm hmapsEqual
      have hzNode : z = G.node y := by
        apply G.edge.injective
        rw [hedgeEq, Hypermap.edge_node_eq_face_symm]
      simpa [y, hzNode] using
        (RLink.edge_self_of_plain (G := G) hG.plain (G.node y))

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
