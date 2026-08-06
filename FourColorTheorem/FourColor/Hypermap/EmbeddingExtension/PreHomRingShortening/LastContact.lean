import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingShortening.PathTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

open PreHomRingShortening

/-- Kernel and image equations for the two node darts following the old last
dart, after the first half of Coq `trivial_hom_ring` has produced its return
`rlink`. -/
theorem PreHomRing.last_node_extension_data
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    {z : G.Dart}
    (hzMem : z ∈ x :: p)
    (henyRz :
      G.RLink (G.edge (G.node ((x :: p).getLastD x))) z) :
    let y := (x :: p).getLastD x
    let enny := G.edge (G.node (G.node y))
    G.Kernel r (G.node y) ∧
      h (G.node y) = H.node (h y) ∧
        G.Kernel r enny ∧
          h enny = H.edge (H.node (H.node (h y))) := by
  dsimp only
  let y := (x :: p).getLastD x
  let eny := G.edge (G.node y)
  let enny := G.edge (G.node (G.node y))
  have hyMem : y ∈ x :: p := by
    have hne : x :: p ≠ [] := List.cons_ne_nil x p
    dsimp [y, List.getLastD]
    exact List.getLast_mem hne
  have hyKernel : G.Kernel r y := hpre.kernel y hyMem
  have hzKernel : G.Kernel r z := hpre.kernel z hzMem
  have henyKernel : G.Kernel r eny := by
    apply G.kernel_faceClosed r hyKernel
    simpa [eny, Hypermap.edge_node_eq_face_symm] using
      (PermReachable.backward G.face y)
  have hnodeYKernel : G.Kernel r (G.node y) := by
    have hedgeEnyKernel : G.Kernel r (G.edge eny) :=
      G.kernel_faceClosed r hzKernel
        (PermReachable.symm G.face (by simpa [eny, y] using henyRz))
    simpa [eny, Hypermap.Plain.edge_edge (G := G) hG.plain] using
      hedgeEnyKernel
  have henyMap : h eny = H.edge (H.node (h y)) := by
    apply H.face.injective
    calc
      H.face (h eny) = h (G.face eny) := (hembed.face henyKernel).symm
      _ = h y := by simp [eny, Hypermap.edge_node_eq_face_symm]
      _ = H.face (H.edge (H.node (h y))) := by
        simp [Hypermap.edge_node_eq_face_symm]
  have hnodeYMap : h (G.node y) = H.node (h y) := by
    apply H.edge.injective
    calc
      H.edge (h (G.node y)) = h eny :=
        (hG.embedFunctor hH hembed hnodeYKernel henyKernel).symm
      _ = H.edge (H.node (h y)) := henyMap
  have hennyKernel : G.Kernel r enny := by
    apply G.kernel_faceClosed r hnodeYKernel
    simpa [enny, Hypermap.edge_node_eq_face_symm] using
      (PermReachable.backward G.face (G.node y))
  have hennyMap : h enny = H.edge (H.node (H.node (h y))) := by
    apply H.face.injective
    calc
      H.face (h enny) = h (G.face enny) := (hembed.face hennyKernel).symm
      _ = h (G.node y) := by
        simp [enny, Hypermap.edge_node_eq_face_symm]
      _ = H.node (h y) := hnodeYMap
      _ = H.face (H.edge (H.node (H.node (h y)))) := by
        simp [Hypermap.edge_node_eq_face_symm]
  exact ⟨hnodeYKernel, hnodeYMap, hennyKernel, hennyMap⟩

/-- Second occurrence branch of Coq `trivial_hom_ring`.  Target cubicity puts
`node (node (h last))` in the closing face.  If that dart is listed, image
face-simplicity forces the source contact to be the first successor, after
which face-orbit injectivity identifies the source head with
`node (node last)`. -/
theorem PreHomRing.edge_node_node_last_rLink_of_mem
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    {z : G.Dart} {p₁ p₂ : List G.Dart}
    (hp : p = p₁ ++ p₂)
    (hlast : (x :: p₁).getLastD x = z)
    (hp₁Ne : p₁ ≠ [])
    (hzFace : PermReachable H.face (h z)
      (H.node (h ((x :: p).getLastD x))))
    (henyRz :
      G.RLink (G.edge (G.node ((x :: p).getLastD x))) z)
    (hnnNodeMem :
      H.node (H.node (h ((x :: p).getLastD x))) ∈ (x :: p).map h) :
    G.RLink (G.edge (G.node (G.node ((x :: p).getLastD x)))) x := by
  let y := (x :: p).getLastD x
  let eny := G.edge (G.node y)
  let enny := G.edge (G.node (G.node y))
  let w := p₁.head hp₁Ne
  change PermReachable H.face (h z) (H.node (h y)) at hzFace
  change G.RLink eny z at henyRz
  change H.node (H.node (h y)) ∈ (x :: p).map h at hnnNodeMem
  have hwMemP₁ : w ∈ p₁ := by
    exact List.head_mem hp₁Ne
  have hwMem : w ∈ x :: p := by
    rw [hp]
    simp [hwMemP₁]
  have hxMem : x ∈ x :: p := by simp
  have hzMem : z ∈ x :: p := by
    rw [hp]
    have hzP₁ : z ∈ p₁ := by
      rw [eq_dropLast_append_singleton_of_getLastD_append
        (G := G) [] p₁ hp₁Ne hlast]
      simp
    simp [hzP₁]
  have hpathFirst : G.RLink x w := by
    have hp₁Cons : w :: p₁.tail = p₁ := List.cons_head_tail hp₁Ne
    have hpath : G.RLinkPath x ((w :: p₁.tail) ++ p₂) := by
      rw [hp₁Cons, ← hp]
      exact hpre.path
    simpa [RLinkPath] using hpath.1
  have hyMem : y ∈ x :: p := by
    have hne : x :: p ≠ [] := List.cons_ne_nil x p
    dsimp [y, List.getLastD]
    exact List.getLast_mem hne
  have hclose : H.RLink (h y) (h x) := by
    simpa [y] using hpre.imageClosing
  have hcubicH : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hnnHx : PermReachable H.face (H.node (H.node (h y))) (h x) :=
    nodeNode_faceReachable_of_rLink hcubicH hclose
  have hxMapNN : h x = H.node (H.node (h y)) := by
    exact (FaceSimple.eq_of_faceReachable_of_mem
      (G := H) hpre.imageCycle.faceSimple hnnNodeMem
      (List.mem_map.mpr ⟨x, hxMem, rfl⟩) hnnHx).symm
  have hxKernel : G.Kernel r x := hpre.kernel x hxMem
  have hwKernel : G.Kernel r w := hpre.kernel w hwMem
  have hmapXW : H.RLink (h x) (h w) :=
    hG.rLink_map_of_kernel hH hembed hpathFirst hxKernel hwKernel
  have hnodeHw : PermReachable H.face (H.node (h y)) (h w) := by
    have hfaceSymmHw :
        PermReachable H.face (H.face.symm (H.node (h y))) (h w) := by
      simpa [RLink, hxMapNN, Hypermap.edge_node_eq_face_symm] using hmapXW
    exact PermReachable.trans H.face
      (PermReachable.backward H.face (H.node (h y))) hfaceSymmHw
  have hzHw : PermReachable H.face (h z) (h w) :=
    PermReachable.trans H.face hzFace hnodeHw
  have hzMapW : h z = h w :=
    FaceSimple.eq_of_faceReachable_of_mem
      (G := H) hpre.imageCycle.faceSimple
      (List.mem_map.mpr ⟨z, hzMem, rfl⟩)
      (List.mem_map.mpr ⟨w, hwMem, rfl⟩) hzHw
  have hzw : z = w :=
    eq_of_map_nodup_of_mem hpre.imageCycle.faceSimple.nodup
      hzMem hwMem hzMapW
  have hxRz : G.RLink x z := by simpa [hzw] using hpathFirst
  rcases hpre.last_node_extension_data hG hH hembed hzMem henyRz with
    ⟨_hnodeYKernel, _hnodeYMap, hennyKernel, hennyMap⟩
  have hzKernel : G.Kernel r z := hpre.kernel z hzMem
  have hedgeXKernel : G.Kernel r (G.edge x) :=
    G.kernel_faceClosed r hzKernel (PermReachable.symm G.face hxRz)
  have hedgeXMap : h (G.edge x) = H.edge (h x) :=
    hG.embedFunctor hH hembed hxKernel hedgeXKernel
  have hedgeXEnny : PermReachable G.face (G.edge x) enny := by
    have hnodeYZ : PermReachable G.face (G.node y) z := by
      change PermReachable G.face (G.edge eny) z at henyRz
      have hedgeEny : G.edge eny = G.node y := by
        simp [eny, Hypermap.Plain.edge_edge (G := G) hG.plain]
      rw [hedgeEny] at henyRz
      exact henyRz
    have hnodeYEnny : PermReachable G.face (G.node y) enny := by
      dsimp [enny]
      rw [Hypermap.edge_node_eq_face_symm]
      exact PermReachable.backward G.face (G.node y)
    exact PermReachable.trans G.face hxRz
      (PermReachable.trans G.face
        (PermReachable.symm G.face hnodeYZ) hnodeYEnny)
  have hmapsEqual : h (G.edge x) = h enny := by
    calc
      h (G.edge x) = H.edge (h x) := hedgeXMap
      _ = H.edge (H.node (H.node (h y))) := by rw [hxMapNN]
      _ = h enny := hennyMap.symm
  have hedgeEq : G.edge x = enny :=
    hembed.injective_of_faceReachable (G.kernel_faceClosed r)
      hedgeXKernel hedgeXEnny hmapsEqual
  change G.RLink enny x
  rw [← hedgeEq]
  exact RLink.edge_self_of_plain (G := G) hG.plain x

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
