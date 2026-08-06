import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingShortening.LastContact

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

open PreHomRingShortening

/-- The first recursive branch of Coq `trivial_hom_ring`.  If the node after
the last image dart is not itself listed, cut at its boundary-face contact and
replace the old last dart by `edge (node last)`.  The target list is exactly a
rotation of the corresponding chord ring, so `diskF_chord_ring` preserves the
empty selected disk while the nonempty omitted prefix gives strict descent. -/
theorem PreHomRing.exists_shorter_suffix
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hnoDisk : ∀ u : H.Dart,
      ¬ H.DiskF ((x :: p).map h) u)
    {z : G.Dart} {p₁ p₂ : List G.Dart}
    (hp : p = p₁ ++ p₂)
    (hlast : (x :: p₁).getLastD x = z)
    (hp₁Ne : p₁ ≠ []) (hp₂Ne : p₂ ≠ [])
    (hzFace : PermReachable H.face (h z)
      (H.node (h ((x :: p).getLastD x))))
    (hnodeNotMem :
      H.node (h ((x :: p).getLastD x)) ∉ (x :: p).map h) :
    ∃ q : List G.Dart,
      PreHomRing r h z q ∧
        (z :: q).getLastD z =
          G.edge (G.node ((x :: p).getLastD x)) ∧
          q.length < p.length ∧
        ∀ u : H.Dart, ¬ H.DiskF ((z :: q).map h) u := by
  let y := (x :: p).getLastD x
  let q₁ := p₁.dropLast
  let q₂ := p₂.dropLast
  let eny := G.edge (G.node y)
  let q := q₂ ++ [eny]
  change PermReachable H.face (h z) (H.node (h y)) at hzFace
  change H.node (h y) ∉ (x :: p).map h at hnodeNotMem
  have hshapes := split_dropLast_shapes_of_getLastD
    (G := G) hp hlast hp₁Ne hp₂Ne
  have hp₁Shape : p₁ = q₁ ++ [z] := hshapes.1
  have hp₂Shape : p₂ = q₂ ++ [y] := hshapes.2
  have hpathSplit :
      G.RLinkPath x (q₁ ++ z :: (q₂ ++ [y])) := by
    simpa [hp, hp₁Shape, hp₂Shape, List.append_assoc] using hpre.path
  have hpathZY : G.RLinkPath z (q₂ ++ [y]) :=
    RLinkPath.suffix_of_append_cons (G := G) hpathSplit
  have hyEny : PermReachable G.face y eny := by
    dsimp [eny]
    rw [Hypermap.edge_node_eq_face_symm]
    exact PermReachable.backward G.face y
  have hpathCandidate : G.RLinkPath z q := by
    simpa [q] using
      (RLinkPath.replace_last_of_faceReachable (G := G) hpathZY hyEny)
  have hyMem : y ∈ x :: p := by
    rw [hp, hp₂Shape]
    simp
  have hyKernel : G.Kernel r y := hpre.kernel y hyMem
  have henyKernel : G.Kernel r eny := by
    apply G.kernel_faceClosed r hyKernel
    simpa [eny, Hypermap.edge_node_eq_face_symm] using
      (PermReachable.backward G.face y)
  have henyMap : h eny = H.edge (H.node (h y)) := by
    apply H.face.injective
    calc
      H.face (h eny) = h (G.face eny) := (hembed.face henyKernel).symm
      _ = h y := by simp [eny, Hypermap.edge_node_eq_face_symm]
      _ = H.face (H.edge (H.node (h y))) := by
        simp [Hypermap.edge_node_eq_face_symm]
  have hcandidateKernel :
      ∀ t : G.Dart, t ∈ z :: q → G.Kernel r t := by
    intro t ht
    rcases List.mem_cons.mp ht with htHead | ht
    · apply hpre.kernel t
      rw [hp, hp₁Shape]
      simp [htHead]
    · change t ∈ q₂ ++ [eny] at ht
      rw [List.mem_append] at ht
      rcases ht with htq₂ | htEny
      · apply hpre.kernel t
        rw [hp, hp₂Shape]
        simp [htq₂]
      · have htEq : t = eny := by simpa using htEny
        simpa [htEq] using henyKernel
  let pre : List G.Dart := x :: q₁
  let arranged : List H.Dart :=
    h z :: q₂.map h ++ h y :: h x :: q₁.map h
  have hsourceDecomp :
      x :: p = pre ++ z :: (q₂ ++ [y]) := by
    simp [pre, hp, hp₁Shape, hp₂Shape, List.append_assoc]
  have hrotateEq :
      ((x :: p).map h).rotate pre.length = arranged := by
    rw [← List.map_rotate]
    rw [hsourceDecomp, List.rotate_append_length_eq]
    simp [arranged, pre, List.map_append, List.append_assoc]
  have hcycleArranged : H.SimpleRLinkCycle arranged := by
    have hrot := SimpleRLinkCycle.rotate (G := H) pre.length hpre.imageCycle
    rw [hrotateEq] at hrot
    exact hrot
  have hyEnyTarget : PermReachable H.face (h y) (h eny) := by
    rw [henyMap, Hypermap.edge_node_eq_face_symm]
    exact PermReachable.backward H.face (h y)
  have hzEdgeEny : PermReachable H.face (h z) (H.edge (h eny)) := by
    simpa [henyMap, Hypermap.Plain.edge_edge (G := H) hH.plain]
      using hzFace
  have henyRz : H.RLink (h eny) (h z) := by
    unfold RLink
    exact PermReachable.symm H.face hzEdgeEny
  have hchord :
      H.SimpleRLinkCycle (h eny :: h z :: q₂.map h) := by
    exact SimpleRLinkCycle.chord_prefix_of_decomposition
      (G := H) hcycleArranged henyRz hyEnyTarget
  have hcandCycle : H.SimpleRLinkCycle ((z :: q).map h) := by
    have hrot := SimpleRLinkCycle.rotate (G := H) 1 hchord
    simpa [q, List.map_append, List.rotate_cons_succ,
      List.append_assoc] using hrot
  have hpreCandidate : PreHomRing r h z q :=
    ⟨hpathCandidate, hcandidateKernel, hcandCycle⟩
  have hlastCandidate : (z :: q).getLastD z = G.edge (G.node y) := by
    simp [q, eny, List.getLastD]
  have hshort : q.length < p.length := by
    have hp₁Pos : 0 < p₁.length := List.length_pos_iff.mpr hp₁Ne
    have hp₂Pos : 0 < p₂.length := List.length_pos_iff.mpr hp₂Ne
    have hqLen : q.length = p₂.length := by
      simp [q, q₂, List.length_dropLast]
      omega
    rw [hqLen, hp, List.length_append]
    omega
  have hconnected : H.Connected :=
    Unavoidability.connectedMinimalCounterexamples_proved H hH
  have hJordan : H.Jordan :=
    Unavoidability.eulerPlanar_jordan H hH.planar
  have hproperArranged : H.ProperRing arranged := by
    apply H.properRing_of_length_gt_two
    have hp₁Pos : 0 < p₁.length := List.length_pos_iff.mpr hp₁Ne
    have hp₂Pos : 0 < p₂.length := List.length_pos_iff.mpr hp₂Ne
    have hlen : arranged.length = (x :: p).length := by
      rw [← hrotateEq, List.length_rotate]
      simp
    rw [hlen]
    simp [hp]
    omega
  have hhyMem : h y ∈ (x :: p).map h := List.mem_map.mpr ⟨y, hyMem, rfl⟩
  have hnodeDisk : H.DiskN ((x :: p).map h) (H.node (h y)) :=
    (H.diskN_node_iff (r := (x :: p).map h)).2
      (H.diskN_of_mem hhyMem)
  have hnodeE : H.DiskE ((x :: p).map h) (H.node (h y)) :=
    ⟨hnodeDisk, hnodeNotMem⟩
  have henyEOrig : H.DiskE ((x :: p).map h) (h eny) := by
    apply (H.diskE_edge_iff hJordan hH.plain hpre.imageCycle).1
    simpa [henyMap, Hypermap.Plain.edge_edge (G := H) hH.plain]
      using hnodeE
  have henyEArranged : H.DiskE arranged (h eny) := by
    have hrot :
        H.DiskE (((x :: p).map h).rotate pre.length) (h eny) :=
      (DiskE.rotate (G := H) pre.length).2 henyEOrig
    rw [hrotateEq] at hrot
    exact hrot
  have hcomplement :
      H.SimpleRLinkCycle (H.edge (h eny) :: h y :: h x :: q₁.map h) := by
    exact SimpleRLinkCycle.edge_chord_suffix_of_decomposition
      (G := H) hH.plain hcycleArranged hyEnyTarget hzEdgeEny
  have hnoChord :
      ∀ u : H.Dart, ¬ H.DiskF (h eny :: h z :: q₂.map h) u := by
    intro u hu
    have huArranged : H.DiskF arranged u :=
      (H.diskF_chord_prefix hconnected hJordan hH.plain
        hcycleArranged hproperArranged henyEArranged
        (by simp) (by simp)
        hyEnyTarget hzEdgeEny hchord hcomplement).1 hu |>.1
    have huOrig : H.DiskF ((x :: p).map h) u := by
      apply (DiskF.rotate (G := H) pre.length).1
      rw [hrotateEq]
      exact huArranged
    exact hnoDisk u huOrig
  have hnoCandidate :
      ∀ u : H.Dart, ¬ H.DiskF ((z :: q).map h) u := by
    intro u hu
    have huRot :
        H.DiskF ((h eny :: h z :: q₂.map h).rotate 1) u := by
      simpa [q, List.map_append, List.rotate_cons_succ,
        List.append_assoc] using hu
    exact hnoChord u ((DiskF.rotate (G := H) 1).1 huRot)
  exact ⟨q, hpreCandidate, hlastCandidate, hshort, hnoCandidate⟩

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
