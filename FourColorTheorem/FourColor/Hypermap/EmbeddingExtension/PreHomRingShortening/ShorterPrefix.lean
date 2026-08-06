import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingShortening.ShorterSuffix

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

open PreHomRingShortening

/-- The symmetric recursive branch of Coq `trivial_hom_ring`.  Once the first
return link has been established, a missing `node (node (h last))` cuts off
the nonempty right arc and replaces the contact by
`edge (node (node last))`. -/
theorem PreHomRing.exists_shorter_prefix
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
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
    (henyRz :
      G.RLink (G.edge (G.node ((x :: p).getLastD x))) z)
    (hnnNodeNotMem :
      H.node (H.node (h ((x :: p).getLastD x))) ∉ (x :: p).map h) :
    ∃ q : List G.Dart,
      PreHomRing r h x q ∧
        (x :: q).getLastD x =
          G.edge (G.node (G.node ((x :: p).getLastD x))) ∧
          q.length < p.length ∧
            ∀ u : H.Dart, ¬ H.DiskF ((x :: q).map h) u := by
  let y := (x :: p).getLastD x
  let q₁ := p₁.dropLast
  let q₂ := p₂.dropLast
  let eny := G.edge (G.node y)
  let enny := G.edge (G.node (G.node y))
  let q := q₁ ++ [enny]
  change PermReachable H.face (h z) (H.node (h y)) at hzFace
  change G.RLink eny z at henyRz
  change H.node (H.node (h y)) ∉ (x :: p).map h at hnnNodeNotMem
  have hshapes := split_dropLast_shapes_of_getLastD
    (G := G) hp hlast hp₁Ne hp₂Ne
  have hp₁Shape : p₁ = q₁ ++ [z] := hshapes.1
  have hp₂Shape : p₂ = q₂ ++ [y] := hshapes.2
  have hzMem : z ∈ x :: p := by
    rw [hp, hp₁Shape]
    simp
  rcases hpre.last_node_extension_data hG hH hembed hzMem henyRz with
    ⟨_hnodeYKernel, _hnodeYMap, hennyKernel, hennyMap⟩
  have hpathP₁ : G.RLinkPath x p₁ := by
    apply RLinkPath.prefix_of_append (G := G)
    simpa [hp] using hpre.path
  have hpathXZ : G.RLinkPath x (q₁ ++ [z]) := by
    simpa [hp₁Shape] using hpathP₁
  have hzEnny : PermReachable G.face z enny := by
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
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hnodeYZ) hnodeYEnny
  have hpathCandidate : G.RLinkPath x q := by
    simpa [q] using
      (RLinkPath.replace_last_of_faceReachable (G := G) hpathXZ hzEnny)
  have hcandidateKernel :
      ∀ t : G.Dart, t ∈ x :: q → G.Kernel r t := by
    intro t ht
    rcases List.mem_cons.mp ht with htHead | htTail
    · exact hpre.kernel t (by simp [htHead])
    · change t ∈ q₁ ++ [enny] at htTail
      rw [List.mem_append] at htTail
      rcases htTail with htq₁ | htEnny
      · apply hpre.kernel t
        rw [hp, hp₁Shape]
        simp [htq₁]
      · have htEq : t = enny := by simpa using htEnny
        simpa [htEq] using hennyKernel
  let arranged : List H.Dart :=
    h x :: q₁.map h ++ h z :: (q₂.map h ++ [h y])
  have hsourceDecomp :
      x :: p = x :: q₁ ++ z :: (q₂ ++ [y]) := by
    simp [hp, hp₁Shape, hp₂Shape, List.append_assoc]
  have hmapArranged : (x :: p).map h = arranged := by
    rw [hsourceDecomp]
    simp [arranged, List.map_append]
  have hcycleArranged : H.SimpleRLinkCycle arranged := by
    rw [← hmapArranged]
    exact hpre.imageCycle
  have hzHenny : PermReachable H.face (h z) (h enny) := by
    have hnodeHenny :
        PermReachable H.face (H.node (h y)) (h enny) := by
      rw [hennyMap, Hypermap.edge_node_eq_face_symm]
      exact PermReachable.backward H.face (H.node (h y))
    exact PermReachable.trans H.face hzFace hnodeHenny
  have hclose : H.RLink (h y) (h x) := by
    simpa [y] using hpre.imageClosing
  have hcubicH : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hnnHx : PermReachable H.face (H.node (H.node (h y))) (h x) :=
    nodeNode_faceReachable_of_rLink hcubicH hclose
  have hedgeHenny : H.edge (h enny) = H.node (H.node (h y)) := by
    calc
      H.edge (h enny) =
          H.edge (H.edge (H.node (H.node (h y)))) :=
        congrArg H.edge hennyMap
      _ = H.node (H.node (h y)) :=
        Hypermap.Plain.edge_edge (G := H) hH.plain _
  have hennyRx : H.RLink (h enny) (h x) := by
    unfold RLink
    rw [hedgeHenny]
    exact hnnHx
  have hxEdgeHenny : PermReachable H.face (h x) (H.edge (h enny)) := by
    rw [hedgeHenny]
    exact PermReachable.symm H.face hnnHx
  have hchord :
      H.SimpleRLinkCycle (h enny :: h x :: q₁.map h) := by
    exact SimpleRLinkCycle.chord_prefix_of_decomposition
      (G := H) hcycleArranged hennyRx hzHenny
  have hcandCycle : H.SimpleRLinkCycle ((x :: q).map h) := by
    have hrot := SimpleRLinkCycle.rotate (G := H) 1 hchord
    simpa [q, List.map_append, List.rotate_cons_succ,
      List.append_assoc] using hrot
  have hpreCandidate : PreHomRing r h x q :=
    ⟨hpathCandidate, hcandidateKernel, hcandCycle⟩
  have hlastCandidate :
      (x :: q).getLastD x = G.edge (G.node (G.node y)) := by
    simp [q, enny, List.getLastD]
  have hshort : q.length < p.length := by
    have hp₁Pos : 0 < p₁.length := List.length_pos_iff.mpr hp₁Ne
    have hp₂Pos : 0 < p₂.length := List.length_pos_iff.mpr hp₂Ne
    have hqLen : q.length = p₁.length := by
      simp [q, q₁, List.length_dropLast]
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
    rw [← hmapArranged]
    simp [hp]
    omega
  have hyMem : y ∈ x :: p := by
    rw [hp, hp₂Shape]
    simp
  have hhyMem : h y ∈ (x :: p).map h :=
    List.mem_map.mpr ⟨y, hyMem, rfl⟩
  have hnnDisk : H.DiskN ((x :: p).map h) (H.node (H.node (h y))) :=
    (H.diskN_node_iff (r := (x :: p).map h)).2
      ((H.diskN_node_iff (r := (x :: p).map h)).2
        (H.diskN_of_mem hhyMem))
  have hnnE : H.DiskE ((x :: p).map h) (H.node (H.node (h y))) :=
    ⟨hnnDisk, hnnNodeNotMem⟩
  have hennyEOrig : H.DiskE ((x :: p).map h) (h enny) := by
    apply (H.diskE_edge_iff hJordan hH.plain hpre.imageCycle).1
    rw [hedgeHenny]
    exact hnnE
  have hennyEArranged : H.DiskE arranged (h enny) := by
    simpa [hmapArranged] using hennyEOrig
  have hcomplement :
      H.SimpleRLinkCycle
        (H.edge (h enny) :: h z :: (q₂.map h ++ [h y])) := by
    exact SimpleRLinkCycle.edge_chord_suffix_of_decomposition
      (G := H) hH.plain hcycleArranged hzHenny hxEdgeHenny
  have hnoChord :
      ∀ u : H.Dart, ¬ H.DiskF (h enny :: h x :: q₁.map h) u := by
    intro u hu
    have huArranged : H.DiskF arranged u :=
      (H.diskF_chord_prefix hconnected hJordan hH.plain
        hcycleArranged hproperArranged hennyEArranged
        (by simp) (by simp)
        hzHenny hxEdgeHenny hchord hcomplement).1 hu |>.1
    exact hnoDisk u (by simpa [hmapArranged] using huArranged)
  have hnoCandidate :
      ∀ u : H.Dart, ¬ H.DiskF ((x :: q).map h) u := by
    intro u hu
    have huRot :
        H.DiskF ((h enny :: h x :: q₁.map h).rotate 1) u := by
      simpa [q, List.map_append, List.rotate_cons_succ,
        List.append_assoc] using hu
    exact hnoChord u ((DiskF.rotate (G := H) 1).1 huRot)
  exact ⟨q, hpreCandidate, hlastCandidate, hshort, hnoCandidate⟩

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
