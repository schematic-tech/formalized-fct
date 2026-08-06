import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingReversal

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- The loop-erasure induction inside Coq `embed_full`.  A kernel-contained
`rlink` path of length at most five has a no-longer mapped path with the same
endpoint and a face-simple image.  When a mapped face repeats, the repeated
target face is lifted to the source.  The only obstruction to erasing the
resulting loop would be a nonclosing pre-hom ring of length at most five,
which `shortPreHomRing_closes` excludes. -/
theorem mappedFaceSimpleSubpath
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x₀ : G.Dart} {p : List G.Dart}
    (hpath : G.RLinkPath x₀ p)
    (hkernel : ∀ z : G.Dart, z ∈ p → G.Kernel r z)
    (hbound : p.length ≤ 5) :
    ∃ q : List G.Dart,
      G.RLinkPath x₀ q ∧
        (x₀ :: q).getLastD x₀ = (x₀ :: p).getLastD x₀ ∧
          (∀ z : G.Dart, z ∈ q → G.Kernel r z) ∧
            H.FaceSimple (q.map h) ∧ q.length ≤ p.length := by
  classical
  induction p generalizing x₀ with
  | nil =>
      exact ⟨[], by simp [RLinkPath, FaceSimple, List.getLastD]⟩
  | cons x₁ p ih =>
      have hpathParts : G.RLink x₀ x₁ ∧ G.RLinkPath x₁ p := by
        simpa [RLinkPath] using hpath
      have hx₁Kernel : G.Kernel r x₁ := hkernel x₁ (by simp)
      have hpKernel : ∀ z : G.Dart, z ∈ p → G.Kernel r z := by
        intro z hz
        exact hkernel z (by simp [hz])
      have hpBound : p.length ≤ 5 := by
        simp only [List.length_cons] at hbound
        omega
      rcases ih hpathParts.2 hpKernel hpBound with
        ⟨q, hqPath, hqLast, hqKernel, hqSimple, hqLength⟩
      by_cases hx₁Band : H.FaceBand (q.map h) (h x₁)
      · rcases hx₁Band with ⟨_, hzMap, hzFace⟩
        rcases List.mem_map.mp hzMap with ⟨x₂, hx₂Q, rfl⟩
        have hx₂Kernel : G.Kernel r x₂ := hqKernel x₂ hx₂Q
        rcases hembed.faceReachable_lift (G.kernel_faceClosed r)
            hx₂Kernel hzFace with ⟨x₃, hx₂x₃, hx₃Map⟩
        have hx₃Kernel : G.Kernel r x₃ :=
          G.kernel_faceClosed r hx₂Kernel hx₂x₃
        rcases (List.mem_iff_append).1 hx₂Q with ⟨q₁, q₂, hqSplit⟩
        have hqPathSplit : G.RLinkPath x₁ (q₁ ++ x₂ :: q₂) := by
          simpa [hqSplit] using hqPath
        have hqSimpleSplit :
            H.FaceSimple ((q₁ ++ x₂ :: q₂).map h) := by
          simpa [hqSplit] using hqSimple
        by_cases hx₃Eq : x₃ = x₁
        · have hx₀x₂ : G.RLink x₀ x₂ :=
            RLink.of_faceReachable_right (G := G) hpathParts.1
              (PermReachable.symm G.face (by simpa [hx₃Eq] using hx₂x₃))
          have hq₂Path : G.RLinkPath x₂ q₂ :=
            RLinkPath.suffix_of_append_cons (G := G) hqPathSplit
          have hnewLast :
              (x₀ :: x₂ :: q₂).getLastD x₀ =
                (x₀ :: x₁ :: p).getLastD x₀ := by
            calc
              (x₀ :: x₂ :: q₂).getLastD x₀ =
                  (x₁ :: (q₁ ++ x₂ :: q₂)).getLastD x₁ := by
                    simp [List.getLastD]
              _ = (x₁ :: p).getLastD x₁ := by
                    simpa [hqSplit] using hqLast
              _ = (x₀ :: x₁ :: p).getLastD x₀ := by
                    simp [List.getLastD]
          have hnewSimple : H.FaceSimple ((x₂ :: q₂).map h) := by
            rw [FaceSimple] at hqSimpleSplit ⊢
            apply List.Pairwise.sublist
              (List.Sublist.map h
                (List.sublist_append_right q₁ (x₂ :: q₂)))
              hqSimpleSplit
          refine ⟨x₂ :: q₂, ⟨hx₀x₂, hq₂Path⟩, hnewLast,
            ?_, hnewSimple, ?_⟩
          · intro z hz
            exact hqKernel z (by
              rw [hqSplit]
              exact List.mem_append_right q₁ hz)
          · simp only [hqSplit, List.length_cons, List.length_append] at hqLength
            simp only [List.length_cons]
            omega
        · cases q₁ with
          | nil =>
              have hx₁x₂ : G.RLink x₁ x₂ := by
                simpa [RLinkPath] using hqPathSplit.1
              have hedgeX₁Kernel : G.Kernel r (G.edge x₁) :=
                G.kernel_faceClosed r hx₂Kernel
                  (PermReachable.symm G.face hx₁x₂)
              have hedgeMap : h (G.edge x₁) = H.edge (h x₁) :=
                hG.embedFunctor hH hembed hx₁Kernel hedgeX₁Kernel
              have htargetBridge :
                  PermReachable H.face (H.edge (h x₁)) (h x₁) := by
                have hfirst := hembed.faceReachable_map
                  (G.kernel_faceClosed r) hedgeX₁Kernel hx₁x₂
                exact PermReachable.trans H.face
                  (by simpa [hedgeMap] using hfirst) hzFace
              exact False.elim
                (hH.bridgeless (h x₁)
                  (PermReachable.symm H.face htargetBridge))
          | cons x qs =>
              have hpathPartsQ₁ :
                  G.RLink x₁ x ∧ G.RLinkPath x (qs ++ x₂ :: q₂) := by
                simpa [RLinkPath, List.append_assoc] using hqPathSplit
              have hxKernel : G.Kernel r x := hqKernel x (by
                rw [hqSplit]
                simp)
              have htoX₂ : G.RLinkPath x (qs ++ [x₂]) := by
                apply RLinkPath.prefix_of_append (G := G)
                  (q := q₂)
                simpa [List.append_assoc] using hpathPartsQ₁.2
              have hcandidatePath : G.RLinkPath x (qs ++ [x₃]) :=
                RLinkPath.replace_last_of_faceReachable
                  (G := G) htoX₂ hx₂x₃
              have hcandidateKernel :
                  ∀ z : G.Dart, z ∈ x :: (qs ++ [x₃]) → G.Kernel r z := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hxKernel
                · rw [List.mem_append] at hz
                  rcases hz with hz | hz
                  · exact hqKernel z (by
                      rw [hqSplit]
                      simp [hz])
                  · simp at hz
                    subst z
                    exact hx₃Kernel
              have hedgeX₁Kernel : G.Kernel r (G.edge x₁) :=
                G.kernel_faceClosed r hxKernel
                  (PermReachable.symm G.face hpathPartsQ₁.1)
              have hedgeX₁Map :
                  h (G.edge x₁) = H.edge (h x₁) :=
                hG.embedFunctor hH hembed hx₁Kernel hedgeX₁Kernel
              have hcandidateClose : H.RLink (h x₃) (h x) := by
                have hmapFirst := hembed.faceReachable_map
                  (G.kernel_faceClosed r) hedgeX₁Kernel hpathPartsQ₁.1
                unfold RLink
                simpa [hx₃Map, hedgeX₁Map] using hmapFirst
              have hprefixSimple : H.FaceSimple ((x :: qs).map h) := by
                rw [FaceSimple] at hqSimpleSplit ⊢
                apply List.Pairwise.sublist
                  (List.Sublist.map h
                    (List.sublist_append_left (x :: qs) (x₂ :: q₂)))
                  hqSimpleSplit
              have hprefixCross :
                  ∀ a : H.Dart, a ∈ (x :: qs).map h →
                    ¬ PermReachable H.face a (h x₂) := by
                intro a ha haFace
                have hqSimpleAppend :
                    H.FaceSimple
                      (((x :: qs).map h) ++ (x₂ :: q₂).map h) := by
                  simpa [List.map_append] using hqSimpleSplit
                rw [FaceSimple, List.pairwise_append] at hqSimpleAppend
                exact hqSimpleAppend.2.2 a ha (h x₂) (by simp) haFace
              have hcandidateSimple :
                  H.FaceSimple ((x :: (qs ++ [x₃])).map h) := by
                have happend :
                    H.FaceSimple (((x :: qs).map h) ++ [h x₃]) := by
                  rw [FaceSimple, List.pairwise_append]
                  refine ⟨hprefixSimple, by simp, ?_⟩
                  intro a ha b hb hab
                  simp only [List.mem_singleton] at hb
                  subst b
                  apply hprefixCross a ha
                  exact PermReachable.trans H.face hab
                    (by simpa [hx₃Map] using
                      (PermReachable.symm H.face hzFace))
                simpa [List.map_append] using happend
              have hpre : PreHomRing r h x (qs ++ [x₃]) :=
                hG.introPreHomRing hH hembed hcandidatePath
                  (by simpa [List.getLastD] using hcandidateClose)
                  hcandidateKernel hcandidateSimple
              have hopen : ¬ G.RLink x₃ x := by
                intro hx₃x
                have hedgeX₃Kernel : G.Kernel r (G.edge x₃) :=
                  G.kernel_faceClosed r hxKernel
                    (PermReachable.symm G.face hx₃x)
                have hedgeX₃Map :
                    h (G.edge x₃) = H.edge (h x₃) :=
                  hG.embedFunctor hH hembed hx₃Kernel hedgeX₃Kernel
                have hedgeReach :
                    PermReachable G.face (G.edge x₃) (G.edge x₁) :=
                  PermReachable.trans G.face hx₃x
                    (PermReachable.symm G.face hpathPartsQ₁.1)
                have hedgeEq : G.edge x₃ = G.edge x₁ :=
                  hembed.injective_of_faceReachable
                    (G.kernel_faceClosed r) hedgeX₃Kernel hedgeReach (by
                      rw [hedgeX₃Map, hedgeX₁Map, hx₃Map])
                exact hx₃Eq (G.edge.injective hedgeEq)
              have hcandidateBound : (qs ++ [x₃]).length ≤ 4 := by
                simp [hqSplit] at hqLength
                simp at hbound ⊢
                omega
              exact False.elim
                (hopen (by simpa [List.getLastD] using
                  (hG.shortPreHomRing_closes hH hembed hpre
                    hcandidateBound)))
      · refine ⟨x₁ :: q, ⟨hpathParts.1, hqPath⟩, ?_, ?_, ?_, ?_⟩
        · simpa [List.getLastD] using hqLast
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hx₁Kernel
          · exact hqKernel z hz
        · rw [List.map_cons, FaceSimple, List.pairwise_cons]
          refine ⟨?_, hqSimple⟩
          intro z hz hzFace
          apply hx₁Band
          exact FaceBand.of_mem (G := H) hz
            (PermReachable.symm H.face hzFace)
        · simp only [List.length_cons] at hqLength ⊢
          omega

/-- Coq's outer `IHf5` exclusion inside `embed_full`.  If a kernel path of
at most five links has the mapped edge relation required to close its image,
then its endpoint is its start.  Loop erasure packages any contrary path as
a nonclosing pre-hom ring with tail length at most four. -/
theorem shortKernelPath_returns
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x₀ : G.Dart} {p : List G.Dart}
    (hpath : G.RLinkPath x₀ p)
    (hkernel : ∀ z : G.Dart, z ∈ p → G.Kernel r z)
    (hedgeImage :
      H.edge (h ((x₀ :: p).getLastD x₀)) = h (G.edge x₀))
    (hbound : p.length ≤ 5) :
    (x₀ :: p).getLastD x₀ = x₀ := by
  classical
  by_contra hreturn
  rcases hG.mappedFaceSimpleSubpath hH hembed hpath hkernel hbound with
    ⟨q, hqPath, hqLast, hqKernel, hqSimple, hqLength⟩
  cases q with
  | nil =>
      apply hreturn
      simpa [List.getLastD] using hqLast.symm
  | cons x qs =>
      let y : G.Dart := (x :: qs).getLastD x
      have hqPathParts : G.RLink x₀ x ∧ G.RLinkPath x qs := by
        simpa [RLinkPath] using hqPath
      have hxKernel : G.Kernel r x := hqKernel x (by simp)
      have hedgeX₀Kernel : G.Kernel r (G.edge x₀) :=
        G.kernel_faceClosed r hxKernel
          (PermReachable.symm G.face hqPathParts.1)
      have hlastEq : y = (x₀ :: p).getLastD x₀ := by
        simpa [y, List.getLastD] using hqLast
      have hedgeImage' : H.edge (h y) = h (G.edge x₀) := by
        rw [hlastEq]
        exact hedgeImage
      have hmapFirst :
          PermReachable H.face (h (G.edge x₀)) (h x) :=
        hembed.faceReachable_map (G.kernel_faceClosed r)
          hedgeX₀Kernel hqPathParts.1
      have htargetClose : H.RLink (h y) (h x) := by
        unfold RLink
        rw [hedgeImage']
        exact hmapFirst
      have hpre : PreHomRing r h x qs :=
        hG.introPreHomRing hH hembed hqPathParts.2
          (by simpa [y, List.getLastD] using htargetClose)
          (by
            intro z hz
            exact hqKernel z (by simpa using hz))
          (by simpa using hqSimple)
      have hopen : ¬ G.RLink y x := by
        intro hyx
        have hyMem : y ∈ x :: qs := by
          dsimp [y, List.getLastD]
          exact List.getLast_mem (List.cons_ne_nil x qs)
        have hyKernel : G.Kernel r y := hqKernel y hyMem
        have hedgeYKernel : G.Kernel r (G.edge y) :=
          G.kernel_faceClosed r hxKernel
            (PermReachable.symm G.face hyx)
        have hedgeYMap : h (G.edge y) = H.edge (h y) :=
          hG.embedFunctor hH hembed hyKernel hedgeYKernel
        have hedgeReach :
            PermReachable G.face (G.edge y) (G.edge x₀) :=
          PermReachable.trans G.face hyx
            (PermReachable.symm G.face hqPathParts.1)
        have hedgeEq : G.edge y = G.edge x₀ :=
          hembed.injective_of_faceReachable
            (G.kernel_faceClosed r) hedgeYKernel hedgeReach (by
              rw [hedgeYMap, hedgeImage'])
        have hyEq : y = x₀ := G.edge.injective hedgeEq
        apply hreturn
        calc
          (x₀ :: p).getLastD x₀ = y := hlastEq.symm
          _ = x₀ := hyEq
      have hshort : qs.length ≤ 4 := by
        simp only [List.length_cons] at hqLength
        omega
      have hclose : G.RLink y x := by
        simpa [y, List.getLastD] using
          (hG.shortPreHomRing_closes hH hembed hpre hshort)
      exact hopen hclose

/-- Coq `embed_full`: edge reflection throughout the configuration kernel.
The radius-two center joins two kernel darts by a fixed five-link path.  A
target edge equality gives that path the mapped closing-edge relation, so
`shortKernelPath_returns` forces its last endpoint to be its start. -/
theorem embedFull
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x₁ x₂ : G.Dart}
    (hx₁Kernel : G.Kernel r x₁)
    (hx₂Kernel : G.Kernel r x₂)
    (hedgeImage : H.edge (h x₁) = h x₂) :
    G.edge x₁ = x₂ := by
  rcases hG.kernelRadiusTwo with ⟨x₀, hx₀Kernel, hradius⟩
  rcases hradius x₁ hx₁Kernel with
    ⟨x₀₁, x₁₀, hx₀x₀₁, hx₁x₁₀,
      hedgeX₀₁Kernel, hedgeX₀₁X₁₀⟩
  rcases hradius x₂ hx₂Kernel with
    ⟨x₀₂, x₂₀, hx₀x₀₂, hx₂x₂₀,
      hedgeX₀₂Kernel, hedgeX₀₂X₂₀⟩
  let p : List G.Dart :=
    [x₁₀, G.edge x₀₁, x₀₂, G.edge x₂₀, x₂]
  have hpath : G.RLinkPath (G.edge x₁) p := by
    dsimp [p]
    simp only [RLinkPath]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold RLink
      rw [Hypermap.Plain.edge_edge (G := G) hG.plain]
      exact hx₁x₁₀
    · unfold RLink
      exact PermReachable.symm G.face hedgeX₀₁X₁₀
    · unfold RLink
      rw [Hypermap.Plain.edge_edge (G := G) hG.plain]
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hx₀x₀₁) hx₀x₀₂
    · unfold RLink
      exact hedgeX₀₂X₂₀
    · unfold RLink
      change PermReachable G.face (G.edge (G.edge x₂₀)) x₂ ∧ True
      rw [Hypermap.Plain.edge_edge (G := G) hG.plain]
      exact ⟨PermReachable.symm G.face hx₂x₂₀, trivial⟩
  have hpKernel : ∀ z : G.Dart, z ∈ p → G.Kernel r z := by
    intro z hz
    dsimp [p] at hz
    simp at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact G.kernel_faceClosed r hx₁Kernel hx₁x₁₀
    · exact hedgeX₀₁Kernel
    · exact G.kernel_faceClosed r hx₀Kernel hx₀x₀₂
    · exact G.kernel_faceClosed r hedgeX₀₂Kernel
        hedgeX₀₂X₂₀
    · exact hx₂Kernel
  have hedgeClosing :
      H.edge (h x₂) = h (G.edge (G.edge x₁)) := by
    calc
      H.edge (h x₂) = H.edge (H.edge (h x₁)) := by rw [hedgeImage]
      _ = h x₁ := Hypermap.Plain.edge_edge (G := H) hH.plain _
      _ = h (G.edge (G.edge x₁)) := by
        rw [Hypermap.Plain.edge_edge (G := G) hG.plain]
  have hreturn := hG.shortKernelPath_returns hH hembed hpath hpKernel
    (by simpa [p, List.getLastD] using hedgeClosing) (by simp [p])
  have hx₂Eq : x₂ = G.edge x₁ := by
    simpa [p, List.getLastD] using hreturn
  exact hx₂Eq.symm

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
