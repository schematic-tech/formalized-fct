import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.KernelReturn

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `pre_embed_inj`: the preembedding map is globally injective on the
configuration kernel.  A short central spoke from `edge x` toward `y`
reduces equality of images either directly to one source face, or via
`embedFull` after lifting the corresponding target face. -/
theorem preEmbedInj
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart}
    (hxKernel : G.Kernel r x)
    (hyKernel : G.Kernel r y)
    (hxyMap : h x = h y) :
    x = y := by
  have hedgeEdgeXKernel : G.Kernel r (G.edge (G.edge x)) := by
    simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hxKernel
  rcases hembed.simplePath (G.kernel_faceClosed r)
      hedgeEdgeXKernel hyKernel with
    ⟨p, hp, hlastFace, hpNe, _hpSimple, hpAll⟩
  cases p with
  | nil => contradiction
  | cons z₁ p =>
      cases p with
      | nil =>
          have hxz₁ : PermReachable G.face x z₁ := by
            have hlink : G.RLink (G.edge x) z₁ := by
              simpa [RLinkPath] using hp
            unfold RLink at hlink
            simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hlink
          have hz₁y : PermReachable G.face z₁ y := by
            simpa [List.getLastD] using hlastFace
          exact hembed.injective_of_faceReachable
            (G.kernel_faceClosed r) hxKernel
            (PermReachable.trans G.face hxz₁ hz₁y) hxyMap
      | cons z₂ p =>
          have hpathParts :
              G.RLink (G.edge x) z₁ ∧
                G.RLink z₁ z₂ ∧ G.RLinkPath z₂ p := by
            simpa [RLinkPath] using hp
          have hxz₁ : PermReachable G.face x z₁ := by
            unfold RLink at hpathParts
            simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using
              hpathParts.1
          have hz₁Kernel : G.Kernel r z₁ :=
            (hpAll z₁ (by simp)).1
          have hz₁Central : EdgeCentral G H h z₁ :=
            (hpAll z₁ (by simp)).2
          have hz₂Kernel : G.Kernel r z₂ :=
            (hpAll z₂ (by simp)).1
          have hedgeZ₁Kernel : G.Kernel r (G.edge z₁) :=
            G.kernel_faceClosed r hz₂Kernel
              (PermReachable.symm G.face hpathParts.2.1)
          have htargetFace :
              PermReachable H.face (h y) (h z₁) := by
            have hmap := hembed.faceReachable_map
              (G.kernel_faceClosed r) hxKernel hxz₁
            simpa [hxyMap] using hmap
          rcases hembed.faceReachable_lift (G.kernel_faceClosed r)
              hyKernel htargetFace with ⟨t, hyt, htMap⟩
          have htKernel : G.Kernel r t :=
            G.kernel_faceClosed r hyKernel hyt
          have htargetEdge : H.edge (h t) = h (G.edge z₁) := by
            rw [htMap]
            exact hz₁Central.symm
          have hedgeEq : G.edge t = G.edge z₁ :=
            hG.embedFull hH hembed htKernel hedgeZ₁Kernel htargetEdge
          have htEq : t = z₁ := G.edge.injective hedgeEq
          have hxyFace : PermReachable G.face x y :=
            PermReachable.trans G.face hxz₁ (by
              rw [← htEq]
              exact PermReachable.symm G.face hyt)
          exact hembed.injective_of_faceReachable
            (G.kernel_faceClosed r) hxKernel hxyFace hxyMap

/-- Coq `embed_cases`: the four clauses of the total extension cover every
source dart.  The only apparent uncovered boundary pattern would put both
`face x` and `edge (node x)` on the face-simple perimeter, forcing a face
orbit of length at most two and contradicting `GoodRingArity`. -/
theorem kernelExtensionCases
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    (x : G.Dart) :
    (G.Kernel r x ∨ G.Kernel r (G.edge x)) ∨
      G.Kernel r (G.node x) ∨ G.Kernel r (G.node (G.edge x)) := by
  have hnodeMem (z : G.Dart) : G.node z ∈ r ↔ z ∈ r :=
    hG.cycle.image_mem_iff G.node.injective z
  have hoffCases : ∀ z : G.Dart, z ∉ r →
      (G.Kernel r z ∨ G.Kernel r (G.edge z)) ∨
        G.Kernel r (G.node z) := by
    intro z hzOff
    by_cases hedgeMem : G.edge z ∈ r
    · by_cases hedgeNodeMem : G.edge (G.node z) ∈ r
      · have hnodeSymmEdgeMem : G.node.symm (G.edge z) ∈ r := by
          apply (hnodeMem (G.node.symm (G.edge z))).mp
          simpa using hedgeMem
        have hfaceMem : G.face z ∈ r := by
          have hfaceEq : G.face z = G.node.symm (G.edge z) := by
            calc
              G.face z = G.face (G.edge (G.edge z)) := by
                rw [Hypermap.Plain.edge_edge (G := G) hG.plain z]
              _ = G.node.symm (G.edge z) :=
                G.face_edge_eq_node_symm (G.edge z)
          simpa [hfaceEq] using hnodeSymmEdgeMem
        have hfaceReach :
            PermReachable G.face (G.face z) (G.edge (G.node z)) := by
          rw [Hypermap.edge_node_eq_face_symm]
          exact PermReachable.trans G.face
            (by simpa using PermReachable.backward G.face (G.face z))
            (PermReachable.backward G.face z)
        have hfaceEq : G.face z = G.edge (G.node z) :=
          FaceSimple.eq_of_faceReachable_of_mem
            (G := G) hG.faceSimple hfaceMem hedgeNodeMem hfaceReach
        have hperiodTwo : G.face (G.face z) = z := by
          rw [hfaceEq, Hypermap.edge_node_eq_face_symm]
          simp
        have hdiv : G.arity z ∣ 2 := by
          apply G.arity_dvd_of_face_iterate_eq_self
          simpa [Function.iterate_succ_apply'] using hperiodTwo
        have harityLe : G.arity z ≤ 2 := Nat.le_of_dvd (by omega) hdiv
        have harityEq : G.arity (G.face z) = G.arity z :=
          G.arity_eq_of_faceReachable
            (PermReachable.symm G.face
              (PermReachable.forward G.face z))
        have harityGe : 3 ≤ G.arity (G.face z) :=
          (hG.ringArity hfaceMem).bounds.1
        omega
      · have hnodeOff : G.node z ∉ r := by
          intro hnodeOn
          exact hzOff ((hnodeMem z).mp hnodeOn)
        rcases hG.chordlessPerimeter hembed hnodeOff hedgeNodeMem with
          hnodeKernel | hedgeNodeKernel
        · exact Or.inr hnodeKernel
        · left
          left
          apply G.kernel_faceClosed r hedgeNodeKernel
          rw [Hypermap.edge_node_eq_face_symm]
          simpa using PermReachable.forward G.face (G.face.symm z)
    · exact Or.inl
        (hG.chordlessPerimeter hembed hzOff hedgeMem)
  rcases hG.edgePerimeter x with hxOff | hedgeOff
  · rcases hoffCases x hxOff with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hoffCases (G.edge x) hedgeOff with h | h
    · rcases h with hedgeKernel | hedgeEdgeKernel
      · exact Or.inl (Or.inr hedgeKernel)
      · exact Or.inl (Or.inl (by
          simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using
            hedgeEdgeKernel))
    · exact Or.inr (Or.inr h)

/-- Coq `embed`: extend the preembedding from the face-closed kernel to all
darts, choosing the first available kernel representative among `x`,
`edge x`, `node x`, and `node (edge x)`. -/
noncomputable def extendEmbedding
    {H : Hypermap.{u}} (r : List G.Dart) (h : G.Dart → H.Dart)
    (x : G.Dart) : H.Dart := by
  classical
  exact
    if G.Kernel r x then h x
    else if G.Kernel r (G.edge x) then H.edge (h (G.edge x))
    else if G.Kernel r (G.node x) then H.face (H.edge (h (G.node x)))
    else H.edge (H.node (H.node (h (G.node (G.edge x)))))

/-- Coq `embedE`: the total extension commutes with edge reversal. -/
theorem extendEmbedding_edge
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (x : G.Dart) :
    extendEmbedding r h (G.edge x) =
      H.edge (extendEmbedding r h x) := by
  classical
  have hcubic : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have proveOff : ∀ z : G.Dart, z ∉ r →
      extendEmbedding r h (G.edge z) =
        H.edge (extendEmbedding r h z) := by
    intro z hzOff
    by_cases hzKernel : G.Kernel r z
    · by_cases hedgeKernel : G.Kernel r (G.edge z)
      · simp [extendEmbedding, hzKernel, hedgeKernel,
          hG.embedFunctor hH hembed hzKernel hedgeKernel]
      · simp [extendEmbedding, hzKernel, hedgeKernel,
          Hypermap.Plain.edge_edge (G := G) hG.plain]
    · by_cases hedgeKernel : G.Kernel r (G.edge z)
      · simp [extendEmbedding, hzKernel, hedgeKernel,
          Hypermap.Plain.edge_edge (G := H) hH.plain]
      · by_cases hnodeEdgeKernel : G.Kernel r (G.node (G.edge z))
        · have hnodeEdgeOff : G.node (G.edge z) ∉ r :=
            G.kernel_off_ring hnodeEdgeKernel
          have hedgeOff : G.edge z ∉ r := by
            intro hedgeMem
            exact hnodeEdgeOff (hG.cycle.image_mem hedgeMem)
          rcases hG.chordlessPerimeter hembed hzOff hedgeOff with h | h
          · exact False.elim (hzKernel h)
          · exact False.elim (hedgeKernel h)
        · have hnodeKernel : G.Kernel r (G.node z) := by
            rcases hG.kernelExtensionCases hembed z with h | h
            · exact False.elim (h.elim hzKernel hedgeKernel)
            · exact h.resolve_right hnodeEdgeKernel
          simp [extendEmbedding, hzKernel, hedgeKernel, hnodeKernel,
            hnodeEdgeKernel,
            Hypermap.Plain.edge_edge (G := G) hG.plain,
            Hypermap.face_edge_eq_node_symm,
            Hypermap.Cubic.node_symm_eq_node_node hcubic]
  by_cases hxOff : x ∉ r
  · exact proveOff x hxOff
  · have hedgeOff : G.edge x ∉ r :=
      (hG.edgePerimeter x).resolve_left hxOff
    have hEdge := proveOff (G.edge x) hedgeOff
    have h' :
        extendEmbedding r h (G.edge (G.edge x)) =
          H.edge (extendEmbedding r h (G.edge x)) := hEdge
    have h'' := congrArg H.edge h'
    simpa [Hypermap.Plain.edge_edge (G := G) hG.plain,
      Hypermap.Plain.edge_edge (G := H) hH.plain] using h''.symm

/-- Coq `embedN`: off the literal perimeter, the total extension commutes
with the node permutation. -/
theorem extendEmbedding_node
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} (hxOff : x ∉ r) :
    extendEmbedding r h (G.node x) =
      H.node (extendEmbedding r h x) := by
  classical
  have hcubic : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hedgeFaceSymm (a : H.Dart) :
      H.edge (H.face.symm a) = H.node a := by
    have h := congrArg H.edge
      (Hypermap.edge_node_eq_face_symm (G := H) a)
    simpa [Hypermap.Plain.edge_edge (G := H) hH.plain] using h.symm
  have hmapFaceSymm : ∀ {a : G.Dart}, G.Kernel r a →
      h (G.face.symm a) = H.face.symm (h a) := by
    intro a ha
    have hfaceSymmKernel : G.Kernel r (G.face.symm a) :=
      G.kernel_faceClosed r ha (PermReachable.backward G.face a)
    apply H.face.injective
    calc
      H.face (h (G.face.symm a)) =
          h (G.face (G.face.symm a)) :=
        (hembed.face hfaceSymmKernel).symm
      _ = h a := by simp
      _ = H.face (H.face.symm (h a)) := by simp
  by_cases hxKernel : G.Kernel r x
  · have hedgeNodeKernel : G.Kernel r (G.edge (G.node x)) := by
      have hfaceSymmKernel : G.Kernel r (G.face.symm x) :=
        G.kernel_faceClosed r hxKernel
          (PermReachable.backward G.face x)
      simpa [Hypermap.edge_node_eq_face_symm] using hfaceSymmKernel
    by_cases hnodeKernel : G.Kernel r (G.node x)
    · have hnodeMap : h (G.node x) = H.node (h x) := by
        apply H.edge.injective
        calc
          H.edge (h (G.node x)) = h (G.edge (G.node x)) :=
            (hG.embedFunctor hH hembed hnodeKernel hedgeNodeKernel).symm
          _ = h (G.face.symm x) := by
            rw [Hypermap.edge_node_eq_face_symm]
          _ = H.face.symm (h x) := hmapFaceSymm hxKernel
          _ = H.edge (H.node (h x)) :=
            (Hypermap.edge_node_eq_face_symm (G := H) (h x)).symm
      simp [extendEmbedding, hxKernel, hnodeKernel, hnodeMap]
    · have hnodeValue :
          H.edge (h (G.edge (G.node x))) = H.node (h x) := by
        rw [Hypermap.edge_node_eq_face_symm, hmapFaceSymm hxKernel]
        exact hedgeFaceSymm (h x)
      simp [extendEmbedding, hxKernel, hnodeKernel, hedgeNodeKernel,
        hnodeValue]
  · by_cases hedgeKernel : G.Kernel r (G.edge x)
    · have hperiod := (hG.quasicubic x hxOff).1
      have hnodeNodeEq : G.node (G.node x) = G.face (G.edge x) :=
        Hypermap.node_node_eq_face_edge_of_period_three
          (G := G) hperiod
      have hnodeNodeKernel : G.Kernel r (G.node (G.node x)) := by
        rw [hnodeNodeEq]
        exact G.kernel_faceClosed r hedgeKernel
          (PermReachable.forward G.face (G.edge x))
      have hnodeNodeMap :
          h (G.node (G.node x)) = H.face (h (G.edge x)) := by
        rw [hnodeNodeEq]
        exact hembed.face hedgeKernel
      by_cases hnodeKernel : G.Kernel r (G.node x)
      · have hedgeNodeNodeKernel :
            G.Kernel r (G.edge (G.node (G.node x))) := by
          have hfaceSymmKernel : G.Kernel r (G.face.symm (G.node x)) :=
            G.kernel_faceClosed r hnodeKernel
              (PermReachable.backward G.face (G.node x))
          simpa [Hypermap.edge_node_eq_face_symm] using hfaceSymmKernel
        have hfaceEdgeNodeNode :
            G.face (G.edge (G.node (G.node x))) = G.node x := by
          rw [Hypermap.face_edge_eq_node_symm]
          apply G.node.injective
          simp
        have hnodeMap :
            h (G.node x) = H.node (H.edge (h (G.edge x))) := by
          calc
            h (G.node x) =
                h (G.face (G.edge (G.node (G.node x)))) := by
              rw [hfaceEdgeNodeNode]
            _ = H.face (h (G.edge (G.node (G.node x)))) :=
              hembed.face hedgeNodeNodeKernel
            _ = H.face (H.edge (h (G.node (G.node x)))) := by
              rw [hG.embedFunctor hH hembed hnodeNodeKernel
                hedgeNodeNodeKernel]
            _ = H.node.symm (h (G.node (G.node x))) :=
              Hypermap.face_edge_eq_node_symm (G := H) _
            _ = H.node (H.node (h (G.node (G.node x)))) :=
              Hypermap.Cubic.node_symm_eq_node_node hcubic _
            _ = H.node (H.node (H.face (h (G.edge x)))) := by
              rw [hnodeNodeMap]
            _ = H.node (H.edge (h (G.edge x))) := by
              rw [Hypermap.Plain.node_face_eq_edge (G := H) hH.plain]
        simp [extendEmbedding, hxKernel, hedgeKernel, hnodeKernel, hnodeMap]
      · have hedgeNodeNotKernel :
            ¬ G.Kernel r (G.edge (G.node x)) := by
          intro hedgeNodeKernel
          apply hxKernel
          apply G.kernel_faceClosed r hedgeNodeKernel
          rw [Hypermap.edge_node_eq_face_symm]
          simpa using PermReachable.forward G.face (G.face.symm x)
        have hnodeValue :
            H.face (H.edge (h (G.node (G.node x)))) =
              H.node (H.edge (h (G.edge x))) := by
          calc
            H.face (H.edge (h (G.node (G.node x)))) =
                H.node.symm (h (G.node (G.node x))) :=
              Hypermap.face_edge_eq_node_symm (G := H) _
            _ = H.node (H.node (h (G.node (G.node x)))) :=
              Hypermap.Cubic.node_symm_eq_node_node hcubic _
            _ = H.node (H.node (H.face (h (G.edge x)))) := by
              rw [hnodeNodeMap]
            _ = H.node (H.edge (h (G.edge x))) := by
              rw [Hypermap.Plain.node_face_eq_edge (G := H) hH.plain]
        simp [extendEmbedding, hxKernel, hedgeKernel, hnodeKernel,
          hedgeNodeNotKernel, hnodeNodeKernel, hnodeValue]
    · have hnodeKernel : G.Kernel r (G.node x) := by
        rcases hG.kernelExtensionCases hembed x with h | h
        · exact False.elim (h.elim hxKernel hedgeKernel)
        · rcases h with hnodeKernel | hnodeEdgeKernel
          · exact hnodeKernel
          · have hnodeEdgeOff : G.node (G.edge x) ∉ r :=
              G.kernel_off_ring hnodeEdgeKernel
            have hedgeOff : G.edge x ∉ r := by
              intro hedgeMem
              exact hnodeEdgeOff (hG.cycle.image_mem hedgeMem)
            exact False.elim ((hG.chordlessPerimeter hembed hxOff hedgeOff).elim
              hxKernel hedgeKernel)
      simp [extendEmbedding, hxKernel, hedgeKernel, hnodeKernel,
        Hypermap.face_edge_eq_node_symm]

/-- Coq `embed_inj`: the total extension is injective on the complement of
the literal perimeter. -/
theorem extendEmbedding_injective
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart}
    (hxOff : x ∉ r) (hyOff : y ∉ r)
    (hxy : extendEmbedding r h x = extendEmbedding r h y) :
    x = y := by
  classical
  have hnodeMem (z : G.Dart) : G.node z ∈ r ↔ z ∈ r :=
    hG.cycle.image_mem_iff G.node.injective z
  have hnodeOff : ∀ {z : G.Dart}, z ∉ r → G.node z ∉ r := by
    intro z hzOff hnodeOn
    exact hzOff ((hnodeMem z).mp hnodeOn)
  have hnodeKernelOfUncovered : ∀ {z : G.Dart}, z ∉ r →
      ¬ G.Kernel r z → ¬ G.Kernel r (G.edge z) →
        G.Kernel r (G.node z) := by
    intro z hzOff hzNot hedgeNot
    rcases hG.kernelExtensionCases hembed z with h | h
    · exact False.elim (h.elim hzNot hedgeNot)
    · rcases h with hnodeKernel | hnodeEdgeKernel
      · exact hnodeKernel
      · have hnodeEdgeOff : G.node (G.edge z) ∉ r :=
          G.kernel_off_ring hnodeEdgeKernel
        have hedgeOff : G.edge z ∉ r := by
          intro hedgeOn
          exact hnodeEdgeOff (hG.cycle.image_mem hedgeOn)
        exact False.elim ((hG.chordlessPerimeter hembed hzOff hedgeOff).elim
          hzNot hedgeNot)
  have kernelFirst : ∀ {a b : G.Dart}, a ∉ r → b ∉ r →
      G.Kernel r a →
        extendEmbedding r h a = extendEmbedding r h b → a = b := by
    intro a b haOff hbOff haKernel hab
    by_cases hbKernel : G.Kernel r b
    · apply hG.preEmbedInj hH hembed haKernel hbKernel
      simpa [extendEmbedding, haKernel, hbKernel] using hab
    · by_cases hedgeBKernel : G.Kernel r (G.edge b)
      · have htarget : H.edge (h (G.edge b)) = h a := by
          have := hab
          simp [extendEmbedding, haKernel, hbKernel, hedgeBKernel] at this
          exact this.symm
        have hedgeEq : G.edge (G.edge b) = a :=
          hG.embedFull hH hembed hedgeBKernel haKernel htarget
        have hbEq : b = a := by
          simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hedgeEq
        exact hbEq.symm
      · have hnodeBKernel : G.Kernel r (G.node b) :=
          hnodeKernelOfUncovered hbOff hbKernel hedgeBKernel
        have hedgeNodeAKernel : G.Kernel r (G.edge (G.node a)) := by
          have hfaceSymmKernel : G.Kernel r (G.face.symm a) :=
            G.kernel_faceClosed r haKernel
              (PermReachable.backward G.face a)
          simpa [Hypermap.edge_node_eq_face_symm] using hfaceSymmKernel
        have hmapA :
            h a = H.face (h (G.edge (G.node a))) := by
          calc
            h a = h (G.face (G.edge (G.node a))) := by
              rw [Hypermap.edge_node_eq_face_symm]
              simp
            _ = H.face (h (G.edge (G.node a))) :=
              hembed.face hedgeNodeAKernel
        have hab' : h a = H.face (H.edge (h (G.node b))) := by
          simpa [extendEmbedding, haKernel, hbKernel, hedgeBKernel,
            hnodeBKernel] using hab
        have htarget :
            H.edge (h (G.node b)) = h (G.edge (G.node a)) := by
          exact (H.face.injective (hmapA.symm.trans hab')).symm
        have hedgeEq :
            G.edge (G.node b) = G.edge (G.node a) :=
          hG.embedFull hH hembed hnodeBKernel hedgeNodeAKernel htarget
        have hnodeEq : G.node b = G.node a := G.edge.injective hedgeEq
        exact (G.node.injective hnodeEq).symm
  by_cases hxKernel : G.Kernel r x
  · exact kernelFirst hxOff hyOff hxKernel hxy
  · by_cases hyKernel : G.Kernel r y
    · exact (kernelFirst hyOff hxOff hyKernel hxy.symm).symm
    · by_cases hnodeXKernel : G.Kernel r (G.node x)
      · have hnodeEq :
            extendEmbedding r h (G.node x) =
              extendEmbedding r h (G.node y) := by
          rw [hG.extendEmbedding_node hH hembed hxOff,
            hG.extendEmbedding_node hH hembed hyOff, hxy]
        exact G.node.injective
          (kernelFirst (hnodeOff hxOff) (hnodeOff hyOff)
            hnodeXKernel hnodeEq)
      · by_cases hnodeYKernel : G.Kernel r (G.node y)
        · have hnodeEq :
              extendEmbedding r h (G.node y) =
                extendEmbedding r h (G.node x) := by
            rw [hG.extendEmbedding_node hH hembed hyOff,
              hG.extendEmbedding_node hH hembed hxOff, hxy]
          exact (G.node.injective
            (kernelFirst (hnodeOff hyOff) (hnodeOff hxOff)
              hnodeYKernel hnodeEq)).symm
        · have hedgeXKernel : G.Kernel r (G.edge x) := by
            by_contra hedgeXNot
            exact hnodeXKernel
              (hnodeKernelOfUncovered hxOff hxKernel hedgeXNot)
          have hedgeYKernel : G.Kernel r (G.edge y) := by
            by_contra hedgeYNot
            exact hnodeYKernel
              (hnodeKernelOfUncovered hyOff hyKernel hedgeYNot)
          have hedgeEq :
              extendEmbedding r h (G.edge x) =
                extendEmbedding r h (G.edge y) := by
            rw [hG.extendEmbedding_edge hH hembed x,
              hG.extendEmbedding_edge hH hembed y, hxy]
          exact G.edge.injective
            (kernelFirst (G.kernel_off_ring hedgeXKernel)
              (G.kernel_off_ring hedgeYKernel) hedgeXKernel hedgeEq)

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
