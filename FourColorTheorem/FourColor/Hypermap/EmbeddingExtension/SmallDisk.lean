import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PerimeterInterior

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- The finite intersection counted by Coq
`predI (cface x) [preim edge of fband rc]`. -/
noncomputable def adjacentBandDarts
    (G : Hypermap.{u}) (r : List G.Dart) (x : G.Dart) : Finset G.Dart := by
  classical
  exact (G.faceOrbitFinset x).filter
    (fun z : G.Dart => G.FaceBand r (G.edge z))

@[simp]
theorem mem_adjacentBandDarts
    {x z : G.Dart} :
    z ∈ adjacentBandDarts G r x ↔
      PermReachable G.face x z ∧ G.FaceBand r (G.edge z) := by
  classical
  simp [adjacentBandDarts]

/-- The finite intersection counted by Coq
`predI (cface x) [preim edge of ac]`. -/
noncomputable def adjacentKernelDarts
    (G : Hypermap.{u}) (r : List G.Dart) (x : G.Dart) : Finset G.Dart := by
  classical
  exact (G.faceOrbitFinset x).filter
    (fun z : G.Dart => G.Kernel r (G.edge z))

@[simp]
theorem mem_adjacentKernelDarts
    {x z : G.Dart} :
    z ∈ adjacentKernelDarts G r x ↔
      PermReachable G.face x z ∧ G.Kernel r (G.edge z) := by
  classical
  simp [adjacentKernelDarts]

theorem card_faceOrbitFinset (x : G.Dart) :
    (G.faceOrbitFinset x).card = G.arity x := by
  classical
  let e : {y : G.Dart // y ∈ G.faceOrbitFinset x} ≃ G.FaceClass x :=
    Equiv.subtypeEquivRight (fun y => mem_faceOrbitFinset (G := G))
  calc
    (G.faceOrbitFinset x).card =
        Fintype.card {y : G.Dart // y ∈ G.faceOrbitFinset x} := by
          exact (Fintype.card_coe _).symm
    _ = Fintype.card (G.FaceClass x) := Fintype.card_congr e
    _ = G.arity x := by
      simp [Hypermap.arity, Nat.card_eq_fintype_card]

/-- Coq `fcard_adj_perimeter`: exactly two darts of a perimeter-band face
have their opposite dart in the perimeter face band. -/
theorem fcardAdjPerimeter
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} (hxNotKernel : ¬ G.Kernel r x) :
    (adjacentBandDarts G r x).card = 2 := by
  classical
  have hxBand : G.FaceBand r x := Classical.not_not.mp hxNotKernel
  rcases hxBand with ⟨y, hyR, hyx⟩
  let w : G.Dart := G.edge (G.node y)
  have hnyR : G.node y ∈ r := hG.cycle.image_mem hyR
  have hyOrbit : y ∈ G.faceOrbitFinset x := by
    rw [mem_faceOrbitFinset]
    exact PermReachable.symm G.face hyx
  have hedgeYBand : G.FaceBand r (G.edge y) := by
    have hnodeSymmY : G.node.symm y ∈ r := by
      apply (FunctionCycle.image_mem_iff hG.cycle G.node.injective
        (G.node.symm y)).mp
      simpa using hyR
    refine ⟨G.node.symm y, hnodeSymmY, ?_⟩
    exact PermReachable.symm G.face
      (by simpa [face_edge_eq_node_symm (G := G) y] using
        PermReachable.forward G.face (G.edge y))
  have hwOrbit : w ∈ G.faceOrbitFinset x := by
    rw [mem_faceOrbitFinset]
    have hyw : PermReachable G.face y w :=
      PermReachable.symm G.face
        (by simpa [w] using PermReachable.forward G.face w)
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hyx) hyw
  have hedgeWBand : G.FaceBand r (G.edge w) := by
    have hedgeW : G.edge w = G.node y := by
      simp [w, Hypermap.Plain.edge_edge (G := G) hG.plain]
    rw [hedgeW]
    exact FaceBand.of_mem (G := G) hnyR
      (PermReachable.refl G.face (G.node y))
  have hwNeY : w ≠ y := by
    intro hwy
    rcases hG.edgePerimeter (G.node y) with hnodeOff | hedgeNodeOff
    · exact hnodeOff hnyR
    · exact hedgeNodeOff (by simpa [w, hwy] using hyR)
  have hset : adjacentBandDarts G r x = {y, w} := by
    ext z
    rw [mem_adjacentBandDarts]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxz, hedgeZBand⟩
      by_cases hzy : z = y
      · exact Or.inl hzy
      by_cases hzw : z = w
      · exact Or.inr hzw
      have hyz : PermReachable G.face y z :=
        PermReachable.trans G.face hyx hxz
      have hzOff : z ∉ r := by
        intro hzR
        have hyEqZ := FaceSimple.eq_of_faceReachable_of_mem
          (G := G) hG.faceSimple hyR hzR hyz
        exact hzy hyEqZ.symm
      have hedgeZOff : G.edge z ∉ r := by
        intro hedgeZR
        have hq := hG.edgePerimeterSimpleRLinkCycle (by
          intro hr
          simp [hr] at hyR)
        have hzQ : z ∈ G.RevRing r.reverse :=
          (hG.mem_edgePerimeter_iff z).2 hedgeZR
        have hwQ : w ∈ G.RevRing r.reverse := by
          apply (hG.mem_edgePerimeter_iff w).2
          simpa [w, Hypermap.Plain.edge_edge (G := G) hG.plain] using hnyR
        have hwy : PermReachable G.face w y := by
          simpa [w] using PermReachable.forward G.face w
        have hwz : PermReachable G.face w z :=
          PermReachable.trans G.face hwy hyz
        have hwEqZ := FaceSimple.eq_of_faceReachable_of_mem
          (G := G) hq.faceSimple hwQ hzQ hwz
        exact hzw hwEqZ.symm
      rcases hG.chordlessPerimeter hembed hzOff hedgeZOff with
        hzKernel | hedgeZKernel
      · exact False.elim (hzKernel
          (FaceBand.of_mem (G := G) hyR hyz))
      · exact False.elim (hedgeZKernel hedgeZBand)
    · rintro (rfl | rfl)
      · exact ⟨(mem_faceOrbitFinset (G := G)).mp hyOrbit, hedgeYBand⟩
      · exact ⟨(mem_faceOrbitFinset (G := G)).mp hwOrbit, hedgeWBand⟩
  rw [hset]
  have hyNeW : y ≠ w := fun h => hwNeY h.symm
  rw [Finset.card_insert_of_notMem (by simp [hyNeW])]
  simp

/-- Coq `adj_kernel_min`: every perimeter-band face has an edge-adjacent
kernel face. -/
theorem adjKernelMin
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} (hxNotKernel : ¬ G.Kernel r x) :
    ∃ y : G.Dart,
      G.Kernel r y ∧ PermReachable G.face x (G.edge y) := by
  classical
  have hxBand : G.FaceBand r x := Classical.not_not.mp hxNotKernel
  rcases hxBand with ⟨a, haR, hax⟩
  have harityGe : 3 ≤ G.arity x := by
    have harityEq : G.arity a = G.arity x :=
      G.arity_eq_of_faceReachable hax
    rw [← harityEq]
    exact (hG.ringArity haR).bounds.1
  have hbandCard : (adjacentBandDarts G r x).card = 2 :=
    hG.fcardAdjPerimeter hembed hxNotKernel
  have horbitCard : (G.faceOrbitFinset x).card = G.arity x :=
    card_faceOrbitFinset (G := G) x
  have hlt :
      (adjacentBandDarts G r x).card < (G.faceOrbitFinset x).card := by
    omega
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with
    ⟨z, hzOrbit, hzNotBand⟩
  have hedgeZKernel : G.Kernel r (G.edge z) := by
    intro hedgeZBand
    exact hzNotBand ((mem_adjacentBandDarts (G := G) (r := r)).2
      ⟨(mem_faceOrbitFinset (G := G)).1 hzOrbit, hedgeZBand⟩)
  refine ⟨G.edge z, ?_, ?_⟩
  · simpa [Hypermap.Plain.edge_edge (G := G) hG.plain z] using hedgeZKernel
  · simpa [Hypermap.Plain.edge_edge (G := G) hG.plain z] using
      (mem_faceOrbitFinset (G := G)).1 hzOrbit

/-- Coq `adj_kernel_max`: a perimeter-band face has at most four darts whose
opposite dart lies in the kernel. -/
theorem adjKernelMax
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} (hxNotKernel : ¬ G.Kernel r x) :
    (adjacentKernelDarts G r x).card ≤ 4 := by
  classical
  have hxBand : G.FaceBand r x := Classical.not_not.mp hxNotKernel
  rcases hxBand with ⟨a, haR, hax⟩
  have harityLe : G.arity x ≤ 6 := by
    have harityEq : G.arity a = G.arity x :=
      G.arity_eq_of_faceReachable hax
    rw [← harityEq]
    exact (hG.ringArity haR).bounds.2
  have hbandCard : (adjacentBandDarts G r x).card = 2 :=
    hG.fcardAdjPerimeter hembed hxNotKernel
  have horbitCard : (G.faceOrbitFinset x).card = G.arity x :=
    card_faceOrbitFinset (G := G) x
  have hsum :
      (adjacentBandDarts G r x).card +
          (adjacentKernelDarts G r x).card =
        (G.faceOrbitFinset x).card := by
    simpa [adjacentBandDarts, adjacentKernelDarts, Kernel] using
      (Finset.card_filter_add_card_filter_not
        (s := G.faceOrbitFinset x)
        (p := fun z : G.Dart => G.FaceBand r (G.edge z)))
  omega

/-- Face-simple lists meet one face orbit per entry, so inclusion of their
face bands bounds their lengths.  This is the finite-list form of Coq's
`subset_leq_card` on `fcard face`. -/
private theorem faceSimple_length_le_of_faceBand_subset
    {s t : List G.Dart}
    (hs : G.FaceSimple s) (ht : G.FaceSimple t)
    (hsub : ∀ u : G.Dart, G.FaceBand s u → G.FaceBand t u) :
    s.length ≤ t.length := by
  classical
  let f : G.Dart → G.FaceOrbit := PermOrbit.of G.face
  have hsNodup : (s.map f).Nodup :=
    (faceSimple_iff_nodup_faceOrbit_map G).mp hs
  have htNodup : (t.map f).Nodup :=
    (faceSimple_iff_nodup_faceOrbit_map G).mp ht
  have hfinset : (s.map f).toFinset ⊆ (t.map f).toFinset := by
    intro o ho
    rw [List.mem_toFinset] at ho ⊢
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    rw [← faceBand_iff_mem_faceOrbit_map]
    exact hsub u (FaceBand.of_mem (G := G) hu
      (PermReachable.refl G.face u))
  have hcard := Finset.card_le_card hfinset
  calc
    s.length = (s.map f).toFinset.card :=
      by simpa using (List.toFinset_card_of_nodup hsNodup).symm
    _ ≤ (t.map f).toFinset.card := hcard
    _ = t.length := by
      simpa using List.toFinset_card_of_nodup htNodup

/-- Equal-length face-simple lists and a one-way face-band inclusion meet
exactly the same face orbits. -/
private theorem faceBand_iff_of_faceSimple_subset_length_eq
    {s t : List G.Dart}
    (hs : G.FaceSimple s) (ht : G.FaceSimple t)
    (hsub : ∀ u : G.Dart, G.FaceBand s u → G.FaceBand t u)
    (hlen : s.length = t.length) (u : G.Dart) :
    G.FaceBand s u ↔ G.FaceBand t u := by
  classical
  let f : G.Dart → G.FaceOrbit := PermOrbit.of G.face
  have hsNodup : (s.map f).Nodup :=
    (faceSimple_iff_nodup_faceOrbit_map G).mp hs
  have htNodup : (t.map f).Nodup :=
    (faceSimple_iff_nodup_faceOrbit_map G).mp ht
  have hfinsetSub : (s.map f).toFinset ⊆ (t.map f).toFinset := by
    intro o ho
    rw [List.mem_toFinset] at ho ⊢
    rcases List.mem_map.mp ho with ⟨v, hv, rfl⟩
    rw [← faceBand_iff_mem_faceOrbit_map]
    exact hsub v (FaceBand.of_mem (G := G) hv
      (PermReachable.refl G.face v))
  have hcardReverse :
      (t.map f).toFinset.card ≤ (s.map f).toFinset.card := by
    rw [List.toFinset_card_of_nodup htNodup,
      List.toFinset_card_of_nodup hsNodup]
    simpa using hlen.ge
  have hfinsetEq : (s.map f).toFinset = (t.map f).toFinset :=
    Finset.eq_of_subset_of_card_le hfinsetSub hcardReverse
  rw [faceBand_iff_mem_faceOrbit_map, faceBand_iff_mem_faceOrbit_map]
  simpa only [List.mem_toFinset] using
    Finset.ext_iff.mp hfinsetEq (PermOrbit.of G.face u)

/-- One source `rlink` step whose image is the spoke successor step carries
the two source node darts into the same face orbit. -/
private theorem mappedSpokeStep_node_faceReachable
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart}
    (hxy : G.RLink x y)
    (hxKernel : G.Kernel r x) (hyKernel : G.Kernel r y)
    (hmap : H.face (H.face (H.edge (h x))) = h y) :
    PermReachable G.face (G.node x) (G.node y) := by
  have hedgeKernel : G.Kernel r (G.edge x) :=
    G.kernel_faceClosed r hyKernel (PermReachable.symm G.face hxy)
  have hfaceEdgeKernel : G.Kernel r (G.face (G.edge x)) :=
    G.kernel_faceClosed r hedgeKernel
      (PermReachable.forward G.face (G.edge x))
  have hfaceFaceEdgeKernel :
      G.Kernel r (G.face (G.face (G.edge x))) :=
    G.kernel_faceClosed r hfaceEdgeKernel
      (PermReachable.forward G.face (G.face (G.edge x)))
  have hsourceMap :
      h (G.face (G.face (G.edge x))) = h y := by
    calc
      h (G.face (G.face (G.edge x))) =
          H.face (h (G.face (G.edge x))) :=
        hembed.face hfaceEdgeKernel
      _ = H.face (H.face (h (G.edge x))) := by
        rw [hembed.face hedgeKernel]
      _ = H.face (H.face (H.edge (h x))) := by
        rw [hG.embedFunctor hH hembed hxKernel hedgeKernel]
      _ = h y := hmap
  have hyReach :
      PermReachable G.face y (G.face (G.face (G.edge x))) :=
    PermReachable.trans G.face (PermReachable.symm G.face hxy)
      (PermReachable.trans G.face
        (PermReachable.forward G.face (G.edge x))
        (PermReachable.forward G.face (G.face (G.edge x))))
  have hyEq : y = G.face (G.face (G.edge x)) :=
    hembed.injective_of_faceReachable (G.kernel_faceClosed r)
      hyKernel hyReach hsourceMap.symm
  have hperiod : G.node (G.node (G.node x)) = x :=
    (hG.quasicubic x (G.kernel_off_ring hxKernel)).1
  have hnodeEq :
      G.node (G.face (G.face (G.edge x))) =
        G.face.symm (G.node x) := by
    calc
      G.node (G.face (G.face (G.edge x))) =
          G.edge (G.face (G.edge x)) :=
        Hypermap.Plain.node_face_eq_edge (G := G) hG.plain _
      _ = G.edge (G.node (G.node x)) := by
        rw [Hypermap.node_node_eq_face_edge_of_period_three
          (G := G) hperiod]
      _ = G.face.symm (G.node x) :=
        Hypermap.edge_node_eq_face_symm (G := G) (G.node x)
  rw [hyEq, hnodeEq]
  exact PermReachable.backward G.face (G.node x)

/-- Path induction for the node-face containment at the end of Coq
`embed_full`. -/
private theorem mappedSpokePath_nodes_faceReachable
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpath : G.RLinkPath x p)
    (hkernel : ∀ z : G.Dart, z ∈ x :: p → G.Kernel r z)
    (hfun : FunctionPath
      (fun z : H.Dart => H.face (H.face (H.edge z)))
      (h x) (p.map h)) :
    ∀ z : G.Dart, z ∈ (x :: p).map G.node →
      PermReachable G.face (G.node x) z := by
  induction p generalizing x with
  | nil =>
      intro z hz
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hz
      rw [hz]
      exact PermReachable.refl G.face (G.node x)
  | cons y p ih =>
      have hpathParts : G.RLink x y ∧ G.RLinkPath y p := by
        simpa [RLinkPath] using hpath
      have hfunParts :
          H.face (H.face (H.edge (h x))) = h y ∧
            FunctionPath
              (fun z : H.Dart => H.face (H.face (H.edge z)))
              (h y) (p.map h) := by
        simpa [FunctionPath] using hfun
      have hxKernel : G.Kernel r x := hkernel x (by simp)
      have hyKernel : G.Kernel r y := hkernel y (by simp)
      have hnodeXY :
          PermReachable G.face (G.node x) (G.node y) :=
        mappedSpokeStep_node_faceReachable hG hH hembed
          hpathParts.1 hxKernel hyKernel hfunParts.1
      have htailKernel :
          ∀ z : G.Dart, z ∈ y :: p → G.Kernel r z := by
        intro z hz
        exact hkernel z (by simp [hz])
      have htail := ih hpathParts.2 htailKernel hfunParts.2
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact PermReachable.refl G.face (G.node x)
      · exact PermReachable.trans G.face hnodeXY (htail z hz)

/-- Consecutive entries of a simple `rlink` cycle are linked, including the
wraparound entry selected by `List.next`. -/
private theorem SimpleRLinkCycle.rLink_next
    {q : List G.Dart}
    (hq : G.SimpleRLinkCycle q)
    (x : G.Dart) (hx : x ∈ q) :
    G.RLink x (q.next x hx) := by
  have hchain : List.IsChain G.RLink q := by
    cases q with
    | nil => simp at hx
    | cons y p =>
        have path_isChain :
            ∀ {z : G.Dart} {s : List G.Dart},
              G.RLinkPath z s → List.IsChain G.RLink (z :: s) := by
          intro z s hs
          induction s generalizing z with
          | nil => simp
          | cons w s ih =>
              rw [List.isChain_cons]
              refine ⟨?_, ih hs.2⟩
              intro t ht
              have htw : t = w := by simpa using ht.symm
              subst t
              exact hs.1
        exact path_isChain hq.cycle.path
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem q hq.faceSimple.nodup i hi]
  by_cases hsucc : i + 1 < q.length
  · simp only [Nat.mod_eq_of_lt hsucc]
    exact (List.isChain_iff_getElem.mp hchain) i hsucc
  · have hlast : i + 1 = q.length := by omega
    have hmod : (i + 1) % q.length = 0 := by
      rw [hlast, Nat.mod_self]
    simp only [hmod]
    cases q with
    | nil => simp at hi
    | cons y ys =>
        have hi' : i = ys.length := by simpa using hlast
        subst i
        simpa [List.getLastD, List.getLast_eq_getElem,
          List.head_eq_getElem] using hq.cycle.closing

/-- The innermost forbidden-ring assertion in Coq `embed_full`.  A nonclosing
pre-hom ring of length five cannot have at most one target face orbit in its
selected disk; shorter rings reduce to `trivialHomRing`. -/
theorem smallDiskPreHomRing_closes
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hsmall :
      H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤
        if (x :: p).length = 5 then 1 else 0) :
    G.RLink ((x :: p).getLastD x) x := by
  by_contra hopen
  by_cases hlenFive : (x :: p).length = 5
  · have hcountLe :
        H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤ 1 := by
      simpa [hlenFive] using hsmall
    have hcountPos :
        0 < H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) := by
      by_contra hnotPos
      have hzero :
          H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤ 0 := by
        omega
      exact hopen (hG.trivialHomRing hH hembed hpre hzero)
    rcases (H.faceOrbitCountOf_pos_iff_exists).1 hcountPos with
      ⟨u, huDisk⟩
    let q : List H.Dart := (x :: p).map h
    let ru : List H.Dart := Birkhoff.spokeRing H u
    have hqCycle : H.SimpleRLinkCycle q := by
      simpa [q] using hpre.imageCycle
    have hqLen : q.length = 5 := by
      simpa [q] using hlenFive
    have hconnected : H.Connected :=
      Unavoidability.connectedMinimalCounterexamples_proved H hH
    have hcubic : H.Cubic :=
      Unavoidability.cubicMinimalCounterexamples_proved H hH
    have hJordan : H.Jordan :=
      Unavoidability.eulerPlanar_jordan H hH.planar
    have hruCycle : H.SimpleRLinkCycle ru := by
      simpa [ru] using
        Birkhoff.spokeRing_simpleRLinkCycle hH hconnected hcubic u
    have hDiskIff : ∀ v : H.Dart,
        H.DiskF q v ↔ PermReachable H.face u v := by
      intro v
      constructor
      · intro hv
        by_contra huv
        have htwo :
            1 < H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) :=
          (H.one_lt_faceOrbitCountOf_iff_exists_not_faceReachable).2
            ⟨u, huDisk, v, by simpa [q] using hv, huv⟩
        omega
      · intro huv
        simpa [q] using H.diskF_of_faceReachable huv huDisk
    have hbandSub : ∀ v : H.Dart,
        H.FaceBand ru v → H.FaceBand q v := by
      intro v hv
      rcases hv with ⟨z, hzRing, hzv⟩
      have huNodeZ : PermReachable H.face u (H.node z) :=
        (Birkhoff.mem_spokeRing_iff H u z).mp (by simpa [ru] using hzRing)
      have hnodeZDisk : H.DiskF q (H.node z) :=
        (hDiskIff (H.node z)).2 huNodeZ
      have hzDiskN : H.DiskN q z :=
        (H.diskN_node_iff (r := q)).1 hnodeZDisk.1
      have hzNotDiskF : ¬ H.DiskF q z := by
        intro hzDisk
        have huz : PermReachable H.face u z := (hDiskIff z).1 hzDisk
        exact Hypermap.Bridgeless.not_faceReachable_node
          (G := H) hH.bridgeless z
          (PermReachable.trans H.face
            (PermReachable.symm H.face huz) huNodeZ)
      have hzBand : H.FaceBand q z := by
        by_contra hzNotBand
        exact hzNotDiskF ⟨hzDiskN, hzNotBand⟩
      exact FaceBand.of_faceReachable (G := H) hzBand hzv
    have hruLe : ru.length ≤ q.length :=
      faceSimple_length_le_of_faceBand_subset
        hruCycle.faceSimple hqCycle.faceSimple hbandSub
    have hruGe : 5 ≤ ru.length := by
      simpa [ru] using Birkhoff.minArity hH hconnected hcubic u
    have hruLen : ru.length = q.length := by omega
    have hbandIff : ∀ v : H.Dart,
        H.FaceBand ru v ↔ H.FaceBand q v :=
      faceBand_iff_of_faceSimple_subset_length_eq
        hruCycle.faceSimple hqCycle.faceSimple hbandSub hruLen
    have hqProper : H.ProperRing q :=
      H.properRing_of_length_gt_two (by omega)
    have hqSub : ∀ v : H.Dart, v ∈ q → v ∈ ru := by
      intro v hv
      have hvBandQ : H.FaceBand q v :=
        FaceBand.of_mem (G := H) hv
          (PermReachable.refl H.face v)
      have huAdjV : H.RingAdj u v :=
        (Birkhoff.faceBand_spokeRing_iff_ringAdj u v).1
          ((hbandIff v).2 hvBandQ)
      have hnextMem : q.next v hv ∈ q := List.next_mem q v hv
      have hnextLink : H.RLink v (q.next v hv) :=
        SimpleRLinkCycle.rLink_next (G := H) hqCycle v hv
      have hedgeVBandQ : H.FaceBand q (H.edge v) :=
        FaceBand.of_mem (G := H) hnextMem
          (PermReachable.symm H.face hnextLink)
      have huAdjEdgeV : H.RingAdj u (H.edge v) :=
        (Birkhoff.faceBand_spokeRing_iff_ringAdj u (H.edge v)).1
          ((hbandIff (H.edge v)).2 hedgeVBandQ)
      rcases Birkhoff.ringAdj_or_edge_mem_spokeRing
          hH hconnected hcubic u v huAdjV huAdjEdgeV with hvRu | hedgeVRu
      · simpa [ru] using hvRu
      · have huNodeEdgeV :
            PermReachable H.face u (H.node (H.edge v)) :=
          (Birkhoff.mem_spokeRing_iff H u (H.edge v)).mp hedgeVRu
        have hnodeEdgeDisk : H.DiskF q (H.node (H.edge v)) :=
          (hDiskIff (H.node (H.edge v))).2 huNodeEdgeV
        have hedgeVDisk : H.DiskN q (H.edge v) :=
          (H.diskN_node_iff (r := q)).1 hnodeEdgeDisk.1
        exact False.elim
          (H.diskN_edge_ring hJordan hH.plain hqCycle hqProper hv
            hedgeVDisk)
    let spokeNext : H.Dart → H.Dart :=
      fun v => H.face (H.face (H.edge v))
    have hqFunctionCycle : FunctionCycle spokeNext q := by
      apply FunctionCycle.of_eq_next hqCycle.faceSimple.nodup
      intro v hv
      have hvRu : v ∈ ru := hqSub v hv
      have hnextQRu : q.next v hv ∈ ru :=
        hqSub (q.next v hv) (List.next_mem q v hv)
      have hnextSpoke : ru.next v hvRu = spokeNext v := by
        simpa [ru, spokeNext, Birkhoff.spoke] using
          Birkhoff.next_spokeRing hH.plain hcubic u v
            (by simpa [ru] using hvRu)
      have hspokeMem : spokeNext v ∈ ru := by
        rw [← hnextSpoke]
        exact List.next_mem ru v hvRu
      have hlink : H.RLink v (q.next v hv) :=
        SimpleRLinkCycle.rLink_next (G := H) hqCycle v hv
      have hreach :
          PermReachable H.face (spokeNext v) (q.next v hv) := by
        exact PermReachable.trans H.face
          (by simpa [spokeNext] using
            PermReachable.backward H.face (H.face (H.face (H.edge v))))
          (PermReachable.trans H.face
            (by simpa using
              PermReachable.backward H.face (H.face (H.edge v))) hlink)
      exact FaceSimple.eq_of_faceReachable_of_mem
        (G := H) hruCycle.faceSimple hspokeMem hnextQRu hreach
    have hfunPath : FunctionPath spokeNext (h x) (p.map h) := by
      have hshape : q = h x :: p.map h := by simp [q]
      rw [hshape] at hqFunctionCycle
      exact hqFunctionCycle.1
    have hnodes : ∀ z : G.Dart, z ∈ (x :: p).map G.node →
        PermReachable G.face (G.node x) z := by
      exact mappedSpokePath_nodes_faceReachable hG hH hembed
        hpre.path hpre.kernel (by simpa [spokeNext] using hfunPath)
    have hnodeXOff : ¬ G.Kernel r (G.node x) := by
      intro hnodeXKernel
      let y := (x :: p).getLastD x
      have hyMem : y ∈ x :: p := by
        dsimp [y, List.getLastD]
        exact List.getLast_mem (List.cons_ne_nil x p)
      have hyKernel : G.Kernel r y := hpre.kernel y hyMem
      have hnodeYReach :
          PermReachable G.face (G.node x) (G.node y) :=
        hnodes (G.node y) (List.mem_map.mpr ⟨y, hyMem, rfl⟩)
      have hnodeYKernel : G.Kernel r (G.node y) :=
        G.kernel_faceClosed r hnodeXKernel hnodeYReach
      have hxKernel : G.Kernel r x := hpre.kernel x (by simp)
      have hedgeNodeXKernel : G.Kernel r (G.edge (G.node x)) := by
        rw [Hypermap.edge_node_eq_face_symm]
        exact G.kernel_faceClosed r hxKernel
          (PermReachable.backward G.face x)
      have hedgeNodeYKernel : G.Kernel r (G.edge (G.node y)) := by
        rw [Hypermap.edge_node_eq_face_symm]
        exact G.kernel_faceClosed r hyKernel
          (PermReachable.backward G.face y)
      have hnodeXMap : h (G.node x) = H.node (h x) :=
        hembed.map_node_of_edgeCentral_node (G.kernel_faceClosed r)
          hxKernel
          (hG.embedFunctor hH hembed hnodeXKernel hedgeNodeXKernel)
      have hnodeYMap : h (G.node y) = H.node (h y) :=
        hembed.map_node_of_edgeCentral_node (G.kernel_faceClosed r)
          hyKernel
          (hG.embedFunctor hH hembed hnodeYKernel hedgeNodeYKernel)
      have hshape : q = h x :: p.map h := by simp [q]
      have hcycleShape : FunctionCycle spokeNext (h x :: p.map h) := by
        simpa [hshape] using hqFunctionCycle
      have hlastMap :
          (h x :: p.map h).getLastD (h x) = h y := by
        simpa [y] using
          (List.getLastD_map (f := h) (l := x :: p) (a := x))
      have hfunClose : spokeNext (h y) = h x := by
        rw [← hlastMap]
        exact hcycleShape.2
      have htargetNode :
          H.node (h y) = H.face (H.node (h x)) := by
        symm
        calc
          H.face (H.node (h x)) =
              H.face (H.node
                (H.face (H.face (H.edge (h y))))) := by
            rw [← hfunClose]
          _ = H.face (H.edge (H.face (H.edge (h y)))) := by
            rw [Hypermap.Plain.node_face_eq_edge (G := H) hH.plain]
          _ = H.face (H.edge (H.node (H.node (h y)))) := by
            rw [Hypermap.Cubic.node_node_eq_face_edge
              (G := H) hcubic (h y)]
          _ = H.face (H.face.symm (H.node (h y))) := by
            rw [Hypermap.edge_node_eq_face_symm]
          _ = H.node (h y) := by simp
      have hfaceNodeXKernel : G.Kernel r (G.face (G.node x)) :=
        G.kernel_faceClosed r hnodeXKernel
          (PermReachable.forward G.face (G.node x))
      have hnodeMapEq : h (G.node y) = h (G.face (G.node x)) := by
        calc
          h (G.node y) = H.node (h y) := hnodeYMap
          _ = H.face (H.node (h x)) := htargetNode
          _ = H.face (h (G.node x)) := by rw [hnodeXMap]
          _ = h (G.face (G.node x)) :=
            (hembed.face hnodeXKernel).symm
      have hnodeYToFaceNodeX :
          PermReachable G.face (G.node y) (G.face (G.node x)) :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hnodeYReach)
          (PermReachable.forward G.face (G.node x))
      have hnodeEq : G.node y = G.face (G.node x) :=
        hembed.injective_of_faceReachable (G.kernel_faceClosed r)
          hnodeYKernel hnodeYToFaceNodeX hnodeMapEq
      have hperiodY : G.node (G.node (G.node y)) = y :=
        (hG.quasicubic y (G.kernel_off_ring hyKernel)).1
      have hfaceEdgeEq : G.face (G.edge y) = G.face.symm x := by
        calc
          G.face (G.edge y) = G.node (G.node y) :=
            (Hypermap.node_node_eq_face_edge_of_period_three
              (G := G) hperiodY).symm
          _ = G.node (G.face (G.node x)) := by rw [hnodeEq]
          _ = G.edge (G.node x) :=
            Hypermap.Plain.node_face_eq_edge (G := G) hG.plain _
          _ = G.face.symm x :=
            Hypermap.edge_node_eq_face_symm (G := G) x
      apply hopen
      unfold RLink
      exact PermReachable.trans G.face
        (PermReachable.forward G.face (G.edge y))
        (by
          rw [hfaceEdgeEq]
          simpa using PermReachable.forward G.face (G.face.symm x))
    have hnodesSub : ∀ z : G.Dart,
        z ∈ (x :: p).map G.node →
          z ∈ adjacentKernelDarts G r (G.node x) := by
      intro z hz
      rw [mem_adjacentKernelDarts]
      constructor
      · exact hnodes z hz
      · rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
        rw [Hypermap.edge_node_eq_face_symm]
        exact G.kernel_faceClosed r (hpre.kernel v hv)
          (PermReachable.backward G.face v)
    have hsourceNodup : (x :: p).Nodup :=
      hpre.imageCycle.faceSimple.nodup.of_map h
    have hnodesNodup : ((x :: p).map G.node).Nodup :=
      hsourceNodup.map G.node.injective
    have hfinsetSub : ((x :: p).map G.node).toFinset ⊆
        adjacentKernelDarts G r (G.node x) := by
      intro z hz
      exact hnodesSub z (List.mem_toFinset.mp hz)
    have hfiveLe : 5 ≤ (adjacentKernelDarts G r (G.node x)).card := by
      have hcard := Finset.card_le_card hfinsetSub
      have hnodesLen : ((x :: p).map G.node).length = 5 := by
        simpa using hlenFive
      calc
        5 = ((x :: p).map G.node).toFinset.card := by
          rw [List.toFinset_card_of_nodup hnodesNodup]
          exact hnodesLen.symm
        _ ≤ (adjacentKernelDarts G r (G.node x)).card := hcard
    have hfour := hG.adjKernelMax hembed hnodeXOff
    omega
  · have hzero :
        H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤ 0 := by
      have hpNotFour : p.length ≠ 4 := by
        intro hp
        apply hlenFive
        simp [hp]
      simpa [hpNotFour] using hsmall
    exact False.elim (hopen (hG.trivialHomRing hH hembed hpre hzero))

/-- Coq's `hp_ok` inside `embed_full`: a nonclosing pre-hom ring has a
proper image ring. -/
theorem PreHomRing.imageProper_of_not_closing
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hopen : ¬ G.RLink ((x :: p).getLastD x) x) :
    H.ProperRing ((x :: p).map h) := by
  cases p with
  | nil =>
      have hself : H.RLink (h x) (h x) := by
        simpa [List.getLastD] using hpre.imageClosing
      exact False.elim
        (Hypermap.Bridgeless.not_ringAdj_self
          (G := H) hH.bridgeless (h x) ⟨h x,
            PermReachable.refl H.face (h x), hself⟩)
  | cons y p =>
      cases p with
      | nil =>
          change ¬ H.EdgePath (h x) [h y] ∨
            2 < (h x :: [h y]).length
          left
          intro hedgePath
          have hedgeMap : H.edge (h x) = h y := hedgePath.1
          have hxy : G.RLink x y := hpre.path.1
          have hxKernel : G.Kernel r x := hpre.kernel x (by simp)
          have hyKernel : G.Kernel r y := hpre.kernel y (by simp)
          have hedgeXKernel : G.Kernel r (G.edge x) :=
            G.kernel_faceClosed r hyKernel
              (PermReachable.symm G.face hxy)
          have hsourceMap : h (G.edge x) = h y := by
            rw [hG.embedFunctor hH hembed hxKernel hedgeXKernel]
            exact hedgeMap
          have hedgeXY :
              PermReachable G.face (G.edge x) y := hxy
          have hedgeEq : G.edge x = y :=
            hembed.injective_of_faceReachable (G.kernel_faceClosed r)
              hedgeXKernel hedgeXY hsourceMap
          have hclose : G.RLink y x := by
            unfold RLink
            rw [← hedgeEq,
              Hypermap.Plain.edge_edge (G := G) hG.plain]
            exact PermReachable.refl G.face x
          exact hopen (by simpa [List.getLastD] using hclose)
      | cons z p =>
          exact H.properRing_of_length_gt_two (by simp)


end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
