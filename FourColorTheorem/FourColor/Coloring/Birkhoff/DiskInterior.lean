import FourColorTheorem.FourColor.Coloring.Birkhoff.SpokeRing

/-! Disk interior and chordlessness of the spoke ring. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- Once a disk contour path for the spoke ring has entered the hub face, it
cannot take another reverse-node step: that step would land on the ring. -/
private theorem spokeRing_dPath_endpoint_faceReachable
    {G : Hypermap.{u}}
    (x : G.Dart)
    {a : G.Dart} {p : List G.Dart}
    (hxa : PermReachable G.face x a)
    (hp : G.DPath (spokeRing G x) a p)
    (hout : ¬ G.FaceBand (spokeRing G x) ((a :: p).getLastD a)) :
    PermReachable G.face x ((a :: p).getLastD a) := by
  induction p generalizing a with
  | nil =>
      simpa [List.getLastD] using hxa
  | cons b p ih =>
      have hab : G.DLink (spokeRing G x) a b := hp.1
      rcases hab.2 with hnode | hface
      · subst b
        have hbmem : G.node.symm a ∈ spokeRing G x :=
          (mem_spokeRing_iff G x (G.node.symm a)).2 (by simpa using hxa)
        cases p with
        | nil =>
            exact False.elim (hout
              (Hypermap.FaceBand.of_mem (G := G) hbmem
                (PermReachable.refl G.face (G.node.symm a))))
        | cons c p =>
            exact False.elim (hp.2.1.1 hbmem)
      · subst b
        apply ih
        · exact PermReachable.trans G.face hxa
            (PermReachable.forward G.face a)
        · exact hp.2
        · simpa [List.getLastD] using hout

/-- Coq `birkhoff.v::diskF_spoke_ring`: the strict inside of the spoke ring
is exactly the face orbit of its hub. -/
theorem diskF_spokeRing_iff
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hcubic : G.Cubic)
    (x y : G.Dart) :
    G.DiskF (spokeRing G x) y ↔ PermReachable G.face x y := by
  constructor
  · rintro ⟨hyDisk, hyBand⟩
    rcases hyDisk with ⟨z, hzmem, hzy⟩
    rcases Hypermap.DConnect.exists_dPath (G := G) hzy with
      ⟨p, hp, hlast⟩
    let z0 := G.node.symm z
    have hcycle := spokeRing_functionCycle hG.plain hcubic x
    have hnextEq := hcycle.eq_next (spokeRing_nodup G x) z hzmem
    have hfaceZ0Mem : G.face z0 ∈ spokeRing G x := by
      have hnextMem : G.face (spoke G z) ∈ spokeRing G x := by
        rw [hnextEq]
        exact List.next_mem (spokeRing G x) z hzmem
      simpa [z0, spoke, Hypermap.face_edge_eq_node_symm] using hnextMem
    cases p with
    | nil =>
        apply False.elim
        apply hyBand
        refine Hypermap.FaceBand.of_mem (G := G) hfaceZ0Mem ?_
        have hz0y : z0 = y := by
          simpa [z0, List.getLastD] using hlast
        rw [← hz0y]
        simpa using PermReachable.backward G.face (G.face z0)
    | cons z1 q =>
        have hz0z1 : G.DLink (spokeRing G x) z0 z1 := hp.1
        rcases hz0z1.2 with hnode | hface
        · subst z1
          have hnodeNode : G.node.symm z0 = G.node z := by
            apply G.node.injective
            simpa [z0] using
              Hypermap.Cubic.node_symm_eq_node_node (G := G) hcubic z
          have hxStart : PermReachable G.face x (G.node.symm z0) := by
            rw [hnodeNode]
            exact (mem_spokeRing_iff G x z).mp hzmem
          have hlast' :
              ((G.node.symm z0 :: q).getLastD (G.node.symm z0)) = y := by
            simpa [List.getLastD] using hlast
          have hout' : ¬ G.FaceBand (spokeRing G x)
              ((G.node.symm z0 :: q).getLastD (G.node.symm z0)) := by
            rw [hlast']
            exact hyBand
          have hreach := spokeRing_dPath_endpoint_faceReachable
            x hxStart hp.2 hout'
          rw [hlast'] at hreach
          exact hreach
        · subst z1
          cases q with
          | nil =>
              apply False.elim
              apply hyBand
              refine Hypermap.FaceBand.of_mem (G := G) hfaceZ0Mem ?_
              have hfaceY : G.face z0 = y := by
                simpa [z0, List.getLastD] using hlast
              rw [← hfaceY]
              exact PermReachable.refl G.face (G.face z0)
          | cons z2 q =>
              exact False.elim (hp.2.1.1 hfaceZ0Mem)
  · intro hxy
    have hzmem : G.node.symm y ∈ spokeRing G x :=
      (mem_spokeRing_iff G x (G.node.symm y)).2 (by simpa using hxy)
    have hyDisk : G.DiskN (spokeRing G x) y := by
      have hzDisk : G.DiskN (spokeRing G x) (G.node.symm y) :=
        G.diskN_of_mem hzmem
      simpa using
        (G.diskN_node_iff (r := spokeRing G x)).2 hzDisk
    refine ⟨hyDisk, ?_⟩
    rintro ⟨z, hzmem, hzy⟩
    have hxNodeZ : PermReachable G.face x (G.node z) :=
      (mem_spokeRing_iff G x z).mp hzmem
    have hxz : PermReachable G.face x z :=
      PermReachable.trans G.face hxy
        (PermReachable.symm G.face hzy)
    exact Hypermap.Bridgeless.not_faceReachable_node
      (G := G) hG.bridgeless z
      (PermReachable.trans G.face
        (PermReachable.symm G.face hxz) hxNodeZ)

/-- Coq `birkhoff.v::chordless_spoke_ring`: every adjacency between spoke
faces joins cyclic neighbours. -/
theorem chordless_spokeRing
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (x : G.Dart) :
    G.Chordless (spokeRing G x) := by
  have hrSimple := spokeRing_simpleRLinkCycle hG hconnected hcubic x
  intro y1 hy1 y2 hy2 hadj
  by_contra hneighbors
  have hnotPrev : y2 ≠ (spokeRing G x).prev y1 hy1 :=
    fun h => hneighbors (Or.inl h)
  have hnotNext : y2 ≠ (spokeRing G x).next y1 hy1 :=
    fun h => hneighbors (Or.inr h)
  have hy1y2 : y1 ≠ y2 := by
    intro h
    subst y2
    exact Hypermap.Bridgeless.not_ringAdj_self
      (G := G) hG.bridgeless y1 hadj
  rcases hadj with ⟨z, hy1z, hedgeZY2⟩
  have hxNodeY1 : PermReachable G.face x (G.node y1) :=
    (mem_spokeRing_iff G x y1).mp hy1
  have hxNodeY2 : PermReachable G.face x (G.node y2) :=
    (mem_spokeRing_iff G x y2).mp hy2
  have hcY1 :
      PermReachable G.face (G.edge (G.node y1)) y1 := by
    rw [Hypermap.edge_node_eq_face_symm]
    simpa using PermReachable.forward G.face (G.face.symm y1)
  have hab : G.RLink (G.node y2) (G.edge z) := by
    unfold Hypermap.RLink
    rw [Hypermap.edge_node_eq_face_symm]
    exact PermReachable.trans G.face
      (by simpa using PermReachable.forward G.face (G.face.symm y2))
      (PermReachable.symm G.face hedgeZY2)
  have hbc : G.RLink (G.edge z) (G.edge (G.node y1)) := by
    unfold Hypermap.RLink
    rw [Hypermap.Plain.edge_edge (G := G) hG.plain z]
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hy1z)
      (by
        rw [Hypermap.edge_node_eq_face_symm]
        exact PermReachable.backward G.face y1)
  have hca : G.RLink (G.edge (G.node y1)) (G.node y2) := by
    unfold Hypermap.RLink
    rw [Hypermap.Plain.edge_edge (G := G) hG.plain (G.node y1)]
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hxNodeY1) hxNodeY2
  have hfaceAB : ¬ PermReachable G.face (G.node y2) (G.edge z) := by
    intro h
    exact Hypermap.Bridgeless.not_faceReachable_node_left
      (G := G) hG.bridgeless y2
      (PermReachable.trans G.face h hedgeZY2)
  have hfaceAC :
      ¬ PermReachable G.face (G.node y2) (G.edge (G.node y1)) := by
    intro h
    have hxY1 : PermReachable G.face x y1 :=
      PermReachable.trans G.face hxNodeY2
        (PermReachable.trans G.face h hcY1)
    exact Hypermap.Bridgeless.not_faceReachable_node
      (G := G) hG.bridgeless y1
      (PermReachable.trans G.face
        (PermReachable.symm G.face hxY1) hxNodeY1)
  have hfaceBC :
      ¬ PermReachable G.face (G.edge z) (G.edge (G.node y1)) := by
    intro h
    have hy2y1 : PermReachable G.face y2 y1 :=
      PermReachable.trans G.face
        (PermReachable.symm G.face hedgeZY2)
        (PermReachable.trans G.face h hcY1)
    have heq := Hypermap.FaceSimple.eq_of_faceReachable_of_mem
      (G := G) hrSimple.2
      hy2 hy1 hy2y1
    exact hy1y2 heq.symm
  let q : List G.Dart :=
    [G.node y2, G.edge z, G.edge (G.node y1)]
  have hq : G.SimpleRLinkCycle q := by
    constructor
    · exact ⟨⟨hab, ⟨hbc, by simp⟩⟩, hca⟩
    · simp [q, Hypermap.FaceSimple, hfaceAB, hfaceAC, hfaceBC]
  let t := G.node (G.edge (G.node y1))
  have htPrev : t = (spokeRing G x).prev y1 hy1 :=
    node_edge_node_eq_prev_spokeRing hG.plain hcubic x y1 hy1
  have htMem : t ∈ spokeRing G x := by
    rw [htPrev]
    exact List.prev_mem (spokeRing G x) y1 hy1
  have htDisk : G.DiskN q t := by
    have hcDisk : G.DiskN q (G.edge (G.node y1)) :=
      G.diskN_of_mem (by simp [q])
    simpa [t] using (G.diskN_node_iff (r := q)).2 hcDisk
  have htBand : ¬ G.FaceBand q t := by
    rintro ⟨s, hs, hst⟩
    simp only [q, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs
    · subst s
      have hxNodeT : PermReachable G.face x (G.node t) :=
        (mem_spokeRing_iff G x t).mp htMem
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless t
        (PermReachable.trans G.face
          (PermReachable.symm G.face hst)
          (PermReachable.trans G.face
            (PermReachable.symm G.face hxNodeY2) hxNodeT))
    · subst s
      have hty2 : PermReachable G.face t y2 :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hst) hedgeZY2
      have heq := Hypermap.FaceSimple.eq_of_faceReachable_of_mem
        (G := G) hrSimple.2
        htMem hy2 hty2
      exact hnotPrev (heq.symm.trans htPrev)
    · subst s
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless (G.edge (G.node y1)) (by simpa [t] using hst)
  have hinside : G.DiskF q t := ⟨htDisk, htBand⟩
  let u := G.node (G.node y1)
  have hJordan : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hG.planar
  have hproperQ : G.ProperRing q :=
    Hypermap.properRing_of_length_gt_two (G := G) (by simp [q])
  have huDisk : ¬ G.DiskN q u := by
    intro hu
    have hnodeY1Disk : G.DiskN q (G.node y1) := by
      exact (G.diskN_node_iff (r := q)).1 (by simpa [u] using hu)
    have hnotEdge := G.diskN_edge_ring hJordan hG.plain hq hproperQ
      (x := G.edge (G.node y1)) (by simp [q])
    exact hnotEdge (by
      simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hnodeY1Disk)
  have huBand : ¬ G.FaceBand q u := by
    rintro ⟨s, hs, hsu⟩
    simp only [q, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs
    · subst s
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless (G.node y1)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hxNodeY1)
          (PermReachable.trans G.face hxNodeY2 hsu))
    · subst s
      have hy2u : PermReachable G.face y2 u :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hedgeZY2) hsu
      have hspokeY1 : spoke G y1 = u := by
        simp [spoke, u, Hypermap.face_edge_eq_node_symm,
          Hypermap.Cubic.node_symm_eq_node_node (G := G) hcubic]
      have huNext :
          PermReachable G.face u ((spokeRing G x).next y1 hy1) := by
        rw [next_spokeRing hG.plain hcubic x y1 hy1, hspokeY1]
        exact PermReachable.forward G.face u
      have hy2Next := PermReachable.trans G.face hy2u huNext
      have heq := Hypermap.FaceSimple.eq_of_faceReachable_of_mem
        (G := G) hrSimple.2
        hy2 (List.next_mem (spokeRing G x) y1 hy1) hy2Next
      exact hnotNext heq
    · subst s
      have hy1u : PermReachable G.face y1 u :=
        PermReachable.trans G.face
          (by
            rw [Hypermap.edge_node_eq_face_symm]
            exact PermReachable.backward G.face y1) hsu
      exact Hypermap.Bridgeless.not_faceReachable_node_symm
        (G := G) hG.bridgeless y1 (by
          simpa [u, Hypermap.Cubic.node_symm_eq_node_node
            (G := G) hcubic] using hy1u)
  have houtside : G.DiskFC q u := ⟨huDisk, huBand⟩
  have hnt : G.NontrivialRing 0 q :=
    (Hypermap.nontrivialRing_zero_iff (G := G)).2
      ⟨⟨t, hinside⟩, ⟨u, houtside⟩⟩
  have hnot := Birkhoff hG hconnected hcubic q (by simp [q]) hq
  exact hnot hnt


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
