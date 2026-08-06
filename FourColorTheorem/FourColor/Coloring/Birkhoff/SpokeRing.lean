import FourColorTheorem.FourColor.Coloring.Birkhoff.CertificateSoundness

/-! Face cycles and the spoke-ring contour around a cubic hub. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- In a bridgeless cubic map, the face of an edge cannot also contain the
next dart at the source node.  This is the orbit contradiction hidden in the
rewrite proof of Coq `birkhoff.v::nontrivial_cycle2`. -/
private theorem not_faceReachable_edge_node_of_cubic
    {G : Hypermap.{u}}
    (hbridgeless : G.Bridgeless) (hcubic : G.Cubic) (x : G.Dart) :
    ¬ PermReachable G.face (G.edge x) (G.node x) := by
  intro hedgeNode
  have hnodeNodeEdge :
      PermReachable G.face (G.node (G.node x)) (G.edge x) := by
    rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hcubic x]
    simpa using PermReachable.backward G.face (G.face (G.edge x))
  have hnodeEdge :
      PermReachable G.face (G.node x)
        (G.edge (G.node (G.node x))) := by
    rw [Hypermap.edge_node_eq_face_symm]
    exact PermReachable.backward G.face (G.node x)
  exact hbridgeless (G.node (G.node x))
    (PermReachable.trans G.face hnodeNodeEdge
      (PermReachable.trans G.face hedgeNode hnodeEdge))

/-- Coq `birkhoff.v::nontrivial_cycle2`: a simple two-dart contour whose
first edge is not its second dart has a strict face on each side. -/
theorem nontrivialCycleTwo
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hcubic : G.Cubic)
    {x y : G.Dart}
    (hr : G.SimpleRLinkCycle [x, y])
    (hedgeXY : G.edge x ≠ y) :
    G.NontrivialRing 0 [x, y] := by
  have hxy : G.RLink x y := hr.1.1.1
  have hinsideBand : ¬ G.FaceBand [x, y] (G.node x) := by
    rintro ⟨z, hz, hzNode⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · subst z
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless x hzNode
    · subst z
      exact not_faceReachable_edge_node_of_cubic hG.bridgeless hcubic x
        (PermReachable.trans G.face hxy hzNode)
  have hinside : G.DiskF [x, y] (G.node x) := by
    refine ⟨(G.diskN_node_iff (r := [x, y])).2 ?_, hinsideBand⟩
    exact G.diskN_of_mem (by simp)
  let nex := G.node (G.edge x)
  have houtsideBand : ¬ G.FaceBand [x, y] nex := by
    rintro ⟨z, hz, hzNex⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · subst z
      apply not_faceReachable_edge_node_of_cubic
        hG.bridgeless hcubic (G.edge x)
      simpa [nex, Hypermap.Plain.edge_edge (G := G) hG.plain x] using hzNex
    · subst z
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless (G.edge x)
        (PermReachable.trans G.face hxy hzNex)
  have houtsideDisk : ¬ G.DiskN [x, y] nex := by
    intro hnex
    have hedgeDisk : G.DiskN [x, y] (G.edge x) :=
      (G.diskN_node_iff (r := [x, y])).1 hnex
    have hedgeNotMem : G.edge x ∉ [x, y] := by
      simp [Hypermap.Plain.edge_ne (G := G) hG.plain x, hedgeXY]
    have hedgeE : G.DiskE [x, y] (G.edge x) :=
      ⟨hedgeDisk, hedgeNotMem⟩
    have hJordan : G.Jordan :=
      Unavoidability.eulerPlanar_jordan G hG.planar
    have hxE : G.DiskE [x, y] x :=
      (G.diskE_edge_iff hJordan hG.plain hr).1 hedgeE
    exact hxE.2 (by simp)
  rw [Hypermap.nontrivialRing_zero_iff]
  exact ⟨⟨G.node x, hinside⟩,
    ⟨nex, houtsideDisk, houtsideBand⟩⟩

/-- Coq `birkhoff.v::double_dart`: in a minimal counterexample, two darts
whose sources and opposite darts respectively lie on common faces coincide. -/
theorem doubleDart
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hedgeXY : PermReachable G.face (G.edge x) (G.edge y)) :
    x = y := by
  by_contra hne
  have hringFace : ¬ PermReachable G.face x (G.edge y) := by
    intro hxEdgeY
    exact hG.bridgeless y
      (PermReachable.trans G.face
        (PermReachable.symm G.face hxy) hxEdgeY)
  have hr : G.SimpleRLinkCycle [x, G.edge y] := by
    constructor
    · refine ⟨⟨hedgeXY, by simp⟩, ?_⟩
      unfold Hypermap.RLink
      simpa [Hypermap.Plain.edge_edge (G := G) hG.plain y] using
        PermReachable.symm G.face hxy
    · simp [Hypermap.FaceSimple, hringFace]
  have hedgeNe : G.edge x ≠ G.edge y := by
    intro h
    exact hne (G.edge.injective h)
  have hnt : G.NontrivialRing 0 [x, G.edge y] :=
    nontrivialCycleTwo hG hcubic hr hedgeNe
  have hnot := Birkhoff hG hconnected hcubic [x, G.edge y]
    (by simp) hr
  exact hnot hnt

/-! ### The spoke ring

This is the first part of Coq `birkhoff.v::SpokeRing`.  Keeping the concrete
face cycle here, rather than choosing an arbitrary orbit enumeration, makes
the reversal and the final arity calculation definitionally visible. -/

/-- The face orbit of `x`, listed once in forward cyclic order. -/
noncomputable def faceCycle (G : Hypermap.{u}) (x : G.Dart) : List G.Dart :=
  (List.range (G.arity x)).map
    (fun n => ((G.face : G.Dart → G.Dart)^[n]) x)

@[simp]
theorem length_faceCycle (G : Hypermap.{u}) (x : G.Dart) :
    (faceCycle G x).length = G.arity x := by
  simp [faceCycle]

theorem faceCycle_nodup (G : Hypermap.{u}) (x : G.Dart) :
    (faceCycle G x).Nodup := by
  unfold faceCycle
  apply List.Nodup.map_on
  · intro i hi j hj hij
    have hi' : i < Function.minimalPeriod
        (G.face : G.Dart → G.Dart) x := by
      simpa [G.arity_eq_minimalPeriod x] using List.mem_range.mp hi
    have hj' : j < Function.minimalPeriod
        (G.face : G.Dart → G.Dart) x := by
      simpa [G.arity_eq_minimalPeriod x] using List.mem_range.mp hj
    exact
      (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (f := (G.face : G.Dart → G.Dart)) (x := x) hi' hj').mp hij
  · exact List.nodup_range

@[simp]
theorem mem_faceCycle_iff
    (G : Hypermap.{u}) (x y : G.Dart) :
    y ∈ faceCycle G x ↔ PermReachable G.face x y := by
  constructor
  · intro hy
    rcases List.mem_map.mp hy with ⟨n, hn, rfl⟩
    exact permReachable_of_iterate_eq G.face rfl
  · intro hxy
    rcases permReachable_exists_iterate_lt_minimalPeriod G.face hxy with
      ⟨n, hn, hiter⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_range.mpr ?_, hiter⟩
    simpa [G.arity_eq_minimalPeriod x] using hn

theorem faceCycle_functionCycle (G : Hypermap.{u}) (x : G.Dart) :
    FunctionCycle G.face (faceCycle G x) := by
  apply FunctionCycle.of_eq_next (faceCycle_nodup G x)
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  rw [List.next_getElem (faceCycle G x) (faceCycle_nodup G x) i hi]
  simp only [faceCycle, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range]
  rw [G.arity_eq_minimalPeriod x,
    Function.iterate_mod_minimalPeriod_eq,
    Function.iterate_succ_apply']

theorem faceCycle_reverse_functionCycle (G : Hypermap.{u}) (x : G.Dart) :
    FunctionCycle G.face.symm (faceCycle G x).reverse := by
  simpa using functionCycle_reverse_of_symm
    (σ := G.face.symm) (faceCycle_functionCycle G x) (faceCycle_nodup G x)

/-- Coq `spoke y = face (edge y)`. -/
def spoke (G : Hypermap.{u}) (y : G.Dart) : G.Dart :=
  G.face (G.edge y)

theorem spoke_injective (G : Hypermap.{u}) :
    Function.Injective (spoke G) := by
  intro y z hyz
  have h := congrArg G.node hyz
  simpa [spoke] using h

/-- The cancellation identity behind Coq `next_spoke_ring`. -/
theorem face_spoke_spoke_eq_spoke_face_symm
    {G : Hypermap.{u}}
    (hPlain : G.Plain) (hCubic : G.Cubic) (z : G.Dart) :
    G.face (spoke G (spoke G z)) = spoke G (G.face.symm z) := by
  simp only [spoke, Hypermap.face_edge_eq_node_symm]
  have htwo : G.node.symm (G.node.symm z) = G.node z := by
    rw [Hypermap.Cubic.node_symm_eq_node_node (G := G) hCubic]
    simp
  rw [htwo]
  apply G.node.injective
  rw [G.node.apply_symm_apply]
  calc
    G.node (G.face (G.node z)) = G.edge.symm (G.node z) := by
      apply G.edge.injective
      simp
    _ = G.edge (G.node z) := by
      rw [Hypermap.Plain.edge_symm_eq (G := G) hPlain]
    _ = G.face.symm z := by
      exact G.edge_node_eq_face_symm z

/-- Coq `spoke_ring x`: spokes in the reverse order of the hub face. -/
noncomputable def spokeRing (G : Hypermap.{u}) (x : G.Dart) : List G.Dart :=
  (faceCycle G x).reverse.map (spoke G)

@[simp]
theorem mem_spokeRing_iff
    (G : Hypermap.{u}) (x y : G.Dart) :
    y ∈ spokeRing G x ↔ PermReachable G.face x (G.node y) := by
  constructor
  · intro hy
    rcases List.mem_map.mp hy with ⟨z, hz, hzy⟩
    have hz' : z ∈ faceCycle G x := List.mem_reverse.mp hz
    have hxz := (mem_faceCycle_iff G x z).mp hz'
    simpa [← hzy, spoke] using hxz
  · intro hxy
    apply List.mem_map.mpr
    refine ⟨G.node y, List.mem_reverse.mpr ?_, ?_⟩
    · exact (mem_faceCycle_iff G x (G.node y)).mpr hxy
    · simp [spoke]

@[simp]
theorem length_spokeRing (G : Hypermap.{u}) (x : G.Dart) :
    (spokeRing G x).length = G.arity x := by
  simp [spokeRing]

theorem spokeRing_nodup (G : Hypermap.{u}) (x : G.Dart) :
    (spokeRing G x).Nodup := by
  unfold spokeRing
  exact (List.nodup_reverse.mpr (faceCycle_nodup G x)).map
    (spoke_injective G)

/-- The spoke ring is cycled by Coq's successor `face (spoke y)`. -/
theorem spokeRing_functionCycle
    {G : Hypermap.{u}}
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    FunctionCycle (fun y => G.face (spoke G y)) (spokeRing G x) := by
  unfold spokeRing
  apply (faceCycle_reverse_functionCycle G x).map
  intro z _hz
  exact face_spoke_spoke_eq_spoke_face_symm hPlain hCubic z

/-- Coq `next_spoke_ring`: the concrete successor of a listed spoke. -/
theorem next_spokeRing
    {G : Hypermap.{u}}
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart)
    (y : G.Dart) (hy : y ∈ spokeRing G x) :
    (spokeRing G x).next y hy = G.face (spoke G y) := by
  exact (FunctionCycle.eq_next
    (spokeRing_functionCycle hPlain hCubic x)
    (spokeRing_nodup G x) y hy).symm

/-- The predecessor identity used for the inside witness in Coq
`chordless_spoke_ring`. -/
theorem node_edge_node_eq_prev_spokeRing
    {G : Hypermap.{u}}
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart)
    (y : G.Dart) (hy : y ∈ spokeRing G x) :
    G.node (G.edge (G.node y)) = (spokeRing G x).prev y hy := by
  let p := (spokeRing G x).prev y hy
  have hp : p ∈ spokeRing G x := List.prev_mem (spokeRing G x) y hy
  have hnextPrev : (spokeRing G x).next p hp = y :=
    List.next_prev (spokeRing G x) (spokeRing_nodup G x) y hy
  calc
    G.node (G.edge (G.node y)) =
        G.node (G.edge (G.node ((spokeRing G x).next p hp))) := by
      rw [hnextPrev]
    _ = G.node (G.edge (G.node (G.face (spoke G p)))) := by
      rw [next_spokeRing hPlain hCubic x p hp]
    _ = p := by
      simp [spoke]

private theorem rLinkPath_of_functionPath
    {G : Hypermap.{u}} {f : G.Dart → G.Dart} {r : List G.Dart}
    (hlink : ∀ y : G.Dart, y ∈ r → G.RLink y (f y)) :
    ∀ {y : G.Dart} {p : List G.Dart},
      FunctionPath f y p → y ∈ r → (∀ z ∈ p, z ∈ r) →
        G.RLinkPath y p
  | _, [], _, _, _ => by simp
  | y, z :: p, hp, hy, hsub => by
      exact ⟨by simpa [hp.1] using hlink y hy,
        rLinkPath_of_functionPath hlink hp.2
          (hsub z (by simp)) (fun w hw => hsub w (by simp [hw]))⟩

private theorem rLinkCycle_of_functionCycle
    {G : Hypermap.{u}} {f : G.Dart → G.Dart} {r : List G.Dart}
    (hc : FunctionCycle f r)
    (hne : r ≠ [])
    (hlink : ∀ y : G.Dart, y ∈ r → G.RLink y (f y)) :
    G.RLinkCycle r := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons y p =>
      refine ⟨rLinkPath_of_functionPath hlink hc.1 (by simp)
        (fun z hz => by simp [hz]), ?_⟩
      have hlast : (y :: p).getLastD y ∈ y :: p := by
        simp [List.getLastD]
      exact Eq.mp
        (congrArg (fun z => G.RLink ((y :: p).getLastD y) z) hc.2)
        (hlink ((y :: p).getLastD y) hlast)

theorem spokeRing_rLinkCycle
    {G : Hypermap.{u}}
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    G.RLinkCycle (spokeRing G x) := by
  apply rLinkCycle_of_functionCycle
    (spokeRing_functionCycle hPlain hCubic x)
  · intro hnil
    have := length_spokeRing G x
    rw [hnil] at this
    simp at this
    exact (G.arity_pos x).ne' this.symm
  · intro y _hy
    unfold Hypermap.RLink
    exact PermReachable.trans G.face
      (PermReachable.forward G.face (G.edge y))
      (PermReachable.forward G.face (spoke G y))

/-- Coq `scycle_spoke_ring`, with its sole global ingredient (`double_dart`)
made explicit. -/
theorem spokeRing_faceSimple_of_doubleDart
    {G : Hypermap.{u}} {x : G.Dart}
    (hDouble : ∀ {y z : G.Dart},
      PermReachable G.face y z →
        PermReachable G.face (G.edge y) (G.edge z) → y = z) :
    G.FaceSimple (spokeRing G x) := by
  let s := (faceCycle G x).reverse
  have hsNodup : s.Nodup :=
    List.nodup_reverse.mpr (faceCycle_nodup G x)
  have hsOrbit : ∀ y : G.Dart, y ∈ s → PermReachable G.face x y := by
    intro y hy
    exact (mem_faceCycle_iff G x y).mp (List.mem_reverse.mp hy)
  have hpair : ∀ (t : List G.Dart), t.Nodup →
      (∀ y : G.Dart, y ∈ t → PermReachable G.face x y) →
      (t.map (spoke G)).Pairwise
        (fun y z => ¬ PermReachable G.face y z) := by
    intro t ht
    induction t with
    | nil => simp
    | cons y t ih =>
        intro htOrbit
        rw [List.map_cons, List.pairwise_cons]
        have htNodup := (List.nodup_cons.mp ht)
        constructor
        · intro z hz hspokes
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          apply htNodup.1
          have hyw : y = w := hDouble
            (PermReachable.trans G.face
              (PermReachable.symm G.face (htOrbit y (by simp)))
              (htOrbit w (by simp [hw])))
            (PermReachable.trans G.face
              (PermReachable.forward G.face (G.edge y))
              (PermReachable.trans G.face hspokes
                (by simpa [spoke] using
                  PermReachable.backward G.face (spoke G w))))
          simpa [hyw] using hw
        · exact ih htNodup.2 (fun z hz => htOrbit z (by simp [hz]))
  change (s.map (spoke G)).Pairwise
    (fun y z => ¬ PermReachable G.face y z)
  exact hpair s hsNodup hsOrbit

theorem spokeRing_simpleRLinkCycle_of_doubleDart
    {G : Hypermap.{u}} {x : G.Dart}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hDouble : ∀ {y z : G.Dart},
      PermReachable G.face y z →
        PermReachable G.face (G.edge y) (G.edge z) → y = z) :
    G.SimpleRLinkCycle (spokeRing G x) :=
  ⟨spokeRing_rLinkCycle hPlain hCubic x,
    spokeRing_faceSimple_of_doubleDart hDouble⟩

/-- Coq `scycle_spoke_ring`: the spokes around any face form a simple
`rlink` cycle in a connected cubic minimal counterexample. -/
theorem spokeRing_simpleRLinkCycle
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (x : G.Dart) :
    G.SimpleRLinkCycle (spokeRing G x) :=
  spokeRing_simpleRLinkCycle_of_doubleDart hG.plain hcubic
    (fun hyz hedgeYZ => doubleDart hG hconnected hcubic hyz hedgeYZ)


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
