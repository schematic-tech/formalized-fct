import FourColorTheorem.FourColor.Hypermap.Patch.Boundary

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

/-- Coq's local `hdF`: the disk injection commutes with `face` away from the
cut edge cycle. -/
theorem map_faceD_of_not_boundary
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) (hxd : xd ∉ bGd) :
    hd (Gd.face xd) = G.face (hd xd) := by
  have hnfx : Gd.node (Gd.face xd) ∉ bGd := by
    intro hmem
    have hedgeMem :
        Gd.edge (Gd.node (Gd.face xd)) ∈ bGd :=
      P.cycleD.image_mem hmem
    have : xd ∈ bGd := by simpa using hedgeMem
    exact hxd this
  apply G.node.injective
  apply G.edge.injective
  calc
    G.edge (G.node (hd (Gd.face xd))) =
        G.edge (hd (Gd.node (Gd.face xd))) := by
          rw [P.map_nodeD]
    _ = hd (Gd.edge (Gd.node (Gd.face xd))) :=
      (P.map_edgeD (Gd.node (Gd.face xd)) hnfx).symm
    _ = hd xd := by rw [Gd.edge_node_face]
    _ = G.edge (G.node (G.face (hd xd))) :=
      (G.edge_node_face (hd xd)).symm

/-- Coq's local `hrF`: the remainder injection commutes with `face` when the
target of the face step is off the node boundary. -/
theorem map_faceR_of_face_not_boundary
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xr : Gr.Dart) (hfxr : Gr.face xr ∉ bGr) :
    hr (Gr.face xr) = G.face (hr xr) := by
  apply G.node.injective
  apply G.edge.injective
  calc
    G.edge (G.node (hr (Gr.face xr))) =
        G.edge (hr (Gr.node (Gr.face xr))) := by
          rw [P.map_nodeR (Gr.face xr) hfxr]
    _ = hr (Gr.edge (Gr.node (Gr.face xr))) :=
      (P.map_edgeR (Gr.node (Gr.face xr))).symm
    _ = hr xr := by rw [Gr.edge_node_face]
    _ = G.edge (G.node (G.face (hr xr))) :=
      (G.edge_node_face (hr xr)).symm

/-- Coq `hdFrF`: a disk face step crossing the patch boundary corresponds to
the oppositely oriented remainder face step. -/
theorem map_faceD_eq_face_mapR_iff_mapD_eq_map_faceR
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) (xr : Gr.Dart) :
    hd (Gd.face xd) = G.face (hr xr) ↔
      hd xd = hr (Gr.face xr) := by
  have htarget :
      G.node (G.face (hr xr)) = hr (Gr.node (Gr.face xr)) := by
    apply G.edge.injective
    calc
      G.edge (G.node (G.face (hr xr))) = hr xr := G.edge_node_face (hr xr)
      _ = hr (Gr.edge (Gr.node (Gr.face xr))) := by
        rw [Gr.edge_node_face]
      _ = G.edge (hr (Gr.node (Gr.face xr))) :=
        P.map_edgeR (Gr.node (Gr.face xr))
  have hcross :=
    P.map_edgeD_eq_mapR_iff_mapD_eq_map_nodeR
      (Gd.node (Gd.face xd)) (Gr.face xr)
  constructor
  · intro hface
    have hnode := congrArg G.node hface
    rw [← P.map_nodeD, htarget] at hnode
    have hedge :
        hd (Gd.edge (Gd.node (Gd.face xd))) = hr (Gr.face xr) :=
      hcross.2 hnode
    simpa using hedge
  · intro hface
    have hedge :
        hd (Gd.edge (Gd.node (Gd.face xd))) = hr (Gr.face xr) := by
      simpa using hface
    have hnode :
        hd (Gd.node (Gd.face xd)) = hr (Gr.node (Gr.face xr)) :=
      hcross.1 hedge
    apply G.node.injective
    rw [← P.map_nodeD, htarget]
    exact hnode

/-- Coq's local `cFhd`: even at a boundary dart, one disk face step maps into
the same face orbit of the glued map. -/
theorem map_faceD_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) :
    PermReachable G.face (hd xd) (hd (Gd.face xd)) := by
  by_cases hxd : xd ∈ bGd
  · by_cases hfixed : Gd.face xd = xd
    · rw [hfixed]
      exact PermReachable.refl G.face (hd xd)
    · have hback : PermReachable Gd.face (Gd.face xd) xd := by
        simpa using PermReachable.backward Gd.face (Gd.face xd)
      rcases permReachable_exists_first_positive_iterate
          Gd.face hback hfixed with ⟨n, hnpos, hn, hminimal⟩
      have hoff : ∀ k : ℕ, k < n →
          ((Gd.face : Gd.Dart → Gd.Dart)^[k]) (Gd.face xd) ∉ bGd := by
        intro k hk hmem
        let y := ((Gd.face : Gd.Dart → Gd.Dart)^[k]) (Gd.face xd)
        have hstartY : PermReachable Gd.face (Gd.face xd) y :=
          permReachable_of_iterate_eq Gd.face rfl
        have hyXd : PermReachable Gd.face y xd :=
          PermReachable.trans Gd.face
            (PermReachable.symm Gd.face hstartY) hback
        have hyEq : y = xd :=
          Hypermap.FaceSimple.eq_of_faceReachable_of_mem
            (G := Gd) P.boundaryD_faceSimple hmem hxd hyXd
        exact hminimal k hk hyEq
      have hmapPrefix : ∀ k : ℕ, k ≤ n →
          ((G.face : G.Dart → G.Dart)^[k]) (hd (Gd.face xd)) =
            hd (((Gd.face : Gd.Dart → Gd.Dart)^[k]) (Gd.face xd)) := by
        intro k hk
        induction k with
        | zero => simp
        | succ k ih =>
            have hklt : k < n := Nat.lt_of_succ_le hk
            calc
              ((G.face : G.Dart → G.Dart)^[k + 1]) (hd (Gd.face xd)) =
                  G.face (((G.face : G.Dart → G.Dart)^[k])
                    (hd (Gd.face xd))) := by
                    rw [Function.iterate_succ_apply']
              _ = G.face (hd (((Gd.face : Gd.Dart → Gd.Dart)^[k])
                    (Gd.face xd))) := by rw [ih (Nat.le_of_lt hklt)]
              _ = hd (Gd.face
                    (((Gd.face : Gd.Dart → Gd.Dart)^[k])
                      (Gd.face xd))) :=
                (P.map_faceD_of_not_boundary _ (hoff k hklt)).symm
              _ = hd (((Gd.face : Gd.Dart → Gd.Dart)^[k + 1])
                    (Gd.face xd)) := by
                    rw [Function.iterate_succ_apply']
      have hiter :
          ((G.face : G.Dart → G.Dart)^[n]) (hd (Gd.face xd)) = hd xd := by
        rw [hmapPrefix n le_rfl, hn]
      exact PermReachable.symm G.face
        (permReachable_of_iterate_eq G.face hiter)
  · have hmap := P.map_faceD_of_not_boundary xd hxd
    simpa [hmap] using PermReachable.forward G.face (hd xd)

/-- Coq `patch_face_d'`: disk face-orbit reachability is preserved by the
disk injection, including across the glued boundary. -/
theorem map_faceD_reachable_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart}
    (hxy : PermReachable Gd.face xd yd) :
    PermReachable G.face (hd xd) (hd yd) := by
  induction hxy with
  | refl => exact PermReachable.refl G.face (hd xd)
  | @tail y z _ hyz ih =>
      apply PermReachable.trans G.face ih
      cases hyz with
      | forward => exact P.map_faceD_reachable y
      | backward =>
          have hstep := P.map_faceD_reachable (Gd.face.symm y)
          simpa using PermReachable.symm G.face hstep

theorem map_nodeD_symm
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) :
    hd (Gd.node.symm xd) = G.node.symm (hd xd) := by
  apply G.node.injective
  rw [← P.map_nodeD]
  simp

/-- One remainder face step maps into one host face orbit, including when the
step enters the sewn boundary. -/
theorem map_faceR_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xr : Gr.Dart) :
    PermReachable G.face (hr xr) (hr (Gr.face xr)) := by
  by_cases hfaceBoundary : Gr.face xr ∈ bGr
  · rcases P.exists_disk_boundary_companion hfaceBoundary with
      ⟨xd, hEdge, hNode⟩
    have hxrEq : hr xr = G.edge (hd xd) := by
      calc
        hr xr = hr (Gr.edge (Gr.node (Gr.face xr))) := by
          rw [Gr.edge_node_face]
        _ = G.edge (hr (Gr.node (Gr.face xr))) :=
          P.map_edgeR (Gr.node (Gr.face xr))
        _ = G.edge (hd xd) := by rw [← hNode]
    have hfaceEdge :
        hd (Gd.face (Gd.edge xd)) = G.node.symm (hd xd) := by
      rw [Gd.face_edge_eq_node_symm, P.map_nodeD_symm]
    have hedgeEq :
        G.edge (hd xd) = G.face.symm (hd (Gd.face (Gd.edge xd))) := by
      calc
        G.edge (hd xd) = G.face.symm (G.node.symm (hd xd)) := by
          simpa using G.edge_node_eq_face_symm (G.node.symm (hd xd))
        _ = G.face.symm (hd (Gd.face (Gd.edge xd))) := by rw [hfaceEdge]
    have htoDiskFace :
        PermReachable G.face (G.edge (hd xd))
          (hd (Gd.face (Gd.edge xd))) := by
      rw [hedgeEq]
      simpa using
        PermReachable.forward G.face
          (G.face.symm (hd (Gd.face (Gd.edge xd))))
    have hdStep := P.map_faceD_reachable (Gd.edge xd)
    rw [hxrEq, ← hEdge]
    exact PermReachable.trans G.face htoDiskFace
      (PermReachable.symm G.face hdStep)
  · have hmap := P.map_faceR_of_face_not_boundary xr hfaceBoundary
    simpa [hmap] using PermReachable.forward G.face (hr xr)

/-- The forward implication of Coq `patch_face_r`: remainder face
reachability is preserved by the remainder injection. -/
theorem map_faceR_reachable_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart}
    (hxy : PermReachable Gr.face xr yr) :
    PermReachable G.face (hr xr) (hr yr) := by
  induction hxy with
  | refl => exact PermReachable.refl G.face (hr xr)
  | @tail y z _ hyz ih =>
      apply PermReachable.trans G.face ih
      cases hyz with
      | forward => exact P.map_faceR_reachable y
      | backward =>
          have hstep := P.map_faceR_reachable (Gr.face.symm y)
          simpa using PermReachable.symm G.face hstep

/-- State invariant for the reverse implication of Coq `patch_face_r`.
Following a host face from a remainder dart either stays in the corresponding
remainder face, or is strictly inside a disk face reached from its most recent
remainder-boundary representative. -/
def FaceLiftState
    (P : Patch G Gd Gr hd hr bGd bGr)
    (root : Gr.Dart) (x : G.Dart) : Prop :=
  (∃ zr : Gr.Dart,
      hr zr = x ∧ PermReachable Gr.face root zr) ∨
    (¬ P.InRemainderImage x ∧
      ∃ zr : Gr.Dart, ∃ yd xd : Gd.Dart,
        PermReachable Gr.face root zr ∧
          hd yd = hr zr ∧
            PermReachable Gd.face yd xd ∧ hd xd = x)

theorem faceLiftState_face
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gr.Dart} {x : G.Dart}
    (hs : P.FaceLiftState root x) :
    P.FaceLiftState root (G.face x) := by
  rcases hs with hrem | ⟨hxNotR, hdisk⟩
  · rcases hrem with ⟨zr, hzrMap, hrootZr⟩
    by_cases hfaceBoundary : Gr.face zr ∈ bGr
    · rcases P.exists_disk_boundary_companion hfaceBoundary with
        ⟨yd, hEdge, _hNode⟩
      let zd : Gd.Dart := Gd.face (Gd.edge yd)
      have hzdMap : hd zd = G.face x := by
        calc
          hd zd = G.face (hr zr) :=
            (P.map_faceD_eq_face_mapR_iff_mapD_eq_map_faceR
              (Gd.edge yd) zr).2 hEdge
          _ = G.face x := congrArg G.face hzrMap
      have hyBoundary : Gd.edge yd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap (Gd.edge yd)).2
          ⟨Gr.face zr, hEdge.symm⟩
      by_cases hnextR : P.InRemainderImage (G.face x)
      · rcases hnextR with ⟨zr', hzr'Map⟩
        have hzdBoundary : zd ∈ bGd :=
          (P.disk_boundary_iff_remainder_overlap zd).2
            ⟨zr', hzr'Map.trans hzdMap.symm⟩
        have hyzReach :
            PermReachable Gd.face (Gd.edge yd) zd := by
          exact PermReachable.forward Gd.face (Gd.edge yd)
        have hyEq : Gd.edge yd = zd :=
          Hypermap.FaceSimple.eq_of_faceReachable_of_mem
            (G := Gd) P.boundaryD_faceSimple
            hyBoundary hzdBoundary hyzReach
        have hzr'Eq : zr' = Gr.face zr := by
          apply P.injr
          calc
            hr zr' = G.face x := hzr'Map
            _ = hd zd := hzdMap.symm
            _ = hd (Gd.edge yd) := congrArg hd hyEq.symm
            _ = hr (Gr.face zr) := hEdge
        exact Or.inl ⟨zr', hzr'Map,
          hzr'Eq ▸ PermReachable.trans Gr.face hrootZr
            (PermReachable.forward Gr.face zr)⟩
      · exact Or.inr ⟨hnextR, Gr.face zr, Gd.edge yd, zd,
          PermReachable.trans Gr.face hrootZr
            (PermReachable.forward Gr.face zr),
          hEdge, PermReachable.forward Gd.face (Gd.edge yd), hzdMap⟩
    · have hmap := P.map_faceR_of_face_not_boundary zr hfaceBoundary
      exact Or.inl ⟨Gr.face zr,
        by calc
          hr (Gr.face zr) = G.face (hr zr) := hmap
          _ = G.face x := congrArg G.face hzrMap,
        PermReachable.trans Gr.face hrootZr
          (PermReachable.forward Gr.face zr)⟩
  · rcases hdisk with ⟨zr, yd, xd, hrootZr, hydMap, hydXd, hxdMap⟩
    have hxdOff : xd ∉ bGd := by
      intro hxdBoundary
      apply hxNotR
      have hoverlap : P.InRemainderImage (hd xd) :=
        (P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary
      simpa [hxdMap] using hoverlap
    have hnextMap : hd (Gd.face xd) = G.face x := by
      calc
        hd (Gd.face xd) = G.face (hd xd) :=
          P.map_faceD_of_not_boundary xd hxdOff
        _ = G.face x := congrArg G.face hxdMap
    by_cases hnextR : P.InRemainderImage (G.face x)
    · rcases hnextR with ⟨zr', hzr'Map⟩
      have hfaceBoundary : Gd.face xd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap (Gd.face xd)).2
          ⟨zr', hzr'Map.trans hnextMap.symm⟩
      have hydBoundary : yd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap yd).2
          ⟨zr, hydMap.symm⟩
      have hydFace : PermReachable Gd.face yd (Gd.face xd) :=
        PermReachable.trans Gd.face hydXd
          (PermReachable.forward Gd.face xd)
      have hydEq : yd = Gd.face xd :=
        Hypermap.FaceSimple.eq_of_faceReachable_of_mem
          (G := Gd) P.boundaryD_faceSimple
          hydBoundary hfaceBoundary hydFace
      have hzr'Eq : zr' = zr := by
        apply P.injr
        calc
          hr zr' = G.face x := hzr'Map
          _ = hd (Gd.face xd) := hnextMap.symm
          _ = hd yd := congrArg hd hydEq.symm
          _ = hr zr := hydMap
      exact Or.inl ⟨zr', hzr'Map, hzr'Eq ▸ hrootZr⟩
    · exact Or.inr ⟨hnextR, zr, yd, Gd.face xd,
        hrootZr, hydMap,
        PermReachable.trans Gd.face hydXd
          (PermReachable.forward Gd.face xd),
        hnextMap⟩

theorem faceLiftState_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gr.Dart} {x : G.Dart}
    (hreach : PermReachable G.face (hr root) x) :
    P.FaceLiftState root x := by
  rcases permReachable_exists_iterate G.face hreach with ⟨n, hn⟩
  have hstate : ∀ k : ℕ,
      P.FaceLiftState root
        (((G.face : G.Dart → G.Dart)^[k]) (hr root)) := by
    intro k
    induction k with
    | zero => exact Or.inl ⟨root, rfl, PermReachable.refl Gr.face root⟩
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact P.faceLiftState_face ih
  simpa [hn] using hstate n

/-- The reverse implication of Coq `patch_face_r`: host face reachability
between remainder images reflects to the remainder map. -/
theorem reachableR_of_map_face_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart}
    (hxy : PermReachable G.face (hr xr) (hr yr)) :
    PermReachable Gr.face xr yr := by
  have hend : P.FaceLiftState xr (hr yr) :=
    P.faceLiftState_of_reachable hxy
  rcases hend with ⟨zr, hzrMap, hreach⟩ | ⟨hnotR, _⟩
  · exact P.injr hzrMap ▸ hreach
  · exact False.elim (hnotR ⟨yr, rfl⟩)

/-- Coq `patch_face_r`: the remainder injection preserves and reflects face
orbits. -/
theorem map_faceR_reachable_iff
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xr yr : Gr.Dart) :
    PermReachable Gr.face xr yr ↔
      PermReachable G.face (hr xr) (hr yr) :=
  ⟨P.map_faceR_reachable_of_reachable,
    P.reachableR_of_map_face_reachable⟩

theorem reachableR_of_boundary_mem
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart} (hxr : xr ∈ bGr) (hyr : yr ∈ bGr) :
    Gr.Reachable xr yr :=
  Gr.nodePermReachable_reachable
    (P.cycleR.permReachable_of_mem_mem hxr hyr)
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
