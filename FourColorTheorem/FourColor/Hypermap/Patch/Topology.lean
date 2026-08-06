import FourColorTheorem.FourColor.Hypermap.Patch.FaceReachability

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

set_option linter.unusedVariables false in
/-- Component-level analogue of `FaceLiftState`, used for Coq
`patch_connected_r`. -/
def ComponentLiftState
    (P : Patch G Gd Gr hd hr bGd bGr)
    (root : Gr.Dart) (x : G.Dart) : Prop :=
  (∃ zr : Gr.Dart, hr zr = x ∧ Gr.Reachable root zr) ∨
    (∃ zr : Gr.Dart, ∃ yd xd : Gd.Dart,
      Gr.Reachable root zr ∧ hd yd = hr zr ∧
        Gd.Reachable yd xd ∧ hd xd = x)

theorem componentLiftState_of_faceLiftState
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root zr : Gr.Dart} {x : G.Dart}
    (hroot : Gr.Reachable root zr)
    (hs : P.FaceLiftState zr x) :
    P.ComponentLiftState root x := by
  rcases hs with ⟨yr, hyrMap, hzrYr⟩ |
      ⟨_, yr, yd, xd, hzrYr, hydMap, hydXd, hxdMap⟩
  · exact Or.inl ⟨yr, hyrMap,
      hroot.trans (Gr.facePermReachable_reachable hzrYr)⟩
  · exact Or.inr ⟨yr, yd, xd,
      hroot.trans (Gr.facePermReachable_reachable hzrYr),
      hydMap, Gd.facePermReachable_reachable hydXd, hxdMap⟩

theorem componentLiftState_link
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gr.Dart} {x y : G.Dart}
    (hs : P.ComponentLiftState root x) (hxy : G.Link x y) :
    P.ComponentLiftState root y := by
  rcases hxy with rfl | rfl | rfl
  · rcases hs with ⟨zr, hzrMap, hrootZr⟩ |
        ⟨zr, yd, xd, hrootZr, hydMap, hydXd, hxdMap⟩
    · exact Or.inl ⟨Gr.edge zr,
        by calc
          hr (Gr.edge zr) = G.edge (hr zr) := P.map_edgeR zr
          _ = G.edge x := congrArg G.edge hzrMap,
        hrootZr.trans (Gr.reachable_edge zr)⟩
    · by_cases hxdBoundary : xd ∈ bGd
      · rcases (P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary with
          ⟨yr, hyrMap⟩
        have hzrBoundary : zr ∈ bGr :=
          (P.remainder_boundary_iff_disk_overlap zr).2 ⟨yd, hydMap⟩
        have hyrBoundary : yr ∈ bGr :=
          (P.remainder_boundary_iff_disk_overlap yr).2 ⟨xd, hyrMap.symm⟩
        have hrootYr : Gr.Reachable root yr :=
          hrootZr.trans (P.reachableR_of_boundary_mem hzrBoundary hyrBoundary)
        exact Or.inl ⟨Gr.edge yr,
          by calc
            hr (Gr.edge yr) = G.edge (hr yr) := P.map_edgeR yr
            _ = G.edge (hd xd) := by rw [hyrMap]
            _ = G.edge x := congrArg G.edge hxdMap,
          hrootYr.trans (Gr.reachable_edge yr)⟩
      · exact Or.inr ⟨zr, yd, Gd.edge xd,
          hrootZr, hydMap, hydXd.trans (Gd.reachable_edge xd),
          by calc
            hd (Gd.edge xd) = G.edge (hd xd) := P.map_edgeD xd hxdBoundary
            _ = G.edge x := congrArg G.edge hxdMap⟩
  · rcases hs with ⟨zr, hzrMap, hrootZr⟩ |
        ⟨zr, yd, xd, hrootZr, hydMap, hydXd, hxdMap⟩
    · by_cases hzrBoundary : zr ∈ bGr
      · rcases P.exists_disk_boundary_companion hzrBoundary with
          ⟨yd, hEdge, _⟩
        exact Or.inr ⟨zr, Gd.edge yd, Gd.node (Gd.edge yd),
          hrootZr, hEdge,
          Gd.reachable_node (Gd.edge yd),
          by calc
            hd (Gd.node (Gd.edge yd)) = G.node (hd (Gd.edge yd)) :=
              P.map_nodeD (Gd.edge yd)
            _ = G.node (hr zr) := by rw [hEdge]
            _ = G.node x := congrArg G.node hzrMap⟩
      · exact Or.inl ⟨Gr.node zr,
          by calc
            hr (Gr.node zr) = G.node (hr zr) := P.map_nodeR zr hzrBoundary
            _ = G.node x := congrArg G.node hzrMap,
          hrootZr.trans (Gr.reachable_node zr)⟩
    · exact Or.inr ⟨zr, yd, Gd.node xd,
        hrootZr, hydMap, hydXd.trans (Gd.reachable_node xd),
        by calc
          hd (Gd.node xd) = G.node (hd xd) := P.map_nodeD xd
          _ = G.node x := congrArg G.node hxdMap⟩
  · rcases hs with ⟨zr, hzrMap, hrootZr⟩ |
        ⟨zr, yd, xd, hrootZr, hydMap, hydXd, hxdMap⟩
    · have hfaceReach : PermReachable G.face (hr zr) (G.face x) := by
        rw [hzrMap]
        exact PermReachable.forward G.face x
      exact P.componentLiftState_of_faceLiftState hrootZr
        (P.faceLiftState_of_reachable hfaceReach)
    · by_cases hxdBoundary : xd ∈ bGd
      · rcases (P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary with
          ⟨yr, hyrMap⟩
        have hzrBoundary : zr ∈ bGr :=
          (P.remainder_boundary_iff_disk_overlap zr).2 ⟨yd, hydMap⟩
        have hyrBoundary : yr ∈ bGr :=
          (P.remainder_boundary_iff_disk_overlap yr).2 ⟨xd, hyrMap.symm⟩
        have hrootYr : Gr.Reachable root yr :=
          hrootZr.trans (P.reachableR_of_boundary_mem hzrBoundary hyrBoundary)
        have hfaceReach : PermReachable G.face (hr yr) (G.face x) := by
          rw [hyrMap, hxdMap]
          exact PermReachable.forward G.face x
        exact P.componentLiftState_of_faceLiftState hrootYr
          (P.faceLiftState_of_reachable hfaceReach)
      · exact Or.inr ⟨zr, yd, Gd.face xd,
          hrootZr, hydMap, hydXd.trans (Gd.reachable_face xd),
          by calc
            hd (Gd.face xd) = G.face (hd xd) :=
              P.map_faceD_of_not_boundary xd hxdBoundary
            _ = G.face x := congrArg G.face hxdMap⟩

theorem componentLiftState_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gr.Dart} {x : G.Dart}
    (hreach : G.Reachable (hr root) x) :
    P.ComponentLiftState root x := by
  induction hreach with
  | refl => exact Or.inl ⟨root, rfl, Gr.reachable_refl root⟩
  | tail _ hstep ih => exact P.componentLiftState_link ih hstep

/-- Coq `patch_connected_r`: a nonempty remainder of a connected patch is
connected. -/
theorem connected_remainder
    (P : Patch G Gd Gr hd hr bGd bGr)
    (hG : G.Connected) (xr : Gr.Dart) :
    Gr.Connected := by
  refine ⟨⟨xr⟩, ?_⟩
  intro yr zr
  have hhost : G.Reachable (hr yr) (hr zr) :=
    Connected.reachable (G := G) hG (hr yr) (hr zr)
  rcases P.componentLiftState_of_reachable hhost with
    ⟨tr, htrMap, hyrTr⟩ |
      ⟨tr, yd, xd, hyrTr, hydMap, hydXd, hxdMap⟩
  · exact P.injr htrMap ▸ hyrTr
  · have htrBoundary : tr ∈ bGr :=
      (P.remainder_boundary_iff_disk_overlap tr).2 ⟨yd, hydMap⟩
    have hzrBoundary : zr ∈ bGr :=
      (P.remainder_boundary_iff_disk_overlap zr).2 ⟨xd, hxdMap⟩
    exact hyrTr.trans (P.reachableR_of_boundary_mem htrBoundary hzrBoundary)

/-- Coq `outer`: the union of host face orbits meeting the remainder image. -/
def Outer
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) : Prop :=
  ∃ y : G.Dart,
    P.InRemainderImage y ∧ PermReachable G.face y x

theorem outer_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x y : G.Dart} (hx : P.Outer x)
    (hxy : PermReachable G.face x y) :
    P.Outer y := by
  rcases hx with ⟨z, hzR, hzx⟩
  exact ⟨z, hzR, PermReachable.trans G.face hzx hxy⟩

theorem outer_congr_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x y : G.Dart} (hxy : PermReachable G.face x y) :
    P.Outer x ↔ P.Outer y := by
  constructor
  · exact fun hx => P.outer_of_reachable hx hxy
  · exact fun hy => P.outer_of_reachable hy
      (PermReachable.symm G.face hxy)

/-- Coq `outer_hd`: a mapped disk dart lies in the outer host face band
exactly when its disk face meets the patch boundary. -/
theorem outer_mapD_iff_faceBand
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) :
    P.Outer (hd xd) ↔ Gd.FaceBand bGd xd := by
  constructor
  · rintro ⟨y, ⟨zr, hzrMap⟩, hyXd⟩
    have hreach : PermReachable G.face (hr zr) (hd xd) := by
      rw [hzrMap]
      exact hyXd
    rcases P.faceLiftState_of_reachable hreach with
      ⟨zr', hzr'Map, _⟩ |
        ⟨_, zr', yd, zd, _, hydMap, hydZd, hzdMap⟩
    · have hxdBoundary : xd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap xd).2
          ⟨zr', hzr'Map⟩
      exact ⟨xd, hxdBoundary, PermReachable.refl Gd.face xd⟩
    · have hzdEq : zd = xd := P.injd (hzdMap.trans rfl)
      have hydBoundary : yd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap yd).2
          ⟨zr', hydMap.symm⟩
      exact ⟨yd, hydBoundary, hzdEq ▸ hydZd⟩
  · rintro ⟨yd, hydBoundary, hydXd⟩
    refine ⟨hd yd, ?_, P.map_faceD_reachable_of_reachable hydXd⟩
    exact (P.disk_boundary_iff_remainder_overlap yd).1 hydBoundary

/-- Outside the outer face band, host face reachability between disk images
reflects to the disk.  This is Coq `patch_face_d`. -/
theorem reachableD_of_map_face_reachable_of_not_faceBand
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart}
    (hxdBand : ¬ Gd.FaceBand bGd xd)
    (hxy : PermReachable G.face (hd xd) (hd yd)) :
    PermReachable Gd.face xd yd := by
  have hxdOuter : ¬ P.Outer (hd xd) := by
    simpa [P.outer_mapD_iff_faceBand xd] using hxdBand
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  have hmapPrefix : ∀ k : ℕ, k ≤ n →
      ((G.face : G.Dart → G.Dart)^[k]) (hd xd) =
        hd (((Gd.face : Gd.Dart → Gd.Dart)^[k]) xd) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        let zd := ((Gd.face : Gd.Dart → Gd.Dart)^[k]) xd
        have hprefix := ih (Nat.le_of_lt hklt)
        have hzdOff : zd ∉ bGd := by
          intro hzdBoundary
          apply hxdOuter
          have hcurrentR : P.InRemainderImage (hd zd) :=
            (P.disk_boundary_iff_remainder_overlap zd).1 hzdBoundary
          have htoCurrent :
              PermReachable G.face (hd xd)
                (((G.face : G.Dart → G.Dart)^[k]) (hd xd)) :=
            permReachable_of_iterate_eq G.face rfl
          refine ⟨hd zd, hcurrentR, ?_⟩
          rw [← hprefix]
          exact PermReachable.symm G.face htoCurrent
        calc
          ((G.face : G.Dart → G.Dart)^[k + 1]) (hd xd) =
              G.face (((G.face : G.Dart → G.Dart)^[k]) (hd xd)) := by
                rw [Function.iterate_succ_apply']
          _ = G.face (hd zd) := by rw [hprefix]
          _ = hd (Gd.face zd) :=
            (P.map_faceD_of_not_boundary zd hzdOff).symm
          _ = hd (((Gd.face : Gd.Dart → Gd.Dart)^[k + 1]) xd) := by
            rw [Function.iterate_succ_apply']
  have hfinalMap :
      hd (((Gd.face : Gd.Dart → Gd.Dart)^[n]) xd) = hd yd := by
    rw [← hmapPrefix n le_rfl, hn]
  exact permReachable_of_iterate_eq Gd.face (P.injd hfinalMap)

/-- The host edge of a mapped disk dart lies in the host face containing the
mapped disk-edge successor.  This is the boundary-safe identity used by Coq
`patch_bridgeless`. -/
theorem map_edgeD_face_reachable_host_edge
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) :
    PermReachable G.face (hd (Gd.edge xd)) (G.edge (hd xd)) := by
  have hfaceEdge :
      hd (Gd.face (Gd.edge xd)) = G.node.symm (hd xd) := by
    rw [Gd.face_edge_eq_node_symm, P.map_nodeD_symm]
  have hedgeEq :
      G.edge (hd xd) = G.face.symm (hd (Gd.face (Gd.edge xd))) := by
    calc
      G.edge (hd xd) = G.face.symm (G.node.symm (hd xd)) := by
        simpa using G.edge_node_eq_face_symm (G.node.symm (hd xd))
      _ = G.face.symm (hd (Gd.face (Gd.edge xd))) := by rw [hfaceEdge]
  have hedgeToFace :
      PermReachable G.face (G.edge (hd xd))
        (hd (Gd.face (Gd.edge xd))) := by
    rw [hedgeEq]
    simpa using
      PermReachable.forward G.face
        (G.face.symm (hd (Gd.face (Gd.edge xd))))
  exact PermReachable.trans G.face
    (P.map_faceD_reachable (Gd.edge xd))
    (PermReachable.symm G.face hedgeToFace)

/-- Coq `patch_bridgeless`: bridgelessness of a patched map descends to both
the disk and remainder maps. -/
theorem bridgeless_parts
    (P : Patch G Gd Gr hd hr bGd bGr)
    (hG : G.Bridgeless) :
    Gd.Bridgeless ∧ Gr.Bridgeless := by
  constructor
  · intro xd hbridge
    apply hG (hd xd)
    exact PermReachable.trans G.face
      (P.map_faceD_reachable_of_reachable hbridge)
      (P.map_edgeD_face_reachable_host_edge xd)
  · intro xr hbridge
    apply hG (hr xr)
    have hmap :
        PermReachable G.face (hr xr) (hr (Gr.edge xr)) :=
      (P.map_faceR_reachable_iff xr (Gr.edge xr)).1 hbridge
    simpa [P.map_edgeR xr] using hmap

/-- Coq `bridgeless_patch`: if both parts are bridgeless and the disk boundary
has no chord, then the patched host is bridgeless. -/
theorem bridgeless_of_parts_of_chordless
    (P : Patch G Gd Gr hd hr bGd bGr)
    (hD : Gd.Bridgeless) (hR : Gr.Bridgeless)
    (hChordless : Gd.Chordless bGd) :
    G.Bridgeless := by
  intro x hbridge
  by_cases hxR : P.InRemainderImage x
  · rcases hxR with ⟨xr, rfl⟩
    apply hR xr
    apply (P.map_faceR_reachable_iff xr (Gr.edge xr)).2
    simpa [P.map_edgeR xr] using hbridge
  · rcases P.cover x with ⟨xd, rfl⟩ | hxR'
    · have hxdOff : xd ∉ bGd := by
        intro hxdBoundary
        exact hxR
          ((P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary)
      have hEdgeMap : hd (Gd.edge xd) = G.edge (hd xd) :=
        P.map_edgeD xd hxdOff
      have hbridgeD :
          PermReachable G.face (hd xd) (hd (Gd.edge xd)) := by
        rw [hEdgeMap]
        exact hbridge
      by_cases hxdBand : Gd.FaceBand bGd xd
      · have hOuterX : P.Outer (hd xd) :=
          (P.outer_mapD_iff_faceBand xd).2 hxdBand
        have hOuterEdge : P.Outer (hd (Gd.edge xd)) :=
          P.outer_of_reachable hOuterX hbridgeD
        have hedgeBand : Gd.FaceBand bGd (Gd.edge xd) :=
          (P.outer_mapD_iff_faceBand (Gd.edge xd)).1 hOuterEdge
        rcases hxdBand with ⟨yd, hydBoundary, hydXd⟩
        rcases hedgeBand with ⟨zd, hzdBoundary, hedgeZd⟩
        have hedgeZd' : PermReachable Gd.face (Gd.edge xd) zd :=
          PermReachable.symm Gd.face hedgeZd
        have hadj : Gd.RingAdj yd zd := ⟨xd, hydXd, hedgeZd'⟩
        have hnext : bGd.next yd hydBoundary = Gd.edge yd :=
          (P.cycleD.eq_next P.boundaryD_nodup yd hydBoundary).symm
        have hprevMem : bGd.prev yd hydBoundary ∈ bGd :=
          List.prev_mem bGd yd hydBoundary
        have hedgePrev :
            Gd.edge (bGd.prev yd hydBoundary) = yd := by
          calc
            Gd.edge (bGd.prev yd hydBoundary) =
                bGd.next (bGd.prev yd hydBoundary) hprevMem :=
              P.cycleD.eq_next P.boundaryD_nodup _ _
            _ = yd := List.next_prev bGd P.boundaryD_nodup yd hydBoundary
        have hprev : bGd.prev yd hydBoundary = Gd.edge.symm yd := by
          apply Gd.edge.injective
          rw [hedgePrev]
          simp
        have hmapYZ : PermReachable G.face (hd yd) (hd zd) :=
          PermReachable.trans G.face
            (P.map_faceD_reachable_of_reachable hydXd)
            (PermReachable.trans G.face hbridgeD
              (P.map_faceD_reachable_of_reachable hedgeZd'))
        rcases P.exists_remainder_boundary_companion hydBoundary with
          ⟨yr, hEdgeY, hNodeY⟩
        rcases hChordless yd hydBoundary zd hzdBoundary hadj with
          hzdPrev | hzdNext
        · have hzdEdgeSymm : zd = Gd.edge.symm yd := hzdPrev.trans hprev
          have hPrevMap :
              hd (Gd.edge.symm yd) = hr (Gr.node (Gr.node yr)) := by
            apply
              (P.map_edgeD_eq_mapR_iff_mapD_eq_map_nodeR
                (Gd.edge.symm yd) (Gr.node yr)).1
            simpa using hNodeY
          have hmapGr :
              PermReachable G.face (hr (Gr.node yr))
                (hr (Gr.node (Gr.node yr))) := by
            rw [← hNodeY, ← hPrevMap, ← hzdEdgeSymm]
            exact hmapYZ
          have hreachGr :
              PermReachable Gr.face (Gr.node yr)
                (Gr.node (Gr.node yr)) :=
            (P.map_faceR_reachable_iff
              (Gr.node yr) (Gr.node (Gr.node yr))).2 hmapGr
          apply hR (Gr.node (Gr.node yr))
          have hback :
              PermReachable Gr.face (Gr.node yr)
                (Gr.edge (Gr.node (Gr.node yr))) := by
            simpa [Gr.edge_node_eq_face_symm] using
              PermReachable.backward Gr.face (Gr.node yr)
          exact PermReachable.trans Gr.face
            (PermReachable.symm Gr.face hreachGr) hback
        · have hzdEdge : zd = Gd.edge yd := hzdNext.trans hnext
          have hmapGr :
              PermReachable G.face (hr (Gr.node yr)) (hr yr) := by
            rw [← hNodeY, ← hEdgeY, ← hzdEdge]
            exact hmapYZ
          have hreachGr : PermReachable Gr.face (Gr.node yr) yr :=
            (P.map_faceR_reachable_iff (Gr.node yr) yr).2 hmapGr
          apply hR (Gr.node yr)
          have hback :
              PermReachable Gr.face yr (Gr.edge (Gr.node yr)) := by
            simpa [Gr.edge_node_eq_face_symm] using
              PermReachable.backward Gr.face yr
          exact PermReachable.trans Gr.face hreachGr hback
      · exact hD xd
          (P.reachableD_of_map_face_reachable_of_not_faceBand
            hxdBand hbridgeD)
    · exact False.elim (hxR hxR')
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
