import FourColorTheorem.FourColor.Reducibility.ProgramMap.Configuration.RingAndSimplicity

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpMapCover_nil :
    cpMapCover [] := by
  intro x
  change cpmap0.FaceBand [false, true] x
  rw [cpmap0_faceBand_iff]
  cases x <;> simp

theorem cpMapCover_y_of_ring_kernel_eq
    {cp : CProg}
    (hcover : cpMapCover cp)
    (hringY :
      cpRing (CpStep.y :: cp) =
        (cpmap cp).y.map.node (cpmap cp).y.point ::
          (cpmap cp).y.point ::
            ((cpRing cp).drop 1).map (fun x => (cpmap cp).yOld x))
    (hkernelY :
      cpKernel (CpStep.y :: cp) =
        (cpKernel cp).map (fun x => (cpmap cp).yOld x)) :
    cpMapCover (CpStep.y :: cp) := by
  let P := cpmap cp
  let target : List P.y.map.Dart :=
    P.y.map.node P.y.point :: P.y.point ::
      ((cpRing cp).drop 1).map P.yOld ++ (cpKernel cp).map P.yOld
  have hringOld :
      cpRing cp = P.map.node P.point :: (cpRing cp).drop 1 := by
    simpa [P] using cpRing_eq_nodePoint_cons_drop_one cp
  have htail_old :
      ∀ {z : P.map.Dart},
        z ∈ (cpRing cp).drop 1 ++ cpKernel cp →
          P.y.map.FaceBand target (P.yOld z) := by
    intro z hz
    apply Hypermap.FaceBand.of_mem
      (G := P.y.map) (x := P.yOld z) (u := P.yOld z)
    · have htail :
          P.yOld z ∈ ((cpRing cp).drop 1 ++ cpKernel cp).map P.yOld :=
        List.mem_map.mpr ⟨z, hz, rfl⟩
      simpa [target, List.map_append] using
        (List.mem_cons_of_mem (P.y.map.node P.y.point)
          (List.mem_cons_of_mem P.y.point htail))
    · exact PermReachable.refl P.y.map.face (P.yOld z)
  have hsource_old :
      ∀ {z : P.map.Dart},
        z ∈ cpRing cp ++ cpKernel cp →
          P.y.map.FaceBand target (P.yOld z) := by
    intro z hz
    rcases List.mem_append.mp hz with hzr | hzk
    · rw [hringOld] at hzr
      rcases List.mem_cons.mp hzr with hnode | hdrop
      · subst z
        exact Hypermap.FaceBand.of_mem
          (G := P.y.map)
          (x := P.y.map.node P.y.point)
          (u := P.yOld (P.map.node P.point))
          (by
            have hmem :
                P.y.map.node P.y.point ∈
                  P.y.map.node P.y.point :: P.y.point ::
                    ((cpRing cp).drop 1).map P.yOld ++
                      (cpKernel cp).map P.yOld := by
              exact List.Mem.head _
            simpa [target] using
              hmem)
          ((y_faceReachable_node_point_old_iff P).2
            (PermReachable.refl P.map.face (P.map.node P.point)))
      · exact htail_old (List.mem_append.mpr (Or.inl hdrop))
    · exact htail_old (List.mem_append.mpr (Or.inr hzk))
  intro u
  cases y_exists_old_faceReachable_or_point P u with
  | inl hold =>
      rcases hold with ⟨x, hux⟩
      rcases hcover x with ⟨z, hz, hzx⟩
      have hbandZ : P.y.map.FaceBand target (P.yOld z) :=
        hsource_old hz
      have hzX :
          PermReachable P.y.map.face (P.yOld z) (P.yOld x) :=
        yOld_faceReachable_of_faceReachable P hzx
      have hbandX : P.y.map.FaceBand target (P.yOld x) :=
        Hypermap.FaceBand.of_faceReachable (G := P.y.map) hbandZ hzX
      have hbandU : P.y.map.FaceBand target u :=
        Hypermap.FaceBand.of_faceReachable (G := P.y.map) hbandX
          (PermReachable.symm P.y.map.face hux)
      simpa [cpMapCover, P, target, hringY, hkernelY, List.cons_append]
        using hbandU
  | inr hpoint =>
      have hbandU : P.y.map.FaceBand target u :=
        Hypermap.FaceBand.of_mem
          (G := P.y.map)
          (x := P.y.point)
          (u := u)
          (by
            have hmem :
                P.y.point ∈
                  P.y.map.node P.y.point :: P.y.point ::
                    ((cpRing cp).drop 1).map P.yOld ++
                      (cpKernel cp).map P.yOld := by
              exact List.Mem.tail _ (List.Mem.head _)
            simpa [target] using
              hmem)
          hpoint
      simpa [cpMapCover, P, target, hringY, hkernelY, List.cons_append]
        using hbandU

theorem cpMapCover_y_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (hcover : cpMapCover cp) :
    cpMapCover (CpStep.y :: cp) := by
  have hgeom := cpmap_configGeometry_of_config hcfg
  exact cpMapCover_y_of_ring_kernel_eq hcover
    (by
      simpa using
        cpRing_y_eq_of_ringCycle (cp := cp)
          (cpRingCycle_of_config hcfg) hgeom.proper)
    (by
      simpa using cpKernel_y_eq (cp := cp))

theorem cpMapCover_h_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (hcover : cpMapCover cp) :
    cpMapCover (CpStep.h :: cp) := by
  let P := cpmap cp
  let faceEdge := P.map.face (P.map.edge P.point)
  let target : List P.h.map.Dart :=
    P.h.map.node P.h.point :: P.h.point ::
      ((cpRing cp).drop 2).map P.hOld ++
        (P.point :: cpKernel cp).map P.hOld
  have hboundary := ConfigProgram.HBoundary.of_config hcfg
  have hgeom := hboundary.geometry
  have hringH := hboundary.extendedRing
  have hkernelH := hboundary.extendedKernel
  have hringOld := hboundary.oldRing
  have hdrop2 := hboundary.dropTwo
  have hsource_old :
      ∀ {z : P.map.Dart},
        z ∈ cpRing cp ++ cpKernel cp →
          P.h.map.FaceBand target (P.hOld z) := by
    intro z hz
    rcases List.mem_append.mp hz with hzr | hzk
    · rw [hringOld] at hzr
      rcases List.mem_cons.mp hzr with hnode | hrest
      · subst z
        exact Hypermap.FaceBand.of_mem
          (G := P.h.map)
          (x := P.h.map.node P.h.point)
          (u := P.hOld (P.map.node P.point))
          (by
            have hmem :
                P.h.map.node P.h.point ∈
                  P.h.map.node P.h.point :: P.h.point ::
                    ((cpRing cp).drop 2).map P.hOld ++
                      (P.point :: cpKernel cp).map P.hOld := by
              exact List.Mem.head _
            simpa [target] using
              hmem)
          ((h_faceReachable_node_point_old_iff P hgeom.proper).2
            (PermReachable.refl P.map.face (P.map.node P.point)))
      rcases List.mem_cons.mp hrest with hpoint | hrest
      · subst z
        exact Hypermap.FaceBand.of_mem
          (G := P.h.map)
          (x := P.hOld P.point)
          (u := P.hOld P.point)
          (by
            have htail :
                P.hOld P.point ∈
                  ((cpRing cp).drop 2).map P.hOld ++
                    (P.point :: cpKernel cp).map P.hOld :=
              List.mem_append.mpr
                (Or.inr
                  (List.mem_map.mpr
                    ⟨P.point, List.Mem.head _, rfl⟩))
            simpa [target] using
              (List.mem_cons_of_mem (P.h.map.node P.h.point)
                (List.mem_cons_of_mem P.h.point htail)))
          (PermReachable.refl P.h.map.face (P.hOld P.point))
      rcases List.mem_cons.mp hrest with hface | hdrop
      · subst z
        exact Hypermap.FaceBand.of_mem
          (G := P.h.map)
          (x := P.hOld faceEdge)
          (u := P.hOld faceEdge)
          (by
            have hdrop : faceEdge ∈ (cpRing cp).drop 2 := by
              rw [hdrop2]
              exact List.Mem.head _
            have htail :
                P.hOld faceEdge ∈
                  ((cpRing cp).drop 2).map P.hOld ++
                    (P.point :: cpKernel cp).map P.hOld :=
              List.mem_append.mpr
                (Or.inl (List.mem_map.mpr ⟨faceEdge, hdrop, rfl⟩))
            simpa [target] using
              (List.mem_cons_of_mem (P.h.map.node P.h.point)
                (List.mem_cons_of_mem P.h.point htail)))
          (PermReachable.refl P.h.map.face (P.hOld faceEdge))
      · exact Hypermap.FaceBand.of_mem
          (G := P.h.map)
          (x := P.hOld z)
          (u := P.hOld z)
          (by
            have hdrop' : z ∈ (cpRing cp).drop 2 := by
              rw [hdrop2]
              exact List.mem_cons_of_mem faceEdge hdrop
            have htail :
                P.hOld z ∈
                  ((cpRing cp).drop 2).map P.hOld ++
                    (P.point :: cpKernel cp).map P.hOld :=
              List.mem_append.mpr
                (Or.inl (List.mem_map.mpr ⟨z, hdrop', rfl⟩))
            simpa [target] using
              (List.mem_cons_of_mem (P.h.map.node P.h.point)
                (List.mem_cons_of_mem P.h.point htail)))
          (PermReachable.refl P.h.map.face (P.hOld z))
    · exact Hypermap.FaceBand.of_mem
        (G := P.h.map)
        (x := P.hOld z)
        (u := P.hOld z)
        (by
          have htail :
              P.hOld z ∈
                ((cpRing cp).drop 2).map P.hOld ++
                  (P.point :: cpKernel cp).map P.hOld :=
            List.mem_append.mpr
              (Or.inr
                (List.mem_map.mpr
                  ⟨z, List.mem_cons_of_mem P.point hzk, rfl⟩))
          simpa [target] using
            (List.mem_cons_of_mem (P.h.map.node P.h.point)
              (List.mem_cons_of_mem P.h.point htail)))
        (PermReachable.refl P.h.map.face (P.hOld z))
  intro u
  cases h_exists_old_faceReachable_or_freshFace_of_proper P hgeom.proper u with
  | inl hold =>
      rcases hold with ⟨x, hux⟩
      rcases hcover x with ⟨z, hz, hzx⟩
      have hbandZ : P.h.map.FaceBand target (P.hOld z) :=
        hsource_old hz
      have hzX :
          PermReachable P.h.map.face (P.hOld z) (P.hOld x) :=
        hOld_faceReachable_of_faceReachable P hzx
      have hbandX : P.h.map.FaceBand target (P.hOld x) :=
        Hypermap.FaceBand.of_faceReachable (G := P.h.map) hbandZ hzX
      have hbandU : P.h.map.FaceBand target u :=
        Hypermap.FaceBand.of_faceReachable (G := P.h.map) hbandX
          (PermReachable.symm P.h.map.face hux)
      simpa [cpMapCover, P, target, hringH, hkernelH, List.cons_append]
        using hbandU
  | inr hfresh =>
      have hfreshBand : P.h.map.FaceBand [P.h.point] u := by
        change (Hypermap.extensionH P.map P.point).FaceBand
          [ExtDart.new] u
        exact
          (Hypermap.extensionH_freshFace_iff_faceBand_new_of_proper
            (G := P.map) P.point hgeom.proper).1 hfresh
      have hbandU : P.h.map.FaceBand target u :=
        Hypermap.FaceBand.subset
          (G := P.h.map)
          (r := [P.h.point])
          (s := target)
          (by
            intro z hz
            have hz' : z = P.h.point := by
              exact List.mem_singleton.mp hz
            subst z
            have hmem :
                P.h.point ∈
                  P.h.map.node P.h.point :: P.h.point ::
                    ((cpRing cp).drop 2).map P.hOld ++
                      (P.point :: cpKernel cp).map P.hOld := by
              exact List.Mem.tail _ (List.Mem.head _)
            simpa [target] using
              hmem)
          hfreshBand
      simpa [cpMapCover, P, target, hringH, hkernelH, List.cons_append]
        using hbandU

theorem cpMapCover_rotate_of_ringCycle
    {cp : CProg} {n : Nat}
    (hcycle : cpRingCycle cp)
    (hcover : cpMapCover cp) :
    cpMapCover (CpStep.rotate n :: cp) := by
  let P := cpmap cp
  have hring :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle (cp := cp) (n := n) hcycle
  intro x
  have hrotPerm :
      (CProg.rotateLeft n (cpRing cp)).Perm (cpRing cp) := by
    exact CProg.perm_rotateLeft n (cpRing cp)
  have hfullPerm :
      (CProg.rotateLeft n (cpRing cp) ++ cpKernel cp).Perm
        (cpRing cp ++ cpKernel cp) :=
    hrotPerm.append_right (cpKernel cp)
  have hband :
      P.map.FaceBand (CProg.rotateLeft n (cpRing cp) ++ cpKernel cp) x :=
    (Hypermap.FaceBand.perm (G := P.map) hfullPerm).2
      (hcover x)
  simpa [cpMapCover, P, cpmap, step, hring, cpKernel]
    using hband

theorem cpMapCover_of_config :
    ∀ {cp : CProg}, CProg.config cp = true → cpMapCover cp :=
  ConfigProgram.property_of_config cpMapCover
    (fun {n cp} hcfg hcover =>
      cpMapCover_rotate_of_ringCycle (cp := cp) (n := n)
        (cpRingCycle_of_config hcfg) hcover)
    (by
      have hproper : (cpmap []).ProperRingHead := by
        simpa [cpmap] using base_properRingHead
      exact cpMapCover_y_of_ring_kernel_eq
        (cp := []) cpMapCover_nil
        (by
          simpa [cpmap, step] using
            cpRing_y_eq_of_ringCycle (cp := []) cpRingCycle_nil hproper)
        (by simpa using cpKernel_y_eq (cp := [])))
    (fun hcfg hcover => cpMapCover_y_of_config hcfg hcover)
    (fun hcfg hcover => cpMapCover_h_of_config hcfg hcover)

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
