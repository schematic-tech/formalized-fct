import FourColorTheorem.FourColor.Reducibility.ProgramMap.Configuration.HBoundary

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpMapSimple_y_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (hsimple : cpMapSimple cp) :
    cpMapSimple (CpStep.y :: cp) := by
  let P := cpmap cp
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 1 < CProg.ringSize cp := by
    have hgt := CProg.ringSize_gt_two_of_config hcfg
    omega
  have hringY :
      cpRing (CpStep.y :: cp) =
        P.y.map.node P.y.point :: P.y.point ::
          ((cpRing cp).drop 1).map P.yOld := by
    simpa [P] using
      cpRing_y_eq_of_ringCycle (cp := cp)
        (cpRingCycle_of_config hcfg) hgeom.proper
  have hkernelY :
      cpKernel (CpStep.y :: cp) = (cpKernel cp).map P.yOld := by
    simpa [P] using cpKernel_y_eq (cp := cp)
  have hfullOld :
      P.map.FaceSimple
        (P.map.node P.point :: ((cpRing cp).drop 1 ++ cpKernel cp)) := by
    have hsimple' : P.map.FaceSimple (cpRing cp ++ cpKernel cp) := by
      simpa [cpMapSimple, P] using hsimple
    rw [cpRing_eq_nodePoint_cons_drop_one cp] at hsimple'
    simpa only [List.cons_append] using hsimple'
  have hnodeOld :
      ∀ y,
        y ∈ (cpRing cp).drop 1 ++ cpKernel cp →
          ¬ PermReachable P.map.face (P.map.node P.point) y :=
    (List.pairwise_cons.mp hfullOld).1
  have htailOld :
      P.map.FaceSimple ((cpRing cp).drop 1 ++ cpKernel cp) :=
    (List.pairwise_cons.mp hfullOld).2
  have htailMap :
      P.y.map.FaceSimple
        (((cpRing cp).drop 1 ++ cpKernel cp).map P.yOld) :=
    (Hypermap.FaceSimple.map_iff
      (G := P.map) (H := P.y.map) (f := P.yOld)
      (fun x y => yOld_faceReachable_iff P)).2 htailOld
  have htarget :
      P.y.map.FaceSimple
        (P.y.map.node P.y.point :: P.y.point ::
          (((cpRing cp).drop 1 ++ cpKernel cp).map P.yOld)) := by
    rw [Hypermap.FaceSimple]
    refine List.Pairwise.cons ?hnode ?htail
    · intro y hy hreach
      rcases List.mem_cons.mp hy with rfl | hyOld
      · exact y_not_faceReachable_point_node_point P
          (PermReachable.symm P.y.map.face hreach)
      · rcases List.mem_map.mp hyOld with ⟨x, hx, rfl⟩
        exact hnodeOld x hx
          ((y_faceReachable_node_point_old_iff P).1 hreach)
    · refine List.Pairwise.cons ?hpoint ?hmap
      · intro y hy hreach
        rcases List.mem_map.mp hy with ⟨x, _hx, rfl⟩
        exact y_not_faceReachable_point_old P x hreach
      · simpa [Hypermap.FaceSimple] using htailMap
  have htarget' :
      P.y.map.FaceSimple
        (P.y.map.node P.y.point :: P.y.point ::
          ((cpRing cp).drop 1).map P.yOld ++
            (cpKernel cp).map P.yOld) := by
    simpa [List.map_append] using htarget
  simpa [cpMapSimple, P, hringY, hkernelY, List.cons_append]
    using htarget'

theorem cpMapSimple_h_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (hsimple : cpMapSimple cp) :
    cpMapSimple (CpStep.h :: cp) := by
  let P := cpmap cp
  let faceEdge := P.map.face (P.map.edge P.point)
  let source := (cpRing cp).drop 2 ++ (P.point :: cpKernel cp)
  have hboundary := ConfigProgram.HBoundary.of_config hcfg
  have hgeom := hboundary.geometry
  have hringH := hboundary.extendedRing
  have hkernelH := hboundary.extendedKernel
  have hringOld := hboundary.oldRing
  have hdrop2 := hboundary.dropTwo
  have hfullOld :
      P.map.FaceSimple
        (P.map.node P.point :: P.point :: faceEdge ::
          ((cpRing cp).drop 3 ++ cpKernel cp)) := by
    have hsimple' : P.map.FaceSimple (cpRing cp ++ cpKernel cp) := by
      simpa [cpMapSimple, P] using hsimple
    rw [hringOld] at hsimple'
    simpa only [List.cons_append] using hsimple'
  have hnodeOld :
      ∀ y,
        y ∈ P.point :: faceEdge :: ((cpRing cp).drop 3 ++ cpKernel cp) →
          ¬ PermReachable P.map.face (P.map.node P.point) y :=
    (List.pairwise_cons.mp hfullOld).1
  have htailOld :
      P.map.FaceSimple
        (P.point :: faceEdge :: ((cpRing cp).drop 3 ++ cpKernel cp)) :=
    (List.pairwise_cons.mp hfullOld).2
  have hsourcePerm :
      source.Perm
        (P.point :: faceEdge :: ((cpRing cp).drop 3 ++ cpKernel cp)) := by
    dsimp [source]
    rw [hdrop2]
    simpa [List.cons_append, List.append_assoc] using
      (List.perm_middle
        (a := P.point)
        (l₁ := faceEdge :: (cpRing cp).drop 3)
        (l₂ := cpKernel cp))
  have hsourceOld : P.map.FaceSimple source :=
    Hypermap.FaceSimple.perm (G := P.map) hsourcePerm.symm htailOld
  have hsourceMap :
      P.h.map.FaceSimple (source.map P.hOld) :=
    (Hypermap.FaceSimple.map_iff
      (G := P.map) (H := P.h.map) (f := P.hOld)
      (fun x y => hOld_faceReachable_iff P)).2 hsourceOld
  have htarget :
      P.h.map.FaceSimple
        (P.h.map.node P.h.point :: P.h.point :: source.map P.hOld) := by
    rw [Hypermap.FaceSimple]
    refine List.Pairwise.cons ?hnode ?htail
    · intro y hy hreach
      rcases List.mem_cons.mp hy with rfl | hyOld
      · exact h_not_faceReachable_point_node_point P hgeom.proper
          (PermReachable.symm P.h.map.face hreach)
      · rcases List.mem_map.mp hyOld with ⟨x, hx, rfl⟩
        exact hnodeOld x ((hsourcePerm.mem_iff).1 hx)
          ((h_faceReachable_node_point_old_iff P hgeom.proper).1 hreach)
    · refine List.Pairwise.cons ?hpoint ?hmap
      · intro y hy hreach
        rcases List.mem_map.mp hy with ⟨x, _hx, rfl⟩
        exact h_not_faceReachable_point_old P x hreach
      · simpa [Hypermap.FaceSimple] using hsourceMap
  have htarget' :
      P.h.map.FaceSimple
        (P.h.map.node P.h.point :: P.h.point ::
          ((cpRing cp).drop 2).map P.hOld ++
            (P.point :: cpKernel cp).map P.hOld) := by
    simpa [source, List.map_append] using htarget
  simpa [cpMapSimple, P, hringH, hkernelH, List.cons_append]
    using htarget'

theorem cpMapSimple_rotate_of_ringCycle
    {cp : CProg} {n : Nat}
    (hcycle : cpRingCycle cp)
    (hsimple : cpMapSimple cp) :
    cpMapSimple (CpStep.rotate n :: cp) := by
  let P := cpmap cp
  have hring :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle (cp := cp) (n := n) hcycle
  have hrotPerm :
      (CProg.rotateLeft n (cpRing cp)).Perm (cpRing cp) := by
    exact CProg.perm_rotateLeft n (cpRing cp)
  have hfullPerm :
      (CProg.rotateLeft n (cpRing cp) ++ cpKernel cp).Perm
        (cpRing cp ++ cpKernel cp) :=
    hrotPerm.append_right (cpKernel cp)
  have htarget :
      P.map.FaceSimple (CProg.rotateLeft n (cpRing cp) ++ cpKernel cp) :=
    Hypermap.FaceSimple.perm (G := P.map) hfullPerm.symm
      (by simpa [cpMapSimple, P] using hsimple)
  simpa [cpMapSimple, P, cpmap, step, hring, cpKernel]
    using htarget

theorem cpMapSimple_of_config :
    ∀ {cp : CProg}, CProg.config cp = true → cpMapSimple cp :=
  ConfigProgram.property_of_config cpMapSimple
    (fun {n cp} hcfg hsimple =>
      cpMapSimple_rotate_of_ringCycle (cp := cp) (n := n)
        (cpRingCycle_of_config hcfg) hsimple)
    (by
      have hproper : (cpmap []).ProperRingHead := by
        simpa [cpmap] using base_properRingHead
      have hringY :
          cpRing [CpStep.y] =
            (cpmap [CpStep.y]).map.node (cpmap [CpStep.y]).point ::
              (cpmap [CpStep.y]).point ::
                ((cpRing []).drop 1).map (fun x => (cpmap []).yOld x) := by
        simpa [cpmap, step] using
          cpRing_y_eq_of_ringCycle (cp := []) cpRingCycle_nil hproper
      have hdrop :
          ((cpRing []).drop 1).map (fun x => (cpmap []).yOld x) =
            [base.yOld base.point] := by
        change ((ringDarts base 2).drop 1).map (fun x => base.yOld x) =
          [base.yOld base.point]
        rw [show (2 : Nat) = 0 + 2 by rfl, ringDarts_succ_succ]
        simp [base]
      have hbaseNodePoint :
          ¬ PermReachable base.map.face
            (base.map.node base.point) base.point := by
        change ¬ PermReachable (Equiv.refl Bool) false true
        intro h
        have heq : false = true := permReachable_refl_eq h
        cases heq
      have htarget :
          base.y.map.FaceSimple
            (base.y.map.node base.y.point :: base.y.point ::
              [base.yOld base.point]) := by
        rw [Hypermap.FaceSimple]
        refine List.Pairwise.cons ?hnode ?htail
        · intro y hy hreach
          rcases List.mem_cons.mp hy with rfl | hyOld
          · exact y_not_faceReachable_point_node_point base
              (PermReachable.symm base.y.map.face hreach)
          · have hyEq : y = base.yOld base.point := by
              simpa using List.mem_singleton.mp hyOld
            subst y
            exact hbaseNodePoint
              ((y_faceReachable_node_point_old_iff base).1 hreach)
        · refine List.Pairwise.cons ?hpoint ?hmap
          · intro y hy hreach
            have hyEq : y = base.yOld base.point := by
              simpa using List.mem_singleton.mp hy
            subst y
            exact y_not_faceReachable_point_old base base.point hreach
          · simp
      simpa [cpMapSimple, hringY, cpKernel_y_eq, cpKernel_nil,
        hdrop, cpmap, step, List.cons_append] using htarget)
    (fun hcfg hsimple => cpMapSimple_y_of_config hcfg hsimple)
    (fun hcfg hsimple => cpMapSimple_h_of_config hcfg hsimple)

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
