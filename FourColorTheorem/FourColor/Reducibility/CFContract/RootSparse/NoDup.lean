import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Helpers

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

private theorem nodup_insertEdges_cpRing_contractDarts_y_nil :
    ((cpmap [CpStep.y]).map.insertEdges
      (cpRing [CpStep.y] ++ cpContractDarts [CpStep.y])).Nodup := by
  let P := cpmap []
  have hbase : (P.map.insertEdges [P.point]).Nodup := by
    change (cpmap0.insertEdges [true]).Nodup
    decide
  have hfresh := CFContract.Internal.insertEdges_y_fresh P [P.point] hbase
  have hproper : P.ProperRingHead := by
    simpa [P, cpmap] using base_properRingHead
  have hring :
      cpRing [CpStep.y] =
        P.y.map.node P.y.point :: P.y.point :: [P.yOld P.point] := by
    have h := cpRing_y_eq_of_ringCycle
      (cp := []) cpRingCycle_nil hproper
    simpa [P, cpRing_nil] using h
  rw [hring, cpContractDarts_y_nil]
  change
    ((cpmap [CpStep.y]).map.insertEdges
      [P.y.map.node P.y.point, P.y.point, P.yOld P.point]).Nodup
  simpa [P, cpmap, step] using hfresh

/-- Coq `uniq_ctrenum`: the ring and kernel-edge transversal, with both
orientations of every represented edge, is duplicate-free. -/
theorem nodup_insertEdges_cpRing_contractDarts :
    ∀ {cp : CProg}, CProg.config cp = true →
      ((cpmap cp).map.insertEdges (cpRing cp ++ cpContractDarts cp)).Nodup
  | [], hcfg => by
      simp [CProg.config] at hcfg
  | CpStep.rotate n :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      have ih := nodup_insertEdges_cpRing_contractDarts htail
      have hring :
          cpRing (CpStep.rotate n :: cp) =
            CProg.rotateLeft n (cpRing cp) :=
        cpRing_rotate_of_ringCycle
          (n := n) (cpRingCycle_of_config htail)
      have hringPerm :
          (cpRing (CpStep.rotate n :: cp)).Perm (cpRing cp) := by
        rw [hring]
        exact CProg.perm_rotateLeft n (cpRing cp)
      have hfull :
          (cpRing (CpStep.rotate n :: cp) ++
              cpContractDarts (CpStep.rotate n :: cp)).Perm
            (cpRing cp ++ cpContractDarts cp) := by
        simpa using hringPerm.append_right (cpContractDarts cp)
      exact
        ((cpmap cp).map.insertEdges_perm hfull).nodup_iff.mpr ih
  | CpStep.reverseRotate :: cp, hcfg => by
      simp [CProg.config] at hcfg
  | CpStep.y :: [], _hcfg =>
      nodup_insertEdges_cpRing_contractDarts_y_nil
  | CpStep.y :: s :: cp, hcfg => by
      have htail : CProg.config (s :: cp) = true := by
        simpa [CProg.config] using hcfg
      let P := cpmap (s :: cp)
      let oldContract := cpContractDarts (s :: cp)
      let source :=
        (cpRing (s :: cp)).drop 1 ++
          P.map.node P.point :: oldContract
      have hsourcePerm :
          source.Perm (cpRing (s :: cp) ++ oldContract) := by
        have h := List.perm_middle
          (a := P.map.node P.point)
          (l₁ := (cpRing (s :: cp)).drop 1)
          (l₂ := oldContract)
        rw [cpRing_eq_nodePoint_cons_drop_one (s :: cp)]
        simpa [source, P, List.cons_append] using h
      have hsource : (P.map.insertEdges source).Nodup := by
        exact (P.map.insertEdges_perm hsourcePerm).nodup_iff.mpr
          (nodup_insertEdges_cpRing_contractDarts htail)
      have hgeom := cpmap_configGeometry_of_config htail
      have hring :
          cpRing (CpStep.y :: s :: cp) =
            P.y.map.node P.y.point :: P.y.point ::
              ((cpRing (s :: cp)).drop 1).map P.yOld := by
        simpa [P] using
          cpRing_y_eq_of_ringCycle
            (cp := s :: cp) (cpRingCycle_of_config htail) hgeom.proper
      have hlist :
          cpRing (CpStep.y :: s :: cp) ++
              cpContractDarts (CpStep.y :: s :: cp) =
            P.y.map.node P.y.point :: P.y.point :: source.map P.yOld := by
        rw [hring, cpContractDarts_y_cons]
        dsimp [source, oldContract, P]
        have htail :=
          (List.map_append
            (f := (cpmap (s :: cp)).yOld)
            (l₁ := (cpRing (s :: cp)).drop 1)
            (l₂ := (cpmap (s :: cp)).map.node (cpmap (s :: cp)).point ::
              cpContractDarts (s :: cp))).symm
        exact congrArg
          (fun zs =>
            (cpmap (CpStep.y :: s :: cp)).map.node
                (cpmap (CpStep.y :: s :: cp)).point ::
              (cpmap (CpStep.y :: s :: cp)).point :: zs)
          (by simpa only [List.map_cons] using htail)
      rw [hlist]
      simpa [P, cpmap, step] using
        CFContract.Internal.insertEdges_y_fresh P source hsource
  | CpStep.h :: cp, hcfg => by
      have htail : CProg.config cp = true := by
        simpa [CProg.config] using hcfg
      let P := cpmap cp
      let oldContract := cpContractDarts cp
      let source :=
        (cpRing cp).drop 2 ++
          P.map.node P.point :: P.point :: oldContract
      have hsize : 1 < CProg.ringSize cp := by
        have hgt := CProg.ringSize_gt_two_of_config htail
        omega
      have hsourcePerm :
          source.Perm (cpRing cp ++ oldContract) := by
        have hswap :=
          (List.perm_append_comm :
            ((cpRing cp).drop 2 ++ [P.map.node P.point, P.point]).Perm
              ([P.map.node P.point, P.point] ++ (cpRing cp).drop 2))
        have hswap' := hswap.append_right oldContract
        rw [cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
          (cp := cp) hsize]
        simpa [source, P, List.cons_append, List.append_assoc] using hswap'
      have hsource : (P.map.insertEdges source).Nodup := by
        exact (P.map.insertEdges_perm hsourcePerm).nodup_iff.mpr
          (nodup_insertEdges_cpRing_contractDarts htail)
      have hgeom := cpmap_configGeometry_of_config htail
      have hfresh :=
        CFContract.Internal.insertEdges_h_fresh P source hgeom.proper hsource
      have hring :
          cpRing (CpStep.h :: cp) =
            P.h.map.node P.h.point :: P.h.point ::
              ((cpRing cp).drop 2).map P.hOld := by
        simpa [P] using
          cpRing_h_eq_of_ringCycle
            (cp := cp) (cpRingCycle_of_config htail)
            hgeom.proper hgeom.long
            (CProg.ringSize_gt_two_of_config htail)
      let crossbar := P.h.map.face P.h.point
      have htailPerm :
          (((cpRing cp).drop 2).map P.hOld ++
              crossbar ::
                (P.map.node P.point :: P.point :: oldContract).map P.hOld).Perm
            (crossbar :: source.map P.hOld) := by
        have h := List.perm_middle
          (a := crossbar)
          (l₁ := ((cpRing cp).drop 2).map P.hOld)
          (l₂ := (P.map.node P.point :: P.point :: oldContract).map P.hOld)
        simpa [source, List.map_append, List.cons_append,
          List.append_assoc] using h
      have hfullPerm :
          (cpRing (CpStep.h :: cp) ++
              cpContractDarts (CpStep.h :: cp)).Perm
            (P.h.map.node P.h.point :: P.h.point ::
              crossbar :: source.map P.hOld) := by
        rw [hring, cpContractDarts_h]
        change
          (P.h.map.node P.h.point :: P.h.point ::
              (((cpRing cp).drop 2).map P.hOld ++
                crossbar ::
                  (P.map.node P.point :: P.point :: oldContract).map P.hOld)).Perm
            (P.h.map.node P.h.point :: P.h.point ::
              crossbar :: source.map P.hOld)
        exact (htailPerm.cons P.h.point).cons (P.h.map.node P.h.point)
      exact
        ((cpmap (CpStep.h :: cp)).map.insertEdges_perm hfullPerm).nodup_iff.mpr
          (by simpa [P, cpmap, step] using hfresh)
  | CpStep.u :: cp, hcfg => by
      simp [CProg.config] at hcfg
  | CpStep.k :: cp, hcfg => by
      simp [CProg.config] at hcfg
  | CpStep.a :: cp, hcfg => by
      simp [CProg.config] at hcfg


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
