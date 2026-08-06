import FourColorTheorem.FourColor.Reducibility.ProgramMap.Configuration.RingCycle

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap
namespace ConfigProgram

/-- Boundary geometry and list identities shared by configuration proofs for an
`H` extension. -/
structure HBoundary (cp : CProg) : Prop where
  geometry : (cpmap cp).ConfigGeometry
  ringSize_gt_two : 2 < CProg.ringSize cp
  extendedRing :
    cpRing (CpStep.h :: cp) =
      (cpmap cp).h.map.node (cpmap cp).h.point ::
        (cpmap cp).h.point :: ((cpRing cp).drop 2).map (cpmap cp).hOld
  extendedKernel :
    cpKernel (CpStep.h :: cp) =
      ((cpmap cp).point :: cpKernel cp).map (cpmap cp).hOld
  oldRing :
    cpRing cp =
      (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point ::
        (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) ::
          (cpRing cp).drop 3
  dropTwo :
    (cpRing cp).drop 2 =
      (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) ::
        (cpRing cp).drop 3

theorem HBoundary.of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true) :
    HBoundary cp := by
  have hgeometry := cpmap_configGeometry_of_config hcfg
  have hsize2 := CProg.ringSize_gt_two_of_config hcfg
  have hsize1 : 1 < CProg.ringSize cp := by omega
  constructor
  · exact hgeometry
  · exact hsize2
  · exact cpRing_h_eq_of_ringCycle
      (cpRingCycle_of_config hcfg) hgeometry.proper hgeometry.long hsize2
  · exact cpKernel_h_eq_of_ringSize_gt_one hsize1
  · exact cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
      hsize2
  · exact cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two hsize2

end ConfigProgram
end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
