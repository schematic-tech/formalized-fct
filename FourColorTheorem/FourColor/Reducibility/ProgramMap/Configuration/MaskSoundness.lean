import FourColorTheorem.FourColor.Reducibility.ProgramMap.Configuration.Cover

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpMaskAdjInvariant_y_of_tailSeparation_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (h : cpMaskAdjInvariant cp)
    (hsep : cpTailSeparation cp) :
    cpMaskAdjInvariant (CpStep.y :: cp) := by
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 1 < CProg.ringSize cp := by
    have hgt := CProg.ringSize_gt_two_of_config hcfg
    omega
  exact cpMaskAdjInvariant_y_of_tailSeparation
    h hgeom.proper
    (y_plain (cpmap cp) hgeom.plain)
    (y_bridgeless_of_proper (cpmap cp) hgeom.proper hgeom.bridgeless)
    hsize hsep

theorem cpMaskAdjInvariant_h_of_tailSeparation_config
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (h : cpMaskAdjInvariant cp)
    (hsep : cpTailSeparation cp) :
    cpMaskAdjInvariant (CpStep.h :: cp) := by
  have hgeom := cpmap_configGeometry_of_config hcfg
  have hsize : 2 < CProg.ringSize cp :=
    CProg.ringSize_gt_two_of_config hcfg
  exact cpMaskAdjInvariant_h_of_tailSeparation
    h hgeom.proper hgeom.long
    (h_plain (cpmap cp) hgeom.plain)
    (h_bridgeless_of_proper
      (cpmap cp) hgeom.proper hgeom.bridgeless)
    hsize hsep

theorem cpTailSeparation_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true) :
    cpTailSeparation cp :=
  cpTailSeparation_of_cpMapSimple_config hcfg
    (cpMapSimple_of_config hcfg)

theorem cpMaskAdjInvariant_of_config :
    ∀ {cp : CProg}, CProg.config cp = true → cpMaskAdjInvariant cp :=
  ConfigProgram.property_of_config cpMaskAdjInvariant
    (fun {n cp} _hcfg h => cpMaskAdjInvariant_rotate (cp := cp) (n := n) h)
    (by
      have hproper : (cpmap []).ProperRingHead := by
        simpa [cpmap] using base_properRingHead
      have hplainY : ((cpmap []).y).map.Plain := by
        simpa [cpmap] using y_plain base base_plain
      have hbridgeY : ((cpmap []).y).map.Bridgeless := by
        simpa [cpmap] using
          y_bridgeless_of_proper base base_properRingHead base_bridgeless
      have hsize : 1 < CProg.ringSize [] := by simp [CProg.ringSize]
      have hring :
          ∀ x : (cpmap []).map.Dart,
            x ∈ (cpRing []).drop 2 →
              ¬ (cpmap []).map.FaceBand
                [(cpmap []).point, (cpmap []).map.node (cpmap []).point] x := by
        intro x hx
        have hxEmpty : x ∈ ([] : List (cpmap []).map.Dart) := by
          simpa [cpRing, ringDarts, CProg.ringSize] using hx
        cases hxEmpty
      have hkernel :
          ∀ x : (cpmap []).map.Dart,
            x ∈ cpKernel [] →
              ¬ (cpmap []).map.FaceBand
                [(cpmap []).point, (cpmap []).map.node (cpmap []).point] x := by
        intro x hx
        cases hx
      exact cpMaskAdjInvariant_y_of_tail_lists_avoid
        (cp := []) cpMaskAdjInvariant_nil hproper hplainY hbridgeY
        hsize hring hkernel)
    (fun hcfg h => cpMaskAdjInvariant_y_of_tailSeparation_config
      hcfg h (cpTailSeparation_of_config hcfg))
    (fun hcfg h => cpMaskAdjInvariant_h_of_tailSeparation_config
      hcfg h (cpTailSeparation_of_config hcfg))

/-- Coq `cpmask_adj`, packaged for all proper masks of a configuration
program. -/
theorem cpMaskAdjSoundAllProper_of_config
    {cp : CProg}
    (hcfg : CProg.config cp = true) :
    cpMaskAdjSoundAllProper cp :=
  (cpMaskAdjInvariant_of_config hcfg).maskAdj

/-- Coq `cpmask_adj`: adjacency propagation computes exactly the face band of
all darts adjacent to the selected mask. -/
theorem cpMaskAdjSound_of_config
    {cp : CProg} {m : CfMask}
    (hcfg : CProg.config cp = true)
    (hm : CfMask.Proper cp m) :
    cpMaskAdjSound cp m :=
  cpMaskAdjSoundAllProper_of_config hcfg m hm

theorem cpmap_supportedGeometry_of_mapSupported
    {cp : CProg}
    (hcp : CProg.mapSupported cp = true) :
    (cpmap cp).SupportedGeometry :=
  cpmap?_supportedGeometry_of_mapSupported hcp
    (cpmap?_eq_some_cpmap_of_mapSupported hcp)

theorem cpmap_supportedGeometry_of_plainConnectedSupported
    {cp : CProg}
    (hcp : CProg.plainConnectedSupported cp = true) :
    (cpmap cp).SupportedGeometry :=
  cpmapPlainConnected?_supportedGeometry_of_plainConnectedSupported hcp
    (cpmapPlainConnected?_eq_some_cpmap_of_plainConnectedSupported hcp)

theorem cpmap_supportedGeometry_of_not_mem_a
    {cp : CProg}
    (hcp : CpStep.a ∉ cp) :
    (cpmap cp).SupportedGeometry :=
  cpmap_supportedGeometry_of_plainConnectedSupported
    (CProg.plainConnectedSupported_of_not_mem_a hcp)

theorem cpmap_supportedGeometry_of_cubic
    {cp : CProg}
    (hcp : CProg.cubic cp = true) :
    (cpmap cp).SupportedGeometry :=
  (cpmap_cubicGeometry_of_cubic hcp).supported

theorem cpmap_supportedGeometry_of_config
    {cp : CProg}
    (hcp : CProg.config cp = true) :
    (cpmap cp).SupportedGeometry :=
  (cpmap_configGeometry_of_config hcp).supported

end PointedHypermap

end FourColor
end Schematic.Math.GraphTheory
