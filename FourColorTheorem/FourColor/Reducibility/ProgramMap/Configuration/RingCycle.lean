import FourColorTheorem.FourColor.Reducibility.ProgramMap.Geometry

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpRingCycle_of_config :
    ∀ {cp : CProg}, CProg.config cp = true → cpRingCycle cp :=
  ConfigProgram.property_of_config cpRingCycle
    (fun {n cp} _hcfg hcycle => cpRingCycle_rotate (cp := cp) (n := n) hcycle)
    (by
      have hproper : (cpmap []).ProperRingHead := by
        simpa [cpmap] using base_properRingHead
      have hsize : 1 < CProg.ringSize [] := by simp [CProg.ringSize]
      exact cpRingCycle_y cpRingCycle_nil hproper hsize)
    (fun {s cp} hcfg hcycle => by
      have hgeom := cpmap_configGeometry_of_config hcfg
      have hsize : 1 < CProg.ringSize (s :: cp) := by
        have hgt := CProg.ringSize_gt_two_of_config hcfg
        omega
      exact cpRingCycle_y hcycle hgeom.proper hsize)
    (fun {cp} hcfg hcycle => by
      have hgeom := cpmap_configGeometry_of_config hcfg
      exact cpRingCycle_h hcycle hgeom.proper hgeom.long
        (CProg.ringSize_gt_two_of_config hcfg))

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
