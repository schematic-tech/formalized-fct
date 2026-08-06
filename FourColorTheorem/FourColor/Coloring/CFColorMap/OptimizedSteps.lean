import FourColorTheorem.FourColor.Coloring.CFColorMap.ConfigurationSemantics
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Program-level optimized `CpY` soundness, both Coq branches. -/
theorem ringTrace_cpRing_y_left
    {cp : CProg} (hcycle : cpRingCycle cp)
    {e : Color} {et : ColSeq}
    (htrace : (cpmap cp).map.RingTrace (cpRing cp) (e :: et))
    (he : e ≠ Color.zero) :
    (cpmap (CpStep.y :: cp)).map.RingTrace
      (cpRing (CpStep.y :: cp))
      (EdgePerm.p231 e :: EdgePerm.p312 e :: et) := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_y] using
    ringTrace_y_left hcycle (CProg.ringSize_pos cp) htrace he

theorem ringTrace_cpRing_y_right
    {cp : CProg} (hcycle : cpRingCycle cp)
    {e : Color} {et : ColSeq}
    (htrace : (cpmap cp).map.RingTrace (cpRing cp) (e :: et))
    (he : e ≠ Color.zero) :
    (cpmap (CpStep.y :: cp)).map.RingTrace
      (cpRing (CpStep.y :: cp))
      (EdgePerm.p312 e :: EdgePerm.p231 e :: et) := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_y] using
    ringTrace_y_right hcycle (CProg.ringSize_pos cp) htrace he

/-- Program-level optimized `CpH` soundness, matching its equal and unequal
head cases. -/
theorem ringTrace_cpRing_h_equal_left
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 1 < CProg.ringSize cp)
    {e : Color} {et : ColSeq}
    (htrace : (cpmap cp).map.RingTrace (cpRing cp) (e :: e :: et))
    (he : e ≠ Color.zero) :
    (cpmap (CpStep.h :: cp)).map.RingTrace
      (cpRing (CpStep.h :: cp))
      (EdgePerm.p231 e :: EdgePerm.p231 e :: et) := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_h] using
    ringTrace_h_equal_left hcycle hsize htrace he

theorem ringTrace_cpRing_h_equal_right
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 1 < CProg.ringSize cp)
    {e : Color} {et : ColSeq}
    (htrace : (cpmap cp).map.RingTrace (cpRing cp) (e :: e :: et))
    (he : e ≠ Color.zero) :
    (cpmap (CpStep.h :: cp)).map.RingTrace
      (cpRing (CpStep.h :: cp))
      (EdgePerm.p312 e :: EdgePerm.p312 e :: et) := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_h] using
    ringTrace_h_equal_right hcycle hsize htrace he

theorem ringTrace_cpRing_h_unequal
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 1 < CProg.ringSize cp)
    {e1 e2 : Color} {et : ColSeq}
    (htrace : (cpmap cp).map.RingTrace (cpRing cp) (e1 :: e2 :: et))
    (he1 : e1 ≠ Color.zero) (he2 : e2 ≠ Color.zero)
    (hne : e1 ≠ e2) :
    (cpmap (CpStep.h :: cp)).map.RingTrace
      (cpRing (CpStep.h :: cp)) (e2 :: e1 :: et) := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_h] using
    ringTrace_h_unequal hcycle hsize htrace he1 he2 hne


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
