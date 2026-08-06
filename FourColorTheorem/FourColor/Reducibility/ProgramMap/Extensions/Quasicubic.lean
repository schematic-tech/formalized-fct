import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.N
import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.H
import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.U

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
theorem y_quasicubic
    (P : PointedHypermap)
    (hP : P.Quasicubic) :
    P.y.Quasicubic := by
  change P.u.n.Quasicubic
  exact n_quasicubic P.u (u_properRingHead P) (u_quasicubic P hP)

theorem h_quasicubic
    (P : PointedHypermap)
    (hP : P.Quasicubic) :
    P.h.Quasicubic := by
  change P.y.n.Quasicubic
  exact n_quasicubic P.y (y_properRingHead P) (y_quasicubic P hP)

theorem uOld_ringAdj_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    P.u.map.RingAdj (P.uOld x) (P.uOld y) ↔
      P.map.RingAdj x y := by
  change (Hypermap.extensionU P.map P.point).RingAdj
      (ExtDart.old x) (ExtDart.old y) ↔ P.map.RingAdj x y
  exact Hypermap.extensionU_ringAdj_old_iff
    (G := P.map) (x0 := P.point)

theorem uOld_ringAdj_of_ringAdj
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.u.map.RingAdj (P.uOld x) (P.uOld y) :=
  (uOld_ringAdj_iff P).2 hxy

theorem uOld_reachable_of_reachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.Reachable x y) :
    P.u.map.Reachable (P.uOld x) (P.uOld y) := by
  change (Hypermap.extensionU P.map P.point).Reachable
    (ExtDart.old x) (ExtDart.old y)
  exact Hypermap.extensionU_old_reachable_of_reachable
    (G := P.map) (x0 := P.point) hxy


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
