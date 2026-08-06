import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.H.NodeTransport

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
theorem hOld_onRing_implies_yOld_onRing
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : P.h.OnRing (P.hOld x)) :
    P.y.OnRing (P.yOld x) := by
  change PermReachable (Hypermap.extensionH P.map P.point).node
      ExtDart.new (Hypermap.extensionHOld P.map P.point x) at hx
  unfold Hypermap.extensionH Hypermap.extensionHOld at hx
  have hcode :=
    Hypermap.extensionNNodeOrbitCode_of_reachable
      (G := Hypermap.extensionY P.map P.point)
      (x0 := ExtDart.new) hx
  by_cases hlongY :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new
  · have hnodeY :
        (Hypermap.extensionY P.map P.point).node ExtDart.new =
          ExtDart.old ExtDart.newEdge :=
      Hypermap.extensionY_node_new (G := P.map) P.point
    by_cases hface :
        Hypermap.extensionYOld P.map P.point x =
          (Hypermap.extensionY P.map P.point).face
            ((Hypermap.extensionY P.map P.point).edge ExtDart.new)
    · have hbad :
          (some (PermOrbit.of
            (Hypermap.extensionY P.map P.point).node
            ((Hypermap.extensionY P.map P.point).node ExtDart.new)) :
            Option (Hypermap.extensionY P.map P.point).NodeOrbit) = none := by
        have hy_ne_new :
            Hypermap.extensionYOld P.map P.point x ≠
              (ExtDart.new :
                (Hypermap.extensionY P.map P.point).Dart) := by
          unfold Hypermap.extensionYOld
          simp
        simp [Hypermap.extensionNNodeOrbitCode, hlongY, hnodeY, hface]
          at hcode
      cases hbad
    · have horbit :
          PermOrbit.of (Hypermap.extensionY P.map P.point).node
              ((Hypermap.extensionY P.map P.point).node ExtDart.new) =
            PermOrbit.of (Hypermap.extensionY P.map P.point).node
              (Hypermap.extensionYOld P.map P.point x) := by
        have hpair := by
          simpa [Hypermap.extensionNNodeOrbitCode, hlongY,
            Hypermap.extensionYOld, hface] using hcode
        exact hpair.2
      have hY :
          PermReachable (Hypermap.extensionY P.map P.point).node
            ((Hypermap.extensionY P.map P.point).node ExtDart.new)
            (Hypermap.extensionYOld P.map P.point x) :=
        Quotient.exact horbit
      change PermReachable (Hypermap.extensionY P.map P.point).node
        ExtDart.new (Hypermap.extensionYOld P.map P.point x)
      exact PermReachable.trans (Hypermap.extensionY P.map P.point).node
        (PermReachable.forward (Hypermap.extensionY P.map P.point).node
          ExtDart.new) hY
  · have hbad :
        (none : Option (Hypermap.extensionY P.map P.point).NodeOrbit) =
          some (PermOrbit.of (Hypermap.extensionY P.map P.point).node
            (Hypermap.extensionYOld P.map P.point x)) := by
      simp [Hypermap.extensionNNodeOrbitCode, hlongY] at hcode
    cases hbad

theorem hOld_onRing_implies_onRing
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : P.h.OnRing (P.hOld x)) :
    P.OnRing x :=
  yOld_onRing_implies_onRing P
    (hOld_onRing_implies_yOld_onRing P hx)

theorem hOld_not_onRing_of_not_onRing
    (P : PointedHypermap) {x : P.map.Dart}
    (hx : ¬ P.OnRing x) :
    ¬ P.h.OnRing (P.hOld x) := by
  intro hh
  exact hx (hOld_onRing_implies_onRing P hh)

theorem hOld_injective (P : PointedHypermap) :
    Function.Injective P.hOld := by
  intro x y hxy
  change Hypermap.extensionHOld P.map P.point x =
      Hypermap.extensionHOld P.map P.point y at hxy
  simp only [Hypermap.extensionHOld, Hypermap.extensionYOld] at hxy
  injection hxy with hxy'
  injection hxy' with hxy''
  injection hxy'' with hxy'''

theorem hOld_ringAdj_iff
    (P : PointedHypermap) {x y : P.map.Dart} :
    P.h.map.RingAdj (P.hOld x) (P.hOld y) ↔
      P.map.RingAdj x y := by
  change (Hypermap.extensionH P.map P.point).RingAdj
      (Hypermap.extensionHOld P.map P.point x)
      (Hypermap.extensionHOld P.map P.point y) ↔
    P.map.RingAdj x y
  exact Hypermap.extensionHOld_ringAdj_iff
    (G := P.map) (x0 := P.point)

theorem hOld_ringAdj_of_ringAdj
    (P : PointedHypermap) {x y : P.map.Dart}
    (hxy : P.map.RingAdj x y) :
    P.h.map.RingAdj (P.hOld x) (P.hOld y) :=
  (hOld_ringAdj_iff P).2 hxy

theorem h_ringAdj_point_old_iff_faceBand
    (P : PointedHypermap) {y : P.map.Dart} :
    P.h.map.RingAdj P.h.point (P.hOld y) ↔
      Hypermap.extensionHNewEdgeBand P.map P.point y ∨
        P.map.FaceBand [P.point, P.map.node P.point] y := by
  change (Hypermap.extensionH P.map P.point).RingAdj
      ExtDart.new (Hypermap.extensionHOld P.map P.point y) ↔
    Hypermap.extensionHNewEdgeBand P.map P.point y ∨
      P.map.FaceBand [P.point, P.map.node P.point] y
  exact Hypermap.extensionH_ringAdj_new_old_iff_faceBand
    (G := P.map) P.point

theorem h_ringAdj_point_old_iff_faceBand_of_proper_long
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    {y : P.map.Dart} :
    P.h.map.RingAdj P.h.point (P.hOld y) ↔
      P.map.FaceBand [P.map.face (P.map.edge P.point), P.point,
        P.map.node P.point] y := by
  change (Hypermap.extensionH P.map P.point).RingAdj
      ExtDart.new (Hypermap.extensionHOld P.map P.point y) ↔
    P.map.FaceBand [P.map.face (P.map.edge P.point), P.point,
      P.map.node P.point] y
  exact Hypermap.extensionH_ringAdj_new_old_iff_faceBand_of_proper_long
    (G := P.map) P.point hproper hlong

theorem h_ringAdj_point_old_iff_faceBand_coq_of_proper_long
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    {y : P.map.Dart} :
    P.h.map.RingAdj P.h.point (P.hOld y) ↔
      P.map.FaceBand [P.map.node P.point, P.point,
        P.map.face (P.map.edge P.point)] y := by
  change (Hypermap.extensionH P.map P.point).RingAdj
      ExtDart.new (Hypermap.extensionHOld P.map P.point y) ↔
    P.map.FaceBand [P.map.node P.point, P.point,
      P.map.face (P.map.edge P.point)] y
  exact Hypermap.extensionH_ringAdj_new_old_iff_faceBand_coq_of_proper_long
    (G := P.map) P.point hproper hlong

theorem hOld_ringAdj_point_iff_faceBand_coq_of_plain_proper_long
    (P : PointedHypermap)
    (hplain : P.h.map.Plain)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    {x : P.map.Dart} :
    P.h.map.RingAdj (P.hOld x) P.h.point ↔
      P.map.FaceBand [P.map.node P.point, P.point,
        P.map.face (P.map.edge P.point)] x := by
  constructor
  · intro h
    exact (h_ringAdj_point_old_iff_faceBand_coq_of_proper_long
      P hproper hlong).1
      (Hypermap.RingAdj.symm_of_plain (G := P.h.map) hplain h)
  · intro h
    exact Hypermap.RingAdj.symm_of_plain (G := P.h.map) hplain
      ((h_ringAdj_point_old_iff_faceBand_coq_of_proper_long
        P hproper hlong).2 h)

end Schematic.Math.GraphTheory.FourColor.PointedHypermap
