
import FourColorTheorem.FourColor.Theorem.Combinatorial
import FourColorTheorem.FourColor.Theorem.Cube

/-!
Coq-style bridge from arbitrary planar bridgeless hypermaps to the local
plain/precubic hypermap four-colour theorem.

Coq's `four_color_hypermap` applies the main theorem to `cube G` and then
pulls the colouring back along `cube_colorable`. This file ports that
construction, including Euler-planarity and bridgelessness preservation.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

universe u

namespace Hypermap

/-- Coq theorem surface `four_color_hypermap`: arbitrary planar bridgeless
hypermaps are four-colourable. -/
def PlanarBridgelessFourColorTheorem : Prop :=
  ∀ G : Hypermap.{u}, G.PlanarBridgeless → G.FourColorable

namespace Cube

/-- Component-count statement for Coq `genus_cube`. -/
def ComponentCountPreservation : Prop :=
  ∀ G : Hypermap.{u},
    (hypermap (G := G)).componentCount = G.componentCount

/-- Planar-counting statement matching Coq `genus_cube` and `planar_cube`. -/
def EulerPlanarPreservation : Prop :=
  ∀ G : Hypermap.{u},
    G.EulerPlanar → (hypermap (G := G)).EulerPlanar

theorem eulerPlanarPreservation_of_componentCountPreservation
    (hcomp : ComponentCountPreservation.{u}) :
    EulerPlanarPreservation.{u} := by
  intro G hG
  exact eulerPlanar_of_componentCount_eq (G := G) (hcomp G) hG

theorem componentCountPreservation :
    ComponentCountPreservation.{u} := by
  intro G
  exact componentCount_eq (G := G)

theorem eulerPlanarPreservation :
    EulerPlanarPreservation.{u} :=
  eulerPlanarPreservation_of_componentCountPreservation
    componentCountPreservation

/-- Geometry preservation matching Coq `planar_cube` plus
`bridgeless_cube`. -/
def PlanarBridgelessPreservation : Prop :=
  ∀ G : Hypermap.{u},
    G.PlanarBridgeless → (hypermap (G := G)).PlanarBridgeless

theorem planarBridgelessPreservation_of_eulerPlanarPreservation
    (hplanar : EulerPlanarPreservation.{u}) :
    PlanarBridgelessPreservation.{u} := by
  intro G hG
  exact
    { planar := hplanar G hG.planar
      bridgeless := bridgeless_of_bridgeless (G := G) hG.bridgeless }

theorem planarBridgelessPreservation :
    PlanarBridgelessPreservation.{u} :=
  planarBridgelessPreservation_of_eulerPlanarPreservation
    eulerPlanarPreservation

theorem geometry_of_planarBridgeless
    (hpres : PlanarBridgelessPreservation.{u})
    {G : Hypermap.{u}}
    (hG : G.PlanarBridgeless) :
    (hypermap (G := G)).PlanarBridgelessPlainPrecubic where
  base := by
    exact
      { base := hpres G hG
        plain := plain (G := G) }
  precubic := precubic (G := G)

theorem fourColorable_of_planarBridgeless
    (hpres : PlanarBridgelessPreservation.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {G : Hypermap.{u}}
    (hG : G.PlanarBridgeless) :
    G.FourColorable :=
  fourColorable_pullback (G := G)
    (hfct (hypermap (G := G))
      (geometry_of_planarBridgeless (G := G) hpres hG))

theorem planarBridgelessFourColor_of_preservation
    (hpres : PlanarBridgelessPreservation.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u}) :
    PlanarBridgelessFourColorTheorem.{u} := by
  intro G hG
  exact fourColorable_of_planarBridgeless hpres hfct hG

theorem planarBridgelessFourColor_of_eulerPlanarPreservation
    (hplanar : EulerPlanarPreservation.{u})
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u}) :
    PlanarBridgelessFourColorTheorem.{u} :=
  planarBridgelessFourColor_of_preservation
    (planarBridgelessPreservation_of_eulerPlanarPreservation hplanar)
    hfct

theorem planarBridgelessFourColor
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{u}) :
    PlanarBridgelessFourColorTheorem.{u} :=
  planarBridgelessFourColor_of_preservation
    planarBridgelessPreservation
    hfct

end Cube

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
