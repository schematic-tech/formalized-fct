import FourColorTheorem.FourColor.Coloring.KempeMap.ColoringExtension

/-!
Planarity and plainness of the Kempe reduction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

theorem kempeReduction_eulerPlanar
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hplanar : G.EulerPlanar) :
    (G.kempeReduction z hplain).EulerPlanar :=
  Unavoidability.walkupE_eulerPlanar_of_eulerPlanar
    (G.walkupN z) (G.kempeEdgeDart z hplain)
    (Unavoidability.walkupN_eulerPlanar_of_eulerPlanar G z hplanar)

theorem kempeReduction_plain
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    (G.kempeReduction z hplain).Plain := by
  intro x
  constructor
  · apply G.kempeProjection_injective z hplain
    rw [G.kempeProjection_edge, G.kempeProjection_edge,
      Plain.edge_edge (G := G) hplain]
  · intro hfixed
    have h := congrArg (G.kempeProjection z hplain) hfixed
    rw [G.kempeProjection_edge] at h
    exact Plain.edge_ne (G := G) hplain _ h


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
