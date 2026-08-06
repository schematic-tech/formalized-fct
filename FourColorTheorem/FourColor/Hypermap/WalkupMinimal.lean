
import FourColorTheorem.FourColor.Hypermap.Minimal
import Schematic.Math.GraphTheory.Embedding.WalkupGeometry

/-!
Minimal-counterexample accessors for Walkup transforms.

Coq's cubicity proof repeatedly applies the minimality field of a minimal
counterexample to one or two Walkup transforms.  This file packages the
cardinality descent part, and uses the proved Walkup `Precubic` preservation so
only the remaining planarity/bridgelessness/plainness obligations have to be
supplied by later files.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

namespace MinimalCounterexample

variable {G : Hypermap.{u}}

theorem fourColorable_walkupE
    (hG : G.MinimalCounterexample)
    (z : G.Dart)
    (hgeom : (G.walkupE z).PlanarBridgelessPlainPrecubic) :
    (G.walkupE z).FourColorable :=
  hG.colorable_of_smaller (G.walkupE z) hgeom
    (G.walkupE_dart_card_lt z)

theorem fourColorable_walkupE_of_geometry_parts
    (hG : G.MinimalCounterexample)
    (z : G.Dart)
    (hplanar : (G.walkupE z).EulerPlanar)
    (hbridgeless : (G.walkupE z).Bridgeless)
    (hplain : (G.walkupE z).Plain) :
    (G.walkupE z).FourColorable :=
  hG.fourColorable_walkupE z
    (G.walkupE_planarBridgelessPlainPrecubic_of_parts
      hG.precubic z hplanar hbridgeless hplain)

theorem fourColorable_walkupN
    (hG : G.MinimalCounterexample)
    (z : G.Dart)
    (hgeom : (G.walkupN z).PlanarBridgelessPlainPrecubic) :
    (G.walkupN z).FourColorable :=
  hG.colorable_of_smaller (G.walkupN z) hgeom
    (by
      rw [G.walkupN_dart_card]
      exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨z⟩) Nat.zero_lt_one)

theorem fourColorable_walkupF
    (hG : G.MinimalCounterexample)
    (z : G.Dart)
    (hgeom : (G.walkupF z).PlanarBridgelessPlainPrecubic) :
    (G.walkupF z).FourColorable :=
  hG.colorable_of_smaller (G.walkupF z) hgeom
    (by
      rw [G.walkupF_dart_card]
      exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨z⟩) Nat.zero_lt_one)

theorem fourColorable_walkupE_walkupE
    (hG : G.MinimalCounterexample)
    {z : G.Dart} (u : (G.walkupE z).Dart)
    (hgeom : ((G.walkupE z).walkupE u).PlanarBridgelessPlainPrecubic) :
    ((G.walkupE z).walkupE u).FourColorable :=
  hG.colorable_of_smaller ((G.walkupE z).walkupE u) hgeom
    ((G.walkupE z).walkupE_dart_card_lt u |>.trans
      (G.walkupE_dart_card_lt z))

theorem fourColorable_walkupE_walkupE_of_geometry_parts
    (hG : G.MinimalCounterexample)
    {z : G.Dart} (u : (G.walkupE z).Dart)
    (hplanar : ((G.walkupE z).walkupE u).EulerPlanar)
    (hbridgeless : ((G.walkupE z).walkupE u).Bridgeless)
    (hplain : ((G.walkupE z).walkupE u).Plain) :
    ((G.walkupE z).walkupE u).FourColorable :=
  hG.fourColorable_walkupE_walkupE u
    (G.walkupE_walkupE_planarBridgelessPlainPrecubic_of_parts
      hG.precubic u hplanar hbridgeless hplain)

end MinimalCounterexample

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
