
import Schematic.Math.GraphTheory.Embedding.Coloring
import Schematic.Math.GraphTheory.Embedding.Geometry

/-!
Minimal counterexamples for the hypermap four-colour theorem.

This is the Lean-side counterpart of the `minimal_counter_example` record in
Gonthier's `coloring.v`.  The hard downstream theorem is that no such object
exists; this file only packages the induction hypothesis used by the later
cube/reducibility/unavoidability development.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

/-- A minimal counterexample to the finite hypermap four-colour theorem. -/
structure MinimalCounterexample (G : Hypermap.{u}) : Prop where
  geometry : G.PlanarBridgelessPlainPrecubic
  noncolorable : Not G.FourColorable
  minimal :
    ∀ G' : Hypermap.{u},
      G'.PlanarBridgelessPlainPrecubic →
        Fintype.card G'.Dart < Fintype.card G.Dart →
          G'.FourColorable

namespace MinimalCounterexample

variable {G : Hypermap.{u}}

theorem planar
    (hG : G.MinimalCounterexample) :
    G.EulerPlanar :=
  hG.geometry.base.base.planar

theorem bridgeless
    (hG : G.MinimalCounterexample) :
    G.Bridgeless :=
  hG.geometry.base.base.bridgeless

theorem plain
    (hG : G.MinimalCounterexample) :
    G.Plain :=
  hG.geometry.base.plain

theorem precubic
    (hG : G.MinimalCounterexample) :
    G.Precubic :=
  hG.geometry.precubic

theorem node_ne_self
    (hG : G.MinimalCounterexample)
    (x : G.Dart) :
    G.node x ≠ x :=
  Hypermap.Bridgeless.node_ne_self (G := G) hG.bridgeless x

theorem not_fourColorable
    (hG : G.MinimalCounterexample) :
    Not G.FourColorable :=
  hG.noncolorable

theorem colorable_of_smaller
    (hG : G.MinimalCounterexample)
    (G' : Hypermap.{u})
    (hG' : G'.PlanarBridgelessPlainPrecubic)
    (hcard : Fintype.card G'.Dart < Fintype.card G.Dart) :
    G'.FourColorable :=
  hG.minimal G' hG' hcard

theorem false_of_fourColorable
    (hG : G.MinimalCounterexample)
    (hcolor : G.FourColorable) :
    False :=
  hG.noncolorable hcolor

theorem mirror
    (hG : G.MinimalCounterexample) :
    G.mirror.MinimalCounterexample where
  geometry := hG.geometry.mirror
  noncolorable := by
    intro hcolor
    exact hG.noncolorable (G.fourColorable_of_mirror_fourColorable hcolor)
  minimal := by
    intro G' hG' hcard
    exact hG.minimal G' hG' (by simpa [Hypermap.mirror] using hcard)

theorem mirror_iff :
    G.mirror.MinimalCounterexample ↔ G.MinimalCounterexample := by
  constructor
  · intro hG
    have hm := hG.mirror
    convert hm using 1
    exact (Hypermap.mirror_mirror G).symm
  · exact mirror

theorem iso
    {H : Hypermap.{u}}
    (φ : Iso G H)
    (hG : G.MinimalCounterexample) :
    H.MinimalCounterexample where
  geometry := φ.planarBridgelessPlainPrecubic hG.geometry
  noncolorable := by
    intro hcolor
    exact hG.noncolorable ((φ.fourColorable_iff).mpr hcolor)
  minimal := by
    intro G' hG' hcard
    exact hG.minimal G' hG' (by
      rwa [φ.dart_card_eq])

theorem iso_iff
    {H : Hypermap.{u}}
    (φ : Iso G H) :
    G.MinimalCounterexample ↔ H.MinimalCounterexample := by
  constructor
  · exact iso φ
  · intro hH
    exact iso φ.symm hH

end MinimalCounterexample

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
