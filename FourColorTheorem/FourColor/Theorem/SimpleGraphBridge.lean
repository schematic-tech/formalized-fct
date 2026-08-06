import FourColorTheorem.FourColor.SimpleGraphColoring
import FourColorTheorem.FourColor.Theorem.Combinatorial

/-!
Bridge interface from finite graph colourings to the hypermap four-colour
theorem.

The Coq proof colours maps/hypermaps.  The paper-facing statements in this
repository use `SimpleGraph.Colorable`.  This file contains the non-geometric
part of that bridge: once a graph has been represented by a geometric hypermap
in a way that pulls every hypermap face-colouring back to a vertex-colouring of
the graph, the hypermap four-colour theorem immediately gives a
`SimpleGraph.Colorable 4` proof.

The geometric construction is supplied by `Schematic.Math.GraphTheory.Embedding` and
assembled with this transfer interface in `FourColorTheorem.PlanarBridge`.
-/

namespace Schematic.Math.GraphTheory




open SimpleGraph

namespace FourColor

universe u v

private def transferredColoring
    {V : Type u} {D : Type v} {G : SimpleGraph V}
    {Valid : (D → Color) → Prop}
    (vertexColor : (D → Color) → V → Color)
    (vertexColor_valid :
      ∀ {k : D → Color}, Valid k →
        ∀ {x y : V}, G.Adj x y → vertexColor k x ≠ vertexColor k y)
    {k : D → Color} (hk : Valid k) :
    G.Coloring Color :=
  SimpleGraph.Coloring.mk (vertexColor k) (vertexColor_valid hk)

private theorem colorable_four_of_transferred_hypermap_coloring
    {V : Type u} {G : SimpleGraph V} {H : Hypermap.{v}}
    (vertexColor : (H.Dart → Color) → V → Color)
    (vertexColor_valid :
      ∀ {k : H.Dart → Color}, H.Coloring k →
        ∀ {x y : V}, G.Adj x y → vertexColor k x ≠ vertexColor k y)
    (hmap : H.FourColorable) :
    G.Colorable 4 := by
  rw [colorable_four_iff_coloring_Color]
  rcases hmap with ⟨k, hk⟩
  exact ⟨transferredColoring vertexColor vertexColor_valid hk⟩

/-- A concrete hypermap representation of a simple graph sufficient for
transferring a map four-colouring back to a vertex four-colouring.

The fields intentionally expose only the transfer data needed by the theorem
below. -/
structure SimpleGraphHypermapBridge
    {V : Type u} (G : SimpleGraph V) where
  map : Hypermap.{v}
  geometry : map.PlanarBridgelessPlainPrecubic
  vertexColor : (map.Dart → Color) → V → Color
  vertexColor_valid :
    ∀ {k : map.Dart → Color}, map.Coloring k →
      ∀ {x y : V}, G.Adj x y → vertexColor k x ≠ vertexColor k y

namespace SimpleGraphHypermapBridge

variable {V : Type u} {G : SimpleGraph V}

/-- Pull a hypermap colouring through the bridge to a graph colouring by the
four-colour palette used in the hypermap development. -/
def coloring
    (B : SimpleGraphHypermapBridge.{u, v} G)
    {k : B.map.Dart → Color}
    (hk : B.map.Coloring k) :
    G.Coloring Color :=
  transferredColoring B.vertexColor B.vertexColor_valid hk

theorem colorable_four_of_fourColorable
    (B : SimpleGraphHypermapBridge.{u, v} G)
    (hmap : B.map.FourColorable) :
    G.Colorable 4 :=
  colorable_four_of_transferred_hypermap_coloring
    B.vertexColor B.vertexColor_valid hmap

theorem colorable_four_of_hypermapFourColor
    (B : SimpleGraphHypermapBridge.{u, v} G)
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v}) :
    G.Colorable 4 :=
  B.colorable_four_of_fourColorable (hfct B.map B.geometry)

end SimpleGraphHypermapBridge

/-- Existence of a concrete hypermap bridge for a simple graph. -/
def HasHypermapBridge
    {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (SimpleGraphHypermapBridge.{u, v} G)

theorem colorable_four_of_hasHypermapBridge
    {V : Type u} {G : SimpleGraph V}
    (hfct : CombinatorialFourColor.HypermapFourColorTheorem.{v})
    (hbridge : HasHypermapBridge.{u, v} G) :
    G.Colorable 4 := by
  rcases hbridge with ⟨B⟩
  exact B.colorable_four_of_hypermapFourColor hfct

/-- A concrete representation of a simple graph by an arbitrary planar
bridgeless hypermap.  This is the Coq-facing bridge shape before the `cube`
construction makes the hypermap plain and precubic. -/
structure SimpleGraphPlanarHypermapBridge
    {V : Type u} (G : SimpleGraph V) where
  map : Hypermap.{v}
  geometry : map.PlanarBridgeless
  vertexColor : (map.Dart → Color) → V → Color
  vertexColor_valid :
    ∀ {k : map.Dart → Color}, map.Coloring k →
      ∀ {x y : V}, G.Adj x y → vertexColor k x ≠ vertexColor k y

namespace SimpleGraphPlanarHypermapBridge

variable {V : Type u} {G : SimpleGraph V}

def coloring
    (B : SimpleGraphPlanarHypermapBridge.{u, v} G)
    {k : B.map.Dart → Color}
    (hk : B.map.Coloring k) :
    G.Coloring Color :=
  transferredColoring B.vertexColor B.vertexColor_valid hk

theorem colorable_four_of_fourColorable
    (B : SimpleGraphPlanarHypermapBridge.{u, v} G)
    (hmap : B.map.FourColorable) :
    G.Colorable 4 :=
  colorable_four_of_transferred_hypermap_coloring
    B.vertexColor B.vertexColor_valid hmap

theorem colorable_four_of_planarBridgelessFourColor
    (B : SimpleGraphPlanarHypermapBridge.{u, v} G)
    (hfct : ∀ H : Hypermap.{v}, H.PlanarBridgeless → H.FourColorable) :
    G.Colorable 4 :=
  B.colorable_four_of_fourColorable (hfct B.map B.geometry)

end SimpleGraphPlanarHypermapBridge

/-- Existence of a planar-bridgeless hypermap bridge for a simple graph. -/
def HasPlanarHypermapBridge
    {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (SimpleGraphPlanarHypermapBridge.{u, v} G)

theorem colorable_four_of_hasPlanarHypermapBridge
    {V : Type u} {G : SimpleGraph V}
    (hfct : ∀ H : Hypermap.{v}, H.PlanarBridgeless → H.FourColorable)
    (hbridge : HasPlanarHypermapBridge.{u, v} G) :
    G.Colorable 4 := by
  rcases hbridge with ⟨B⟩
  exact B.colorable_four_of_planarBridgelessFourColor hfct

end FourColor

end Schematic.Math.GraphTheory
