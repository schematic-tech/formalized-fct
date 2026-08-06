import FourColorTheorem.PlanarBridge
import FourColorTheorem.FourColor.Theorem.Certificate

/-!
Final Four Colour Theorem wrappers.

Core strict-subdivision planarity definitions and elementary lemmas are in
`Schematic.Math.GraphTheory.Planarity.Basic`, which is intentionally below the hypermap bridge.
The bridge statements and conditional graph-colouring transfers are in
`FourColorTheorem.PlanarBridge`; this module supplies the final unconditional
graph-colouring theorem.
-/

namespace FourColorTheorem

open Schematic.Math.GraphTheory
open Schematic.Math.GraphTheory.FourColor

open SimpleGraph

universe u

theorem four_color_theorem_of_kuratowskiEulerRotationSystem
    (hrot : FourColor.KuratowskiEulerRotationSystemTheorem.{u})
    (hfct : FourColor.CombinatorialFourColor.HypermapFourColorTheorem.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  FourColor.colorable_four_of_kuratowskiEulerRotationSystem_of_hypermapFourColor
    hrot hfct G h_planar

theorem four_color_theorem
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G) :
    G.Colorable 4 :=
  four_color_theorem_of_kuratowskiEulerRotationSystem
    FourColor.kuratowskiEulerRotationSystem
    FourColor.CombinatorialFourColor.hypermapFourColorTheorem
    G h_planar

end FourColorTheorem
