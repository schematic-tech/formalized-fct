import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorArities

/-! Mirror arity formulas at face-fixed spokes. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace SubpartLoc

theorem arity_mirror_fan1_of_face_fixed_of_spoke_six
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 6) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan1 G x) := by
  simpa [hface] using
    arity_mirror_fan1_face_of_spoke_six (G := G) hPlain x hspoke

theorem arity_mirror_fan1_of_face_fixed_of_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 7) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan2 G x) := by
  simpa [hface] using
    arity_mirror_fan1_face_of_spoke_seven (G := G) hPlain x hspoke

theorem arity_mirror_fan2_of_face_fixed_of_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 7) :
    G.mirror.arity (move Pfan2 G.mirror x) =
      G.arity (move Pfan1 G x) := by
  simpa [hface] using
    arity_mirror_fan2_face_of_spoke_seven (G := G) hPlain x hspoke

theorem arity_mirror_fan1_of_face_fixed_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan3 G x) := by
  simpa [hface] using
    arity_mirror_fan1_face_of_spoke_eight (G := G) hPlain x hspoke

theorem arity_mirror_fan2_of_face_fixed_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan2 G.mirror x) =
      G.arity (move Pfan2 G x) := by
  simpa [hface] using
    arity_mirror_fan2_face_of_spoke_eight (G := G) hPlain x hspoke

theorem arity_mirror_fan3_of_face_fixed_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hface : G.face x = x)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan3 G.mirror x) =
      G.arity (move Pfan1 G x) := by
  simpa [hface] using
    arity_mirror_fan3_face_of_spoke_eight (G := G) hPlain x hspoke

end SubpartLoc

end FourColor

end Schematic.Math.GraphTheory
