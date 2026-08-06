import FourColorTheorem.FourColor.Discharging.PartGeometry.SectorEvaluation

/-! Mirror arity formulas for constrained spoke sectors. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace SubpartLoc

theorem arity_mirror_fan1_face_of_spoke_six
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 6) :
    G.mirror.arity (move Pfan1 G.mirror (G.face x)) =
      G.arity (move Pfan1 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 3) (m := 6) x hspoke (by omega)
  simpa [spokeRayArity_three] using h

theorem arity_mirror_fan1_face_of_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 7) :
    G.mirror.arity (move Pfan1 G.mirror (G.face x)) =
      G.arity (move Pfan2 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 3) (m := 7) x hspoke (by omega)
  simpa [spokeRayArity_three, spokeRayArity_four] using h

theorem arity_mirror_fan2_face_of_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 7) :
    G.mirror.arity (move Pfan2 G.mirror (G.face x)) =
      G.arity (move Pfan1 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 4) (m := 7) x hspoke (by omega)
  simpa [spokeRayArity_three, spokeRayArity_four] using h

theorem arity_mirror_fan1_face_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan1 G.mirror (G.face x)) =
      G.arity (move Pfan3 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 3) (m := 8) x hspoke (by omega)
  simpa [spokeRayArity_three, spokeRayArity_five] using h

theorem arity_mirror_fan2_face_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan2 G.mirror (G.face x)) =
      G.arity (move Pfan2 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 4) (m := 8) x hspoke (by omega)
  simpa [spokeRayArity_four] using h

theorem arity_mirror_fan3_face_of_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart)
    (hspoke : G.arity (move Pspoke G x) = 8) :
    G.mirror.arity (move Pfan3 G.mirror (G.face x)) =
      G.arity (move Pfan1 G x) := by
  have h := spokeRayArity_mirror_face
    (G := G) hPlain (n := 5) (m := 8) x hspoke (by omega)
  simpa [spokeRayArity_three, spokeRayArity_five] using h

theorem arity_mirror_fan1_of_arity_two_of_face_spoke_six
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 6) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan1 G (G.face x)) := by
  have h := arity_mirror_fan1_face_of_spoke_six
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem arity_mirror_fan1_of_arity_two_of_face_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 7) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan2 G (G.face x)) := by
  have h := arity_mirror_fan1_face_of_spoke_seven
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem arity_mirror_fan2_of_arity_two_of_face_spoke_seven
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 7) :
    G.mirror.arity (move Pfan2 G.mirror x) =
      G.arity (move Pfan1 G (G.face x)) := by
  have h := arity_mirror_fan2_face_of_spoke_seven
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem arity_mirror_fan1_of_arity_two_of_face_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 8) :
    G.mirror.arity (move Pfan1 G.mirror x) =
      G.arity (move Pfan3 G (G.face x)) := by
  have h := arity_mirror_fan1_face_of_spoke_eight
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem arity_mirror_fan2_of_arity_two_of_face_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 8) :
    G.mirror.arity (move Pfan2 G.mirror x) =
      G.arity (move Pfan2 G (G.face x)) := by
  have h := arity_mirror_fan2_face_of_spoke_eight
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem arity_mirror_fan3_of_arity_two_of_face_spoke_eight
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart}
    (hx : G.arity x = 2)
    (hspoke : G.arity (move Pspoke G (G.face x)) = 8) :
    G.mirror.arity (move Pfan3 G.mirror x) =
      G.arity (move Pfan1 G (G.face x)) := by
  have h := arity_mirror_fan3_face_of_spoke_eight
    (G := G) hPlain (G.face x) hspoke
  rwa [Hypermap.face_face_eq_self_of_arity_two (G := G) hx] at h

theorem pr66_fan1_mirror_face_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart) (f1 : PRange) :
    (PRange.Pr66 (G.arity (move Pspoke G x)) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror (G.face x)))) =
      (PRange.Pr66 (G.arity (move Pspoke G x)) &&
        f1 (G.arity (move Pfan1 G x))) := by
  by_cases hspoke : G.arity (move Pspoke G x) = 6
  · have hfan :=
      arity_mirror_fan1_face_of_spoke_six (G := G) hPlain x hspoke
    simp [PRange.contains, hspoke, hfan]
  · have hPr66 :
        PRange.Pr66 (G.arity (move Pspoke G x)) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr66]

theorem pr77_fans_mirror_face_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart) (f1 f2 : PRange) :
    (PRange.Pr77 (G.arity (move Pspoke G x)) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror (G.face x))) &&
          f2 (G.mirror.arity (move Pfan2 G.mirror (G.face x)))) =
      (PRange.Pr77 (G.arity (move Pspoke G x)) &&
        f1 (G.arity (move Pfan2 G x)) &&
          f2 (G.arity (move Pfan1 G x))) := by
  by_cases hspoke : G.arity (move Pspoke G x) = 7
  · have hfan1 :=
      arity_mirror_fan1_face_of_spoke_seven (G := G) hPlain x hspoke
    have hfan2 :=
      arity_mirror_fan2_face_of_spoke_seven (G := G) hPlain x hspoke
    simp [PRange.contains, hspoke, hfan1, hfan2]
  · have hPr77 :
        PRange.Pr77 (G.arity (move Pspoke G x)) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr77]

theorem pr88_fans_mirror_face_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    (x : G.Dart) (f1 f2 f3 : PRange) :
    (PRange.Pr88 (G.arity (move Pspoke G x)) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror (G.face x))) &&
          f2 (G.mirror.arity (move Pfan2 G.mirror (G.face x))) &&
            f3 (G.mirror.arity (move Pfan3 G.mirror (G.face x)))) =
      (PRange.Pr88 (G.arity (move Pspoke G x)) &&
        f1 (G.arity (move Pfan3 G x)) &&
          f2 (G.arity (move Pfan2 G x)) &&
            f3 (G.arity (move Pfan1 G x))) := by
  by_cases hspoke : G.arity (move Pspoke G x) = 8
  · have hfan1 :=
      arity_mirror_fan1_face_of_spoke_eight (G := G) hPlain x hspoke
    have hfan2 :=
      arity_mirror_fan2_face_of_spoke_eight (G := G) hPlain x hspoke
    have hfan3 :=
      arity_mirror_fan3_face_of_spoke_eight (G := G) hPlain x hspoke
    simp [PRange.contains, hspoke, hfan1, hfan2, hfan3, Bool.and_assoc]
  · have hPr88 :
        PRange.Pr88 (G.arity (move Pspoke G x)) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr88]

theorem pr66_fan1_mirror_of_arity_two_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart} (hx : G.arity x = 2) (f1 : PRange) :
    (PRange.Pr66 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror x))) =
      (PRange.Pr66 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.arity (move Pfan1 G (G.face x)))) := by
  by_cases hspoke : G.arity (move Pspoke G (G.face x)) = 6
  · have hfan :=
      arity_mirror_fan1_of_arity_two_of_face_spoke_six
        (G := G) hPlain hx hspoke
    simp [PRange.contains, hspoke, hfan]
  · have hPr66 :
        PRange.Pr66 (G.arity (move Pspoke G (G.face x))) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr66]

theorem pr77_fans_mirror_of_arity_two_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart} (hx : G.arity x = 2) (f1 f2 : PRange) :
    (PRange.Pr77 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror x)) &&
          f2 (G.mirror.arity (move Pfan2 G.mirror x))) =
      (PRange.Pr77 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.arity (move Pfan2 G (G.face x))) &&
          f2 (G.arity (move Pfan1 G (G.face x)))) := by
  by_cases hspoke : G.arity (move Pspoke G (G.face x)) = 7
  · have hfan1 :=
      arity_mirror_fan1_of_arity_two_of_face_spoke_seven
        (G := G) hPlain hx hspoke
    have hfan2 :=
      arity_mirror_fan2_of_arity_two_of_face_spoke_seven
        (G := G) hPlain hx hspoke
    simp [PRange.contains, hspoke, hfan1, hfan2]
  · have hPr77 :
        PRange.Pr77 (G.arity (move Pspoke G (G.face x))) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr77]

theorem pr88_fans_mirror_of_arity_two_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {x : G.Dart} (hx : G.arity x = 2) (f1 f2 f3 : PRange) :
    (PRange.Pr88 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.mirror.arity (move Pfan1 G.mirror x)) &&
          f2 (G.mirror.arity (move Pfan2 G.mirror x)) &&
            f3 (G.mirror.arity (move Pfan3 G.mirror x))) =
      (PRange.Pr88 (G.arity (move Pspoke G (G.face x))) &&
        f1 (G.arity (move Pfan3 G (G.face x))) &&
          f2 (G.arity (move Pfan2 G (G.face x))) &&
            f3 (G.arity (move Pfan1 G (G.face x)))) := by
  by_cases hspoke : G.arity (move Pspoke G (G.face x)) = 8
  · have hfan1 :=
      arity_mirror_fan1_of_arity_two_of_face_spoke_eight
        (G := G) hPlain hx hspoke
    have hfan2 :=
      arity_mirror_fan2_of_arity_two_of_face_spoke_eight
        (G := G) hPlain hx hspoke
    have hfan3 :=
      arity_mirror_fan3_of_arity_two_of_face_spoke_eight
        (G := G) hPlain hx hspoke
    simp [PRange.contains, hspoke, hfan1, hfan2, hfan3]
  · have hPr88 :
        PRange.Pr88 (G.arity (move Pspoke G (G.face x))) = false := by
      simp [PRange.contains, hspoke]
    simp [hPr88]

end SubpartLoc

end FourColor

end Schematic.Math.GraphTheory
