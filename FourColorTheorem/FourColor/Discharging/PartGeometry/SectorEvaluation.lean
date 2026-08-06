import FourColorTheorem.FourColor.Discharging.PartGeometry.SpokeGeometry

/-! Evaluation of mirrored six-, seven-, and eight-spoke sectors. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace SubpartLoc

theorem pr66_fan1_mirror_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (f1 : PRange) :
    (PRange.Pr66
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr66
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f1 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  let y := ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)
  have hspokeEq :
      G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
        G.arity (move Pspoke G y) := by
    simpa [y] using arity_mirror_spoke_face_iter_of_hub
      (G := G) hPlain hHub hi
  by_cases hspoke : G.arity (move Pspoke G y) = 6
  · have hfan :
        G.mirror.arity
            (move Pfan1 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan1 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 3) (m := 6)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_three, y] using h
    have hPr : PRange.Pr66 (G.arity (move Pspoke G y)) = true := by
      simp [PRange.contains, hspoke]
    simp [hspokeEq, hfan, hPr, y]
  · have hPr : PRange.Pr66 (G.arity (move Pspoke G y)) = false := by
      simp [PRange.contains, hspoke]
    have hPrOrig :
        PRange.Pr66
          (G.arity
            (move Pspoke G
              ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) = false := by
      simpa [y] using hPr
    simp [hspokeEq, hPr, hPrOrig]

theorem pr77_fans_mirror_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (f1 f2 : PRange) :
    (PRange.Pr77
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f2 (G.mirror.arity
        (move Pfan2 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr77
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f1 (G.arity
        (move Pfan2 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f2 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  let y := ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)
  have hspokeEq :
      G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
        G.arity (move Pspoke G y) := by
    simpa [y] using arity_mirror_spoke_face_iter_of_hub
      (G := G) hPlain hHub hi
  by_cases hspoke : G.arity (move Pspoke G y) = 7
  · have hfan1 :
        G.mirror.arity
            (move Pfan1 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan2 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 3) (m := 7)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_three, spokeRayArity_four, y] using h
    have hfan2 :
        G.mirror.arity
            (move Pfan2 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan1 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 4) (m := 7)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_three, spokeRayArity_four, y] using h
    have hPr : PRange.Pr77 (G.arity (move Pspoke G y)) = true := by
      simp [PRange.contains, hspoke]
    simp [hspokeEq, hfan1, hfan2, hPr, y]
  · have hPr : PRange.Pr77 (G.arity (move Pspoke G y)) = false := by
      simp [PRange.contains, hspoke]
    have hPrOrig :
        PRange.Pr77
          (G.arity
            (move Pspoke G
              ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) = false := by
      simpa [y] using hPr
    simp [hspokeEq, hPr, hPrOrig]

theorem pr88_fans_mirror_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (f1 f2 f3 : PRange) :
    (PRange.Pr88
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f2 (G.mirror.arity
        (move Pfan2 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f3 (G.mirror.arity
        (move Pfan3 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr88
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f1 (G.arity
        (move Pfan3 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f2 (G.arity
        (move Pfan2 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f3 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  let y := ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)
  have hspokeEq :
      G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
        G.arity (move Pspoke G y) := by
    simpa [y] using arity_mirror_spoke_face_iter_of_hub
      (G := G) hPlain hHub hi
  by_cases hspoke : G.arity (move Pspoke G y) = 8
  · have hfan1 :
        G.mirror.arity
            (move Pfan1 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan3 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 3) (m := 8)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_three, spokeRayArity_five, y] using h
    have hfan2 :
        G.mirror.arity
            (move Pfan2 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan2 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 4) (m := 8)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_four, y] using h
    have hfan3 :
        G.mirror.arity
            (move Pfan3 G.mirror
              ((G.mirror.face : G.Dart → G.Dart)^[i] x)) =
          G.arity (move Pfan1 G y) := by
      have h := spokeRayArity_mirror_face_iter_of_hub
        (G := G) hPlain (hub := hub) (i := i) (n := 5) (m := 8)
        (x := x) hHub hi (by simpa [y] using hspoke) (by omega)
      simpa [spokeRayArity_three, spokeRayArity_five, y] using h
    have hPr : PRange.Pr88 (G.arity (move Pspoke G y)) = true := by
      simp [PRange.contains, hspoke]
    simp [hspokeEq, hfan1, hfan2, hfan3, hPr, y]
  · have hPr : PRange.Pr88 (G.arity (move Pspoke G y)) = false := by
      simp [PRange.contains, hspoke]
    have hPrOrig :
        PRange.Pr88
          (G.arity
            (move Pspoke G
              ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) = false := by
      simpa [y] using hPr
    simp [hspokeEq, hPr, hPrOrig]

theorem pcons_mirror_sector_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (s h : PRange) :
    (s (G.mirror.arity
        (move Pspoke G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      h (G.mirror.arity
        (move Phat G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (s (G.arity
        (move Pspoke G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      h (G.arity
        (move Phat G
          ((G.face : G.Dart → G.Dart)^[hub - i] x)))) := by
  have hspoke := arity_mirror_spoke_face_iter_of_hub
    (G := G) hPlain hHub hi
  have hhat := arity_mirror_hat_face_iter_of_hub
    (G := G) hPlain hCubic hHub (by omega : i ≤ hub)
  simp [hspoke, hhat]

theorem pcons6_mirror_sector_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (h f1 : PRange) :
    (PRange.Pr66
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      h (G.mirror.arity
        (move Phat G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr66
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      h (G.arity
        (move Phat G
          ((G.face : G.Dart → G.Dart)^[hub - i] x))) &&
      f1 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  have hsf := pr66_fan1_mirror_face_iter_of_hub_eq
    (G := G) hPlain hHub hi f1
  have hhat := arity_mirror_hat_face_iter_of_hub
    (G := G) hPlain hCubic hHub (by omega : i ≤ hub)
  rw [hhat]
  let H := h (G.arity
    (move Phat G ((G.face : G.Dart → G.Dart)^[hub - i] x)))
  by_cases hH : H = true
  · simp [H, hH, hsf]
  · have hHf : H = false := by
      cases hH' : H <;> simp [hH'] at hH ⊢
    simp [H, hHf]

theorem pcons7_mirror_sector_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (h f1 f2 : PRange) :
    (PRange.Pr77
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      h (G.mirror.arity
        (move Phat G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f2 (G.mirror.arity
        (move Pfan2 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr77
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      h (G.arity
        (move Phat G
          ((G.face : G.Dart → G.Dart)^[hub - i] x))) &&
      f1 (G.arity
        (move Pfan2 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f2 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  have hsf := pr77_fans_mirror_face_iter_of_hub_eq
    (G := G) hPlain hHub hi f1 f2
  have hhat := arity_mirror_hat_face_iter_of_hub
    (G := G) hPlain hCubic hHub (by omega : i ≤ hub)
  rw [hhat]
  let H := h (G.arity
    (move Phat G ((G.face : G.Dart → G.Dart)^[hub - i] x)))
  by_cases hH : H = true
  · simpa [H, hH, Bool.and_assoc] using hsf
  · have hHf : H = false := by
      cases hH' : H <;> simp [hH'] at hH ⊢
    simp [H, hHf]

theorem pcons8_mirror_sector_face_iter_of_hub_eq
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    {hub i : Nat} {x : G.Dart}
    (hHub : G.arity x = hub) (hi : i < hub) (h f1 f2 f3 : PRange) :
    (PRange.Pr88
        (G.mirror.arity
          (move Pspoke G.mirror
            ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      h (G.mirror.arity
        (move Phat G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f1 (G.mirror.arity
        (move Pfan1 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f2 (G.mirror.arity
        (move Pfan2 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x))) &&
      f3 (G.mirror.arity
        (move Pfan3 G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[i] x)))) =
    (PRange.Pr88
        (G.arity
          (move Pspoke G
            ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      h (G.arity
        (move Phat G
          ((G.face : G.Dart → G.Dart)^[hub - i] x))) &&
      f1 (G.arity
        (move Pfan3 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f2 (G.arity
        (move Pfan2 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x))) &&
      f3 (G.arity
        (move Pfan1 G
          ((G.face : G.Dart → G.Dart)^[hub - (i + 1)] x)))) := by
  have hsf := pr88_fans_mirror_face_iter_of_hub_eq
    (G := G) hPlain hHub hi f1 f2 f3
  have hhat := arity_mirror_hat_face_iter_of_hub
    (G := G) hPlain hCubic hHub (by omega : i ≤ hub)
  rw [hhat]
  let H := h (G.arity
    (move Phat G ((G.face : G.Dart → G.Dart)^[hub - i] x)))
  by_cases hH : H = true
  · simpa [H, hH, Bool.and_assoc] using hsf
  · have hHf : H = false := by
      cases hH' : H <;> simp [hH'] at hH ⊢
    simp [H, hHf]

end SubpartLoc

end FourColor

end Schematic.Math.GraphTheory
