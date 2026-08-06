import FourColorTheorem.FourColor.Discharging.PartGeometry.Boundary
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem fitp_mirror_face_pcons
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (s h : PRange) (p : Part) (x : G.Dart) :
  fitp G.mirror (G.face x) (Pcons s h p) =
      (s (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face x))) &&
          fitp G.mirror x p) := by
  simp only [fitp]
  rw [SubpartLoc.arity_mirror_spoke_face (G := G) hPlain x]
  rw [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic (G.face x)]
  have hface : G.mirror.face (G.face x) = x := by
    change G.face.symm (G.face x) = x
    simp
  rw [hface]

theorem fitp_mirror_face_pcons6
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h f1 : PRange) (p : Part) (x : G.Dart) :
    fitp G.mirror (G.face x) (Pcons6 h f1 p) =
      (PRange.Pr66
          (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face x))) &&
          f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) &&
            fitp G.mirror x p) := by
  simp only [fitp]
  rw [SubpartLoc.arity_mirror_spoke_face (G := G) hPlain x]
  rw [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic (G.face x)]
  have hface : G.mirror.face (G.face x) = x := by
    change G.face.symm (G.face x) = x
    simp
  rw [hface]
  have hfanPair :=
    SubpartLoc.pr66_fan1_mirror_face_eq (G := G) hPlain x f1
  cases hPr :
      PRange.Pr66 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x))
  · simp
  · have hfan :
        f1 (G.mirror.arity
            (SubpartLoc.move SubpartLoc.Pfan1 G.mirror (G.face x))) =
          f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) := by
      simpa [hPr] using hfanPair
    simp [hfan, Bool.and_assoc]

theorem fitp_mirror_face_pcons7
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h f1 f2 : PRange) (p : Part) (x : G.Dart) :
    fitp G.mirror (G.face x) (Pcons7 h f1 f2 p) =
      (PRange.Pr77
          (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face x))) &&
          f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) &&
            f2 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) &&
              fitp G.mirror x p) := by
  simp only [fitp]
  rw [SubpartLoc.arity_mirror_spoke_face (G := G) hPlain x]
  rw [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic (G.face x)]
  have hface : G.mirror.face (G.face x) = x := by
    change G.face.symm (G.face x) = x
    simp
  rw [hface]
  have hfanPair :=
    SubpartLoc.pr77_fans_mirror_face_eq (G := G) hPlain x f1 f2
  cases hPr :
      PRange.Pr77 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x))
  · simp
  · have hfans :
        (f1 (G.mirror.arity
            (SubpartLoc.move SubpartLoc.Pfan1 G.mirror (G.face x))) &&
          f2 (G.mirror.arity
            (SubpartLoc.move SubpartLoc.Pfan2 G.mirror (G.face x)))) =
        (f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) &&
          f2 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x))) := by
      simpa [hPr, Bool.and_assoc] using hfanPair
    simp [hfans, Bool.and_assoc]

theorem fitp_mirror_face_pcons8
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart) :
    fitp G.mirror (G.face x) (Pcons8 h f1 f2 f3 p) =
      (PRange.Pr88
          (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face x))) &&
          f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) &&
            f2 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) &&
              f3 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) &&
                fitp G.mirror x p) := by
  simp only [fitp]
  rw [SubpartLoc.arity_mirror_spoke_face (G := G) hPlain x]
  rw [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic (G.face x)]
  have hface : G.mirror.face (G.face x) = x := by
    change G.face.symm (G.face x) = x
    simp
  rw [hface]
  have hfanPair :=
    SubpartLoc.pr88_fans_mirror_face_eq (G := G) hPlain x f1 f2 f3
  cases hPr :
      PRange.Pr88 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x))
  · simp
  · have hfans :
        (f1 (G.mirror.arity
            (SubpartLoc.move SubpartLoc.Pfan1 G.mirror (G.face x))) &&
          f2 (G.mirror.arity
            (SubpartLoc.move SubpartLoc.Pfan2 G.mirror (G.face x))) &&
            f3 (G.mirror.arity
              (SubpartLoc.move SubpartLoc.Pfan3 G.mirror (G.face x)))) =
        (f1 (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) &&
          f2 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) &&
            f3 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x))) := by
      simpa [hPr, Bool.and_assoc] using hfanPair
    simp [hfans, Bool.and_assoc]

theorem pcons_mirror_sector_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1) (s h : PRange) :
    (s (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pspoke G.mirror x)) &&
      h (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Phat G.mirror x))) =
    (s (G.arity
        (SubpartLoc.move SubpartLoc.Pspoke G
          ((G.face : G.Dart → G.Dart)^[n] x))) &&
      h (G.arity (SubpartLoc.move SubpartLoc.Phat G x))) := by
  have hsector :=
    SubpartLoc.pcons_mirror_sector_face_iter_of_hub_eq
      (G := G) hPlain hCubic (hub := n + 1) (i := 0)
      (x := x) hsize (by omega) s h
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n + 1] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  simpa [hcycle] using hsector

theorem pcons6_mirror_sector_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1) (h f1 : PRange) :
    (PRange.Pr66
        (G.mirror.arity
          (SubpartLoc.move SubpartLoc.Pspoke G.mirror x)) &&
      h (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Phat G.mirror x)) &&
      f1 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G.mirror x))) =
    (PRange.Pr66
        (G.arity
          (SubpartLoc.move SubpartLoc.Pspoke G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
      h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
      f1 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G
          ((G.face : G.Dart → G.Dart)^[n] x)))) := by
  have hsector :=
    SubpartLoc.pcons6_mirror_sector_face_iter_of_hub_eq
      (G := G) hPlain hCubic (hub := n + 1) (i := 0)
      (x := x) hsize (by omega) h f1
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n + 1] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  simpa [hcycle, Bool.and_assoc] using hsector

theorem pcons7_mirror_sector_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1) (h f1 f2 : PRange) :
    (PRange.Pr77
        (G.mirror.arity
          (SubpartLoc.move SubpartLoc.Pspoke G.mirror x)) &&
      h (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Phat G.mirror x)) &&
      f1 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G.mirror x)) &&
      f2 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan2 G.mirror x))) =
    (PRange.Pr77
        (G.arity
          (SubpartLoc.move SubpartLoc.Pspoke G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
      h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
      f1 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan2 G
          ((G.face : G.Dart → G.Dart)^[n] x))) &&
      f2 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G
          ((G.face : G.Dart → G.Dart)^[n] x)))) := by
  have hsector :=
    SubpartLoc.pcons7_mirror_sector_face_iter_of_hub_eq
      (G := G) hPlain hCubic (hub := n + 1) (i := 0)
      (x := x) hsize (by omega) h f1 f2
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n + 1] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  simpa [hcycle, Bool.and_assoc] using hsector

theorem pcons8_mirror_sector_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1) (h f1 f2 f3 : PRange) :
    (PRange.Pr88
        (G.mirror.arity
          (SubpartLoc.move SubpartLoc.Pspoke G.mirror x)) &&
      h (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Phat G.mirror x)) &&
      f1 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G.mirror x)) &&
      f2 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan2 G.mirror x)) &&
      f3 (G.mirror.arity
        (SubpartLoc.move SubpartLoc.Pfan3 G.mirror x))) =
    (PRange.Pr88
        (G.arity
          (SubpartLoc.move SubpartLoc.Pspoke G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
      h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
      f1 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan3 G
          ((G.face : G.Dart → G.Dart)^[n] x))) &&
      f2 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan2 G
          ((G.face : G.Dart → G.Dart)^[n] x))) &&
      f3 (G.arity
        (SubpartLoc.move SubpartLoc.Pfan1 G
          ((G.face : G.Dart → G.Dart)^[n] x)))) := by
  have hsector :=
    SubpartLoc.pcons8_mirror_sector_face_iter_of_hub_eq
      (G := G) hPlain hCubic (hub := n + 1) (i := 0)
      (x := x) hsize (by omega) h f1 f2 f3
  have hcycle :
      (G.face : G.Dart → G.Dart)^[n + 1] x = x := by
    simpa [hsize] using G.face_iterate_arity x
  simpa [hcycle, Bool.and_assoc] using hsector

theorem fitp_mirror_pcons_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1)
    (s h : PRange) (p : Part) :
    fitp G.mirror x (Pcons s h p) =
      (s (G.arity
          (SubpartLoc.move SubpartLoc.Pspoke G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
          fitp G.mirror (G.face.symm x) p) := by
  have hsector :=
    pcons_mirror_sector_of_arity_succ
      (G := G) hPlain hCubic (x := x) hsize s h
  have hface : G.mirror.face x = G.face.symm x := rfl
  rw [fitp, hface]
  simpa [Bool.and_assoc] using
    congrArg (fun b => b && fitp G.mirror (G.face.symm x) p) hsector

theorem fitp_mirror_pcons6_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1)
    (h f1 : PRange) (p : Part) :
    fitp G.mirror x (Pcons6 h f1 p) =
      (PRange.Pr66
          (G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G
              ((G.face : G.Dart → G.Dart)^[n] x))) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
        f1 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan1 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
          fitp G.mirror (G.face.symm x) p) := by
  have hsector :=
    pcons6_mirror_sector_of_arity_succ
      (G := G) hPlain hCubic (x := x) hsize h f1
  have hface : G.mirror.face x = G.face.symm x := rfl
  rw [fitp, hface]
  simpa [Bool.and_assoc] using
    congrArg (fun b => b && fitp G.mirror (G.face.symm x) p) hsector

theorem fitp_mirror_pcons7_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1)
    (h f1 f2 : PRange) (p : Part) :
    fitp G.mirror x (Pcons7 h f1 f2 p) =
      (PRange.Pr77
          (G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G
              ((G.face : G.Dart → G.Dart)^[n] x))) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
        f1 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan2 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
        f2 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan1 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
          fitp G.mirror (G.face.symm x) p) := by
  have hsector :=
    pcons7_mirror_sector_of_arity_succ
      (G := G) hPlain hCubic (x := x) hsize h f1 f2
  have hface : G.mirror.face x = G.face.symm x := rfl
  rw [fitp, hface]
  simpa [Bool.and_assoc] using
    congrArg (fun b => b && fitp G.mirror (G.face.symm x) p) hsector

theorem fitp_mirror_pcons8_of_arity_succ
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {n : Nat} {x : G.Dart}
    (hsize : G.arity x = n + 1)
    (h f1 f2 f3 : PRange) (p : Part) :
    fitp G.mirror x (Pcons8 h f1 f2 f3 p) =
      (PRange.Pr88
          (G.arity
            (SubpartLoc.move SubpartLoc.Pspoke G
              ((G.face : G.Dart → G.Dart)^[n] x))) &&
        h (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) &&
        f1 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan3 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
        f2 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan2 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
        f3 (G.arity
          (SubpartLoc.move SubpartLoc.Pfan1 G
            ((G.face : G.Dart → G.Dart)^[n] x))) &&
          fitp G.mirror (G.face.symm x) p) := by
  have hsector :=
    pcons8_mirror_sector_of_arity_succ
      (G := G) hPlain hCubic (x := x) hsize h f1 f2 f3
  have hface : G.mirror.face x = G.face.symm x := rfl
  rw [fitp, hface]
  simpa [Bool.and_assoc] using
    congrArg (fun b => b && fitp G.mirror (G.face.symm x) p) hsector

end

end Part

end FourColor

end Schematic.Math.GraphTheory
