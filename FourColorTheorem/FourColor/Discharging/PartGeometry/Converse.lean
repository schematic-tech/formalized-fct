import FourColorTheorem.FourColor.Discharging.PartGeometry.Rotation
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem convPart5_sound
    (hpenta : G.Pentagonal) {h45 : PRange} {p : Part} {y : G.Dart}
    (Eh45 : h45 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (SubpartLoc.move SubpartLoc.Pspoke G y))))) = true)
    (hfit : fitp G y p = true) :
    let up := convPart5 h45 p
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G y)) = true ∧
      fitp G (G.face (G.face (SubpartLoc.move SubpartLoc.Pspoke G y)))
        up.2 = true := by
  have hspoke59 : PRange.Pr59
      (G.arity (SubpartLoc.move SubpartLoc.Pspoke G y)) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  cases p with
  | Pnil =>
      exact ⟨hspoke59, rfl⟩
  | Pcons u s5 tail =>
      simp only [fitp] at hfit
      rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
      rcases hfit with ⟨⟨hu, hs5⟩, _⟩
      have hs5' : s5 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
          (G.face (G.face (SubpartLoc.move SubpartLoc.Pspoke G y))))) =
            true := by
        simpa [SubpartLoc.move] using hs5
      exact ⟨hu, by simp [convPart5, fitp, hs5', Eh45]⟩
  | Pcons6 _ _ _ =>
      exact ⟨hspoke59, rfl⟩
  | Pcons7 s5 s6 s7 tail =>
      simp only [fitp] at hfit
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true] at hfit
      rcases hfit with ⟨⟨⟨⟨hu, hs5⟩, hs6⟩, hs7⟩, _⟩
      have hs5' : s5 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
          (G.face (G.face (SubpartLoc.move SubpartLoc.Pspoke G y))))) =
            true := by
        simpa [SubpartLoc.move] using hs5
      have hs6' : s6 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
          (G.face (G.face (G.face
            (SubpartLoc.move SubpartLoc.Pspoke G y)))))) = true := by
        simpa [SubpartLoc.move] using hs6
      have hs7' : s7 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
          (G.face (G.face (G.face (G.face
            (SubpartLoc.move SubpartLoc.Pspoke G y))))))) = true := by
        simpa [SubpartLoc.move] using hs7
      have hhat1 : PRange.Pr59
          (G.arity (SubpartLoc.move SubpartLoc.Phat G
            (G.face (G.face (G.face
              (SubpartLoc.move SubpartLoc.Pspoke G y)))))) = true :=
        PRange.contains_Pr59_of_ge_five
          (Hypermap.arity_ge_five_of_pentagonal hpenta _)
      have hhat2 : PRange.Pr59
          (G.arity (SubpartLoc.move SubpartLoc.Phat G
            (G.face (G.face (G.face (G.face
              (SubpartLoc.move SubpartLoc.Pspoke G y))))))) = true :=
        PRange.contains_Pr59_of_ge_five
          (Hypermap.arity_ge_five_of_pentagonal hpenta _)
      exact ⟨hu, by
        simp [convPart5, pconsS, fitp, hs5', Eh45, hs6', hs7',
          hhat1, hhat2]⟩
  | Pcons8 _ _ _ _ _ =>
      exact ⟨hspoke59, rfl⟩

theorem convPart3_sound
    (hPlain : G.Plain) {h23 : PRange} {p q : Part} {x : G.Dart}
    (Eh23 : h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.edge (G.face (G.face x))))) = true)
    (hsize : G.arity x = 5 + p.size)
    (hfit : fitp G ((G.face : G.Dart → G.Dart)^[5] x) p = true)
    (hq : fitp G (G.face (G.edge (G.face (G.face x)))) q = true) :
    fitp G (G.edge (G.face (G.face x))) (convPart3 h23 p q) = true := by
  let effx : G.Dart := G.edge (G.face (G.face x))
  have hEh23 :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true := by
    simpa [effx] using Eh23
  have hqEff : fitp G (G.face effx) q = true := by
    simpa [effx] using hq
  have hspokeArity :
      G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx) = G.arity x := by
    dsimp [effx, SubpartLoc.move]
    rw [Hypermap.Plain.edge_edge (G := G) hPlain]
    exact Hypermap.arity_face_iter (G := G) 2 x
  cases p with
  | Pnil =>
      have hspoke5 :
          G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx) = 5 := by
        rw [hspokeArity]
        simpa [size] using hsize
      have hPr55 :
          PRange.Pr55 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx)) =
            true := by
        simp [PRange.contains, hspoke5]
      simpa [convPart3, fitp] using ⟨⟨hPr55, hEh23⟩, hqEff⟩
  | Pcons f31 _ tail =>
      cases tail with
      | Pnil =>
          have hspoke6 :
              G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx) = 6 := by
            rw [hspokeArity]
            simpa [size] using hsize
          have hPr66 :
              PRange.Pr66
                  (G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx)) =
                true := by
            simp [PRange.contains, hspoke6]
          simpa [convPart3, fitp] using ⟨⟨hPr66, hEh23⟩, hqEff⟩
      | Pcons f32 _ tail2 =>
          cases tail2 with
          | Pnil =>
              have hspoke7 :
                  G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx) = 7 := by
                rw [hspokeArity]
                simpa [size] using hsize
              simp [fitp] at hfit
              rcases hfit with ⟨⟨hf31, _⟩, hf32, _⟩
              have hf31' :
                  f31 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G effx)) =
                    true := by
                simpa [effx, SubpartLoc.move,
                  Hypermap.Plain.edge_edge (G := G) hPlain] using hf31
              have hf32' :
                  f32 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G effx)) =
                    true := by
                simpa [effx, SubpartLoc.move,
                  Hypermap.Plain.edge_edge (G := G) hPlain] using hf32
              have hPr77 :
                  PRange.Pr77
                      (G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx)) =
                    true := by
                simp [PRange.contains, hspoke7]
              have hPcons : fitp G effx (Pcons PRange.Pr77 h23 q) = true := by
                simpa [fitp] using ⟨⟨hPr77, hEh23⟩, hqEff⟩
              have hP7 : fitp G effx (Pcons7 h23 f31 f32 q) = true := by
                simpa [fitp] using
                  ⟨⟨⟨⟨hPr77, hEh23⟩, hf31'⟩, hf32'⟩, hqEff⟩
              cases f31 <;> cases f32 <;> first
                | simpa [convPart3] using hPcons
                | simpa [convPart3] using hP7
          | Pcons f33 _ tail3 =>
              cases tail3 with
              | Pnil =>
                  have hspoke8 :
                      G.arity (SubpartLoc.move SubpartLoc.Pspoke G effx) =
                        8 := by
                    rw [hspokeArity]
                    simpa [size] using hsize
                  simp [fitp] at hfit
                  rcases hfit with ⟨⟨hf31, _⟩, ⟨⟨hf32, _⟩, hf33, _⟩⟩
                  have hf31' :
                      f31
                          (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G effx)) =
                        true := by
                    simpa [effx, SubpartLoc.move,
                      Hypermap.Plain.edge_edge (G := G) hPlain] using hf31
                  have hf32' :
                      f32
                          (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G effx)) =
                        true := by
                    simpa [effx, SubpartLoc.move,
                      Hypermap.Plain.edge_edge (G := G) hPlain] using hf32
                  have hf33' :
                      f33
                          (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G effx)) =
                        true := by
                    simpa [effx, SubpartLoc.move,
                      Hypermap.Plain.edge_edge (G := G) hPlain] using hf33
                  have hPr88 :
                      PRange.Pr88
                          (G.arity
                            (SubpartLoc.move SubpartLoc.Pspoke G effx)) =
                        true := by
                    simp [PRange.contains, hspoke8]
                  have hP8 :
                      fitp G effx (Pcons8 h23 f31 f32 f33 q) = true := by
                    simpa [fitp] using
                      ⟨⟨⟨⟨⟨hPr88, hEh23⟩, hf31'⟩, hf32'⟩, hf33'⟩, hqEff⟩
                  simpa [convPart3] using hP8
              | Pcons _ _ _ => rfl
              | Pcons6 _ _ _ => rfl
              | Pcons7 _ _ _ _ => rfl
              | Pcons8 _ _ _ _ _ => rfl
          | Pcons6 _ _ _ => rfl
          | Pcons7 _ _ _ _ => rfl
          | Pcons8 _ _ _ _ _ => rfl
      | Pcons6 _ _ _ => rfl
      | Pcons7 _ _ _ _ => rfl
      | Pcons8 _ _ _ _ _ => rfl
  | Pcons6 _ _ _ => rfl
  | Pcons7 _ _ _ _ => rfl
  | Pcons8 _ _ _ _ _ => rfl

theorem convPart4_fan_free_sound
    (hPlain : G.Plain) (hCubic : G.Cubic) (hpenta : G.Pentagonal)
    {h34 h s4 : PRange} {tail q5 : Part} {x : G.Dart}
    (hfit : fitp G x (Pcons h34 h (Pcons s4 PRange.Pr59 tail)) = true)
    (hq5 : fitp G (G.face (G.face (G.edge (G.face (G.face x))))) q5 =
      true) :
    let up := convPart4 (Pcons h34 h (Pcons s4 PRange.Pr59 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true := by
  simp [fitp] at hfit
  rcases hfit with ⟨⟨Eh34, _⟩, ⟨⟨Es4, _⟩, _⟩⟩
  have hhead : PRange.Pr59
      (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.face (G.face (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have Es4' : s4 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
      (G := G) hPlain hCubic x]
    exact Es4
  have Eh34' : h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
      (G := G) hPlain hCubic x]
    exact Eh34
  exact ⟨hhead, by
    simp [convPart4, fitp, Es4', Eh34', hq5]⟩

theorem convPart4_spoke6_sound
    (hPlain : G.Plain) (hCubic : G.Cubic) (hpenta : G.Pentagonal)
    {h34 h f41 : PRange} {tail q5 : Part} {x : G.Dart}
    (hfit : fitp G x (Pcons h34 h (Pcons PRange.Pr66 f41 tail)) =
      true)
    (hq5 : fitp G (G.face (G.face (G.edge (G.face (G.face x))))) q5 =
      true) :
    let up := convPart4 (Pcons h34 h (Pcons PRange.Pr66 f41 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true := by
  simp [fitp] at hfit
  rcases hfit with ⟨⟨Eh34, _⟩, ⟨⟨Es4, Ef41⟩, _⟩⟩
  have hhead : PRange.Pr59
      (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.face (G.face (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have Es4' : PRange.Pr66 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
      (G := G) hPlain hCubic x]
    exact Es4
  have Eh34' : h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
      (G := G) hPlain hCubic x]
    exact Eh34
  have Ef41' : f41 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_fan1_face_edge_face_face_eq_hat_face
      (G := G) hPlain hCubic x]
    exact Ef41
  cases f41 <;>
    exact ⟨hhead, by
      simp [convPart4, fitp, Es4', Eh34', Ef41', hq5]⟩

theorem convPart4_spoke7_sound
    (hPlain : G.Plain) (hCubic : G.Cubic) (hpenta : G.Pentagonal)
    {h34 h f41 : PRange} {tail q5 : Part} {x : G.Dart}
    (hfit : fitp G x (Pcons h34 h (Pcons PRange.Pr77 f41 tail)) =
      true)
    (hq5 : fitp G (G.face (G.face (G.edge (G.face (G.face x))))) q5 =
      true) :
    let up := convPart4 (Pcons h34 h (Pcons PRange.Pr77 f41 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true := by
  simp [fitp] at hfit
  rcases hfit with ⟨⟨Eh34, _⟩, ⟨⟨Es4, Ef41⟩, _⟩⟩
  have hhead : PRange.Pr59
      (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.face (G.face (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have Es4' : PRange.Pr77 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
      (G := G) hPlain hCubic x]
    exact Es4
  have Eh34' : h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
      (G := G) hPlain hCubic x]
    exact Eh34
  have Ef41' : f41 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.edge (G.face (G.face x)))))) = true := by
    rw [SubpartLoc.arity_fan1_face_edge_face_face_eq_hat_face
      (G := G) hPlain hCubic x]
    exact Ef41
  have hfan2 : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
      (G.face (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  cases f41 <;>
    exact ⟨hhead, by
      simp [convPart4, fitp, Es4', Eh34', Ef41', hfan2, hq5]⟩

private theorem convPart4_default_sound
    (hpenta : G.Pentagonal) {p q5 : Part} {x : G.Dart}
    (hdefault : convPart4 p =
      (PRange.Pr59, fun _ : Part => Pnil)) :
    let up := convPart4 p
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true := by
  rw [hdefault]
  exact ⟨PRange.contains_Pr59_of_ge_five
    (Hypermap.arity_ge_five_of_pentagonal hpenta _), rfl⟩

theorem convPart4_pnil_sound
    (hpenta : G.Pentagonal) {q5 : Part} {x : G.Dart} :
    let up := convPart4 Pnil
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_pcons6_head_default_sound
    (hpenta : G.Pentagonal) {h f : PRange} {tail q5 : Part}
    {x : G.Dart} :
    let up := convPart4 (Pcons6 h f tail)
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_pcons7_head_default_sound
    (hpenta : G.Pentagonal) {h f1 f2 : PRange} {tail q5 : Part}
    {x : G.Dart} :
    let up := convPart4 (Pcons7 h f1 f2 tail)
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_pcons8_head_default_sound
    (hpenta : G.Pentagonal) {h f1 f2 f3 : PRange} {tail q5 : Part}
    {x : G.Dart} :
    let up := convPart4 (Pcons8 h f1 f2 f3 tail)
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_pcons_pnil_tail_sound
    (hpenta : G.Pentagonal) {h34 h : PRange} {q5 : Part}
    {x : G.Dart} :
    let up := convPart4 (Pcons h34 h Pnil)
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_pcons_pcons8_tail_sound
    (hpenta : G.Pentagonal) {h34 h a b c d : PRange} {tail q5 : Part}
    {x : G.Dart} :
    let up := convPart4 (Pcons h34 h (Pcons8 a b c d tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true :=
  convPart4_default_sound hpenta rfl

theorem convPart4_other_spoke_sound
    (hpenta : G.Pentagonal)
    {h34 h s4 f41 : PRange} {tail q5 : Part} {x : G.Dart}
    (hf41 : f41 ≠ PRange.Pr59)
    (hs55 : s4 ≠ PRange.Pr55) (hs66 : s4 ≠ PRange.Pr66)
    (hs77 : s4 ≠ PRange.Pr77) :
    let up := convPart4 (Pcons h34 h (Pcons s4 f41 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.face (G.edge (G.face (G.face x))))))) = true ∧
      fitp G (G.face (G.edge (G.face (G.face x)))) (up.2 q5) =
        true := by
  have hhead : PRange.Pr59
      (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.face (G.face (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  cases f41 <;> cases s4 <;>
    simp [convPart4, fitp, hhead] at hf41 hs55 hs66 hs77 ⊢

theorem fitp_pconsN_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y) :
    ∀ (n : Nat) (x : G.Dart), fitp G x (pconsN n) = true := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [pconsN, fitp]
  | succ n ih =>
      intro x
      have hs :
          PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) = true :=
        PRange.contains_Pr59_of_ge_five
          (hge (SubpartLoc.move SubpartLoc.Pspoke G x))
      have hh :
          PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true :=
        PRange.contains_Pr59_of_ge_five
          (hge (SubpartLoc.move SubpartLoc.Phat G x))
      simp [pconsN, fitp, hs, hh, ih]

theorem exactFitp_pconsN_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    {x : G.Dart} {n : Nat}
    (hx : G.arity x = n) :
    exactFitp G x (pconsN n) = true := by
  have hfit := fitp_pconsN_of_arity_ge_five (G := G) hge n x
  simp [exactFitp, hx, hfit]

theorem exactFitp_pconsN_self_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (x : G.Dart) :
    exactFitp G x (pconsN (G.arity x)) = true :=
  exactFitp_pconsN_of_arity_ge_five (G := G) hge rfl

theorem exactFitp_pconsN_of_pentagonal
    (hG : G.Pentagonal) {x : G.Dart} {n : Nat}
    (hx : G.arity x = n) :
    exactFitp G x (pconsN n) = true :=
  exactFitp_pconsN_of_arity_ge_five
    (G := G)
    (fun y => Hypermap.arity_ge_five_of_pentagonal hG y)
    hx

theorem exactFitp_pconsN_eq_beq_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (x : G.Dart) (n : Nat) :
    exactFitp G x (pconsN n) = (G.arity x == n) := by
  by_cases h : G.arity x = n
  · rw [show (G.arity x == n) = true by simp [h]]
    exact exactFitp_pconsN_of_arity_ge_five (G := G) hge h
  · simp [exactFitp, h]

theorem exactFitp_pconsN_eq_beq_of_pentagonal
    (hG : G.Pentagonal) (x : G.Dart) (n : Nat) :
    exactFitp G x (pconsN n) = (G.arity x == n) :=
  exactFitp_pconsN_eq_beq_of_arity_ge_five (G := G)
    (fun y => Hypermap.arity_ge_five_of_pentagonal hG y) x n

theorem exactFitp_mirror_pconsN_of_pentagonal
    (hG : G.Pentagonal) (x : G.Dart) (n : Nat) :
    exactFitp G.mirror x (mirror (pconsN n)) =
      exactFitp G x (pconsN n) := by
  rw [mirror_pconsN]
  rw [exactFitp_pconsN_eq_beq_of_pentagonal (G := G.mirror) hG.mirror x n]
  rw [exactFitp_pconsN_eq_beq_of_pentagonal (G := G) hG x n]
  rw [G.arity_mirror x]

end

end Part

end FourColor

end Schematic.Math.GraphTheory
