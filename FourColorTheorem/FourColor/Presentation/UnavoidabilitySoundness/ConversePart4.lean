import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.SourceChecks

/-! Soundness of the first converse-part transformation. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

/-- Semantic correctness target for the canonical source/target discharge-rule
fork: along a hub face, the executable `dbound2` value is the actual
transferred score `dscore2`. -/
def ConversePartSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      G.Cubic →
        G.Pentagonal →
          ∀ {x : G.Dart} {p : Part},
            Part.exactFitp G x p = true →
              Part.tightFitp G
                (G.invFace2 (G.edge (G.face (G.face x))))
                p.converse = true

def ConvPart4Sound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.Plain →
      G.Cubic →
        G.Pentagonal →
          ∀ {x : G.Dart} {p : Part},
            Part.fitp G x p = true →
              let effx : G.Dart := G.edge (G.face (G.face x))
              let up := Part.convPart4 p
              up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face effx)))) = true ∧
                ∀ {q5 : Part},
                  Part.fitp G (G.face (G.face effx)) q5 = true →
                    Part.fitp G (G.face effx) (up.2 q5) = true

def ConvPart4PointwiseSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.Plain →
      G.Cubic →
        G.Pentagonal →
          ∀ {x : G.Dart} {p q5 : Part},
            Part.fitp G x p = true →
              Part.fitp G
                (G.face (G.face (G.edge (G.face (G.face x))))) q5 =
                  true →
                let up := Part.convPart4 p
                up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                  (G.face (G.face (G.edge (G.face (G.face x))))))) =
                    true ∧
                  Part.fitp G (G.face (G.edge (G.face (G.face x))))
                    (up.2 q5) = true

def ConvPart4FaceWrapSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.Plain →
      G.Cubic →
        G.Pentagonal →
          ∀ x : G.Dart,
            (G.arity (SubpartLoc.move SubpartLoc.Pspoke G (G.face x)) =
                5 →
              G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face (G.edge (G.face (G.face x)))))) =
                G.arity (SubpartLoc.move SubpartLoc.Phat G (G.face x))) ∧
            (G.arity (SubpartLoc.move SubpartLoc.Pspoke G (G.face x)) =
                6 →
              G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face (G.edge (G.face (G.face x)))))) =
                G.arity (SubpartLoc.move SubpartLoc.Pfan1 G (G.face x))) ∧
            (G.arity (SubpartLoc.move SubpartLoc.Pspoke G (G.face x)) =
                7 →
              G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face (G.edge (G.face (G.face x)))))) =
                G.arity (SubpartLoc.move SubpartLoc.Pfan2 G (G.face x)))

theorem convPart4FaceWrapSound : ConvPart4FaceWrapSound.{u} := by
  intro G hPlain hCubic _hpenta x
  exact ⟨
    SubpartLoc.arity_phat_face_face_edge_face_face_eq_phat_face_of_spoke5
      (G := G) hPlain hCubic x,
    SubpartLoc.arity_phat_face_face_edge_face_face_eq_fan1_face_of_spoke6
      (G := G) hPlain hCubic x,
    SubpartLoc.arity_phat_face_face_edge_face_face_eq_fan2_face_of_spoke7
      (G := G) hPlain hCubic x⟩

theorem convPart4Sound_of_pointwise
    (hpoint : ConvPart4PointwiseSound.{u}) :
    ConvPart4Sound.{u} := by
  intro G hPlain hCubic hpenta x p hfit
  let effx : G.Dart := G.edge (G.face (G.face x))
  have hhead := hpoint hPlain hCubic hpenta (x := x) (p := p)
    (q5 := Part.Pnil) hfit (by simp [Part.fitp])
  constructor
  · simpa [effx] using hhead.1
  · intro q5 hq5
    have h := hpoint hPlain hCubic hpenta (x := x) (p := p)
      (q5 := q5) hfit (by simpa [effx] using hq5)
    simpa [effx] using h.2

theorem convPart4PointwiseSound_of_faceWrap
    (hwrap : ConvPart4FaceWrapSound.{u}) :
    ConvPart4PointwiseSound.{u} := by
  intro G hPlain hCubic hpenta x p q5 hfit hq5
  cases p with
  | Pnil =>
      exact Part.convPart4_pnil_sound (G := G) hpenta
  | Pcons h34 h tail =>
      cases tail with
      | Pnil =>
          exact Part.convPart4_pcons_pnil_tail_sound (G := G) hpenta
      | Pcons s4 f41 tail2 =>
          by_cases hf59 : f41 = PRange.Pr59
          · subst f41
            exact Part.convPart4_fan_free_sound
              (G := G) hPlain hCubic hpenta hfit hq5
          · cases s4 with
            | Pr55 =>
                simp [Part.fitp] at hfit
                rcases hfit with ⟨⟨Eh34, _⟩, ⟨⟨Es4, Ef41⟩, _⟩⟩
                have hs4 :
                    G.arity (SubpartLoc.move SubpartLoc.Pspoke G
                      (G.face x)) = 5 := by
                  simpa [PRange.contains] using Es4
                have htarget := (hwrap hPlain hCubic hpenta x).1 hs4
                have Es4' :
                    PRange.Pr55
                        (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
                          (G.face (G.edge (G.face (G.face x)))))) =
                      true := by
                  rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
                    (G := G) hPlain hCubic x]
                  exact Es4
                have Eh34' :
                    h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                      (G.face (G.edge (G.face (G.face x)))))) = true := by
                  rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
                    (G := G) hPlain hCubic x]
                  exact Eh34
                cases f41 <;> all_goals
                  exact ⟨by rw [htarget]; exact Ef41,
                    by simp [Part.convPart4, Part.fitp, Es4', Eh34', hq5]⟩
            | Pr66 =>
                exact Part.convPart4_spoke6_sound
                  (G := G) hPlain hCubic hpenta hfit hq5
            | Pr77 =>
                exact Part.convPart4_spoke7_sound
                  (G := G) hPlain hCubic hpenta hfit hq5
            | Pr88 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr99 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr56 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr67 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr78 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr89 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr57 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr68 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr79 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr58 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr69 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
            | Pr59 =>
                exact Part.convPart4_other_spoke_sound
                  (G := G) hpenta hf59 (by decide) (by decide) (by decide)
      | Pcons6 f41 h45 tail2 =>
          simp [Part.fitp] at hfit
          rcases hfit with ⟨⟨Eh34, _⟩, ⟨⟨⟨Es4, Ef41⟩, Eh45⟩, _⟩⟩
          have hs4 :
              G.arity (SubpartLoc.move SubpartLoc.Pspoke G (G.face x)) =
                6 := by
            simpa [PRange.contains] using Es4
          have htarget := (hwrap hPlain hCubic hpenta x).2.1 hs4
          have hhead :
              h45 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face (G.edge (G.face (G.face x))))))) = true := by
            rw [htarget]
            exact Eh45
          have Es4' :
              PRange.Pr66 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
              (G := G) hPlain hCubic x]
            exact Es4
          have Eh34' :
              h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
              (G := G) hPlain hCubic x]
            exact Eh34
          have Ef41' :
              f41 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_fan1_face_edge_face_face_eq_hat_face
              (G := G) hPlain hCubic x]
            exact Ef41
          exact ⟨hhead, by
            simp [Part.convPart4, Part.fitp, Es4', Eh34', Ef41', hq5]⟩
      | Pcons7 f41 f42 h45 tail2 =>
          simp [Part.fitp] at hfit
          rcases hfit with
            ⟨⟨Eh34, _⟩, ⟨⟨⟨⟨Es4, Ef41⟩, Ef42⟩, Eh45⟩, _⟩⟩
          have hs4 :
              G.arity (SubpartLoc.move SubpartLoc.Pspoke G (G.face x)) =
                7 := by
            simpa [PRange.contains] using Es4
          have htarget := (hwrap hPlain hCubic hpenta x).2.2 hs4
          have hhead :
              h45 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.face (G.edge (G.face (G.face x))))))) = true := by
            rw [htarget]
            exact Eh45
          have Es4' :
              PRange.Pr77 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_spoke_face_edge_face_face_eq_spoke_face
              (G := G) hPlain hCubic x]
            exact Es4
          have Eh34' :
              h34 (G.arity (SubpartLoc.move SubpartLoc.Phat G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_hat_face_edge_face_face_eq_spoke
              (G := G) hPlain hCubic x]
            exact Eh34
          have Ef41' :
              f41 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_fan1_face_edge_face_face_eq_hat_face
              (G := G) hPlain hCubic x]
            exact Ef41
          have Ef42' :
              f42 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
                (G.face (G.edge (G.face (G.face x)))))) = true := by
            rw [SubpartLoc.arity_fan2_face_edge_face_face_eq_fan1_face
              (G := G) hPlain hCubic x]
            exact Ef42
          exact ⟨hhead, by
            simp [Part.convPart4, Part.fitp, Es4', Eh34', Ef41', Ef42',
              hq5]⟩
      | Pcons8 _ _ _ _ _ =>
          exact Part.convPart4_pcons_pcons8_tail_sound (G := G) hpenta
  | Pcons6 _ _ _ =>
      exact Part.convPart4_pcons6_head_default_sound (G := G) hpenta
  | Pcons7 _ _ _ _ =>
      exact Part.convPart4_pcons7_head_default_sound (G := G) hpenta
  | Pcons8 _ _ _ _ _ =>
      exact Part.convPart4_pcons8_head_default_sound (G := G) hpenta

theorem convPart4Sound_of_faceWrap
    (hwrap : ConvPart4FaceWrapSound.{u}) :
    ConvPart4Sound.{u} :=
  convPart4Sound_of_pointwise
    (convPart4PointwiseSound_of_faceWrap hwrap)

theorem convPart4Sound : ConvPart4Sound.{u} :=
  convPart4Sound_of_faceWrap convPart4FaceWrapSound


end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
