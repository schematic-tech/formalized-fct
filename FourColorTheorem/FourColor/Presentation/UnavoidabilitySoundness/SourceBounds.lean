import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.TransferBounds

/-! Small-source bounds and their checker consequences. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

theorem sourceRulesSubsetPconsN_of_all {n : Nat}
    (hall :
      ((Discharge.pickSourceDrules n Discharge.theDrules).all
        (fun r =>
          decide (Part.cmp r (Part.pconsN n) = PartRel.Psubset))) = true) :
    ∀ r ∈ Discharge.pickSourceDrules n Discharge.theDrules,
      Part.cmp r (Part.pconsN n) = PartRel.Psubset := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp hall r hr)

private theorem sourceRulesSubsetPconsN_all_small :
    ((Discharge.pickSourceDrules 5 Discharge.theDrules).all
        (fun r =>
          decide (Part.cmp r (Part.pconsN 5) = PartRel.Psubset))) = true ∧
      ((Discharge.pickSourceDrules 6 Discharge.theDrules).all
        (fun r =>
          decide (Part.cmp r (Part.pconsN 6) = PartRel.Psubset))) = true ∧
      ((Discharge.pickSourceDrules 7 Discharge.theDrules).all
        (fun r =>
          decide (Part.cmp r (Part.pconsN 7) = PartRel.Psubset))) = true ∧
      ((Discharge.pickSourceDrules 8 Discharge.theDrules).all
        (fun r =>
          decide (Part.cmp r (Part.pconsN 8) = PartRel.Psubset))) = true := by
  fct_decide

theorem sourceRulesSubsetPconsN_all_five :
    ((Discharge.pickSourceDrules 5 Discharge.theDrules).all
      (fun r =>
        decide (Part.cmp r (Part.pconsN 5) = PartRel.Psubset))) = true :=
  sourceRulesSubsetPconsN_all_small.1

theorem sourceRulesSubsetPconsN_all_six :
    ((Discharge.pickSourceDrules 6 Discharge.theDrules).all
      (fun r =>
        decide (Part.cmp r (Part.pconsN 6) = PartRel.Psubset))) = true :=
  sourceRulesSubsetPconsN_all_small.2.1

theorem sourceRulesSubsetPconsN_all_seven :
    ((Discharge.pickSourceDrules 7 Discharge.theDrules).all
      (fun r =>
        decide (Part.cmp r (Part.pconsN 7) = PartRel.Psubset))) = true :=
  sourceRulesSubsetPconsN_all_small.2.2.1

theorem sourceRulesSubsetPconsN_all_eight :
    ((Discharge.pickSourceDrules 8 Discharge.theDrules).all
      (fun r =>
        decide (Part.cmp r (Part.pconsN 8) = PartRel.Psubset))) = true :=
  sourceRulesSubsetPconsN_all_small.2.2.2

theorem sourceRulesSubsetPconsN_five :
    ∀ r ∈ Discharge.pickSourceDrules 5 Discharge.theDrules,
      Part.cmp r (Part.pconsN 5) = PartRel.Psubset :=
  sourceRulesSubsetPconsN_of_all sourceRulesSubsetPconsN_all_five

theorem sourceRulesSubsetPconsN_six :
    ∀ r ∈ Discharge.pickSourceDrules 6 Discharge.theDrules,
      Part.cmp r (Part.pconsN 6) = PartRel.Psubset :=
  sourceRulesSubsetPconsN_of_all sourceRulesSubsetPconsN_all_six

theorem sourceRulesSubsetPconsN_seven :
    ∀ r ∈ Discharge.pickSourceDrules 7 Discharge.theDrules,
      Part.cmp r (Part.pconsN 7) = PartRel.Psubset :=
  sourceRulesSubsetPconsN_of_all sourceRulesSubsetPconsN_all_seven

theorem sourceRulesSubsetPconsN_eight :
    ∀ r ∈ Discharge.pickSourceDrules 8 Discharge.theDrules,
      Part.cmp r (Part.pconsN 8) = PartRel.Psubset :=
  sourceRulesSubsetPconsN_of_all sourceRulesSubsetPconsN_all_eight

theorem sourceBoundForArity_of_checkDbound1
    {n : Nat}
    (hsubset :
      ∀ r ∈ Discharge.pickSourceDrules n Discharge.theDrules,
        Part.cmp r (Part.pconsN n) = PartRel.Psubset)
    (hredpart : Presentation.RedpartSound.{u})
    (hcheck :
      Discharge.Hubcap.checkDbound1 Presentation.theRedpart
        (Discharge.theDruleFork n) (Part.pconsN n) 5 = true) :
    SourceBoundForArity.{u} n := by
  intro G hG x hx
  by_cases hfull : Part.exactFitp G x (Part.pconsN n) = true
  · exact checkDbound1Rec_sound hredpart hG x
      (m := (Discharge.theDruleFork n).sourceDrules.length + 1)
      (p := Part.pconsN n)
      (rs := (Discharge.theDruleFork n).sourceDrules)
      (ns := 5)
      (by simpa [Discharge.Hubcap.checkDbound1] using hcheck)
      hfull
  · have hzero :
        G.dbound1 (Discharge.pickSourceDrules n Discharge.theDrules) x = 0 := by
      apply G.dbound1_eq_zero_of_forall_fitp_false
      intro r hr
      cases hrfit : Part.fitp G x r with
      | false => rfl
      | true =>
          have hpfit :
              Part.fitp G x (Part.pconsN n) = true :=
            Part.fitp_of_cmp_eq_subset (G := G) r (Part.pconsN n) x
              (hsubset r hr) hrfit
          have hexact :
              Part.exactFitp G x (Part.pconsN n) = true := by
            simp [Part.exactFitp, hx, hpfit]
          exact False.elim (hfull hexact)
    rw [hzero]
    omega

theorem sourceCheckSoundForArity_of_subset
    {n : Nat}
    (hsubset :
      ∀ r ∈ Discharge.pickSourceDrules n Discharge.theDrules,
        Part.cmp r (Part.pconsN n) = PartRel.Psubset) :
    SourceCheckSoundForArity.{u} n := by
  intro hredpart hcheck
  exact sourceBoundForArity_of_checkDbound1 hsubset hredpart hcheck

def SmallSourceCheckSound : Prop :=
  SourceCheckSoundForArity.{u} 5 ∧
    SourceCheckSoundForArity.{u} 6 ∧
      SourceCheckSoundForArity.{u} 7 ∧
        SourceCheckSoundForArity.{u} 8

theorem theSmallSourceCheckSound : SmallSourceCheckSound.{u} :=
  ⟨sourceCheckSoundForArity_of_subset sourceRulesSubsetPconsN_five,
    sourceCheckSoundForArity_of_subset sourceRulesSubsetPconsN_six,
    sourceCheckSoundForArity_of_subset sourceRulesSubsetPconsN_seven,
    sourceCheckSoundForArity_of_subset sourceRulesSubsetPconsN_eight⟩

theorem smallSourceBounds_of_checkSound
    (hredpart : Presentation.RedpartSound.{u})
    (hsound : SmallSourceCheckSound.{u}) :
    SmallSourceBounds.{u} := by
  rcases theSmallSourceChecks with ⟨h5check, h6check, h7check, h8check⟩
  rcases hsound with ⟨h5sound, h6sound, h7sound, h8sound⟩
  exact ⟨
    h5sound hredpart h5check,
    h6sound hredpart h6check,
    h7sound hredpart h7check,
    h8sound hredpart h8check⟩

theorem smallSourceBoundForMinimalCounterexamples_of_checkSound
    (hredpart : Presentation.RedpartSound.{u})
    (hsound : SmallSourceCheckSound.{u}) :
    SmallSourceBoundForMinimalCounterexamples.{u} :=
  smallSourceBoundForMinimalCounterexamples_of_sourceBounds
    (smallSourceBounds_of_checkSound hredpart hsound)

theorem smallSourceBounds_of_redpart
    (hredpart : Presentation.RedpartSound.{u}) :
    SmallSourceBounds.{u} :=
  smallSourceBounds_of_checkSound hredpart theSmallSourceCheckSound

theorem smallSourceBoundForMinimalCounterexamples_of_redpart
    (hredpart : Presentation.RedpartSound.{u}) :
    SmallSourceBoundForMinimalCounterexamples.{u} :=
  smallSourceBoundForMinimalCounterexamples_of_sourceBounds
    (smallSourceBounds_of_redpart hredpart)

theorem dscore1LeFiveMinimalCounterexamples_of_smallSourceBound
    (hsource : SmallSourceBoundForMinimalCounterexamples.{u}) :
    Dscore1LeFiveMinimalCounterexamples.{u} := by
  intro G hG y
  by_cases hsmall : PRange.Pr58 (G.arity (G.invFace2 y)) = true
  · rw [G.dscore1_eq_dbound1_source_invFace2 y]
    exact_mod_cast hsource G hG (G.invFace2 y) hsmall
  · have hlarge : PRange.Pr58 (G.arity (G.invFace2 y)) = false := by
      cases h : PRange.Pr58 (G.arity (G.invFace2 y)) with
      | false => rfl
      | true => exact False.elim (hsmall h)
    rw [G.dscore1_eq_zero_of_invFace2_not_Pr58 hlarge]
    omega

theorem dscore1LeFiveMinimalCounterexamples_of_sourceBounds
    (hbounds : SmallSourceBounds.{u}) :
    Dscore1LeFiveMinimalCounterexamples.{u} :=
  dscore1LeFiveMinimalCounterexamples_of_smallSourceBound
    (smallSourceBoundForMinimalCounterexamples_of_sourceBounds hbounds)

theorem dscore1LeFiveMinimalCounterexamples_of_checkSound
    (hredpart : Presentation.RedpartSound.{u})
    (hsound : SmallSourceCheckSound.{u}) :
    Dscore1LeFiveMinimalCounterexamples.{u} :=
  dscore1LeFiveMinimalCounterexamples_of_smallSourceBound
    (smallSourceBoundForMinimalCounterexamples_of_checkSound
      hredpart hsound)

theorem dscore1LeFiveMinimalCounterexamples_of_redpart
    (hredpart : Presentation.RedpartSound.{u}) :
    Dscore1LeFiveMinimalCounterexamples.{u} :=
  dscore1LeFiveMinimalCounterexamples_of_smallSourceBound
    (smallSourceBoundForMinimalCounterexamples_of_redpart hredpart)

theorem validHubDscore1LeFive_of_minimalCounterexamples
    (hcap : Dscore1LeFiveMinimalCounterexamples.{u}) :
    ValidHubDscore1LeFive.{u} := by
  intro G _x hvalid y
  exact hcap G hvalid.1 y

theorem validHubArityUpperBound_of_dscore1LeFive
    (hcap : ValidHubDscore1LeFive.{u}) :
    ValidHubArityUpperBound.{u} := by
  intro G x hvalid
  exact G.arity_le_eleven_of_dscore_pos_of_dscore1_le_five
    (hcap G x hvalid) hvalid.2

theorem positiveHubInPresentationRange_of_bounds
    (hexists : PositiveHubExists.{u})
    (hpentagonal : ValidHubPentagonal.{u})
    (hupper : ValidHubArityUpperBound.{u}) :
    PositiveHubInPresentationRange.{u} := by
  intro G hG
  rcases hexists G hG with ⟨x, hscore⟩
  have hvalid : Presentation.ValidHub G x := ⟨hG, hscore⟩
  exact ⟨x, hscore,
    Hypermap.arity_ge_five_of_pentagonal (hpentagonal G x hvalid) x,
    hupper G x hvalid⟩


end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
