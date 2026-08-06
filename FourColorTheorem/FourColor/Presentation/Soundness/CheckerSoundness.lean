import FourColorTheorem.FourColor.Presentation.Soundness.SplitApplications

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

/-- Soundness target for the specialized redpart checker.  This is the Lean
counterpart of Coq's `no_fit_the_redpart`, parameterized so the expensive
certificate proof stays outside the lightweight import path. -/
def RedpartSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (x : G.Dart) (p : Part),
        theRedpart p = true →
          Part.exactFitp G x p = false

theorem successful_of_theRedpart_sound
    (hsound : RedpartSound.{u})
    {p : Part}
    (hcheck : theRedpart p = true) :
    Successful.{u} p := by
  intro G x hx
  exact hsound hx.1 x p hcheck

theorem succeedsIn_of_reducibilityCheck_sound
    (hsound : RedpartSound.{u})
    {g : CheckGoal}
    (hcheck : reducibilityCheck g = true) :
    SucceedsIn.{u} g.p0 g.p :=
  succeedsIn_of_successful
    (successful_of_theRedpart_sound.{u} hsound
      (by simpa [reducibilityCheck] using hcheck))

/-- Soundness target for hubcap checks. It packages the semantic theorem
corresponding to Coq's `hubcap_fit_bound` while keeping the expensive proof
outside the lightweight import path. -/
def HubcapSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (p : Part) (hc : Discharge.Hubcap),
        Discharge.Hubcap.cover p.size hc = true →
          Discharge.Hubcap.fit p.size theRedpart
            (Discharge.theDruleFork p.size) p hc = true →
              ∀ x : G.Dart,
                0 < G.dscore x →
                  Part.exactFitp G x p = false

theorem successful_of_hubcapCheck_sound
    (hhubcap : HubcapSound.{u})
    {g : CheckGoal} {hc : Discharge.Hubcap}
    (hcheck : hubcapCheck g hc = true) :
    Successful.{u} g.p := by
  intro G x hx
  have hboth :
      Discharge.Hubcap.cover g.p.size hc = true ∧
        Discharge.Hubcap.fit g.p.size theRedpart
          (Discharge.theDruleFork g.p.size) g.p hc = true := by
    simpa [hubcapCheck] using hcheck
  exact hhubcap hx.1 g.p hc hboth.1 hboth.2 x hx.2

theorem succeedsIn_of_hubcapCheck_sound
    (hhubcap : HubcapSound.{u})
    {g : CheckGoal} {hc : Discharge.Hubcap}
    (hcheck : hubcapCheck g hc = true) :
    SucceedsIn.{u} g.p0 g.p :=
  succeedsIn_of_successful
    (successful_of_hubcapCheck_sound.{u}
      hhubcap hcheck)

/-- If the full free part is successful, then the corresponding hub arity is
excluded. -/
theorem excludedArity_of_successful_full_part
    {n : Nat}
    (hfit : FullPartFitsValidHub.{u} n)
    (hsuccess : Successful.{u} (Part.pconsN n)) :
    ExcludedArity.{u} n := by
  intro _ G x hx harity
  have hfits : Part.exactFitp G x (Part.pconsN n) = true :=
    hfit G x hx harity
  have hfails : Part.exactFitp G x (Part.pconsN n) = false :=
    hsuccess x hx
  rw [hfits] at hfails
  cases hfails

/-- The common presentation shape: proving that the full part succeeds in
itself excludes that arity. -/
theorem excludedArity_of_full_part_succeeds
    {n : Nat}
    (hfit : FullPartFitsValidHub.{u} n)
    (hsucceeds :
      SucceedsIn.{u} (Part.pconsN n) (Part.pconsN n)) :
    ExcludedArity.{u} n :=
  excludedArity_of_successful_full_part.{u} hfit
    (hsucceeds (forcedPart_refl.{u} (Part.pconsN n)))

theorem excludedArity_of_full_part_succeeds_of_pentagonal
    {n : Nat}
    (hPentagonal : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.Pentagonal)
    (hsucceeds :
      SucceedsIn.{u} (Part.pconsN n) (Part.pconsN n)) :
    ExcludedArity.{u} n :=
  excludedArity_of_full_part_succeeds.{u}
    (fullPartFitsValidHub_of_pentagonal.{u} hPentagonal)
    hsucceeds


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
