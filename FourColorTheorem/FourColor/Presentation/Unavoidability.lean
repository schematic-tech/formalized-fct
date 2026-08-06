import FourColorTheorem.FourColor.Presentation.Language

/-!
Unavoidability collation interface.

Coq `unavoidability.v` combines two ingredients: a positive-score hub in every
minimal counterexample has arity in `5..11`, and the seven presentation files
exclude exactly those arities. This file states and proves that collation
interface; the concrete ingredients are discharged in downstream modules.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Unavoidability

noncomputable section

universe u

/-- The score/discharge side of Coq `unavoidability`: every minimal
counterexample contains a positive-score hub whose arity lies between 5 and 11. -/
def PositiveHubInPresentationRange : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample →
    ∃ x : G.Dart, 0 < G.dscore x ∧ 5 ≤ G.arity x ∧ G.arity x ≤ 11

/-- The presentation side: all arities handled by `present5.v` through
`present11.v` are excluded. -/
def PresentationExclusions : Prop :=
  ∀ n : Nat, 5 ≤ n → n ≤ 11 → Presentation.ExcludedArity.{u} n

/-- Conditional unavoidability: once the score range and presentation exclusions
are supplied, no minimal counterexample remains. -/
theorem no_minimalCounterexample
    (hpos : PositiveHubInPresentationRange.{u})
    (hexcl : PresentationExclusions.{u})
    (hred : Presentation.Reducibility) :
    ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample := by
  intro G hG
  rcases hpos G hG with ⟨x, hscore, hlo, hhi⟩
  have hx : Presentation.ValidHub G x := ⟨hG, hscore⟩
  exact (hexcl (G.arity x) hlo hhi hred G x hx) rfl

end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
