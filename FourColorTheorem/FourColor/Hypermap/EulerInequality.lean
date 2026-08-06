import FourColorTheorem.FourColor.Hypermap.Component
import Schematic.Math.GraphTheory.Embedding.EulerCharacteristic
import FourColorTheorem.FourColor.Hypermap.WalkupCubicity

/-!
Euler-difference nonnegativity.

The Walkup count equations imply the standard connected-hypermap Euler
inequality by induction on the number of darts: deleting one dart by
`WalkupE` preserves enough Euler-count structure to lift
`eulerRight ≤ eulerLeft` from the smaller hypermap.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Unavoidability

universe u

theorem connectedEulerDiffNonnegative_proved :
    ConnectedEulerDiffNonnegative.{u} := by
  intro G _hG
  exact Hypermap.eulerRight_le_eulerLeft G

theorem componentEulerDiffNonnegative_proved :
    ComponentEulerDiffNonnegative.{u} :=
  componentEulerDiffNonnegative_of_connectedEulerDiffNonnegative
    connectedEulerDiffNonnegative_proved

theorem componentEulerDiffAdditive_proved :
    ComponentEulerDiffAdditive.{u} :=
  componentEulerDiffAdditive_of_nonnegative
    componentEulerDiffNonnegative_proved

theorem componentEulerPlanarInherited_proved :
    ComponentEulerPlanarInherited.{u} :=
  componentEulerPlanarInherited_of_eulerDiffNonnegative
    componentEulerDiffNonnegative_proved

theorem connectedMinimalCounterexamples_proved :
    ConnectedMinimalCounterexamples.{u} :=
  connectedMinimalCounterexamples_of_componentEulerPlanarInherited
    componentEulerPlanarInherited_proved

theorem evenGenusMinimalCounterexamples_proved :
    EvenGenusMinimalCounterexamples.{u} := by
  intro G _hG
  exact Hypermap.evenGenus G

theorem plainCubicPentagonalMinimalCounterexamples_of_faceArity_proved
    (harity : FaceArityGeFiveMinimalCounterexamples.{u}) :
    PlainCubicPentagonalMinimalCounterexamples.{u} :=
  plainCubicPentagonalMinimalCounterexamples_of_faceArityGeFive
    plainCubicMinimalCounterexamples_proved harity

theorem structuralCountFactsForMinimalCounterexamples_proved :
    StructuralCountFactsForMinimalCounterexamples.{u} := by
  intro G hG
  exact ⟨connectedMinimalCounterexamples_proved G hG,
    cubicMinimalCounterexamples_proved G hG,
    evenGenusMinimalCounterexamples_proved G hG⟩

theorem eulerCountFormulaForMinimalCounterexamples_proved :
    EulerCountFormulaForMinimalCounterexamples.{u} :=
  eulerCountFormula_of_structuralCountFacts
    structuralCountFactsForMinimalCounterexamples_proved

theorem positiveHubExists_proved :
    PositiveHubExists.{u} :=
  positiveHubExists_of_countFormula
    eulerCountFormulaForMinimalCounterexamples_proved

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
