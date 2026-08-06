import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness
import Schematic.Math.GraphTheory.Embedding.HypermapComponent

/-!
Connectedness reduction for minimal counterexamples.

The reusable component construction is in `HypermapComponent`; this file keeps
only the FCT-specific minimal-counterexample consequences.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor


namespace Unavoidability

open Hypermap

universe u

noncomputable section

/-- The remaining Euler-topological component inheritance needed for the
minimal-counterexample connectedness argument.  All permutation and colouring
parts of the argument are proved below. -/
def ComponentEulerPlanarInherited : Prop :=
  ∀ (G : Hypermap.{u}) (c : G.Component),
    G.EulerPlanar → (G.componentHypermap c).EulerPlanar

/-- A count-level form of component planarity: the Euler difference of each
component is bounded by the Euler difference of the ambient hypermap. -/
def ComponentEulerDiffMonotone : Prop :=
  ∀ (G : Hypermap.{u}) (c : G.Component),
    (G.componentHypermap c).eulerLeft -
        (G.componentHypermap c).eulerRight ≤
      G.eulerLeft - G.eulerRight

/-- Additivity of the truncated natural Euler differences over generated
components.  Proving this from the Euler orbit decompositions above is the
remaining arithmetic/topological step behind component planarity. -/
def ComponentEulerDiffAdditive : Prop :=
  ∀ G : Hypermap.{u},
    (∑ c : G.Component,
      ((G.componentHypermap c).eulerLeft -
        (G.componentHypermap c).eulerRight)) =
      G.eulerLeft - G.eulerRight

/-- Nonnegativity of the Euler difference on each generated component.  With
the component orbit decompositions already proved, this implies natural
Euler-difference additivity. -/
def ComponentEulerDiffNonnegative : Prop :=
  ∀ (G : Hypermap.{u}) (c : G.Component),
    (G.componentHypermap c).eulerRight ≤
      (G.componentHypermap c).eulerLeft

/-- The standard connected-hypermap Euler inequality.  This is the permutation
genus inequality `edge cycles + node cycles + face cycles ≤ darts + 2` for a
connected generated dart system. -/
def ConnectedEulerDiffNonnegative : Prop :=
  ∀ G : Hypermap.{u}, G.Connected → G.eulerRight ≤ G.eulerLeft

theorem componentEulerDiffNonnegative_of_connectedEulerDiffNonnegative
    (hconn : ConnectedEulerDiffNonnegative.{u}) :
    ComponentEulerDiffNonnegative.{u} := by
  intro G c
  exact hconn (G.componentHypermap c)
    (Hypermap.componentHypermap.connected (G := G) (c := c))

theorem componentEulerDiffAdditive_of_nonnegative
    (hnonneg : ComponentEulerDiffNonnegative.{u}) :
    ComponentEulerDiffAdditive.{u} := by
  intro G
  have hsum :=
    Hypermap.componentHypermap.sum_nat_sub_eq_sum_sub_of_le
      (s := (Finset.univ : Finset G.Component))
      (a := fun c : G.Component => (G.componentHypermap c).eulerLeft)
      (b := fun c : G.Component => (G.componentHypermap c).eulerRight)
      (by
        intro c _
        exact hnonneg G c)
  calc
    (∑ c : G.Component,
      ((G.componentHypermap c).eulerLeft -
        (G.componentHypermap c).eulerRight)) =
        (∑ c : G.Component, (G.componentHypermap c).eulerLeft) -
          (∑ c : G.Component, (G.componentHypermap c).eulerRight) := by
          simpa using hsum.symm
    _ = G.eulerLeft - G.eulerRight := by
          rw [← Hypermap.componentHypermap.eulerLeft_eq_sum_components (G := G),
            ← Hypermap.componentHypermap.eulerRight_eq_sum_components (G := G)]

theorem componentEulerDiffMonotone_of_additive
    (hadd : ComponentEulerDiffAdditive.{u}) :
    ComponentEulerDiffMonotone.{u} := by
  intro G c
  have hsingle :
      (G.componentHypermap c).eulerLeft -
          (G.componentHypermap c).eulerRight ≤
        ∑ d : G.Component,
          ((G.componentHypermap d).eulerLeft -
            (G.componentHypermap d).eulerRight) :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset G.Component))
      (f := fun d : G.Component =>
        (G.componentHypermap d).eulerLeft -
          (G.componentHypermap d).eulerRight)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simpa [hadd G] using hsingle

theorem componentEulerPlanarInherited_of_eulerDiffMonotone
    (hmono : ComponentEulerDiffMonotone.{u}) :
    ComponentEulerPlanarInherited.{u} := by
  intro G c hplanar
  unfold Hypermap.EulerPlanar Hypermap.genus at hplanar ⊢
  have hle :
      ((G.componentHypermap c).eulerLeft -
          (G.componentHypermap c).eulerRight) / 2 ≤
        (G.eulerLeft - G.eulerRight) / 2 :=
    Nat.div_le_div_right (hmono G c)
  omega

theorem componentEulerPlanarInherited_of_eulerDiffAdditive
    (hadd : ComponentEulerDiffAdditive.{u}) :
    ComponentEulerPlanarInherited.{u} :=
  componentEulerPlanarInherited_of_eulerDiffMonotone
    (componentEulerDiffMonotone_of_additive hadd)

theorem componentEulerPlanarInherited_of_eulerDiffNonnegative
    (hnonneg : ComponentEulerDiffNonnegative.{u}) :
    ComponentEulerPlanarInherited.{u} :=
  componentEulerPlanarInherited_of_eulerDiffAdditive
    (componentEulerDiffAdditive_of_nonnegative hnonneg)

theorem componentEulerPlanarInherited_of_connectedEulerDiffNonnegative
    (hconn : ConnectedEulerDiffNonnegative.{u}) :
    ComponentEulerPlanarInherited.{u} :=
  componentEulerPlanarInherited_of_eulerDiffNonnegative
    (componentEulerDiffNonnegative_of_connectedEulerDiffNonnegative hconn)

theorem connectedMinimalCounterexamples_of_componentEulerPlanarInherited
    (hplanar : ComponentEulerPlanarInherited.{u}) :
    ConnectedMinimalCounterexamples.{u} := by
  intro G hG
  have hnonempty : Nonempty G.Dart :=
    G.nonempty_of_not_fourColorable hG.noncolorable
  refine ⟨hnonempty, ?_⟩
  by_contra hpre
  rcases G.exists_component_not_fourColorable_of_not_fourColorable
      hG.noncolorable with
    ⟨c, hc⟩
  have hsmall :
      Fintype.card (G.componentHypermap c).Dart < Fintype.card G.Dart :=
    componentHypermap.card_lt_of_not_preconnected (G := G) hpre c
  have hgeom :
      (G.componentHypermap c).PlanarBridgelessPlainPrecubic :=
    componentHypermap.planarBridgelessPlainPrecubic
      (G := G) (c := c) (hplanar G c hG.planar) hG.geometry
  exact hc (hG.colorable_of_smaller (G.componentHypermap c) hgeom hsmall)

end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
