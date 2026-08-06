import FourColorTheorem.FourColor.Hypermap.WalkupCubicity
import FourColorTheorem.FourColor.Hypermap.Component
import FourColorTheorem.FourColor.Hypermap.EulerInequality
import FourColorTheorem.FourColor.Presentation.RedPartSoundness

/-!
Combinatorial four-colour theorem bridge.

This file isolates the final minimal-counterexample reduction step for the
hypermap formulation.  The theorem here is conditional on the standard
existence of a minimal counterexample from any non-colourable planar
bridgeless plain precubic hypermap; unavoidability supplies the negation of
such minimal counterexamples.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CombinatorialFourColor

universe u

/-- No minimal counterexample exists in the hypermap formulation. -/
def NoMinimalCounterexample : Prop :=
  ∀ G : Hypermap.{u}, ¬ G.MinimalCounterexample

/-- Standard reduction from a non-four-colourable geometric hypermap to a
minimal counterexample. -/
def MinimalCounterexampleReduction : Prop :=
  ∀ G : Hypermap.{u},
    G.PlanarBridgelessPlainPrecubic →
      Not G.FourColorable →
        ∃ H : Hypermap.{u}, H.MinimalCounterexample

/-- Hypermap formulation of the combinatorial four-colour theorem. -/
def HypermapFourColorTheorem : Prop :=
  ∀ G : Hypermap.{u}, G.PlanarBridgelessPlainPrecubic → G.FourColorable

/-- A universe-zero proof of the finite hypermap four-colour theorem proves
the theorem in every universe.  Relabel the finite dart type onto `Fin`, apply
the universe-zero theorem, and pull the resulting coloring back. -/
theorem hypermapFourColorTheorem_of_zero
    (hfct : HypermapFourColorTheorem.{0}) :
    HypermapFourColorTheorem.{u} := by
  intro G hgeometry
  let e := Hypermap.Iso.finRelabelIso G
  have hgeometry0 :
      (Hypermap.Iso.finRelabel G).PlanarBridgelessPlainPrecubic :=
    e.planarBridgelessPlainPrecubic hgeometry
  exact e.fourColorable_iff.mpr (hfct _ hgeometry0)

theorem hypermapFourColor_of_no_minimalCounterexample
    (hred : MinimalCounterexampleReduction.{u})
    (hno : NoMinimalCounterexample.{u}) :
    HypermapFourColorTheorem.{u} := by
  intro G hgeom
  by_contra hcolor
  rcases hred G hgeom hcolor with ⟨H, hH⟩
  exact hno H hH

/-- Every non-four-colourable geometric hypermap has a minimal
counterexample, by well-founded descent on the finite dart count. -/
theorem minimalCounterexampleReduction :
    MinimalCounterexampleReduction.{u} := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ G : Hypermap.{u},
      Fintype.card G.Dart = n →
        G.PlanarBridgelessPlainPrecubic →
          Not G.FourColorable →
            ∃ H : Hypermap.{u}, H.MinimalCounterexample
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard hgeom hnoncolor
      by_cases hmin :
          ∀ G' : Hypermap.{u},
            G'.PlanarBridgelessPlainPrecubic →
              Fintype.card G'.Dart < Fintype.card G.Dart →
                G'.FourColorable
      · exact ⟨G, {
          geometry := hgeom
          noncolorable := hnoncolor
          minimal := hmin }⟩
      · push Not at hmin
        rcases hmin with ⟨G', hgeom', hcard', hnoncolor'⟩
        exact ih (Fintype.card G'.Dart)
          (by simpa [hcard] using hcard') G' rfl hgeom' hnoncolor'
  intro G hgeom hnoncolor
  exact hP (Fintype.card G.Dart) G rfl hgeom hnoncolor

theorem hypermapFourColor_of_no_minimalCounterexample_reduction
    (hno : NoMinimalCounterexample.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample
    minimalCounterexampleReduction hno


end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
