import Schematic.Math.GraphTheory.Embedding.Counts
import FourColorTheorem.FourColor.Presentation.Soundness
import FourColorTheorem.FourColor.Presentation.Unavoidability

/-!
Lightweight decomposition of the unavoidability side conditions.

Coq `unavoidability.v` obtains a positive-score hub, proves its lower arity
bound from pentagonality, and proves the upper bound by the discharging cap.
This file isolates those inputs as precise Lean targets and proves their
collation into `PositiveHubInPresentationRange` and
`PresentationExclusions`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Unavoidability

noncomputable section

universe u

/-- The score-total part of unavoidability: every minimal counterexample has a
positive-score hub. -/
def PositiveHubExists : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample →
    ∃ x : G.Dart, 0 < G.dscore x

/-- The remaining Euler/discharge total-charge theorem needed for the
positive-hub step.  Coq proves this as `dscore_roots`: total discharged face
score is `120`. -/
def FaceDscoreTotalForMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.faceDscoreSum = 120

def EulerChargeFormulaForMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample →
    60 * (Fintype.card G.FaceOrbit : Int) -
        10 * (Fintype.card G.Dart : Int) =
      120

/-- The count-level Euler side conditions for a planar connected cubic
hypermap.  These are the reusable targets below the discharging total: one
component, two darts per edge orbit, three darts per node orbit, and exact
Euler equality. -/
def EulerCountFormulaForMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample →
    G.componentCount = 1 ∧
      Fintype.card G.Dart = 2 * G.edgeOrbitCount ∧
      Fintype.card G.Dart = 3 * G.nodeOrbitCount ∧
      G.eulerLeft = G.eulerRight

/-- The geometric structural facts that remain below the Euler count package.
Minimal counterexamples already carry plainness and Euler-planarity; proving
connectedness, cubicity, and the nontruncated even-genus formula supplies the
count package. -/
def StructuralCountFactsForMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample →
    G.Connected ∧ G.Cubic ∧ G.EvenGenus

/-- Connectedness of minimal counterexamples.  Coq proves this by decomposing a
disconnected counterexample into smaller components. -/
def ConnectedMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Connected

/-- Cubicity of minimal counterexamples.  Coq derives this from the minimality
argument excluding degree-one and degree-two nodes. -/
def CubicMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic

/-- Plain-cubic geometry of minimal counterexamples.  Plainness is part of the
minimal-counterexample record; cubicity is proved by the Walkup low-node
exclusion. -/
def PlainCubicMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.PlainCubic

/-- The Coq `plain_cubic_pentagonal` geometry package specialized to minimal
counterexamples. -/
def PlainCubicPentagonalMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.PlainCubicPentagonal

/-- The local low-degree exclusions that imply cubicity for the already
precubic minimal counterexamples. -/
def NoShortNodeOrbitsMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    G.node x ≠ x ∧ G.node (G.node x) ≠ x

/-- The remaining nontrivial local low-degree exclusion: no node orbit of
period two in a minimal counterexample.  Fixed nodes are already excluded by
bridgelessness. -/
def NoTwoNodeOrbitsMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    G.node (G.node x) ≠ x

theorem noShortNodeOrbitsMinimalCounterexamples_of_noTwoNodeOrbits
    (htwo : NoTwoNodeOrbitsMinimalCounterexamples.{u}) :
    NoShortNodeOrbitsMinimalCounterexamples.{u} := by
  intro G hG x
  exact ⟨Hypermap.MinimalCounterexample.node_ne_self hG x, htwo G hG x⟩

/-- The nontruncated Euler genus identity for minimal counterexamples. -/
def EvenGenusMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.EvenGenus

theorem cubicMinimalCounterexamples_of_noShortNodeOrbits
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u}) :
    CubicMinimalCounterexamples.{u} := by
  intro G hG
  exact Hypermap.Precubic.cubic_of_no_short_node_orbits
    (G := G)
    (Hypermap.MinimalCounterexample.precubic hG)
    (fun x => (hshort G hG x).1)
    (fun x => (hshort G hG x).2)

theorem plainCubicMinimalCounterexamples_of_cubic
    (hcubic : CubicMinimalCounterexamples.{u}) :
    PlainCubicMinimalCounterexamples.{u} := by
  intro G hG
  exact {
    plain := Hypermap.MinimalCounterexample.plain hG
    cubic := hcubic G hG }

theorem plainCubicMinimalCounterexamples_of_noShortNodeOrbits
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u}) :
    PlainCubicMinimalCounterexamples.{u} :=
  plainCubicMinimalCounterexamples_of_cubic
    (cubicMinimalCounterexamples_of_noShortNodeOrbits hshort)

theorem mirrorDscoreTransport_of_cubicMinimalCounterexamples
    (hcubic : CubicMinimalCounterexamples.{u}) :
    Presentation.MirrorDscoreTransport.{u} :=
  Presentation.mirrorDscoreTransport_of_minimalCounterexample_cubic hcubic

theorem mirrorDscoreTransport_of_noShortNodeOrbits
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u}) :
    Presentation.MirrorDscoreTransport.{u} :=
  mirrorDscoreTransport_of_cubicMinimalCounterexamples
    (cubicMinimalCounterexamples_of_noShortNodeOrbits hshort)

theorem mirrorValidHubTransport_of_noShortNodeOrbits
    (hshort : NoShortNodeOrbitsMinimalCounterexamples.{u}) :
    Presentation.MirrorValidHubTransport.{u} :=
  Presentation.mirrorValidHubTransport_of_dscore_mirror
    (mirrorDscoreTransport_of_noShortNodeOrbits hshort)

theorem structuralCountFacts_of_parts
    (hconnected : ConnectedMinimalCounterexamples.{u})
    (hcubic : CubicMinimalCounterexamples.{u})
    (heven : EvenGenusMinimalCounterexamples.{u}) :
    StructuralCountFactsForMinimalCounterexamples.{u} := by
  intro G hG
  exact ⟨hconnected G hG, hcubic G hG, heven G hG⟩

theorem eulerCountFormula_of_structuralCountFacts
    (hstruct : StructuralCountFactsForMinimalCounterexamples.{u}) :
    EulerCountFormulaForMinimalCounterexamples.{u} := by
  intro G hG
  rcases hstruct G hG with ⟨hconnected, hcubic, heven⟩
  exact ⟨
    Hypermap.Connected.componentCount_eq_one (G := G) hconnected,
    Hypermap.Plain.card_dart_eq_two_mul_edgeOrbitCount (G := G)
      (Hypermap.MinimalCounterexample.plain hG),
    Hypermap.Cubic.card_dart_eq_three_mul_nodeOrbitCount (G := G) hcubic,
    Hypermap.euler_eq_of_evenGenus_planar (G := G) heven
      (Hypermap.MinimalCounterexample.planar hG)⟩

theorem eulerChargeFormula_of_countFormula
    (hcounts : EulerCountFormulaForMinimalCounterexamples.{u}) :
    EulerChargeFormulaForMinimalCounterexamples.{u} := by
  intro G hG
  rcases hcounts G hG with ⟨hcomp, hedge, hnode, heuler⟩
  exact G.eulerChargeFormula_of_counts hcomp hedge hnode heuler

theorem faceDscoreTotal_of_eulerChargeFormula
    (heuler : EulerChargeFormulaForMinimalCounterexamples.{u}) :
    FaceDscoreTotalForMinimalCounterexamples.{u} := by
  intro G hG
  exact G.faceDscoreSum_eq_of_euler_expression (heuler G hG)

theorem positiveHubExists_of_faceDscoreTotal
    (htotal : FaceDscoreTotalForMinimalCounterexamples.{u}) :
    PositiveHubExists.{u} := by
  intro G hG
  exact G.exists_positive_dscore_of_faceDscoreSum_eq (htotal G hG)

theorem positiveHubExists_of_eulerChargeFormula
    (heuler : EulerChargeFormulaForMinimalCounterexamples.{u}) :
    PositiveHubExists.{u} :=
  positiveHubExists_of_faceDscoreTotal
    (faceDscoreTotal_of_eulerChargeFormula heuler)

theorem positiveHubExists_of_countFormula
    (hcounts : EulerCountFormulaForMinimalCounterexamples.{u}) :
    PositiveHubExists.{u} :=
  positiveHubExists_of_eulerChargeFormula
    (eulerChargeFormula_of_countFormula hcounts)

theorem positiveHubExists_of_structuralCountFacts
    (hstruct : StructuralCountFactsForMinimalCounterexamples.{u}) :
    PositiveHubExists.{u} :=
  positiveHubExists_of_countFormula
    (eulerCountFormula_of_structuralCountFacts hstruct)

/-- The geometric lower-bound side condition for valid hubs. -/
def ValidHubPentagonal : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    Presentation.ValidHub G x → G.Pentagonal

/-- Pentagonality of minimal counterexamples.  Coq proves this by excluding
short face orbits in a minimal counterexample. -/
def PentagonalMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Pentagonal

/-- Face-arity lower-bound form of pentagonality for minimal counterexamples.
This is often the cleaner induction target for the short-face exclusion:
every face orbit in a minimal counterexample has at least five darts. -/
def FaceArityGeFiveMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    5 ≤ G.arity x

/-- The local short-face-orbit exclusions that give pentagonality. -/
def NoShortFaceOrbitsMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    x ≠ G.face x ∧
      x ≠ G.face (G.face x) ∧
        x ≠ G.face (G.face (G.face x)) ∧
          x ≠ G.face (G.face (G.face (G.face x)))

theorem noShortFaceOrbitsMinimalCounterexamples_of_pentagonal
    (hpentagonal : PentagonalMinimalCounterexamples.{u}) :
    NoShortFaceOrbitsMinimalCounterexamples.{u} := by
  intro G hG x
  exact hpentagonal G hG x

theorem pentagonalMinimalCounterexamples_of_noShortFaceOrbits
    (hface : NoShortFaceOrbitsMinimalCounterexamples.{u}) :
    PentagonalMinimalCounterexamples.{u} := by
  intro G hG x
  exact hface G hG x

theorem faceArityGeFiveMinimalCounterexamples_of_pentagonal
    (hpentagonal : PentagonalMinimalCounterexamples.{u}) :
    FaceArityGeFiveMinimalCounterexamples.{u} := by
  intro G hG x
  exact Hypermap.arity_ge_five_of_pentagonal
    (G := G) (hpentagonal G hG) x

theorem pentagonalMinimalCounterexamples_of_faceArityGeFive
    (harity : FaceArityGeFiveMinimalCounterexamples.{u}) :
    PentagonalMinimalCounterexamples.{u} := by
  intro G hG
  exact Hypermap.pentagonal_of_arity_ge_five
    (G := G) (fun x => harity G hG x)

theorem faceArityGeFiveMinimalCounterexamples_of_noShortFaceOrbits
    (hface : NoShortFaceOrbitsMinimalCounterexamples.{u}) :
    FaceArityGeFiveMinimalCounterexamples.{u} :=
  faceArityGeFiveMinimalCounterexamples_of_pentagonal
    (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hface)

theorem noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
    (harity : FaceArityGeFiveMinimalCounterexamples.{u}) :
    NoShortFaceOrbitsMinimalCounterexamples.{u} :=
  noShortFaceOrbitsMinimalCounterexamples_of_pentagonal
    (pentagonalMinimalCounterexamples_of_faceArityGeFive harity)

theorem plainCubicPentagonalMinimalCounterexamples_of_parts
    (hplainCubic : PlainCubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u}) :
    PlainCubicPentagonalMinimalCounterexamples.{u} := by
  intro G hG
  exact {
    base := hplainCubic G hG
    pentagonal := hpentagonal G hG }

theorem plainCubicPentagonalMinimalCounterexamples_of_noShortFaceOrbits
    (hplainCubic : PlainCubicMinimalCounterexamples.{u})
    (hface : NoShortFaceOrbitsMinimalCounterexamples.{u}) :
    PlainCubicPentagonalMinimalCounterexamples.{u} :=
  plainCubicPentagonalMinimalCounterexamples_of_parts
    hplainCubic
    (pentagonalMinimalCounterexamples_of_noShortFaceOrbits hface)

theorem plainCubicPentagonalMinimalCounterexamples_of_faceArityGeFive
    (hplainCubic : PlainCubicMinimalCounterexamples.{u})
    (harity : FaceArityGeFiveMinimalCounterexamples.{u}) :
    PlainCubicPentagonalMinimalCounterexamples.{u} :=
  plainCubicPentagonalMinimalCounterexamples_of_parts
    hplainCubic
    (pentagonalMinimalCounterexamples_of_faceArityGeFive harity)

theorem validHubPentagonal_of_minimalCounterexamples
    (hpentagonal : PentagonalMinimalCounterexamples.{u}) :
    ValidHubPentagonal.{u} := by
  intro G x hvalid
  exact hpentagonal G hvalid.1

/-- The discharging upper-bound side condition for valid hubs. -/
def ValidHubArityUpperBound : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    Presentation.ValidHub G x → G.arity x ≤ 11

/-- Source-score cap for valid hubs.  This is the semantic side of Coq's
`dscore_cap1`/hubcap bound: every source transfer score is at most `5`. -/
def ValidHubDscore1LeFive : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    Presentation.ValidHub G x → ∀ y : G.Dart, G.dscore1 y ≤ (5 : Int)

/-- Minimal-counterexample form of the source-score cap. -/
def Dscore1LeFiveMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (y : G.Dart),
    G.dscore1 y ≤ (5 : Int)

/-- A fixed-arity source-rule bound.  This is the semantic conclusion of
Coq's `check_dbound1P` after specializing to the full free hub part. -/
def SourceBoundForArity (n : Nat) : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    G.arity x = n →
      G.dbound1 (Discharge.pickSourceDrules n Discharge.theDrules) x ≤ 5

/-- The only arities whose source rules can contribute to `dscore1`. -/
def SmallSourceBounds : Prop :=
  SourceBoundForArity.{u} 5 ∧
    SourceBoundForArity.{u} 6 ∧
      SourceBoundForArity.{u} 7 ∧
        SourceBoundForArity.{u} 8

theorem arity_eq_five_or_six_or_seven_or_eight_of_Pr58 {n : Nat}
    (h : PRange.Pr58 n = true) :
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by
  simp [PRange.contains] at h
  omega

/-- The remaining small-source-rule bound for the source-score cap.  By
`Discharge.pickSourceDrules_eq_nil_of_not_Pr58`, arities outside `5..8`
contribute no source rules, so the cap only needs the source-rule checker in
the small arity range. -/
def SmallSourceBoundForMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{u}) (_ : G.MinimalCounterexample) (x : G.Dart),
    PRange.Pr58 (G.arity x) = true →
      G.dbound1
        (Discharge.pickSourceDrules (G.arity x) Discharge.theDrules) x ≤ 5

theorem smallSourceBoundForMinimalCounterexamples_of_sourceBounds
    (hbounds : SmallSourceBounds.{u}) :
    SmallSourceBoundForMinimalCounterexamples.{u} := by
  intro G hG x hxsmall
  rcases hbounds with ⟨h5, h6, h7, h8⟩
  rcases arity_eq_five_or_six_or_seven_or_eight_of_Pr58 hxsmall with
    h | h | h | h
  · simpa [h] using h5 G hG x h
  · simpa [h] using h6 G hG x h
  · simpa [h] using h7 G hG x h
  · simpa [h] using h8 G hG x h

/-- The four executable source-bound checks used for the small `Pr58` arities.
These are intentionally kept separate from the 633-configuration reducibility
job aggregate; they are small enough to remain in the lightweight build. -/
def SmallSourceChecks : Prop :=
  Discharge.Hubcap.checkDbound1 Presentation.theRedpart
      (Discharge.theDruleFork 5) (Part.pconsN 5) 5 = true ∧
    Discharge.Hubcap.checkDbound1 Presentation.theRedpart
      (Discharge.theDruleFork 6) (Part.pconsN 6) 5 = true ∧
    Discharge.Hubcap.checkDbound1 Presentation.theRedpart
      (Discharge.theDruleFork 7) (Part.pconsN 7) 5 = true ∧
    Discharge.Hubcap.checkDbound1 Presentation.theRedpart
      (Discharge.theDruleFork 8) (Part.pconsN 8) 5 = true

theorem theSmallSourceChecks : SmallSourceChecks := by
  unfold SmallSourceChecks
  fct_decide


end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
