import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding
import FourColorTheorem.FourColor.Configuration.Database
import FourColorTheorem.FourColor.Presentation.Soundness
import FourColorTheorem.FourColor.Reducibility.RedPartSoundness

/-!
Bridge from the executable redpart soundness theorem to the presentation
interface.

This file does not import the executable 0--633 certificate jobs.  It only
packages the semantic redpart theorem against the presentation-facing
`RedpartSound` dependency.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

theorem all_theConfigs_configQuiz_isQuizR :
    theConfigs.all (fun cf => (CFQuiz.configQuiz cf).isQuizR) = true := by
  fct_decide

theorem configQuiz_isQuizR_of_mem_theConfigs
    {cf : Config} (hcf : cf ∈ theConfigs) :
    (CFQuiz.configQuiz cf).isQuizR = true :=
  List.all_eq_true.mp all_theConfigs_configQuiz_isQuizR cf hcf

end Config

namespace Presentation

noncomputable section

universe u

/-- Minimal-counterexample-facing form of the Coq hypothesis that no compiled
configuration quiz fits anywhere in the minimal counterexample. -/
def NoQuizTreeFitMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u},
    G.MinimalCounterexample →
      RedPart.NoQuizTreeFit G Config.theQuizTree

/-- Minimal-counterexample-facing contrapositive of Coq `qzt_fit_cfquiz`:
none of the 633 configuration quizzes fits in the map or in its mirror. -/
def NoConfigQuizMirrorFitMinimalCounterexamples : Prop :=
  ∀ G : Hypermap.{u},
    G.MinimalCounterexample →
      ∀ cf : Config, cf ∈ Config.theConfigs →
        ¬ QuizTree.Hypermap.ConfigQuizMirrorFitWitness G cf

/-- All listed configuration quizzes are semantically valid for their source
configuration kernel.  This is the all-config form of Coq `valid_cfquiz`. -/
def ConfigQuizSourceValidTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    CFQuiz.ConfigQuizSourceValid cf

/-- All listed configuration quizzes are right-rooted.  This is the executable
part of source-validity already discharged by the compiled quiz list. -/
def ConfigQuizRightRootedTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    (CFQuiz.configQuiz cf).isQuizR = true

/-- The source pointed maps associated to all listed configurations satisfy
the construction-program geometry package. -/
def ConfigSourceConfigGeometryTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.ConfigGeometry

/-- The source maps associated to all listed configurations have proper ring
heads. -/
def ConfigSourceProperRingHeadTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.ProperRingHead

/-- The source maps associated to all listed configurations have long ring
heads. -/
def ConfigSourceLongRingHeadTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.LongRingHead

/-- The source maps associated to all listed configurations are plain. -/
def ConfigSourcePlainTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.map.Plain

/-- The source maps associated to all listed configurations are connected. -/
def ConfigSourceConnectedTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.map.Connected

/-- The source maps associated to all listed configurations are bridgeless. -/
def ConfigSourceBridgelessTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.map.Bridgeless

/-- Constructor-complete semantic correctness of executable configuration
mask adjacency for every proper mask of every listed configuration. -/
def ConfigMaskAdjSoundTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    ∀ m : CfMask, CfMask.Proper cf.program m →
      PointedHypermap.cpMaskAdjSound cf.program m

/-- The semantic radius-two side condition for every listed configuration
kernel. -/
def ConfigRadiusTwoTheConfigs : Prop :=
  ∀ cf : Config, cf ∈ Config.theConfigs →
    cf.map.map.RadiusTwo cf.kernelSet

theorem configQuizRightRootedTheConfigs :
    ConfigQuizRightRootedTheConfigs := by
  intro cf hmem
  exact Config.configQuiz_isQuizR_of_mem_theConfigs hmem

/-- Coq `valid_cfquiz` for the complete executable configuration list. -/
theorem configQuizSourceValidTheConfigs :
    ConfigQuizSourceValidTheConfigs := by
  intro cf hmem
  exact CFQuiz.configQuizSourceValid_of_isQuizR
    (Config.wellFormed_of_mem_theConfigs hmem)
    (configQuizRightRootedTheConfigs cf hmem)

theorem configSourceConfigGeometryTheConfigs :
    ConfigSourceConfigGeometryTheConfigs := by
  intro cf hmem
  exact Config.map_configGeometry_of_wellFormed
    (Config.wellFormed_of_mem_theConfigs hmem)

theorem configSourceProperRingHeadTheConfigs :
    ConfigSourceProperRingHeadTheConfigs := by
  intro cf hmem
  exact (configSourceConfigGeometryTheConfigs cf hmem).proper

theorem configSourceLongRingHeadTheConfigs :
    ConfigSourceLongRingHeadTheConfigs := by
  intro cf hmem
  exact (configSourceConfigGeometryTheConfigs cf hmem).long

theorem configSourcePlainTheConfigs :
    ConfigSourcePlainTheConfigs := by
  intro cf hmem
  exact Config.map_plain_of_wellFormed
    (Config.wellFormed_of_mem_theConfigs hmem)

theorem configSourceConnectedTheConfigs :
    ConfigSourceConnectedTheConfigs := by
  intro cf hmem
  exact (configSourceConfigGeometryTheConfigs cf hmem).connected

theorem configSourceBridgelessTheConfigs :
    ConfigSourceBridgelessTheConfigs := by
  intro cf hmem
  exact (configSourceConfigGeometryTheConfigs cf hmem).bridgeless

theorem configMaskAdjSoundTheConfigs :
    ConfigMaskAdjSoundTheConfigs := by
  intro cf hmem m hm
  exact PointedHypermap.cpMaskAdjSound_of_config
    (Config.wellFormed_of_mem_theConfigs hmem) hm

theorem configRadiusTwoTheConfigs_of_sourceValid_maskAdj
    (hsource : ConfigQuizSourceValidTheConfigs)
    (hadj : ConfigMaskAdjSoundTheConfigs) :
    ConfigRadiusTwoTheConfigs := by
  intro cf hmem
  exact
    CFQuiz.config_radiusTwo_kernelSet_of_configQuiz_isQuizR
      (cf := cf)
      (Config.wellFormed_of_mem_theConfigs hmem)
      (CFQuiz.ConfigQuizSourceValid.rightRooted (hsource cf hmem))
      (hadj cf hmem)

theorem configRadiusTwoTheConfigs_of_maskAdj
    (hadj : ConfigMaskAdjSoundTheConfigs) :
    ConfigRadiusTwoTheConfigs := by
  intro cf hmem
  exact
    CFQuiz.config_radiusTwo_kernelSet_of_configQuiz_isQuizR
      (cf := cf)
      (Config.wellFormed_of_mem_theConfigs hmem)
      (configQuizRightRootedTheConfigs cf hmem)
      (hadj cf hmem)

theorem configRadiusTwoTheConfigs :
    ConfigRadiusTwoTheConfigs :=
  configRadiusTwoTheConfigs_of_maskAdj configMaskAdjSoundTheConfigs

/-- No semantic configuration preembedding exists from a listed source
configuration into a minimal counterexample, in either target orientation.

This is stated at universe 0 because the current `Preembedding` interface is
same-universe. -/
def NoConfigPreembeddingMinimalCounterexamples : Prop :=
  ∀ (G : Hypermap.{0}) (_hG : G.MinimalCounterexample)
    (cf : Config) (_hmem : cf ∈ Config.theConfigs)
    (x0G : cf.map.map.Dart)
    (hvalid :
      cf.map.map.ValidQuizFor cf.kernelSet x0G
        (CFQuiz.configQuiz cf)),
    (∀ x0H : G.Dart,
      ¬ Hypermap.Preembedding cf.map.map G cf.kernelSet
        (hvalid.embedMap G x0H)) ∧
      ∀ x0H : G.mirror.Dart,
        ¬ Hypermap.Preembedding cf.map.map G.mirror cf.kernelSet
          (hvalid.embedMap G.mirror x0H)

theorem noConfigQuizMirrorFitMinimalCounterexamples_of_sourceValid_noPreembedding_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource :
      ∀ cf : Config, cf ∈ Config.theConfigs →
        CFQuiz.ConfigQuizSourceValid cf)
    (hplainSource :
      ∀ cf : Config, cf ∈ Config.theConfigs →
        cf.map.map.Plain)
    (hno :
      ∀ (G : Hypermap.{0}) (_hG : G.MinimalCounterexample)
        (cf : Config) (_hmem : cf ∈ Config.theConfigs)
        (x0G : cf.map.map.Dart)
        (hvalid :
          cf.map.map.ValidQuizFor cf.kernelSet x0G
            (CFQuiz.configQuiz cf)),
        (∀ x0H : G.Dart,
          ¬ Hypermap.Preembedding cf.map.map G cf.kernelSet
            (hvalid.embedMap G x0H)) ∧
          ∀ x0H : G.mirror.Dart,
            ¬ Hypermap.Preembedding cf.map.map G.mirror cf.kernelSet
              (hvalid.embedMap G.mirror x0H)) :
    NoConfigQuizMirrorFitMinimalCounterexamples.{0} := by
  intro G hG cf hmem
  exact
    CFQuiz.ConfigQuizSourceValid.not_configQuizMirrorFitWitness_of_no_preembedding
      (cf := cf) (H := G)
      (hsource cf hmem)
      (Config.wellFormed_of_mem_theConfigs hmem)
      (hplainSource cf hmem)
      (Hypermap.MinimalCounterexample.plain hG)
      (hcubic G hG)
      (hno G hG cf hmem)

theorem noConfigQuizMirrorFitMinimalCounterexamples_of_listedSourceValid_noPreembedding_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource :
      ∀ cf : Config, cf ∈ Config.theConfigs →
        CFQuiz.ConfigQuizSourceValid cf)
    (hno :
      ∀ (G : Hypermap.{0}) (_hG : G.MinimalCounterexample)
        (cf : Config) (_hmem : cf ∈ Config.theConfigs)
        (x0G : cf.map.map.Dart)
        (hvalid :
          cf.map.map.ValidQuizFor cf.kernelSet x0G
            (CFQuiz.configQuiz cf)),
        (∀ x0H : G.Dart,
          ¬ Hypermap.Preembedding cf.map.map G cf.kernelSet
            (hvalid.embedMap G x0H)) ∧
          ∀ x0H : G.mirror.Dart,
            ¬ Hypermap.Preembedding cf.map.map G.mirror cf.kernelSet
              (hvalid.embedMap G.mirror x0H)) :
    NoConfigQuizMirrorFitMinimalCounterexamples.{0} :=
  noConfigQuizMirrorFitMinimalCounterexamples_of_sourceValid_noPreembedding_zero
    hcubic hsource
    configSourcePlainTheConfigs
    hno

theorem noConfigQuizMirrorFitMinimalCounterexamples_of_interfaces_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource : ConfigQuizSourceValidTheConfigs)
    (hno : NoConfigPreembeddingMinimalCounterexamples) :
    NoConfigQuizMirrorFitMinimalCounterexamples.{0} :=
  noConfigQuizMirrorFitMinimalCounterexamples_of_listedSourceValid_noPreembedding_zero
    hcubic hsource hno

theorem noQuizTreeFitMinimalCounterexamples_of_noConfigQuizMirrorFit
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hnofit : NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    NoQuizTreeFitMinimalCounterexamples.{u} := by
  intro G hG y
  exact
    QuizTree.Hypermap.quizTreeFit_cfquizTree_eq_false_of_noConfigQuizMirrorFitWitness
      (G := G) (x1 := y) (cfs := Config.theConfigs)
      (Hypermap.MinimalCounterexample.plain hG) (hcubic G hG)
      (fun cf hmem => hnofit G hG cf hmem)

theorem noQuizTreeFitMinimalCounterexamples_of_interfaces_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource : ConfigQuizSourceValidTheConfigs)
    (hno : NoConfigPreembeddingMinimalCounterexamples) :
    NoQuizTreeFitMinimalCounterexamples.{0} :=
  noQuizTreeFitMinimalCounterexamples_of_noConfigQuizMirrorFit hcubic
    (noConfigQuizMirrorFitMinimalCounterexamples_of_interfaces_zero
      hcubic hsource hno)

theorem exactFitp_eq_false_of_theRedpart_of_noQuizTreeFit
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hnofit : NoQuizTreeFitMinimalCounterexamples.{u})
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample)
    (x : G.Dart) (p : Part)
    (hred : theRedpart p = true) :
    Part.exactFitp G x p = false := by
  by_cases hfit : Part.exactFitp G x p = true
  · have hparts := hfit
    simp [Part.exactFitp] at hparts
    have hfalse :
        Part.exactFitp G x p = false :=
      RedPart.exactFitp_eq_false_of_redpart_of_noQuizTreeFit
        (G := G) (qt := Config.theQuizTree) (p := p) (x := x)
        (Hypermap.MinimalCounterexample.plain hG) (hcubic G hG)
        (hnofit G hG)
        (by simpa [theRedpart] using hred)
        hparts.1
    rw [hfit] at hfalse
    cases hfalse
  · cases h : Part.exactFitp G x p with
    | false => rfl
    | true => exact False.elim (hfit h)

theorem redpartSound_of_noQuizTreeFit
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hnofit : NoQuizTreeFitMinimalCounterexamples.{u}) :
    RedpartSound.{u} := by
  intro G hG x p hred
  exact exactFitp_eq_false_of_theRedpart_of_noQuizTreeFit
    hcubic hnofit hG x p hred

theorem redpartSound_of_noConfigQuizMirrorFit
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hnofit : NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    RedpartSound.{u} :=
  redpartSound_of_noQuizTreeFit hcubic
    (noQuizTreeFitMinimalCounterexamples_of_noConfigQuizMirrorFit
      hcubic hnofit)

theorem redpartSound_of_interfaces_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource : ConfigQuizSourceValidTheConfigs)
    (hno : NoConfigPreembeddingMinimalCounterexamples) :
    RedpartSound.{0} :=
  redpartSound_of_noConfigQuizMirrorFit hcubic
    (noConfigQuizMirrorFitMinimalCounterexamples_of_interfaces_zero
      hcubic hsource hno)

theorem exactFitp_eq_false_of_theRedpart_of_noConfigQuizMirrorFit
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hnofit : NoConfigQuizMirrorFitMinimalCounterexamples.{u})
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample)
    (x : G.Dart) (p : Part)
    (hred : theRedpart p = true) :
    Part.exactFitp G x p = false :=
  exactFitp_eq_false_of_theRedpart_of_noQuizTreeFit
    hcubic
    (noQuizTreeFitMinimalCounterexamples_of_noConfigQuizMirrorFit
      hcubic hnofit)
    hG x p hred

theorem exactFitp_eq_false_of_theRedpart_of_interfaces_zero
    (hcubic : ∀ G : Hypermap.{0}, G.MinimalCounterexample → G.Cubic)
    (hsource : ConfigQuizSourceValidTheConfigs)
    (hno : NoConfigPreembeddingMinimalCounterexamples)
    {G : Hypermap.{0}}
    (hG : G.MinimalCounterexample)
    (x : G.Dart) (p : Part)
    (hred : theRedpart p = true) :
    Part.exactFitp G x p = false :=
  exactFitp_eq_false_of_theRedpart_of_noConfigQuizMirrorFit
    hcubic
    (noConfigQuizMirrorFitMinimalCounterexamples_of_interfaces_zero
      hcubic hsource hno)
    hG x p hred

end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
