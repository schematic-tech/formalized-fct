import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations.StoreSemantics

namespace Schematic.Math.GraphTheory
namespace FourColor

open Question
open QArity

namespace QuizTree

namespace Hypermap

variable (G : Hypermap)
def ConfigQuizFitWitness (cf : Config) : Prop :=
  (CFQuiz.configQuiz cf).isQuizR = true ∧
    ((∃ y : G.Dart, G.fitQuiz y (CFQuiz.configQuiz cf) = true) ∨
      ∃ y : G.Dart, G.fitQuiz y (CFQuiz.configQuiz cf).flip = true)

def ConfigQuizMirrorFitWitness (cf : Config) : Prop :=
  (CFQuiz.configQuiz cf).isQuizR = true ∧
    ((∃ y : G.Dart, G.fitQuiz y (CFQuiz.configQuiz cf) = true) ∨
      ∃ y : G.mirror.Dart,
        G.mirror.fitQuiz y (CFQuiz.configQuiz cf) = true)

theorem ConfigQuizMirrorFitWitness_of_raw
    {cf : Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hwit : ConfigQuizFitWitness G cf) :
    ConfigQuizMirrorFitWitness G cf := by
  rcases hwit with ⟨hR, hfit | hflip⟩
  · exact ⟨hR, Or.inl hfit⟩
  · rcases hflip with ⟨y, hy⟩
    have hmirror :
        G.mirror.fitQuiz (G.face y) (CFQuiz.configQuiz cf) = true := by
      rw [← Hypermap.fitQuiz_flip
        (G := G) hPlain hCubic y (CFQuiz.configQuiz cf) hR]
      exact hy
    exact ⟨hR, Or.inr ⟨G.face y, hmirror⟩⟩

theorem quizTreeFit_cfquizTreeRec_raw
    {x1 : G.Dart} {qt : QuizTree} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (cfquizTreeRec qt cfs) = true) :
    quizTreeFit G x1 qt = true ∨
      ∃ cf : Config, cf ∈ cfs ∧ ConfigQuizFitWitness G cf := by
  induction cfs generalizing qt with
  | nil =>
      exact Or.inl (by simpa [cfquizTreeRec] using hfit)
  | cons cf cfs ih =>
      let qz := CFQuiz.configQuiz cf
      let qt' := storeConfigQuiz qz cf.symmetric qt
      cases hqt' : qt' with
      | nil =>
          have hnil : quizTreeFit G x1 QuizTree.nil = true := by
            simpa [cfquizTreeRec, qz, qt', hqt'] using hfit
          rw [quizTreeFit_nil_eq_false] at hnil
          contradiction
      | leaf q1 q2 q3 tail =>
          have hnil : quizTreeFit G x1 QuizTree.nil = true := by
            simpa [cfquizTreeRec, qz, qt', hqt'] using hfit
          rw [quizTreeFit_nil_eq_false] at hnil
          contradiction
      | node t5 t6 t7 t8 =>
          have hnil : quizTreeFit G x1 QuizTree.nil = true := by
            simpa [cfquizTreeRec, qz, qt', hqt'] using hfit
          rw [quizTreeFit_nil_eq_false] at hnil
          contradiction
      | hubNode t58 t9 t10 t11 =>
          have hrec :
              quizTreeFit G x1
                (cfquizTreeRec (QuizTree.hubNode t58 t9 t10 t11) cfs) =
                  true := by
            simpa [cfquizTreeRec, qz, qt', hqt'] using hfit
          rcases ih hrec with hqtFit | hwitness
          · have hstore :
                quizTreeFit G x1 (storeConfigQuiz (CFQuiz.configQuiz cf)
                  cf.symmetric qt) = true := by
              simpa [qz, qt', hqt'] using hqtFit
            rcases quizTreeFit_storeConfigQuiz_raw
                (G := G) (x1 := x1)
                hPlain hCubic hstore with hnew | hold
            · exact Or.inr ⟨cf, by simp, by
                simpa [ConfigQuizFitWitness] using hnew⟩
            · exact Or.inl hold
          · rcases hwitness with ⟨cf', hmem, hwit⟩
            exact Or.inr ⟨cf', by simp [hmem], hwit⟩

theorem quizTreeFit_cfquizTree_raw
    {x1 : G.Dart} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (cfquizTree cfs) = true) :
    ∃ cf : Config, cf ∈ cfs ∧ ConfigQuizFitWitness G cf := by
  rcases quizTreeFit_cfquizTreeRec_raw
      (G := G) (x1 := x1) (qt := QuizTree.empty) (cfs := cfs)
      hPlain hCubic (by simpa [cfquizTree] using hfit) with hempty | hwit
  · rw [quizTreeFit_empty_eq_false] at hempty
    contradiction
  · exact hwit

theorem quizTreeFit_cfquizTreeRec_mirror
    {x1 : G.Dart} {qt : QuizTree} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (cfquizTreeRec qt cfs) = true) :
    quizTreeFit G x1 qt = true ∨
      ∃ cf : Config, cf ∈ cfs ∧ ConfigQuizMirrorFitWitness G cf := by
  rcases quizTreeFit_cfquizTreeRec_raw
      (G := G) (x1 := x1) (qt := qt) (cfs := cfs)
      hPlain hCubic hfit with hold | hwit
  · exact Or.inl hold
  · rcases hwit with ⟨cf, hmem, hraw⟩
    exact Or.inr
      ⟨cf, hmem,
        ConfigQuizMirrorFitWitness_of_raw
          (G := G) hPlain hCubic hraw⟩

theorem quizTreeFit_cfquizTree_mirror
    {x1 : G.Dart} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hfit : quizTreeFit G x1 (cfquizTree cfs) = true) :
    ∃ cf : Config, cf ∈ cfs ∧ ConfigQuizMirrorFitWitness G cf := by
  rcases quizTreeFit_cfquizTreeRec_mirror
      (G := G) (x1 := x1) (qt := QuizTree.empty) (cfs := cfs)
      hPlain hCubic (by simpa [cfquizTree] using hfit) with hempty | hwit
  · rw [quizTreeFit_empty_eq_false] at hempty
    contradiction
  · exact hwit

theorem quizTreeFit_cfquizTree_eq_false_of_noConfigQuizMirrorFitWitness
    {x1 : G.Dart} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hno : ∀ cf : Config, cf ∈ cfs → ¬ ConfigQuizMirrorFitWitness G cf) :
    quizTreeFit G x1 (cfquizTree cfs) = false := by
  by_cases hfit : quizTreeFit G x1 (cfquizTree cfs) = true
  · rcases quizTreeFit_cfquizTree_mirror
        (G := G) (x1 := x1) (cfs := cfs)
        hPlain hCubic hfit with ⟨cf, hmem, hwit⟩
    exact False.elim (hno cf hmem hwit)
  · cases h : quizTreeFit G x1 (cfquizTree cfs) <;> simp [h] at hfit ⊢

theorem quizTreeFit_cfquizTree_eq_false_of_noConfigQuizFitWitness
    {x1 : G.Dart} {cfs : List Config}
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hno : ∀ cf : Config, cf ∈ cfs → ¬ ConfigQuizFitWitness G cf) :
    quizTreeFit G x1 (cfquizTree cfs) = false := by
  by_cases hfit : quizTreeFit G x1 (cfquizTree cfs) = true
  · rcases quizTreeFit_cfquizTree_raw
        (G := G) (x1 := x1) (cfs := cfs)
        hPlain hCubic hfit with ⟨cf, hmem, hwit⟩
    exact False.elim (hno cf hmem hwit)
  · cases h : quizTreeFit G x1 (cfquizTree cfs) <;> simp [h] at hfit ⊢

end Hypermap

end QuizTree

end FourColor

end Schematic.Math.GraphTheory
