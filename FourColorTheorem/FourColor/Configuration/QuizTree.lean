import FourColorTheorem.FourColor.Configuration.Database
import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations

/-!
Quiz tree for the 633 reducible configurations.

The definitions here name the collation of `Config.theConfigs` into the
quiz-tree representation used by `RedPart`.  They intentionally do not include
the full normalizing sanity check (`size = 3361`) in the lightweight build; that
check belongs in an explicit executable/sanity target.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

/-- The quiz tree obtained from all 633 reducible configurations. -/
def theQuizTree : QuizTree :=
  QuizTree.cfquizTree theConfigs

/-- Expected number of stored quiz triples, left unevaluated in normal builds. -/
def expectedQuizTreeSize : Nat :=
  QuizTree.expectedConfigTreeSize theConfigs

/-- Actual stored-triple count, left unevaluated in normal builds. -/
def actualQuizTreeSize : Nat :=
  QuizTree.size theQuizTree

end Config

end FourColor

end Schematic.Math.GraphTheory
