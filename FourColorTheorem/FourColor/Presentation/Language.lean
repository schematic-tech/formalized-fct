import FourColorTheorem.FourColor.Reducibility.Certificate
import FourColorTheorem.FourColor.Configuration.QuizTree
import FourColorTheorem.FourColor.Discharging.Hubcap
import FourColorTheorem.FourColor.Hypermap.Minimal
import FourColorTheorem.FourColor.Reducibility.RedPart

/-!
Presentation scripting layer.

This ports the non-tactic front of Coq `present.v`: the named reducibility
hypothesis, valid hubs, presentation goals, split/similarity checks, and the
executable reducibility/hubcap closers used by the hub-size presentation files.
The semantic closing lemmas are ported later, after the remaining embedding and
hubcap-bound soundness API is available.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

open PartRel

namespace Presentation

noncomputable section

universe u

/-- All 633 configurations pass the certificate checker.  This is a proposition;
the expensive proof term lives in the separate job aggregate, not here. -/
def Reducibility : Prop :=
  Config.CheckedInRange 0 Config.theConfigs.length Config.theConfigs

/-- A valid hub in a minimal counterexample, matching Coq `valid_hub`. -/
def ValidHub (G : Hypermap.{u}) (x : G.Dart) : Prop :=
  G.MinimalCounterexample ∧ 0 < G.dscore x

/-- Hub arity `n` is excluded by the presentations. -/
def ExcludedArity (n : Nat) : Prop :=
  Reducibility →
    ∀ (G : Hypermap.{u}) (x : G.Dart), ValidHub G x → G.arity x ≠ n

/-- A part is successful when no valid hub fits it exactly. -/
def Successful (p : Part) : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
    ValidHub G x → Part.exactFitp G x p = false

/-- `p` is forced by `p0` when every valid hub fitting `p0` also fits `p`. -/
def ForcedPart (p0 p : Part) : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
    ValidHub G x →
      Part.exactFitp G x p0 = true →
        Part.exactFitp G x p = true

/-- Presentation subgoal: forcedness from `p0` to `p` is enough to make `p`
successful. -/
def SucceedsIn (p0 p : Part) : Prop :=
  ForcedPart.{u} p0 p → Successful.{u} p

theorem forcedPart_refl (p : Part) :
    ForcedPart.{u} p p := by
  intro G x hx hfit
  exact hfit

theorem succeedsIn_of_successful {p0 p : Part}
    (hp : Successful.{u} p) :
    SucceedsIn.{u} p0 p := by
  intro _forced
  exact hp

theorem succeedsIn_self_of_successful {p : Part}
    (hp : Successful.{u} p) :
    SucceedsIn.{u} p p :=
  succeedsIn_of_successful hp

/-- General presentation check goal, rendered in Coq as `Check p in p0`. -/
structure CheckGoal where
  p0 : Part
  p : Part
  deriving DecidableEq, Repr

namespace CheckGoal

def holds (g : CheckGoal) : Prop :=
  SucceedsIn.{u} g.p0 g.p

end CheckGoal

/-- A split assumption `loc[index] <= cutoff` or its complement.  Indices are
zero-based, matching the Lean `Part.split` API. -/
structure SplitAssumption where
  loc : SubpartLoc
  index : Nat
  cutoff : Nat
  low : Bool
  deriving DecidableEq, Repr

namespace SplitAssumption

def apply (a : SplitAssumption) (p : Part) : Part :=
  Part.split a.loc a.index a.cutoff a.low p

def complement (a : SplitAssumption) : SplitAssumption :=
  { a with low := !a.low }

def good (a : SplitAssumption) (p : Part) : Bool :=
  Part.goodSplit a.loc a.index a.cutoff p

def splitGoal (a : SplitAssumption) (g : CheckGoal) : CheckGoal × CheckGoal :=
  let pl := a.apply g.p
  let pr := a.complement.apply g.p
  let p0l := if a.good g.p0 then a.apply g.p0 else pl
  (⟨p0l, pl⟩, ⟨g.p0, pr⟩)

end SplitAssumption

/- Constructors matching the compact part notation from Coq `part.v`. -/
namespace PartSyntax

def nil : Part := Part.Pnil

def spoke (s : PRange) (tail : Part := nil) : Part :=
  Part.Pcons s PRange.Pr59 tail

def hat (h s : PRange) (tail : Part := nil) : Part :=
  Part.Pcons s h tail

def fan6 (h f1 : PRange) (tail : Part := nil) : Part :=
  Part.Pcons6 h f1 tail

def fan7 (h f1 f2 : PRange) (tail : Part := nil) : Part :=
  Part.Pcons7 h f1 f2 tail

def fan8 (h f1 f2 f3 : PRange) (tail : Part := nil) : Part :=
  Part.Pcons8 h f1 f2 f3 tail

def full (n : Nat) : Part :=
  Part.pconsN n

end PartSyntax

/- Constructors matching the one-based sublocation notation from Coq
`present.v`; `le` means `loc[i] <= k`, and `gt` means the complementary
`loc[i] > k`. -/
namespace SublocSyntax

def spoke : SubpartLoc := SubpartLoc.Pspoke
def hat : SubpartLoc := SubpartLoc.Phat
def fan1 : SubpartLoc := SubpartLoc.Pfan1
def fan2 : SubpartLoc := SubpartLoc.Pfan2
def fan3 : SubpartLoc := SubpartLoc.Pfan3

def le (loc : SubpartLoc) (oneBasedIndex cutoff : Nat) : SplitAssumption :=
  { loc := loc, index := oneBasedIndex - 1, cutoff := cutoff, low := true }

def gt (loc : SubpartLoc) (oneBasedIndex cutoff : Nat) : SplitAssumption :=
  { loc := loc, index := oneBasedIndex - 1, cutoff := cutoff, low := false }

end SublocSyntax

/-- Pure executable side condition for a `Similar to ...` presentation step. -/
def similarityCheck (ps p : Part) (j : Nat) (mir : Bool) : Bool :=
  let p1 := if mir then Part.mirror p else p
  let p2 := Part.rotate j p1
  (ps.size == p2.size) &&
    match Part.cmp p2 ps with
    | Psubset => true
    | _ => false

@[simp]
theorem similarityCheck_mirror_false (ps p : Part) (j : Nat) :
    similarityCheck ps (Part.mirror p) j false =
      similarityCheck ps p j true := by
  simp [similarityCheck]

@[simp]
theorem similarityCheck_mirror_true (ps p : Part) (j : Nat) :
    similarityCheck ps (Part.mirror p) j true =
      similarityCheck ps p j false := by
  simp [similarityCheck]

/-- Redpart checker specialized to the 633-configuration quiz tree. -/
def theRedpart (p : Part) : Bool :=
  RedPart.redpart Config.theQuizTree p

theorem theRedpart_true_exists_step
    {p : Part}
    (hred : theRedpart p = true) :
    ∃ d : Nat,
      p.size * 12 = d + 1 ∧
        let ahub := QArity.ofNatCode p.size
        let ctx : RedPart.Context :=
          { qt := Config.theQuizTree
            ahub := ahub
            redRec := fun q => RedPart.redpartLoop Config.theQuizTree ahub d q
            p0l := Part.reverse p
            p0r := p }
        ∃ i : Nat,
          i < ctx.nhub ∧
            RedPart.redZPartStep ctx
              (((fun z : RedPart.ZPart =>
                  RedPart.zshiftR ctx RedPart.ZPartLoc.Zhub z)^[i])
                (RedPart.mkZ RedPart.ZPartLoc.Zhub (Part.drop 1 ctx.p0l)
                  (RedPart.shiftPart ctx.p0l ctx.p0r))) = true := by
  exact RedPart.redpart_true_exists_step (qt := Config.theQuizTree) hred

theorem theRedpart_true_size_bounds
    {p : Part}
    (hred : theRedpart p = true) :
    5 ≤ p.size ∧ p.size ≤ 11 :=
  RedPart.redpart_true_size_bounds (qt := Config.theQuizTree) hred

/-- Reducibility presentation-side executable check. -/
def reducibilityCheck (g : CheckGoal) : Bool :=
  theRedpart g.p

/-- Hubcap presentation-side executable check. -/
def hubcapCheck (g : CheckGoal) (hc : Discharge.Hubcap) : Bool :=
  let n := g.p.size
  Discharge.Hubcap.cover n hc &&
    Discharge.Hubcap.fit n theRedpart (Discharge.theDruleFork n) g.p hc

/- Constructors for the hubcap scripting notation used in the presentation
files. -/
namespace HubcapSyntax

def nil : Discharge.Hubcap :=
  Discharge.Hubcap.Hubcap0

def idx (oneBasedIndex : Nat) : Nat :=
  oneBasedIndex - 1

def oneRaw (i : Nat) (b : Int) (tail : Discharge.Hubcap := nil) :
    Discharge.Hubcap :=
  Discharge.Hubcap.Hubcap1 i b tail

def twoRaw (i j : Nat) (b : Int) (tail : Discharge.Hubcap := nil) :
    Discharge.Hubcap :=
  Discharge.Hubcap.Hubcap2 i j b tail

def one (i : Nat) (b : Int) (tail : Discharge.Hubcap := nil) :
    Discharge.Hubcap :=
  oneRaw (idx i) b tail

def two (i j : Nat) (b : Int) (tail : Discharge.Hubcap := nil) :
    Discharge.Hubcap :=
  twoRaw (idx i) (idx j) b tail

end HubcapSyntax

end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
