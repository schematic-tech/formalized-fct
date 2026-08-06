import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitSemantics.Recovery
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem splitCondition_of_fitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hfit : fitp G x (split i j k lo p) = true) :
    splitCondition k lo
      (G.arity (SubpartLoc.move i G ((G.face : G.Dart → G.Dart)^[j] x))) =
        true := by
  induction j generalizing p x with
  | zero =>
      cases i
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo s hgood hfit.1.1
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp [goodSplit, drop] at hgood
        | Pcons8 h f1 f2 f3 p =>
            simp [goodSplit, drop] at hgood
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo h hgood hfit.1.2
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo h hgood hfit.1.1.2
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo h hgood hfit.1.1.1.2
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo h hgood hfit.1.1.1.1.2
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              first
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.2
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.1.2
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.1.1.2
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f1 hgood hfit.1.2
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f1 hgood hfit.1.1.2
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f1 hgood hfit.1.1.1.2
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              first
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.2
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.1.2
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f2 hgood hfit.1.2
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f2 hgood hfit.1.1.2
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              first
              | exact splitCondition_of_splitRange_of_goodRSplit
                  k lo PRange.Pr59 hgood hfit.1.2
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp [goodSplit, drop] at hgood
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit
            exact splitCondition_of_splitRange_of_goodRSplit
              k lo f3 hgood hfit.1.2
  | succ j ih =>
      cases p with
      | Pnil =>
          simp [goodSplit, drop] at hgood
      | Pcons s h p =>
          simp only [goodSplit_succ_pcons] at hgood
          simp only [split_succ_pcons, fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
          exact by
            simpa [Function.iterate_succ_apply]
              using ih p (G.face x) hgood hfit.2
      | Pcons6 h f1 p =>
          simp only [goodSplit_succ_pcons6] at hgood
          simp only [split_succ_pcons6, fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hfit
          exact by
            simpa [Function.iterate_succ_apply]
              using ih p (G.face x) hgood hfit.2
      | Pcons7 h f1 f2 p =>
          simp only [goodSplit_succ_pcons7] at hgood
          simp only [split_succ_pcons7, fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfit
          exact by
            simpa [Function.iterate_succ_apply]
              using ih p (G.face x) hgood hfit.2
      | Pcons8 h f1 f2 f3 p =>
          simp only [goodSplit_succ_pcons8] at hgood
          simp only [split_succ_pcons8, fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfit
          exact by
            simpa [Function.iterate_succ_apply]
              using ih p (G.face x) hgood hfit.2

theorem splitCondition_of_exactFitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hfit : exactFitp G x (split i j k lo p) = true) :
    splitCondition k lo
      (G.arity (SubpartLoc.move i G ((G.face : G.Dart → G.Dart)^[j] x))) =
        true := by
  have hfits := hfit
  simp [exactFitp] at hfits
  exact splitCondition_of_fitp_split_of_goodSplit
    (G := G) i j k lo p x hgood hfits.2

end

end Part

end FourColor

end Schematic.Math.GraphTheory
