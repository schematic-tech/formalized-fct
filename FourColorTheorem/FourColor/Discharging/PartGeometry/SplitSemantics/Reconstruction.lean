import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitSemantics.Exclusivity
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem fitp_split_of_splitCondition_of_fitp_of_goodSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hcond : splitCondition k lo
      (G.arity (SubpartLoc.move i G ((G.face : G.Dart → G.Dart)^[j] x))) =
        true)
    (hfit : fitp G x p = true) :
    fitp G x (split i j k lo p) = true := by
  induction j generalizing p x with
  | zero =>
      cases i
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨splitRange_of_splitCondition_of_contains_of_goodRSplit
              k lo s hgood (by simpa using hcond) hfit.1.1,
              hfit.1.2⟩, hfit.2⟩
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
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨hfit.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo h hgood (by simpa using hcond) hfit.1.2⟩,
              hfit.2⟩
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit ⊢
            exact ⟨⟨⟨hfit.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo h hgood (by simpa using hcond) hfit.1.1.2⟩,
              hfit.1.2⟩, hfit.2⟩
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨⟨⟨hfit.1.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo h hgood (by simpa using hcond) hfit.1.1.1.2⟩,
              hfit.1.1.2⟩, hfit.1.2⟩, hfit.2⟩
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨⟨⟨⟨hfit.1.1.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo h hgood (by simpa using hcond) hfit.1.1.1.1.2⟩,
              hfit.1.1.1.2⟩, hfit.1.1.2⟩, hfit.1.2⟩, hfit.2⟩
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit hcond ⊢
            all_goals
              first
              | have hfan1 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
                exact ⟨⟨hfit.1,
                  splitRange_of_splitCondition_of_contains_of_goodRSplit
                    k lo PRange.Pr59 hgood (by simpa using hcond)
                    hfan1⟩, hfit.2⟩
              | have hfan1 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
                have hfan2 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))
                exact ⟨⟨⟨hfit.1,
                  splitRange_of_splitCondition_of_contains_of_goodRSplit
                    k lo PRange.Pr59 hgood (by simpa using hcond)
                    hfan1⟩, hfan2⟩, hfit.2⟩
              | have hfan1 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
                have hfan2 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))
                have hfan3 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan3 G x))
                exact ⟨⟨⟨⟨hfit.1,
                  splitRange_of_splitCondition_of_contains_of_goodRSplit
                    k lo PRange.Pr59 hgood (by simpa using hcond)
                    hfan1⟩, hfan2⟩, hfan3⟩, hfit.2⟩
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit ⊢
            exact ⟨⟨hfit.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f1 hgood (by simpa using hcond) hfit.1.2⟩,
              hfit.2⟩
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨⟨hfit.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f1 hgood (by simpa using hcond) hfit.1.1.2⟩,
              hfit.1.2⟩, hfit.2⟩
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨⟨⟨hfit.1.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f1 hgood (by simpa using hcond) hfit.1.1.1.2⟩,
              hfit.1.1.2⟩, hfit.1.2⟩, hfit.2⟩
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit hcond ⊢
            all_goals
              first
              | have hfan1 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
                have hfan2 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))
                exact ⟨⟨⟨hfit.1, hfan1⟩,
                  splitRange_of_splitCondition_of_contains_of_goodRSplit
                    k lo PRange.Pr59 hgood (by simpa using hcond)
                    hfan2⟩, hfit.2⟩
              | have hfan1 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
                have hfan2 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))
                have hfan3 :
                    PRange.Pr59
                        (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) =
                      true :=
                  PRange.contains_Pr59_of_ge_five
                    (hge (SubpartLoc.move SubpartLoc.Pfan3 G x))
                exact ⟨⟨⟨⟨hfit.1, hfan1⟩,
                  splitRange_of_splitCondition_of_contains_of_goodRSplit
                    k lo PRange.Pr59 hgood (by simpa using hcond)
                    hfan2⟩, hfan3⟩, hfit.2⟩
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨hfit.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f2 hgood (by simpa using hcond) hfit.1.2⟩,
              hfit.2⟩
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨⟨hfit.1.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f2 hgood (by simpa using hcond) hfit.1.1.2⟩,
              hfit.1.2⟩, hfit.2⟩
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit hcond ⊢
            all_goals
              have hfan1 :
                  PRange.Pr59
                      (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
                    true :=
                PRange.contains_Pr59_of_ge_five
                  (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))
              have hfan2 :
                  PRange.Pr59
                      (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
                    true :=
                PRange.contains_Pr59_of_ge_five
                  (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))
              have hfan3 :
                  PRange.Pr59
                      (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) =
                    true :=
                PRange.contains_Pr59_of_ge_five
                  (hge (SubpartLoc.move SubpartLoc.Pfan3 G x))
              exact ⟨⟨⟨⟨hfit.1, hfan1⟩, hfan2⟩,
                splitRange_of_splitCondition_of_contains_of_goodRSplit
                  k lo PRange.Pr59 hgood (by simpa using hcond) hfan3⟩,
                hfit.2⟩
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp [goodSplit, drop] at hgood
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            exact ⟨⟨hfit.1.1,
              splitRange_of_splitCondition_of_contains_of_goodRSplit
                k lo f3 hgood (by simpa using hcond) hfit.1.2⟩,
              hfit.2⟩
  | succ j ih =>
      cases p with
      | Pnil =>
          simp [goodSplit, drop] at hgood
      | Pcons s h p =>
          simp only [goodSplit_succ_pcons] at hgood
          simp only [split_succ_pcons, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨hs, hh⟩, ht⟩
          exact ⟨⟨hs, hh⟩,
            ih p (G.face x) hgood
              (by simpa [Function.iterate_succ_apply] using hcond) ht⟩
      | Pcons6 h f1 p =>
          simp only [goodSplit_succ_pcons6] at hgood
          simp only [split_succ_pcons6, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
            at hfit ⊢
          rcases hfit with ⟨⟨⟨hs, hh⟩, hf1⟩, ht⟩
          exact ⟨⟨⟨hs, hh⟩, hf1⟩,
            ih p (G.face x) hgood
              (by simpa [Function.iterate_succ_apply] using hcond) ht⟩
      | Pcons7 h f1 f2 p =>
          simp only [goodSplit_succ_pcons7] at hgood
          simp only [split_succ_pcons7, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, ht⟩
          exact ⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩,
            ih p (G.face x) hgood
              (by simpa [Function.iterate_succ_apply] using hcond) ht⟩
      | Pcons8 h f1 f2 f3 p =>
          simp only [goodSplit_succ_pcons8] at hgood
          simp only [split_succ_pcons8, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, hf3⟩, ht⟩
          exact ⟨⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, hf3⟩,
            ih p (G.face x) hgood
              (by simpa [Function.iterate_succ_apply] using hcond) ht⟩

theorem exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hcond : splitCondition k lo
      (G.arity (SubpartLoc.move i G ((G.face : G.Dart → G.Dart)^[j] x))) =
        true)
    (hfit : exactFitp G x p = true) :
    exactFitp G x (split i j k lo p) = true := by
  have hfits := hfit
  simp [exactFitp] at hfits ⊢
  exact ⟨by simpa [size_split] using hfits.1,
    fitp_split_of_splitCondition_of_fitp_of_goodSplit_of_arity_ge_five
      (G := G) hge i j k lo p x hgood hcond hfits.2⟩

end

end Part

end FourColor

end Schematic.Math.GraphTheory
