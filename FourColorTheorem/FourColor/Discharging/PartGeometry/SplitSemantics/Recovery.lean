import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitSemantics.Choice
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem exactFitp_split_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x p = true) :
    exactFitp G x (split i j k lo p) = true ∨
      exactFitp G x (split i j k (!lo) p) = true := by
  have hfits := hfit
  simp [exactFitp] at hfits
  rcases fitp_split_or_complement_of_arity_ge_five
      (G := G) hge i j k lo p x hfits.2 with hlo | hhi
  · left
    simp [exactFitp, hfits.1, hlo]
  · right
    simp [exactFitp, hfits.1, hhi]

theorem fitp_of_fitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hfit : fitp G x (split i j k lo p) = true) :
    fitp G x p = true := by
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
            have hs :=
              contains_of_splitRange_of_goodRSplit k lo s hgood hfit.1.1
            aesop
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
            have hh :=
              contains_of_splitRange_of_goodRSplit k lo h hgood hfit.1.2
            aesop
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit ⊢
            have hh :=
              contains_of_splitRange_of_goodRSplit k lo h hgood
                hfit.1.1.2
            aesop
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            have hh :=
              contains_of_splitRange_of_goodRSplit k lo h hgood
                hfit.1.1.1.2
            aesop
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            have hh :=
              contains_of_splitRange_of_goodRSplit k lo h hgood
                hfit.1.1.1.1.2
            aesop
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              first
              | exact ⟨hfit.1.1, hfit.2⟩
              | exact ⟨hfit.1.1.1, hfit.2⟩
              | exact ⟨hfit.1.1.1.1, hfit.2⟩
        | Pcons6 h f1 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
              at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f1 hgood hfit.1.2
            aesop
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f1 hgood
                hfit.1.1.2
            aesop
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f1 hgood
                hfit.1.1.1.2
            aesop
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              first
              | exact ⟨hfit.1.1.1, hfit.2⟩
              | exact ⟨hfit.1.1.1.1, hfit.2⟩
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f2 hgood hfit.1.2
            aesop
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f2 hgood
                hfit.1.1.2
            aesop
      · cases p with
        | Pnil =>
            simp [goodSplit, drop] at hgood
        | Pcons s h p =>
            cases s <;>
              simp [goodSplit, split, take, drop, append, fitp]
                at hgood hfit ⊢
            all_goals
              exact ⟨hfit.1.1.1.1, hfit.2⟩
        | Pcons6 h f1 p =>
            simp [goodSplit, drop] at hgood
        | Pcons7 h f1 f2 p =>
            simp [goodSplit, drop] at hgood
        | Pcons8 h f1 f2 f3 p =>
            simp only [goodSplit, drop] at hgood
            simp only [split, take, drop, append, fitp] at hfit ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
            have hf :=
              contains_of_splitRange_of_goodRSplit k lo f3 hgood hfit.1.2
            aesop
  | succ j ih =>
      cases p with
      | Pnil =>
          simp [goodSplit, drop] at hgood
      | Pcons s h p =>
          simp only [goodSplit_succ_pcons] at hgood
          simp only [split_succ_pcons, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨hs, hh⟩, ht⟩
          exact ⟨⟨hs, hh⟩, ih p (G.face x) hgood ht⟩
      | Pcons6 h f1 p =>
          simp only [goodSplit_succ_pcons6] at hgood
          simp only [split_succ_pcons6, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
            at hfit ⊢
          rcases hfit with ⟨⟨⟨hs, hh⟩, hf1⟩, ht⟩
          exact ⟨⟨⟨hs, hh⟩, hf1⟩, ih p (G.face x) hgood ht⟩
      | Pcons7 h f1 f2 p =>
          simp only [goodSplit_succ_pcons7] at hgood
          simp only [split_succ_pcons7, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, ht⟩
          exact ⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩,
            ih p (G.face x) hgood ht⟩
      | Pcons8 h f1 f2 f3 p =>
          simp only [goodSplit_succ_pcons8] at hgood
          simp only [split_succ_pcons8, fitp] at hfit ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfit ⊢
          rcases hfit with ⟨⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, hf3⟩, ht⟩
          exact ⟨⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, hf3⟩,
            ih p (G.face x) hgood ht⟩

theorem exactFitp_of_exactFitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hfit : exactFitp G x (split i j k lo p) = true) :
    exactFitp G x p = true := by
  have hfits := hfit
  simp [exactFitp] at hfits ⊢
  exact ⟨by simpa using hfits.1,
    fitp_of_fitp_split_of_goodSplit
      (G := G) i j k lo p x hgood hfits.2⟩

end

end Part

end FourColor

end Schematic.Math.GraphTheory
