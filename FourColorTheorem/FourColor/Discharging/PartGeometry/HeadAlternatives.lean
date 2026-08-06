import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitStructure
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

private theorem exactFitp_split_pair_of_fitp_split_pair
    (i : SubpartLoc) (k : Nat) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x p = true)
    (hsplit :
      fitp G x p = true →
        fitp G x (split i 0 k true p) = true ∨
          fitp G x (split i 0 k false p) = true) :
    exactFitp G x (split i 0 k true p) = true ∨
      exactFitp G x (split i 0 k false p) = true := by
  have hfit' := hfit
  simp [exactFitp] at hfit'
  rcases hsplit hfit'.2 with hlo | hhi
  · left
    simp [exactFitp, size_split, hfit'.1, hlo]
  · right
    simp [exactFitp, size_split, hfit'.1, hhi]

private theorem fitp_pcons6_free_of_fitp_pcons_pr66_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr66 h p) = true) :
    fitp G x (Pcons6 h PRange.Pr59 p) = true := by
  simp only [fitp] at hfit ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hfit.1,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))⟩, hfit.2⟩

private theorem fitp_pcons7_free_of_fitp_pcons_pr77_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr77 h p) = true) :
    fitp G x (Pcons7 h PRange.Pr59 PRange.Pr59 p) = true := by
  simp only [fitp] at hfit ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true]
  exact ⟨⟨⟨hfit.1,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))⟩,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))⟩, hfit.2⟩

private theorem fitp_pcons8_free_of_fitp_pcons_pr88_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr88 h p) = true) :
    fitp G x (Pcons8 h PRange.Pr59 PRange.Pr59 PRange.Pr59 p) = true := by
  simp only [fitp] at hfit ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hfit.1,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan1 G x))⟩,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan2 G x))⟩,
    PRange.contains_Pr59_of_ge_five
      (hge (SubpartLoc.move SubpartLoc.Pfan3 G x))⟩, hfit.2⟩

theorem fitp_split_head_spoke_low_or_high
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons s h p) = true) :
    fitp G x (split SubpartLoc.Pspoke 0 k true (Pcons s h p)) = true ∨
      fitp G x (split SubpartLoc.Pspoke 0 k false (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePs h).fitp_splitRange_low_or_high (G := G) k s p x hfit

theorem exactFitp_split_head_spoke_low_or_high
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x (split SubpartLoc.Pspoke 0 k true (Pcons s h p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pspoke 0 k false (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePs h).exactFitp_splitRange_low_or_high (G := G) k s p x hfit

theorem fitp_split_head_hat_low_or_high
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons s h p) = true) :
    fitp G x (split SubpartLoc.Phat 0 k true (Pcons s h p)) = true ∨
      fitp G x (split SubpartLoc.Phat 0 k false (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePh s).fitp_splitRange_low_or_high (G := G) k h p x hfit

theorem exactFitp_split_head_hat_low_or_high
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k true (Pcons s h p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k false (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePh s).exactFitp_splitRange_low_or_high (G := G) k h p x hfit

theorem fitp_split_head_hat6_low_or_high
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons6 h f1 p) = true) :
    fitp G x (split SubpartLoc.Phat 0 k true (Pcons6 h f1 p)) =
        true ∨
      fitp G x (split SubpartLoc.Phat 0 k false (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).fitp_splitRange_low_or_high (G := G) k h p x hfit

theorem exactFitp_split_head_hat6_low_or_high
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k true (Pcons6 h f1 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k false (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).exactFitp_splitRange_low_or_high (G := G) k h p x hfit

theorem fitp_split_head_fan1_6_low_or_high
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons6 h f1 p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons6 h f1 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).fitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem exactFitp_split_head_fan1_6_low_or_high
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k true (Pcons6 h f1 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan1 0 k false (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).exactFitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem fitp_split_head_hat7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons7 h f1 f2 p) = true) :
    fitp G x (split SubpartLoc.Phat 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      fitp G x (split SubpartLoc.Phat 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7h f1 f2).fitp_splitRange_low_or_high (G := G) k h p x hfit

theorem exactFitp_split_head_hat7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7h f1 f2).exactFitp_splitRange_low_or_high (G := G) k h p x hfit

theorem fitp_split_head_fan1_7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons7 h f1 f2 p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f1 h f2).fitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem exactFitp_split_head_fan1_7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan1 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f1 h f2).exactFitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem fitp_split_head_fan2_7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons7 h f1 f2 p) = true) :
    fitp G x (split SubpartLoc.Pfan2 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan2 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f2 h f1).fitp_splitRange_low_or_high (G := G) k f2 p x hfit

theorem exactFitp_split_head_fan2_7_low_or_high
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan2 0 k true (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan2 0 k false (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f2 h f1).exactFitp_splitRange_low_or_high (G := G) k f2 p x hfit

theorem fitp_split_head_hat8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons8 h f1 f2 f3 p) = true) :
    fitp G x (split SubpartLoc.Phat 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      fitp G x (split SubpartLoc.Phat 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).fitp_splitRange_low_or_high (G := G) k h p x hfit

theorem exactFitp_split_head_hat8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).exactFitp_splitRange_low_or_high (G := G) k h p x hfit

theorem fitp_split_head_fan1_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons8 h f1 f2 f3 p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).fitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem exactFitp_split_head_fan1_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan1 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).exactFitp_splitRange_low_or_high (G := G) k f1 p x hfit

theorem fitp_split_head_fan2_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons8 h f1 f2 f3 p) = true) :
    fitp G x (split SubpartLoc.Pfan2 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan2 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).fitp_splitRange_low_or_high (G := G) k f2 p x hfit

theorem exactFitp_split_head_fan2_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan2 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan2 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).exactFitp_splitRange_low_or_high (G := G) k f2 p x hfit

theorem fitp_split_head_fan3_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons8 h f1 f2 f3 p) = true) :
    fitp G x (split SubpartLoc.Pfan3 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan3 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).fitp_splitRange_low_or_high (G := G) k f3 p x hfit

theorem exactFitp_split_head_fan3_8_low_or_high
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan3 0 k true (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan3 0 k false (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).exactFitp_splitRange_low_or_high (G := G) k f3 p x hfit

theorem fitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr66 h p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr66 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr66 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).fitp_splitRange_low_or_high (G := G) k PRange.Pr59 p x
      (fitp_pcons6_free_of_fitp_pcons_pr66_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr66 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr66 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr66 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

theorem fitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr77 h p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr77 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr77 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f1 h PRange.Pr59).fitp_splitRange_low_or_high
      (G := G) k PRange.Pr59 p x
      (fitp_pcons7_free_of_fitp_pcons_pr77_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr77 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr77 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

theorem fitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr77 h p) = true) :
    fitp G x (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr77 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr77 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f2 h PRange.Pr59).fitp_splitRange_low_or_high
      (G := G) k PRange.Pr59 p x
      (fitp_pcons7_free_of_fitp_pcons_pr77_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr77 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr77 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

theorem fitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr88 h p) = true) :
    fitp G x (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h PRange.Pr59 PRange.Pr59).fitp_splitRange_low_or_high
      (G := G) k PRange.Pr59 p x
      (fitp_pcons8_free_of_fitp_pcons_pr88_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

theorem fitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr88 h p) = true) :
    fitp G x (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h PRange.Pr59 PRange.Pr59).fitp_splitRange_low_or_high
      (G := G) k PRange.Pr59 p x
      (fitp_pcons8_free_of_fitp_pcons_pr88_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

theorem fitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (Pcons PRange.Pr88 h p) = true) :
    fitp G x (split SubpartLoc.Pfan3 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      fitp G x (split SubpartLoc.Pfan3 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h PRange.Pr59 PRange.Pr59).fitp_splitRange_low_or_high
      (G := G) k PRange.Pr59 p x
      (fitp_pcons8_free_of_fitp_pcons_pr88_of_arity_ge_five
        (G := G) hge h p x hfit)

theorem exactFitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan3 0 k true (Pcons PRange.Pr88 h p)) =
        true ∨
      exactFitp G x
        (split SubpartLoc.Pfan3 0 k false (Pcons PRange.Pr88 h p)) =
        true := by
  exact exactFitp_split_pair_of_fitp_split_pair
    (G := G) _ k _ x hfit
    (fitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x)

end

end Part

end FourColor

end Schematic.Math.GraphTheory
