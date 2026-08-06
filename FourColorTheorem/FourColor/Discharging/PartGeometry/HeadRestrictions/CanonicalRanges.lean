import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadRestrictions.EightRanges
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem exactFitp_of_exactFitp_split_head_fan1_pr66
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr66 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr66 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1, hs.2.1.1.2⟩, hs.2.2⟩⟩

theorem exactFitp_of_exactFitp_split_head_fan1_pr77
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr77 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr77 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1.1, hs.2.1.1.1.2⟩, hs.2.2⟩⟩

theorem exactFitp_of_exactFitp_split_head_fan2_pr77
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr77 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr77 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1.1, hs.2.1.1.1.2⟩, hs.2.2⟩⟩

theorem exactFitp_of_exactFitp_split_head_fan1_pr88
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr88 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1.1.1, hs.2.1.1.1.1.2⟩, hs.2.2⟩⟩

theorem exactFitp_of_exactFitp_split_head_fan2_pr88
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr88 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1.1.1, hs.2.1.1.1.1.2⟩, hs.2.2⟩⟩

theorem exactFitp_of_exactFitp_split_head_fan3_pr88
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    exactFitp G x (Pcons PRange.Pr88 h p) = true := by
  have hs := hfit
  simp [exactFitp, split, take, drop, append, fitp] at hs ⊢
  exact ⟨by simpa [size] using hs.1,
    ⟨⟨hs.2.1.1.1.1.1, hs.2.1.1.1.1.2⟩, hs.2.2⟩⟩

theorem splitCondition_of_exactFitp_split_head_fan1_pr66_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr66 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem splitCondition_of_exactFitp_split_head_fan1_pr77_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr77 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem splitCondition_of_exactFitp_split_head_fan2_pr77_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr77 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem splitCondition_of_exactFitp_split_head_fan1_pr88_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem splitCondition_of_exactFitp_split_head_fan2_pr88_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem splitCondition_of_exactFitp_split_head_fan3_pr88_of_goodRSplit
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons PRange.Pr88 h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) =
      true := by
  simpa using
    (splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) hfit)

theorem exactFitp_split_head_fan1_pr66_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr66 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr66 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

theorem exactFitp_split_head_fan1_pr77_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr77 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

theorem exactFitp_split_head_fan2_pr77_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr77 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

theorem exactFitp_split_head_fan1_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr88 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

theorem exactFitp_split_head_fan2_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr88 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

theorem exactFitp_split_head_fan3_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) = true)
    (hfit : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons PRange.Pr88 h p)) = true := by
  exact
    exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) hge _ 0 k lo _ x
      (by simpa [goodSplit, drop] using hgood) (by simpa using hcond) hfit

end

end Part

end FourColor

end Schematic.Math.GraphTheory
