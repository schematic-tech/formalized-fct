import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadRestrictions.CanonicalRanges
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem not_both_exactFitp_split_head_spoke_of_goodRSplit
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k s = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pspoke 0 k true (Pcons s h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pspoke 0 k false (Pcons s h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_hat_of_goodRSplit
    (k : Nat) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Phat 0 k true (Pcons s h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Phat 0 k false (Pcons s h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_hat6_of_goodRSplit
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Phat 0 k true (Pcons6 h f1 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Phat 0 k false (Pcons6 h f1 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_6_of_goodRSplit
    (k : Nat) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons6 h f1 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons6 h f1 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_hat7_of_goodRSplit
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Phat 0 k true (Pcons7 h f1 f2 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Phat 0 k false (Pcons7 h f1 f2 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_7_of_goodRSplit
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons7 h f1 f2 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons7 h f1 f2 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan2_7_of_goodRSplit
    (k : Nat) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f2 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan2 0 k true (Pcons7 h f1 f2 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan2 0 k false (Pcons7 h f1 f2 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_hat8_of_goodRSplit
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Phat 0 k true (Pcons8 h f1 f2 f3 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Phat 0 k false (Pcons8 h f1 f2 f3 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_8_of_goodRSplit
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons8 h f1 f2 f3 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons8 h f1 f2 f3 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan2_8_of_goodRSplit
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f2 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan2 0 k true (Pcons8 h f1 f2 f3 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan2 0 k false (Pcons8 h f1 f2 f3 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan3_8_of_goodRSplit
    (k : Nat) (h f1 f2 f3 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f3 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan3 0 k true (Pcons8 h f1 f2 f3 p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan3 0 k false (Pcons8 h f1 f2 f3 p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_pr66_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr66 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr66 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_pr77_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr77 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr77 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan2_pr77_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr77 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr77 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan1_pr88_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan1 0 k true (Pcons PRange.Pr88 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan1 0 k false (Pcons PRange.Pr88 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan2_pr88_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan2 0 k true (Pcons PRange.Pr88 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan2 0 k false (Pcons PRange.Pr88 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

theorem not_both_exactFitp_split_head_fan3_pr88_of_goodRSplit
    (k : Nat) (h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k PRange.Pr59 = true)
    (hlo : exactFitp G x
      (split SubpartLoc.Pfan3 0 k true (Pcons PRange.Pr88 h p)) = true)
    (hhi : exactFitp G x
      (split SubpartLoc.Pfan3 0 k false (Pcons PRange.Pr88 h p)) = true) :
    False := by
  exact not_both_exactFitp_split_of_goodSplit
    (G := G) _ 0 k _ x
    (by simpa [goodSplit, drop] using hgood) hlo hhi

end

end Part

end FourColor

end Schematic.Math.GraphTheory
