import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitSemantics
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem exactFitp_of_exactFitp_split_head_spoke_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k s = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pspoke 0 k lo (Pcons s h p)) = true) :
    exactFitp G x (Pcons s h p) = true := by
  simpa [split, take, drop, append] using
    (updatePs h).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo s p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_hat_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons s h p)) = true) :
    exactFitp G x (Pcons s h p) = true := by
  simpa [split, take, drop, append] using
    (updatePh s).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_hat6_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons6 h f1 p)) = true) :
    exactFitp G x (Pcons6 h f1 p) = true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_fan1_6_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons6 h f1 p)) = true) :
    exactFitp G x (Pcons6 h f1 p) = true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f1 p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_spoke_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k s = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pspoke 0 k lo (Pcons s h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updatePs h).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo s p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_hat_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons s h p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updatePh s).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_hat6_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons6 h f1 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_fan1_6_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons6 h f1 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f1 p x hgood hfit

theorem exactFitp_split_head_spoke_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k s = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) = true)
    (hfit : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x
      (split SubpartLoc.Pspoke 0 k lo (Pcons s h p)) = true := by
  simpa [split, take, drop, append] using
    (updatePs h).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo s p x hgood hcond hfit

theorem exactFitp_split_head_hat_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    (hfit : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons s h p)) = true := by
  simpa [split, take, drop, append] using
    (updatePh s).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo h p x hgood hcond hfit

theorem exactFitp_split_head_hat6_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    (hfit : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons6 h f1 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo h p x hgood hcond hfit

theorem exactFitp_split_head_fan1_6_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    (hfit : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons6 h f1 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo f1 p x hgood hcond hfit

end

end Part

end FourColor

end Schematic.Math.GraphTheory
