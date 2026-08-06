import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadRestrictions.SevenRanges
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem exactFitp_of_exactFitp_split_head_hat8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    exactFitp G x (Pcons8 h f1 f2 f3 p) = true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_fan1_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    exactFitp G x (Pcons8 h f1 f2 f3 p) = true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f1 p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_fan2_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f2 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    exactFitp G x (Pcons8 h f1 f2 f3 p) = true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f2 p x hgood hfit

theorem exactFitp_of_exactFitp_split_head_fan3_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f3 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    exactFitp G x (Pcons8 h f1 f2 f3 p) = true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).exactFitp_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f3 p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_hat8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo h p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_fan1_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f1 p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_fan2_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f2 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f2 p x hgood hfit

theorem splitCondition_of_exactFitp_split_head_fan3_8_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f3 = true)
    (hfit : exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons8 h f1 f2 f3 p)) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) =
      true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).splitCondition_of_exactFitp_splitRange_of_goodRSplit
      (G := G) k lo f3 p x hgood hfit

theorem exactFitp_split_head_hat8_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k h = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x
      (split SubpartLoc.Phat 0 k lo (Pcons8 h f1 f2 f3 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo h p x hgood hcond hfit

theorem exactFitp_split_head_fan1_8_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f1 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan1 0 k lo (Pcons8 h f1 f2 f3 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo f1 p x hgood hcond hfit

theorem exactFitp_split_head_fan2_8_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f2 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan2 0 k lo (Pcons8 h f1 f2 f3 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo f2 p x hgood hcond hfit

theorem exactFitp_split_head_fan3_8_of_splitCondition_of_exactFitp_of_goodRSplit
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hgood : goodRSplit k f3 = true)
    (hcond :
      splitCondition k lo
        (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) = true)
    (hfit : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x
      (split SubpartLoc.Pfan3 0 k lo (Pcons8 h f1 f2 f3 p)) = true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).exactFitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo f3 p x hgood hcond hfit

end

end Part

end FourColor

end Schematic.Math.GraphTheory
