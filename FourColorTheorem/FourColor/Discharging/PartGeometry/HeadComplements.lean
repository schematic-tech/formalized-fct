import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadRestrictions
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem exactFitp_split_head_spoke_or_complement
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x (split SubpartLoc.Pspoke 0 k lo (Pcons s h p)) = true ∨
      exactFitp G x (split SubpartLoc.Pspoke 0 k (!lo) (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePs h).exactFitp_splitRange_or_complement
      (G := G) k lo s p x hfits

theorem exactFitp_split_head_hat_or_complement
    (k : Nat) (lo : Bool) (s h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons s h p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k lo (Pcons s h p)) = true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k (!lo) (Pcons s h p)) =
        true := by
  simpa [split, take, drop, append] using
    (updatePh s).exactFitp_splitRange_or_complement
      (G := G) k lo h p x hfits

theorem exactFitp_split_head_hat6_or_complement
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k lo (Pcons6 h f1 p)) = true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k (!lo) (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6h f1).exactFitp_splitRange_or_complement
      (G := G) k lo h p x hfits

theorem exactFitp_split_head_fan1_6_or_complement
    (k : Nat) (lo : Bool) (h f1 : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons6 h f1 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k lo (Pcons6 h f1 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan1 0 k (!lo) (Pcons6 h f1 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP6f1 h).exactFitp_splitRange_or_complement
      (G := G) k lo f1 p x hfits

theorem exactFitp_split_head_hat7_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k lo (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Phat 0 k (!lo) (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7h f1 f2).exactFitp_splitRange_or_complement
      (G := G) k lo h p x hfits

theorem exactFitp_split_head_fan1_7_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k lo (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan1 0 k (!lo) (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f1 h f2).exactFitp_splitRange_or_complement
      (G := G) k lo f1 p x hfits

theorem exactFitp_split_head_fan2_7_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons7 h f1 f2 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan2 0 k lo (Pcons7 h f1 f2 p)) =
        true ∨
      exactFitp G x (split SubpartLoc.Pfan2 0 k (!lo) (Pcons7 h f1 f2 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP7f2 h f1).exactFitp_splitRange_or_complement
      (G := G) k lo f2 p x hfits

theorem exactFitp_split_head_hat8_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hfits : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Phat 0 k lo (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x
          (split SubpartLoc.Phat 0 k (!lo) (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8h f1 f2 f3).exactFitp_splitRange_or_complement
      (G := G) k lo h p x hfits

theorem exactFitp_split_head_fan1_8_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hfits : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan1 0 k lo (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x
          (split SubpartLoc.Pfan1 0 k (!lo) (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f1 h f2 f3).exactFitp_splitRange_or_complement
      (G := G) k lo f1 p x hfits

theorem exactFitp_split_head_fan2_8_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hfits : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan2 0 k lo (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x
          (split SubpartLoc.Pfan2 0 k (!lo) (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f2 h f1 f3).exactFitp_splitRange_or_complement
      (G := G) k lo f2 p x hfits

theorem exactFitp_split_head_fan3_8_or_complement
    (k : Nat) (lo : Bool) (h f1 f2 f3 : PRange) (p : Part)
    (x : G.Dart)
    (hfits : exactFitp G x (Pcons8 h f1 f2 f3 p) = true) :
    exactFitp G x (split SubpartLoc.Pfan3 0 k lo (Pcons8 h f1 f2 f3 p)) =
        true ∨
      exactFitp G x
          (split SubpartLoc.Pfan3 0 k (!lo) (Pcons8 h f1 f2 f3 p)) =
        true := by
  simpa [split, take, drop, append] using
    (updateP8f3 h f1 f2).exactFitp_splitRange_or_complement
      (G := G) k lo f3 p x hfits

theorem exactFitp_split_head_fan1_pr66_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr66 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr66 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan1 0 k (!lo) (Pcons PRange.Pr66 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

theorem exactFitp_split_head_fan1_pr77_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr77 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan1 0 k (!lo) (Pcons PRange.Pr77 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

theorem exactFitp_split_head_fan2_pr77_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr77 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr77 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan2 0 k (!lo) (Pcons PRange.Pr77 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

theorem exactFitp_split_head_fan1_pr88_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan1 0 k lo (Pcons PRange.Pr88 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan1 0 k (!lo) (Pcons PRange.Pr88 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

theorem exactFitp_split_head_fan2_pr88_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan2 0 k lo (Pcons PRange.Pr88 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan2 0 k (!lo) (Pcons PRange.Pr88 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

theorem exactFitp_split_head_fan3_pr88_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (k : Nat) (lo : Bool) (h : PRange) (p : Part) (x : G.Dart)
    (hfits : exactFitp G x (Pcons PRange.Pr88 h p) = true) :
    exactFitp G x
        (split SubpartLoc.Pfan3 0 k lo (Pcons PRange.Pr88 h p)) = true ∨
      exactFitp G x
          (split SubpartLoc.Pfan3 0 k (!lo) (Pcons PRange.Pr88 h p)) =
        true := by
  cases lo <;> simpa [or_comm] using
    exactFitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
      (G := G) hge k h p x hfits

end

end Part

end FourColor

end Schematic.Math.GraphTheory
