import FourColorTheorem.FourColor.Presentation.Soundness.SplitSemantics

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

theorem succeedsIn_of_head_spoke_split
    {k : Nat} {lo : Bool}
    {s0 h0 : PRange} {p0 : Part}
    {s h : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k s0 = true)
    (hgood : Part.goodRSplit k s = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s0 h0 p0))
      (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s0 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons s0 h0 p0)
        (Part.split SubpartLoc.Pspoke 0 k (!lo) (Part.Pcons s h p))) :
    SucceedsIn.{u} (Part.Pcons s0 h0 p0) (Part.Pcons s h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_spoke_or_complement
        (G := G) k lo s h p x hfit)
    (fun hforce =>
      forcedPart_split_head_spoke_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_hat_split
    {k : Nat} {lo : Bool}
    {s0 h0 : PRange} {p0 : Part}
    {s h : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s0 h0 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s0 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons s0 h0 p0)
        (Part.split SubpartLoc.Phat 0 k (!lo) (Part.Pcons s h p))) :
    SucceedsIn.{u} (Part.Pcons s0 h0 p0) (Part.Pcons s h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat_or_complement
        (G := G) k lo s h p x hfit)
    (fun hforce =>
      forcedPart_split_head_hat_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_hat6_split
    {k : Nat} {lo : Bool}
    {h0 f10 : PRange} {p0 : Part}
    {h f1 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h0 f10 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h f1 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h0 f10 p0)) →
      SucceedsIn.{u} (Part.Pcons6 h0 f10 p0)
        (Part.split SubpartLoc.Phat 0 k (!lo) (Part.Pcons6 h f1 p))) :
    SucceedsIn.{u} (Part.Pcons6 h0 f10 p0) (Part.Pcons6 h f1 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat6_or_complement
        (G := G) k lo h f1 p x hfit)
    (fun hforce =>
      forcedPart_split_head_hat6_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_6_split
    {k : Nat} {lo : Bool}
    {h0 f10 : PRange} {p0 : Part}
    {h f1 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h0 f10 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h f1 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h0 f10 p0)) →
      SucceedsIn.{u} (Part.Pcons6 h0 f10 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo) (Part.Pcons6 h f1 p))) :
    SucceedsIn.{u} (Part.Pcons6 h0 f10 p0) (Part.Pcons6 h f1 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_6_or_complement
        (G := G) k lo h f1 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_6_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_hat7_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h0 f10 f20 p0)) →
      SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
        (Part.split SubpartLoc.Phat 0 k (!lo) (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
      (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat7_or_complement
        (G := G) k lo h f1 f2 p x hfit)
    (fun hforce =>
      forcedPart_split_head_hat7_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_7_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h0 f10 f20 p0)) →
      SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo) (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
      (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_7_or_complement
        (G := G) k lo h f1 f2 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_7_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan2_7_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f20 = true)
    (hgood : Part.goodRSplit k f2 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h0 f10 f20 p0)) →
      SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
        (Part.split SubpartLoc.Pfan2 0 k (!lo) (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} (Part.Pcons7 h0 f10 f20 p0)
      (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan2_7_or_complement
        (G := G) k lo h f1 f2 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan2_7_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_hat8_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Phat 0 k lo
          (Part.Pcons8 h0 f10 f20 f30 p0)) →
      SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.split SubpartLoc.Phat 0 k (!lo)
          (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
      (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat8_or_complement
        (G := G) k lo h f1 f2 f3 p x hfit)
    (fun hforce =>
      forcedPart_split_head_hat8_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_8_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo
        (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo
          (Part.Pcons8 h0 f10 f20 f30 p0)) →
      SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo)
          (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
      (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_8_or_complement
        (G := G) k lo h f1 f2 f3 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_8_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan2_8_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f20 = true)
    (hgood : Part.goodRSplit k f2 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo
        (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan2 0 k lo
          (Part.Pcons8 h0 f10 f20 f30 p0)) →
      SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.split SubpartLoc.Pfan2 0 k (!lo)
          (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
      (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan2_8_or_complement
        (G := G) k lo h f1 f2 f3 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan2_8_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan3_8_split
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f30 = true)
    (hgood : Part.goodRSplit k f3 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo
        (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan3 0 k lo
          (Part.Pcons8 h0 f10 f20 f30 p0)) →
      SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.split SubpartLoc.Pfan3 0 k (!lo)
          (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
      (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan3_8_or_complement
        (G := G) k lo h f1 f2 f3 p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan3_8_of_forcedPart_of_goodRSplit
        hgood0 hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_pr66_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr66 h0 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo)
          (Part.Pcons PRange.Pr66 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr66 h0 p0)
      (Part.Pcons PRange.Pr66 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr66_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_pr66_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_pr77_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr77 h0 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo)
          (Part.Pcons PRange.Pr77 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr77 h0 p0)
      (Part.Pcons PRange.Pr77 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr77_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_pr77_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan2_pr77_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h0 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr77 h0 p0)
        (Part.split SubpartLoc.Pfan2 0 k (!lo)
          (Part.Pcons PRange.Pr77 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr77 h0 p0)
      (Part.Pcons PRange.Pr77 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan2_pr77_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan2_pr77_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan1_pr88_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.split SubpartLoc.Pfan1 0 k (!lo)
          (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
      (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr88_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan1_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan2_pr88_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.split SubpartLoc.Pfan2 0 k (!lo)
          (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
      (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan2_pr88_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan2_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_fan3_pr88_split_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hl : SucceedsIn.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
        (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h0 p0)) →
      SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.split SubpartLoc.Pfan3 0 k (!lo)
          (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} (Part.Pcons PRange.Pr88 h0 p0)
      (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_split_cover_forced
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan3_pr88_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) k lo h p x hfit)
    (fun hforce =>
      forcedPart_split_head_fan3_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
        hge hgood hforce)
    hl hr

theorem succeedsIn_of_head_spoke_split_successful
    {p0 : Part} {k : Nat} {s h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pspoke 0 k true (Part.Pcons s h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pspoke 0 k false (Part.Pcons s h p))) :
    SucceedsIn.{u} p0 (Part.Pcons s h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_spoke_low_or_high (G := G) k s h p x hfit)
    hl hr

theorem succeedsIn_of_head_hat_split_successful
    {p0 : Part} {k : Nat} {s h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k true (Part.Pcons s h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k false (Part.Pcons s h p))) :
    SucceedsIn.{u} p0 (Part.Pcons s h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat_low_or_high (G := G) k s h p x hfit)
    hl hr

theorem succeedsIn_of_head_hat6_split_successful
    {p0 : Part} {k : Nat} {h f1 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k true (Part.Pcons6 h f1 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k false (Part.Pcons6 h f1 p))) :
    SucceedsIn.{u} p0 (Part.Pcons6 h f1 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat6_low_or_high (G := G) k h f1 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_6_split_successful
    {p0 : Part} {k : Nat} {h f1 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons6 h f1 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons6 h f1 p))) :
    SucceedsIn.{u} p0 (Part.Pcons6 h f1 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_6_low_or_high
        (G := G) k h f1 p x hfit)
    hl hr

theorem succeedsIn_of_head_hat7_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k true (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k false (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} p0 (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat7_low_or_high
        (G := G) k h f1 f2 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_7_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} p0 (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_7_low_or_high
        (G := G) k h f1 f2 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan2_7_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k true (Part.Pcons7 h f1 f2 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k false (Part.Pcons7 h f1 f2 p))) :
    SucceedsIn.{u} p0 (Part.Pcons7 h f1 f2 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan2_7_low_or_high
        (G := G) k h f1 f2 p x hfit)
    hl hr

theorem succeedsIn_of_head_hat8_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 f3 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k true (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Phat 0 k false (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} p0 (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_hat8_low_or_high
        (G := G) k h f1 f2 f3 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_8_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 f3 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} p0 (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan1_8_low_or_high
        (G := G) k h f1 f2 f3 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan2_8_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 f3 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k true (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k false (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} p0 (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan2_8_low_or_high
        (G := G) k h f1 f2 f3 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan3_8_split_successful
    {p0 : Part} {k : Nat} {h f1 f2 f3 : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan3 0 k true (Part.Pcons8 h f1 f2 f3 p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan3 0 k false (Part.Pcons8 h f1 f2 f3 p))) :
    SucceedsIn.{u} p0 (Part.Pcons8 h f1 f2 f3 p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x _ hfit =>
      Part.exactFitp_split_head_fan3_8_low_or_high
        (G := G) k h f1 f2 f3 p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_pr66_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons PRange.Pr66 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons PRange.Pr66 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr66 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_pr77_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons PRange.Pr77 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons PRange.Pr77 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr77 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr

theorem succeedsIn_of_head_fan2_pr77_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k true (Part.Pcons PRange.Pr77 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k false (Part.Pcons PRange.Pr77 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr77 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr

theorem succeedsIn_of_head_fan1_pr88_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k true (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan1 0 k false (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr

theorem succeedsIn_of_head_fan2_pr88_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k true (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan2 0 k false (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr

theorem succeedsIn_of_head_fan3_pr88_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {p0 : Part} {k : Nat} {h : PRange} {p : Part}
    (hl : Successful.{u}
      (Part.split SubpartLoc.Pfan3 0 k true (Part.Pcons PRange.Pr88 h p)))
    (hr : Successful.{u}
      (Part.split SubpartLoc.Pfan3 0 k false (Part.Pcons PRange.Pr88 h p))) :
    SucceedsIn.{u} p0 (Part.Pcons PRange.Pr88 h p) := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
        (G := G) (hge G x hx) k h p x hfit)
    hl hr


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
