import FourColorTheorem.FourColor.Presentation.Soundness.MirrorTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

/-- Success is contravariant along forcedness: if every valid hub fitting `p`
also fits the already successful part `q`, then `p` is successful. -/
theorem successful_of_forced_part
    {p q : Part}
    (hforce : ForcedPart.{u} p q)
    (hq : Successful.{u} q) :
    Successful.{u} p := by
  intro G x hx
  cases hfit : Part.exactFitp G x p
  · rfl
  · have hqfit : Part.exactFitp G x q = true :=
      hforce x hx hfit
    have hqfail : Part.exactFitp G x q = false :=
      hq x hx
    rw [hqfit] at hqfail
    cases hqfail

/-- If `p` forces a successful part, then `p` succeeds inside any ambient
presentation goal. -/
theorem succeedsIn_of_forced_successful
    {p0 p q : Part}
    (hforce : ForcedPart.{u} p q)
    (hq : Successful.{u} q) :
    SucceedsIn.{u} p0 p := by
  intro _
  exact successful_of_forced_part hforce hq

theorem forcedPart_of_cmp_subset_size_eq {p q : Part}
    (hcmp : Part.cmp p q = PartRel.Psubset)
    (hsize : p.size = q.size) :
    ForcedPart.{u} p q := by
  intro G x _ hfit
  exact Part.exactFitp_of_cmp_eq_subset_of_size_eq hcmp hsize hfit

theorem succeedsIn_of_cmp_subset_successful {p0 p q : Part}
    (hcmp : Part.cmp p q = PartRel.Psubset)
    (hsize : p.size = q.size)
    (hq : Successful.{u} q) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_forced_successful
    (forcedPart_of_cmp_subset_size_eq hcmp hsize) hq

/-- Build forcedness from a pointwise exact-fit transport. -/
theorem forcedPart_of_exactFitp_transport
    {p q : Part}
    (htransport : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x q = true) :
    ForcedPart.{u} p q := by
  intro G x hx hfit
  exact htransport x hx hfit

/-- Lift forcedness through two exact-fit encodings sharing an intermediate
side condition.  Split transports use this with the split predicate as
`Condition`; it packages the source decoding and target reconstruction once. -/
theorem forcedPart_lift_through_exactFitp
    {child0 parent0 parent child : Part}
    {Condition : (G : Hypermap.{u}) → G.Dart → Prop}
    (hsource : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x child0 = true →
          Condition G x ∧ Part.exactFitp G x parent0 = true)
    (htarget : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Condition G x →
          Part.exactFitp G x parent = true →
            Part.exactFitp G x child = true)
    (hforce : ForcedPart.{u} parent0 parent) :
    ForcedPart.{u} child0 child := by
  intro G x hx hfit
  obtain ⟨hcondition, hparent0⟩ := hsource x hx hfit
  exact htarget x hx hcondition (hforce x hx hparent0)

theorem forcedPart_of_split_head_spoke_of_goodRSplit
    {k : Nat} {lo : Bool} {s h : PRange} {p : Part}
    (hgood : Part.goodRSplit k s = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s h p))
      (Part.Pcons s h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_spoke_of_goodRSplit
        (G := G) k lo s h p x hgood hfit

theorem forcedPart_of_split_head_hat_of_goodRSplit
    {k : Nat} {lo : Bool} {s h : PRange} {p : Part}
    (hgood : Part.goodRSplit k h = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s h p))
      (Part.Pcons s h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_hat_of_goodRSplit
        (G := G) k lo s h p x hgood hfit

theorem forcedPart_of_split_head_hat6_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 : PRange} {p : Part}
    (hgood : Part.goodRSplit k h = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h f1 p))
      (Part.Pcons6 h f1 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_hat6_of_goodRSplit
        (G := G) k lo h f1 p x hgood hfit

theorem forcedPart_of_split_head_fan1_6_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f1 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h f1 p))
      (Part.Pcons6 h f1 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_6_of_goodRSplit
        (G := G) k lo h f1 p x hgood hfit

theorem forcedPart_of_split_head_hat7_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 : PRange} {p : Part}
    (hgood : Part.goodRSplit k h = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h f1 f2 p))
      (Part.Pcons7 h f1 f2 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_hat7_of_goodRSplit
        (G := G) k lo h f1 f2 p x hgood hfit

theorem forcedPart_of_split_head_fan1_7_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f1 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h f1 f2 p))
      (Part.Pcons7 h f1 f2 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_7_of_goodRSplit
        (G := G) k lo h f1 f2 p x hgood hfit

theorem forcedPart_of_split_head_fan2_7_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f2 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h f1 f2 p))
      (Part.Pcons7 h f1 f2 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan2_7_of_goodRSplit
        (G := G) k lo h f1 f2 p x hgood hfit

theorem forcedPart_of_split_head_hat8_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 f3 : PRange} {p : Part}
    (hgood : Part.goodRSplit k h = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons8 h f1 f2 f3 p))
      (Part.Pcons8 h f1 f2 f3 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_hat8_of_goodRSplit
        (G := G) k lo h f1 f2 f3 p x hgood hfit

theorem forcedPart_of_split_head_fan1_8_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 f3 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f1 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons8 h f1 f2 f3 p))
      (Part.Pcons8 h f1 f2 f3 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_8_of_goodRSplit
        (G := G) k lo h f1 f2 f3 p x hgood hfit

theorem forcedPart_of_split_head_fan2_8_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 f3 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f2 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons8 h f1 f2 f3 p))
      (Part.Pcons8 h f1 f2 f3 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan2_8_of_goodRSplit
        (G := G) k lo h f1 f2 f3 p x hgood hfit

theorem forcedPart_of_split_head_fan3_8_of_goodRSplit
    {k : Nat} {lo : Bool} {h f1 f2 f3 : PRange} {p : Part}
    (hgood : Part.goodRSplit k f3 = true) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons8 h f1 f2 f3 p))
      (Part.Pcons8 h f1 f2 f3 p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan3_8_of_goodRSplit
        (G := G) k lo h f1 f2 f3 p x hgood hfit

theorem forcedPart_of_split_head_fan1_pr66
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h p))
      (Part.Pcons PRange.Pr66 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_pr66
        (G := G) k lo h p x hfit

theorem forcedPart_of_split_head_fan1_pr77
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h p))
      (Part.Pcons PRange.Pr77 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_pr77
        (G := G) k lo h p x hfit

theorem forcedPart_of_split_head_fan2_pr77
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h p))
      (Part.Pcons PRange.Pr77 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan2_pr77
        (G := G) k lo h p x hfit

theorem forcedPart_of_split_head_fan1_pr88
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h p))
      (Part.Pcons PRange.Pr88 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan1_pr88
        (G := G) k lo h p x hfit

theorem forcedPart_of_split_head_fan2_pr88
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h p))
      (Part.Pcons PRange.Pr88 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan2_pr88
        (G := G) k lo h p x hfit

theorem forcedPart_of_split_head_fan3_pr88
    {k : Nat} {lo : Bool} {h : PRange} {p : Part} :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h p))
      (Part.Pcons PRange.Pr88 h p) :=
  forcedPart_of_exactFitp_transport fun {G} x _ hfit =>
    Part.exactFitp_of_exactFitp_split_head_fan3_pr88
        (G := G) k lo h p x hfit

theorem forcedPart_split_head_spoke_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {s0 h0 : PRange} {p0 : Part}
    {s h : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k s0 = true)
    (hgood : Part.goodRSplit k s = true)
    (hforce : ForcedPart.{u} (Part.Pcons s0 h0 p0) (Part.Pcons s h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s0 h0 p0))
      (Part.split SubpartLoc.Pspoke 0 k lo (Part.Pcons s h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_spoke_of_goodRSplit
            (G := G) k lo s0 h0 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_spoke_of_goodRSplit
            (G := G) k lo s0 h0 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_spoke_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo s h p x hgood hcond hfit

theorem forcedPart_split_head_hat_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {s0 h0 : PRange} {p0 : Part}
    {s h : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hforce : ForcedPart.{u} (Part.Pcons s0 h0 p0) (Part.Pcons s h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s0 h0 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons s h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_hat_of_goodRSplit
            (G := G) k lo s0 h0 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_hat_of_goodRSplit
            (G := G) k lo s0 h0 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_hat_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo s h p x hgood hcond hfit

theorem forcedPart_split_head_hat6_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 : PRange} {p0 : Part}
    {h f1 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hforce : ForcedPart.{u} (Part.Pcons6 h0 f10 p0) (Part.Pcons6 h f1 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h0 f10 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons6 h f1 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_hat6_of_goodRSplit
            (G := G) k lo h0 f10 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_hat6_of_goodRSplit
            (G := G) k lo h0 f10 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_hat6_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 p x hgood hcond hfit

theorem forcedPart_split_head_fan1_6_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 : PRange} {p0 : Part}
    {h f1 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hforce : ForcedPart.{u} (Part.Pcons6 h0 f10 p0) (Part.Pcons6 h f1 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h0 f10 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons6 h f1 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_6_of_goodRSplit
            (G := G) k lo h0 f10 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_6_of_goodRSplit
            (G := G) k lo h0 f10 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_6_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 p x hgood hcond hfit

theorem forcedPart_split_head_hat7_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons7 h0 f10 f20 p0) (Part.Pcons7 h f1 f2 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons7 h f1 f2 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_hat7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_hat7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_hat7_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan1_7_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons7 h0 f10 f20 p0) (Part.Pcons7 h f1 f2 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons7 h f1 f2 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_7_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan2_7_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 : PRange} {p0 : Part}
    {h f1 f2 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f20 = true)
    (hgood : Part.goodRSplit k f2 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons7 h0 f10 f20 p0) (Part.Pcons7 h f1 f2 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h0 f10 f20 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons7 h f1 f2 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan2_7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan2_7_of_goodRSplit
            (G := G) k lo h0 f10 f20 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan2_7_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 p x hgood hcond
          hfit

theorem forcedPart_split_head_hat8_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k h0 = true)
    (hgood : Part.goodRSplit k h = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.Pcons8 h f1 f2 f3 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Phat 0 k lo (Part.Pcons8 h f1 f2 f3 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_hat8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_hat8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_hat8_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 f3 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan1_8_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f10 = true)
    (hgood : Part.goodRSplit k f1 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.Pcons8 h f1 f2 f3 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons8 h f1 f2 f3 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_8_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 f3 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan2_8_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f20 = true)
    (hgood : Part.goodRSplit k f2 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.Pcons8 h f1 f2 f3 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons8 h f1 f2 f3 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan2_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan2_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan2_8_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 f3 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan3_8_of_forcedPart_of_goodRSplit
    {k : Nat} {lo : Bool}
    {h0 f10 f20 f30 : PRange} {p0 : Part}
    {h f1 f2 f3 : PRange} {p : Part}
    (hgood0 : Part.goodRSplit k f30 = true)
    (hgood : Part.goodRSplit k f3 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons8 h0 f10 f20 f30 p0)
        (Part.Pcons8 h f1 f2 f3 p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons8 h0 f10 f20 f30 p0))
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons8 h f1 f2 f3 p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan3_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit,
      Part.exactFitp_of_exactFitp_split_head_fan3_8_of_goodRSplit
            (G := G) k lo h0 f10 f20 f30 p0 x hgood0 hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan3_8_of_splitCondition_of_exactFitp_of_goodRSplit
          (G := G) k lo h f1 f2 f3 p x hgood hcond
          hfit

theorem forcedPart_split_head_fan1_pr66_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr66 h0 p0)
        (Part.Pcons PRange.Pr66 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr66 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_pr66_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_pr66
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_pr66_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit

theorem forcedPart_split_head_fan1_pr77_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr77 h0 p0)
        (Part.Pcons PRange.Pr77 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr77 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_pr77_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_pr77
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_pr77_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit

theorem forcedPart_split_head_fan2_pr77_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr77 h0 p0)
        (Part.Pcons PRange.Pr77 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h0 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr77 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan2_pr77_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan2_pr77
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan2_pr77_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit

theorem forcedPart_split_head_fan1_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.Pcons PRange.Pr88 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan1 0 k lo (Part.Pcons PRange.Pr88 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan1_pr88_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan1_pr88
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan1_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit

theorem forcedPart_split_head_fan2_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.Pcons PRange.Pr88 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan2 0 k lo (Part.Pcons PRange.Pr88 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan2_pr88_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan2_pr88
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan2_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit

theorem forcedPart_split_head_fan3_pr88_of_forcedPart_of_goodRSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {k : Nat} {lo : Bool}
    {h0 : PRange} {p0 : Part}
    {h : PRange} {p : Part}
    (hgood : Part.goodRSplit k PRange.Pr59 = true)
    (hforce :
      ForcedPart.{u} (Part.Pcons PRange.Pr88 h0 p0)
        (Part.Pcons PRange.Pr88 h p)) :
    ForcedPart.{u}
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h0 p0))
      (Part.split SubpartLoc.Pfan3 0 k lo (Part.Pcons PRange.Pr88 h p)) := by
  refine forcedPart_lift_through_exactFitp
    (Condition := fun G x =>
      Part.splitCondition k lo
              (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) = true)
    ?_ ?_ hforce
  · intro G x _ hfit
    exact ⟨
      Part.splitCondition_of_exactFitp_split_head_fan3_pr88_of_goodRSplit
            (G := G) k lo h0 p0 x hgood hfit,
      Part.exactFitp_of_exactFitp_split_head_fan3_pr88
            (G := G) k lo h0 p0 x hfit⟩
  · intro G x hx hcond hfit
    exact
      Part.exactFitp_split_head_fan3_pr88_of_splitCondition_of_exactFitp_of_goodRSplit_of_arity_ge_five
            (G := G) (hge G x hx) k lo h p x hgood hcond
            hfit


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
