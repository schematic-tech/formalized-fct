import FourColorTheorem.FourColor.Presentation.Soundness.Similarity

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

/-- A Boolean cover of exact fits transfers success from both covered branches
to the covered part.  This is the small semantic core behind split-style
presentation steps. -/
theorem successful_of_exactFitp_cover
    {p pl pr : Part}
    (hcover : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x pl = true ∨
            Part.exactFitp G x pr = true)
    (hl : Successful.{u} pl)
    (hr : Successful.{u} pr) :
    Successful.{u} p := by
  intro G x hx
  cases hp : Part.exactFitp G x p
  · rfl
  · rcases hcover x hx hp with hpl | hpr
    · have hfail := hl x hx
      rw [hpl] at hfail
      cases hfail
    · have hfail := hr x hx
      rw [hpr] at hfail
      cases hfail

/-- Semantic core of Coq `succeed_by_split`.

The executable presentation step supplies a cover of the parent part by its
two split branches, and a way to transport the current forcedness hypothesis
to the left subgoal context.  The right subgoal is allowed to depend on the
left context already being successful, matching Coq's `successful p0l -> ...`
premise. -/
theorem succeedsIn_of_split_cover_forced
    {p0 p p0l pl pr : Part}
    (hcover : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x pl = true ∨
            Part.exactFitp G x pr = true)
    (hleft : ForcedPart.{u} p0 p → ForcedPart.{u} p0l pl)
    (hl : SucceedsIn.{u} p0l pl)
    (hr : Successful.{u} p0l → SucceedsIn.{u} p0 pr) :
    SucceedsIn.{u} p0 p := by
  intro hp0p
  have hp0lpl : ForcedPart.{u} p0l pl := hleft hp0p
  have hpl : Successful.{u} pl := hl hp0lpl
  have hp0l_success : Successful.{u} p0l :=
    successful_of_forced_part hp0lpl hpl
  have hp0pr : ForcedPart.{u} p0 pr := by
    intro G x hx hp0fit
    rcases hcover x hx (hp0p x hx hp0fit) with hplfit | hprfit
    · have hfail := hpl x hx
      rw [hplfit] at hfail
      cases hfail
    · exact hprfit
  have hpr : Successful.{u} pr := (hr hp0l_success) hp0pr
  exact successful_of_exactFitp_cover hcover hpl hpr

/-- The same split-success core for the presentation case where the left
subgoal context is the left branch itself, i.e. the ambient context was not
split by the executable `goodSplit` test. -/
theorem succeedsIn_of_split_cover_self_left
    {p0 p pl pr : Part}
    (hcover : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x pl = true ∨
            Part.exactFitp G x pr = true)
    (hl : SucceedsIn.{u} pl pl)
    (hr : Successful.{u} pl → SucceedsIn.{u} p0 pr) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_split_cover_forced hcover
    (fun _ => forcedPart_refl.{u} pl) hl hr

/-- Executable-shape split rule, matching the `p0l` definition used by
`SplitAssumption.splitGoal` and Coq `succeed_by_split`.

The only split-specific semantic dependency is `hleft`, which is needed when
the ambient context itself passes `goodSplit`; when it does not, the left
subgoal context is the left branch and the proof uses reflexive forcedness. -/
theorem succeedsIn_of_splitGoal_cover
    {a : SplitAssumption} {p0 p : Part}
    (hcover : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x (a.apply p) = true ∨
            Part.exactFitp G x (a.complement.apply p) = true)
    (hleft : a.good p0 = true →
      ForcedPart.{u} p0 p → ForcedPart.{u} (a.apply p0) (a.apply p))
    (hl : SucceedsIn.{u}
      (if a.good p0 then a.apply p0 else a.apply p) (a.apply p))
    (hr : Successful.{u}
        (if a.good p0 then a.apply p0 else a.apply p) →
      SucceedsIn.{u} p0 (a.complement.apply p)) :
    SucceedsIn.{u} p0 p := by
  by_cases hgood0 : a.good p0 = true
  · exact succeedsIn_of_split_cover_forced hcover
      (fun hp0p => by
        simpa [hgood0] using hleft hgood0 hp0p)
      (by simpa [hgood0] using hl)
      (by simpa [hgood0] using hr)
  · have hfalse : a.good p0 = false := by
      cases h : a.good p0 <;> simp [h] at hgood0 ⊢
    exact succeedsIn_of_split_cover_self_left hcover
      (by simpa [hfalse] using hl)
      (by simpa [hfalse] using hr)

theorem succeedsIn_of_splitGoal_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {a : SplitAssumption} {p0 p : Part}
    (hleft : a.good p0 = true →
      ForcedPart.{u} p0 p → ForcedPart.{u} (a.apply p0) (a.apply p))
    (hl : SucceedsIn.{u}
      (if a.good p0 then a.apply p0 else a.apply p) (a.apply p))
    (hr : Successful.{u}
        (if a.good p0 then a.apply p0 else a.apply p) →
      SucceedsIn.{u} p0 (a.complement.apply p)) :
    SucceedsIn.{u} p0 p := by
  refine succeedsIn_of_splitGoal_cover
    (a := a) (p0 := p0) (p := p)
    (hcover := ?_) hleft hl hr
  intro G x hx hfit
  exact Part.exactFitp_split_or_complement_of_arity_ge_five
    (G := G) (hge G x hx) a.loc a.index a.cutoff a.low p x hfit

theorem forcedPart_split_of_forcedPart_of_goodSplit_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {i : SubpartLoc} {j k : Nat} {lo : Bool} {p0 p : Part}
    (hgood0 : Part.goodSplit i j k p0 = true)
    (hgood : Part.goodSplit i j k p = true)
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u}
      (Part.split i j k lo p0) (Part.split i j k lo p) := by
  intro G x hx hfit
  have hcond :
      Part.splitCondition k lo
        (G.arity
          (SubpartLoc.move i G
            ((G.face : G.Dart → G.Dart)^[j] x))) = true :=
    Part.splitCondition_of_exactFitp_split_of_goodSplit
      (G := G) i j k lo p0 x hgood0 hfit
  have hparent0 : Part.exactFitp G x p0 = true :=
    Part.exactFitp_of_exactFitp_split_of_goodSplit
      (G := G) i j k lo p0 x hgood0 hfit
  exact
    Part.exactFitp_split_of_splitCondition_of_exactFitp_of_goodSplit_of_arity_ge_five
      (G := G) (hge G x hx) i j k lo p x hgood hcond
      (hforce x hx hparent0)

theorem succeedsIn_of_splitGoal_good_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    {a : SplitAssumption} {p0 p : Part}
    (hgood : a.good p = true)
    (hl : SucceedsIn.{u}
      (if a.good p0 then a.apply p0 else a.apply p) (a.apply p))
    (hr : Successful.{u}
        (if a.good p0 then a.apply p0 else a.apply p) →
      SucceedsIn.{u} p0 (a.complement.apply p)) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_splitGoal_of_arity_ge_five hge
    (fun hgood0 hforce =>
      forcedPart_split_of_forcedPart_of_goodSplit_of_arity_ge_five
        (i := a.loc) (j := a.index) (k := a.cutoff) (lo := a.low)
        hge hgood0 (by simpa [SplitAssumption.good] using hgood) hforce)
    hl hr

theorem succeedsIn_of_exactFitp_cover
    {p0 p pl pr : Part}
    (hcover : ∀ ⦃G : Hypermap.{u}⦄ (x : G.Dart),
      ValidHub G x →
        Part.exactFitp G x p = true →
          Part.exactFitp G x pl = true ∨
            Part.exactFitp G x pr = true)
    (hl : Successful.{u} pl)
    (hr : Successful.{u} pr) :
    SucceedsIn.{u} p0 p := by
  intro _
  exact successful_of_exactFitp_cover hcover hl hr

theorem succeedsIn_of_indexed_split_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    (i : SubpartLoc) (j k : Nat) (lo : Bool)
    {p0 p : Part}
    (hl : Successful.{u} (Part.split i j k lo p))
    (hr : Successful.{u} (Part.split i j k (!lo) p)) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_exactFitp_cover
    (fun {G} x hx hfit =>
      Part.exactFitp_split_or_complement_of_arity_ge_five
        (G := G) (hge G x hx) i j k lo p x hfit)
    hl hr

theorem succeedsIn_of_splitAssumption_successful_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    (a : SplitAssumption) {p0 p : Part}
    (hl : Successful.{u} (a.apply p))
    (hr : Successful.{u} (a.complement.apply p)) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_indexed_split_successful_of_arity_ge_five
    hge a.loc a.index a.cutoff a.low hl hr


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
