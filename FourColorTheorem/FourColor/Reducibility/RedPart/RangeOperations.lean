import FourColorTheorem.FourColor.Reducibility.RedPart.Zipper

/-! Range fitting and executable operations on zipped parts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open Part
open PRange
open Question
open QArity

namespace RedPart

open ZPartLoc
def topQa : PRange → QArity
  | Pr55 => Qa5
  | Pr56 | Pr66 => Qa6
  | Pr57 | Pr67 | Pr77 => Qa7
  | Pr58 | Pr68 | Pr78 | Pr88 => Qa8
  | _ => Qa9

def fitQa : PRange → QArity → Bool
  | Pr55, Qa5 => true
  | Pr56, Qa6 => true
  | Pr66, Qa6 => true
  | Pr57, Qa7 => true
  | Pr67, Qa7 => true
  | Pr77, Qa7 => true
  | Pr58, Qa8 => true
  | Pr68, Qa8 => true
  | Pr78, Qa8 => true
  | Pr88, Qa8 => true
  | _, _ => false

theorem hubRange_fitQa_eq
    {ahub qa : QArity}
    (hfit : fitQa (hubRange ahub) qa = true) :
    ahub.toNat = qa.toNat := by
  cases ahub <;> cases qa <;>
    simp [hubRange, fitQa, QArity.toNat] at hfit ⊢

theorem fitQa_Pr59_false (qa : QArity) :
    fitQa Pr59 qa = false := by
  cases qa <;> rfl

theorem fitQa_topQa_of_fit
    {r : PRange} {qa : QArity}
    (hfit : fitQa r qa = true) :
    topQa r = qa := by
  cases r <;> cases qa <;> simp [fitQa, topQa] at hfit ⊢

theorem fitQa_topQa
    {r : PRange} {qa : QArity}
    (hfit : fitQa r qa = true) :
    fitQa r (topQa r) = true := by
  cases r <;> cases qa <;> simp [fitQa, topQa] at hfit ⊢

def popQa : PRange → PRange
  | Pr56 => Pr55
  | Pr57 => Pr56
  | Pr58 => Pr57
  | Pr67 => Pr66
  | Pr68 => Pr67
  | Pr78 => Pr77
  | _ => Pr99

theorem fitQa_popQa
    {r : PRange} {qa : QArity} {n : Nat}
    (hfit : fitQa r qa = true)
    (hr : PRange.contains r n = true)
    (hpop : PRange.contains (popQa r) 9 = true ∨
      PRange.contains (popQa r) n = false) :
    n = qa.toNat := by
  cases r <;> cases qa <;>
    simp [fitQa, popQa, PRange.contains, QArity.toNat] at hfit hr hpop ⊢
  all_goals omega

def redPcons (ctx : Context) (pc : PRange → Part → Part)
    (r : PRange) (pr : Part) : Bool :=
  let rpc (r' : PRange) :=
    ctx.redRec (Part.take ctx.nhub (Part.append (pc r' pr) ctx.p0r))
  match r with
  | Pr56 => rpc Pr55
  | Pr57 => rpc Pr56
  | Pr58 => rpc Pr57
  | Pr67 => rpc Pr66
  | Pr68 => rpc Pr67
  | Pr78 => rpc Pr77
  | _ => true

theorem bool_eq_false_of_imp_false_of_true
    {b c : Bool}
    (hc : c = true)
    (h : b = true → c = false) :
    b = false := by
  cases b
  · rfl
  · have hcFalse := h rfl
    rw [hc] at hcFalse
    cases hcFalse

theorem redPcons_popQa_guard
    {ctx : Context} {pc : PRange → Part → Part}
    {r : PRange} {pr : Part} {n : Nat}
    (hred : redPcons ctx pc r pr = true)
    (hnot :
      PRange.contains (popQa r) n = true →
        ctx.redRec
          (Part.take ctx.nhub (Part.append (pc (popQa r) pr) ctx.p0r)) =
          false) :
    PRange.contains (popQa r) 9 = true ∨
      PRange.contains (popQa r) n = false := by
  cases r <;>
    simp [redPcons, popQa] at hred hnot ⊢
  all_goals
    first
    | exact Or.inr (bool_eq_false_of_imp_false_of_true hred hnot)
    | exact Or.inl (by simp [PRange.contains])

universe u

theorem redPcons_not_rec_of_exactFit
    {G : Hypermap.{u}} {ctx : Context} {pc : PRange → Part → Part}
    {r : PRange} {pr : Part} {y : G.Dart} {n : Nat}
    (hNoRedRec : NoRedRec G ctx)
    (hy : G.arity y = ctx.nhub)
    (hexact :
      PRange.contains (popQa r) n = true →
        Part.exactFitp G y
          (Part.take ctx.nhub
            (Part.append (pc (popQa r) pr) ctx.p0r)) = true) :
    PRange.contains (popQa r) n = true →
      ctx.redRec
        (Part.take ctx.nhub
          (Part.append (pc (popQa r) pr) ctx.p0r)) = false := by
  intro hcontains
  exact hNoRedRec y _ hy (hexact hcontains)

theorem redPcons_fit_of_update_guard
    {G : Hypermap.{u}} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {qa : QArity}
    {x : G.Dart}
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G x (pc r pr) = true)
    (hfit : fitQa r qa = true)
    (hguard :
      PRange.contains (popQa r) 9 = true ∨
        PRange.contains (popQa r)
          (G.arity (SubpartLoc.move j G x)) = false) :
    G.arity (SubpartLoc.move j G x) = qa.toNat := by
  have hrange :
      PRange.contains r (G.arity (SubpartLoc.move j G x)) = true :=
    ((hupdate r pr).2 G x hfitpc).1
  exact fitQa_popQa hfit hrange hguard

theorem fitp_popped_of_update
    {G : Hypermap.{u}} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {x : G.Dart}
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G x (pc r pr) = true)
    (hcontains :
      PRange.contains (popQa r)
        (G.arity (SubpartLoc.move j G x)) = true) :
    Part.fitp G x (pc (popQa r) pr) = true :=
  ((hupdate r pr).2 G x hfitpc).2 (popQa r) hcontains

theorem redPcons_fit_of_update_not_rec
    {G : Hypermap.{u}} {ctx : Context} {pc : PRange → Part → Part}
    {j : SubpartLoc} {r : PRange} {pr : Part} {qa : QArity}
    {x : G.Dart}
    (hupdate : Part.PartUpdate.{u} pc j)
    (hfitpc : Part.fitp G x (pc r pr) = true)
    (hfit : fitQa r qa = true)
    (hred : redPcons ctx pc r pr = true)
    (hnot :
      PRange.contains (popQa r) (G.arity (SubpartLoc.move j G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub (Part.append (pc (popQa r) pr) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move j G x) = qa.toNat := by
  exact redPcons_fit_of_update_guard
    (G := G) (pc := pc) (j := j) (r := r) (pr := pr)
    (qa := qa) (x := x) hupdate hfitpc hfit
    (redPcons_popQa_guard (ctx := ctx) (pc := pc) (r := r) (pr := pr)
      (n := G.arity (SubpartLoc.move j G x)) hred hnot)

theorem redPcons_fit_updatePs
    {G : Hypermap.{u}} {ctx : Context}
    {s h : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons s h p) = true)
    (hfit : fitQa s qa = true)
    (hred : redPcons ctx (fun r p' => Pcons r h p') s p = true)
    (hnot :
      PRange.contains (popQa s)
          (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons (popQa s) h p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Pspoke G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons r h p')
    (j := SubpartLoc.Pspoke) (r := s) (pr := p) (qa := qa) (x := x)
    (Part.updatePs h) hfitpc hfit hred hnot

theorem redPcons_fit_updatePh
    {G : Hypermap.{u}} {ctx : Context}
    {s h : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons s h p) = true)
    (hfit : fitQa h qa = true)
    (hred : redPcons ctx (fun r p' => Pcons s r p') h p = true)
    (hnot :
      PRange.contains (popQa h)
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons s (popQa h) p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons s r p')
    (j := SubpartLoc.Phat) (r := h) (pr := p) (qa := qa) (x := x)
    (Part.updatePh s) hfitpc hfit hred hnot

theorem redPcons_fit_updateP6h
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons6 h f1 p) = true)
    (hfit : fitQa h qa = true)
    (hred : redPcons ctx (fun r p' => Pcons6 r f1 p') h p = true)
    (hnot :
      PRange.contains (popQa h)
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons6 (popQa h) f1 p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons6 r f1 p')
    (j := SubpartLoc.Phat) (r := h) (pr := p) (qa := qa) (x := x)
    (Part.updateP6h f1) hfitpc hfit hred hnot

theorem redPcons_fit_updateP6f1
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons6 h f1 p) = true)
    (hfit : fitQa f1 qa = true)
    (hred : redPcons ctx (fun r p' => Pcons6 h r p') f1 p = true)
    (hnot :
      PRange.contains (popQa f1)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons6 h (popQa f1) p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons6 h r p')
    (j := SubpartLoc.Pfan1) (r := f1) (pr := p) (qa := qa) (x := x)
    (Part.updateP6f1 h) hfitpc hfit hred hnot

theorem redPcons_fit_updateP7h
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons7 h f1 f2 p) = true)
    (hfit : fitQa h qa = true)
    (hred : redPcons ctx (fun r p' => Pcons7 r f1 f2 p') h p = true)
    (hnot :
      PRange.contains (popQa h)
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons7 (popQa h) f1 f2 p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons7 r f1 f2 p')
    (j := SubpartLoc.Phat) (r := h) (pr := p) (qa := qa) (x := x)
    (Part.updateP7h f1 f2) hfitpc hfit hred hnot

theorem redPcons_fit_updateP7f1
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons7 h f1 f2 p) = true)
    (hfit : fitQa f1 qa = true)
    (hred : redPcons ctx (fun r p' => Pcons7 h r f2 p') f1 p = true)
    (hnot :
      PRange.contains (popQa f1)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons7 h (popQa f1) f2 p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons7 h r f2 p')
    (j := SubpartLoc.Pfan1) (r := f1) (pr := p) (qa := qa) (x := x)
    (Part.updateP7f1 h f2) hfitpc hfit hred hnot

theorem redPcons_fit_updateP7f2
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons7 h f1 f2 p) = true)
    (hfit : fitQa f2 qa = true)
    (hred : redPcons ctx (fun r p' => Pcons7 h f1 r p') f2 p = true)
    (hnot :
      PRange.contains (popQa f2)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons7 h f1 (popQa f2) p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons7 h f1 r p')
    (j := SubpartLoc.Pfan2) (r := f2) (pr := p) (qa := qa) (x := x)
    (Part.updateP7f2 h f1) hfitpc hfit hred hnot

theorem redPcons_fit_updateP8h
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 f3 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons8 h f1 f2 f3 p) = true)
    (hfit : fitQa h qa = true)
    (hred :
      redPcons ctx (fun r p' => Pcons8 r f1 f2 f3 p') h p = true)
    (hnot :
      PRange.contains (popQa h)
          (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons8 (popQa h) f1 f2 f3 p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons8 r f1 f2 f3 p')
    (j := SubpartLoc.Phat) (r := h) (pr := p) (qa := qa) (x := x)
    (Part.updateP8h f1 f2 f3) hfitpc hfit hred hnot

theorem redPcons_fit_updateP8f1
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 f3 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons8 h f1 f2 f3 p) = true)
    (hfit : fitQa f1 qa = true)
    (hred :
      redPcons ctx (fun r p' => Pcons8 h r f2 f3 p') f1 p = true)
    (hnot :
      PRange.contains (popQa f1)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons8 h (popQa f1) f2 f3 p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan1 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons8 h r f2 f3 p')
    (j := SubpartLoc.Pfan1) (r := f1) (pr := p) (qa := qa) (x := x)
    (Part.updateP8f1 h f2 f3) hfitpc hfit hred hnot

theorem redPcons_fit_updateP8f2
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 f3 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons8 h f1 f2 f3 p) = true)
    (hfit : fitQa f2 qa = true)
    (hred :
      redPcons ctx (fun r p' => Pcons8 h f1 r f3 p') f2 p = true)
    (hnot :
      PRange.contains (popQa f2)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons8 h f1 (popQa f2) f3 p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan2 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons8 h f1 r f3 p')
    (j := SubpartLoc.Pfan2) (r := f2) (pr := p) (qa := qa) (x := x)
    (Part.updateP8f2 h f1 f3) hfitpc hfit hred hnot

theorem redPcons_fit_updateP8f3
    {G : Hypermap.{u}} {ctx : Context}
    {h f1 f2 f3 : PRange} {p : Part} {qa : QArity} {x : G.Dart}
    (hfitpc : Part.fitp G x (Pcons8 h f1 f2 f3 p) = true)
    (hfit : fitQa f3 qa = true)
    (hred :
      redPcons ctx (fun r p' => Pcons8 h f1 f2 r p') f3 p = true)
    (hnot :
      PRange.contains (popQa f3)
          (G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x)) = true →
        ctx.redRec
          (Part.take ctx.nhub
            (Part.append (Pcons8 h f1 f2 (popQa f3) p) ctx.p0r)) =
          false) :
    G.arity (SubpartLoc.move SubpartLoc.Pfan3 G x) = qa.toNat :=
  redPcons_fit_of_update_not_rec
    (G := G) (ctx := ctx) (pc := fun r p' => Pcons8 h f1 f2 r p')
    (j := SubpartLoc.Pfan3) (r := f3) (pr := p) (qa := qa) (x := x)
    (Part.updateP8f3 h f1 f2) hfitpc hfit hred hnot

def redPoprSpoke (ctx : Context) : Part → Bool
  | Pcons s h p => redPcons ctx (fun r p' => Pcons r h p') s p
  | _ => true

theorem redPoprSpoke_fit_of_fitp
    {G : Hypermap.{u}} {ctx : Context} {pr : Part} {qa : QArity}
    {x : G.Dart}
    (hfitpr : Part.fitp G x pr = true)
    (hfit : fitQa (Part.getSpoke pr) qa = true)
    (hred : redPoprSpoke ctx pr = true)
    (hnot :
      ∀ {s h : PRange} {p : Part},
        pr = Pcons s h p →
          PRange.contains (popQa s)
              (G.arity (SubpartLoc.move SubpartLoc.Pspoke G x)) = true →
            ctx.redRec
              (Part.take ctx.nhub
                (Part.append (Pcons (popQa s) h p) ctx.p0r)) = false) :
    G.arity (SubpartLoc.move SubpartLoc.Pspoke G x) = qa.toNat := by
  cases pr with
  | Pcons s h p =>
      exact redPcons_fit_updatePs
        (G := G) (ctx := ctx) (s := s) (h := h) (p := p)
        (qa := qa) (x := x) hfitpr hfit
        (by simpa [redPoprSpoke] using hred) (hnot rfl)
  | Pnil =>
      simp [Part.getSpoke, fitQa] at hfit
  | Pcons6 h f1 p =>
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega
  | Pcons7 h f1 f2 p =>
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega
  | Pcons8 h f1 f2 f3 p =>
      cases qa <;>
        simp [Part.getSpoke, fitQa, Part.fitp, PRange.contains,
          QArity.toNat] at hfit hfitpr ⊢
      omega

def redPoprHat (ctx : Context) : Part → Bool
  | Pcons s h p => redPcons ctx (fun r p' => Pcons s r p') h p
  | Pcons6 h f1 p => redPcons ctx (fun r p' => Pcons6 r f1 p') h p
  | Pcons7 h f1 f2 p => redPcons ctx (fun r p' => Pcons7 r f1 f2 p') h p
  | Pcons8 h f1 f2 f3 p => redPcons ctx (fun r p' => Pcons8 r f1 f2 f3 p') h p
  | _ => true

theorem redPoprHat_fit_of_fitp
    {G : Hypermap.{u}} {ctx : Context} {pr : Part} {qa : QArity}
    {x : G.Dart}
    (hfitpr : Part.fitp G x pr = true)
    (hfit : fitQa (Part.getHat pr) qa = true)
    (hred : redPoprHat ctx pr = true)
    (hnotCons :
      ∀ {s h : PRange} {p : Part},
        pr = Pcons s h p →
          PRange.contains (popQa h)
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
            ctx.redRec
              (Part.take ctx.nhub
                (Part.append (Pcons s (popQa h) p) ctx.p0r)) = false)
    (hnot6 :
      ∀ {h f1 : PRange} {p : Part},
        pr = Pcons6 h f1 p →
          PRange.contains (popQa h)
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
            ctx.redRec
              (Part.take ctx.nhub
                (Part.append (Pcons6 (popQa h) f1 p) ctx.p0r)) = false)
    (hnot7 :
      ∀ {h f1 f2 : PRange} {p : Part},
        pr = Pcons7 h f1 f2 p →
          PRange.contains (popQa h)
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
            ctx.redRec
              (Part.take ctx.nhub
                (Part.append (Pcons7 (popQa h) f1 f2 p) ctx.p0r)) =
              false)
    (hnot8 :
      ∀ {h f1 f2 f3 : PRange} {p : Part},
        pr = Pcons8 h f1 f2 f3 p →
          PRange.contains (popQa h)
              (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true →
            ctx.redRec
              (Part.take ctx.nhub
                (Part.append (Pcons8 (popQa h) f1 f2 f3 p) ctx.p0r)) =
              false) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G x) = qa.toNat := by
  cases pr with
  | Pnil =>
      simp [Part.getHat, Part.nextHat, fitQa] at hfit
  | Pcons s h p =>
      exact redPcons_fit_updatePh
        (G := G) (ctx := ctx) (s := s) (h := h) (p := p)
        (qa := qa) (x := x) hfitpr hfit
        (by simpa [redPoprHat] using hred) (hnotCons rfl)
  | Pcons6 h f1 p =>
      exact redPcons_fit_updateP6h
        (G := G) (ctx := ctx) (h := h) (f1 := f1) (p := p)
        (qa := qa) (x := x) hfitpr hfit
        (by simpa [redPoprHat] using hred) (hnot6 rfl)
  | Pcons7 h f1 f2 p =>
      exact redPcons_fit_updateP7h
        (G := G) (ctx := ctx) (h := h) (f1 := f1) (f2 := f2) (p := p)
        (qa := qa) (x := x) hfitpr hfit
        (by simpa [redPoprHat] using hred) (hnot7 rfl)
  | Pcons8 h f1 f2 f3 p =>
      exact redPcons_fit_updateP8h
        (G := G) (ctx := ctx) (h := h) (f1 := f1) (f2 := f2) (f3 := f3)
        (p := p) (qa := qa) (x := x) hfitpr hfit
        (by simpa [redPoprHat] using hred) (hnot8 rfl)

def redPoplSpoke (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons s h _ => redPcons ctx (fun r p' => Pcons r h p') s pr
  | _ => true

def redPoplHat (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons s h _ => redPcons ctx (fun r p' => Pcons s r p') h pr
  | Pcons6 h f1 _ => redPcons ctx (fun r p' => Pcons6 r f1 p') h pr
  | Pcons7 h f1 f2 _ => redPcons ctx (fun r p' => Pcons7 r f1 f2 p') h pr
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 r f1 f2 f3 p') h pr
  | _ => true

def redPoplFan1l (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons6 h f1 _ => redPcons ctx (fun r p' => Pcons6 h r p') f1 pr
  | Pcons7 h f1 f2 _ => redPcons ctx (fun r p' => Pcons7 h f1 r p') f2 pr
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h f1 f2 r p') f3 pr
  | _ => true

def redPoplFan2l (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons7 h f1 f2 _ => redPcons ctx (fun r p' => Pcons7 h r f2 p') f1 pr
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h f1 r f3 p') f2 pr
  | _ => true

def redPoplFan3l (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h r f2 f3 p') f1 pr
  | _ => true

def redPoplFan1r (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons6 h f1 _ => redPcons ctx (fun r p' => Pcons6 h r p') f1 pr
  | Pcons7 h f1 f2 _ => redPcons ctx (fun r p' => Pcons7 h r f2 p') f1 pr
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h r f2 f3 p') f1 pr
  | _ => true

def redPoplFan2r (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons7 h f1 f2 _ => redPcons ctx (fun r p' => Pcons7 h f1 r p') f2 pr
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h f1 r f3 p') f2 pr
  | _ => true

def redPoplFan3r (ctx : Context) (pl pr : Part) : Bool :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => redPcons ctx (fun r p' => Pcons8 h f1 f2 r p') f3 pr
  | _ => true

def redPop (ctx : Context) (zp : ZPart) : Bool :=
  match zp with
  | ⟨Zhubl, pl, pr⟩ => redPoplSpoke ctx pl pr
  | ⟨Zhubr, _, pr⟩ => redPoprSpoke ctx pr
  | ⟨Zhatl, pl, pr⟩ => redPoplSpoke ctx pl pr
  | ⟨Zhat, _, pr⟩ => redPoprHat ctx pr
  | ⟨Zhatr, _, pr⟩ => redPoprSpoke ctx pr
  | ⟨Zfan0l, _, pr⟩ => redPoprHat ctx pr
  | ⟨Zfan1l, pl, pr⟩ => redPoplFan1l ctx pl pr
  | ⟨Zfan2l, pl, pr⟩ => redPoplFan2l ctx pl pr
  | ⟨Zfan3l, pl, pr⟩ => redPoplFan3l ctx pl pr
  | ⟨Zfan0r, pl, pr⟩ => redPoplHat ctx pl pr
  | ⟨Zfan1r, pl, pr⟩ => redPoplFan1r ctx pl pr
  | ⟨Zfan2r, pl, pr⟩ => redPoplFan2r ctx pl pr
  | ⟨Zfan3r, pl, pr⟩ => redPoplFan3r ctx pl pr
  | _ => true

def fitQZP (ctx : Context) (zp : ZPart) : Question → Bool
  | Qask0 => true
  | Qask1 qa => fitQa (zrange ctx zp) qa
  | QaskL qa ql =>
      if fitQa (zrange ctx zp) qa then
        fitQZP ctx (zstepLt ctx zp) ql
      else
        false
  | QaskR qa qr =>
      if fitQa (zrange ctx zp) qa then
        fitQZP ctx (zstepRt ctx zp) qr
      else
        false
  | QaskLR qa ql qr =>
      if fitQa (zrange ctx zp) qa then
        fitQZP ctx (zstepL ctx zp) ql && fitQZP ctx (zstepR ctx zp) qr
      else
        false
  | QaskLL qa ql =>
      let zpl := zstepL ctx zp
      if fitQa (zrange ctx zpl) qa then
        fitQZP ctx (zstepL ctx zpl) ql
      else
        false
  | QaskRR qa qr =>
      let zpr := zstepR ctx zp
      if fitQa (zrange ctx zpr) qa then
        fitQZP ctx (zstepR ctx zpr) qr
      else
        false

theorem proper_of_fitQa_zrange
    {ctx : Context} {zp : ZPart} {qa : QArity}
    (hfit : fitQa (zrange ctx zp) qa = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;> cases qa <;>
    simp [ZPart.proper, zrange, fitQa] at hfit ⊢

theorem proper_of_fitQa_zrange_zstepL
    {ctx : Context} {zp : ZPart} {qa : QArity}
    (hfit : fitQa (zrange ctx (zstepL ctx zp)) qa = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;> simp [ZPart.proper]
  cases pl <;> cases pr <;> cases qa <;>
    simp [zstepL, zrange, fitQa, mkZ] at hfit

theorem proper_of_fitQa_zrange_zstepR
    {ctx : Context} {zp : ZPart} {qa : QArity}
    (hfit : fitQa (zrange ctx (zstepR ctx zp)) qa = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;> simp [ZPart.proper]
  cases pl <;> cases pr <;> cases qa <;>
    simp [zstepR, zrange, fitQa, mkZ] at hfit

theorem fitQZP_proper
    {ctx : Context} {zp : ZPart} :
    ∀ {q : Question}, fitQZP ctx zp q = true → q = Qask0 ∨ zp.proper = true
  | Qask0, _ => Or.inl rfl
  | Qask1 qa, hfit => Or.inr (proper_of_fitQa_zrange (ctx := ctx) hfit)
  | QaskL qa _ql, hfit => by
      simp [fitQZP] at hfit
      exact Or.inr (proper_of_fitQa_zrange (ctx := ctx) hfit.1)
  | QaskR qa _qr, hfit => by
      simp [fitQZP] at hfit
      exact Or.inr (proper_of_fitQa_zrange (ctx := ctx) hfit.1)
  | QaskLR qa _ql _qr, hfit => by
      simp [fitQZP] at hfit
      exact Or.inr (proper_of_fitQa_zrange (ctx := ctx) hfit.1)
  | QaskLL qa _ql, hfit => by
      simp [fitQZP] at hfit
      exact Or.inr (proper_of_fitQa_zrange_zstepL (ctx := ctx) hfit.1)
  | QaskRR qa _qr, hfit => by
      simp [fitQZP] at hfit
      exact Or.inr (proper_of_fitQa_zrange_zstepR (ctx := ctx) hfit.1)

theorem proper_of_fitQZP_of_ne_qask0
    {ctx : Context} {zp : ZPart} {q : Question}
    (hfit : fitQZP ctx zp q = true)
    (hne : q ≠ Qask0) :
    zp.proper = true := by
  rcases fitQZP_proper (ctx := ctx) (zp := zp) hfit with hq | hproper
  · exact False.elim (hne hq)
  · exact hproper

def redPopQZP (ctx : Context) (zp : ZPart) : Question → Bool
  | Qask0 => true
  | Qask1 _ => redPop ctx zp
  | QaskL _ ql => redPop ctx zp && redPopQZP ctx (zstepLt ctx zp) ql
  | QaskR _ qr => redPop ctx zp && redPopQZP ctx (zstepRt ctx zp) qr
  | QaskLR _ ql qr =>
      redPop ctx zp &&
        redPopQZP ctx (zstepL ctx zp) ql &&
          redPopQZP ctx (zstepR ctx zp) qr
  | QaskLL _ ql =>
      let zpl := zstepL ctx zp
      redPop ctx zpl && redPopQZP ctx (zstepL ctx zpl) ql
  | QaskRR _ qr =>
      let zpr := zstepR ctx zp
      redPop ctx zpr && redPopQZP ctx (zstepR ctx zpr) qr


end RedPart

end FourColor

end Schematic.Math.GraphTheory
