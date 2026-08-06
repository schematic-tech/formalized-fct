import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness

/-!
Shared helpers for porting the seven presentation scripts.

These are small wrappers around the semantic lemmas in `PresentationSoundness`.
They keep the proof scripts close to the Coq `presentN.v` structure while
remaining in the lightweight import path.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace PresentationScripts

open Presentation

noncomputable section

universe u

abbrev leAt (loc : SubpartLoc) (idx cutoff : Nat) : SplitAssumption :=
  Presentation.SublocSyntax.le loc idx cutoff

abbrev gtAt (loc : SubpartLoc) (idx cutoff : Nat) : SplitAssumption :=
  Presentation.SublocSyntax.gt loc idx cutoff

abbrev leS (idx cutoff : Nat) : SplitAssumption :=
  leAt SubpartLoc.Pspoke idx cutoff

abbrev gtS (idx cutoff : Nat) : SplitAssumption :=
  gtAt SubpartLoc.Pspoke idx cutoff

abbrev leH (idx cutoff : Nat) : SplitAssumption :=
  leAt SubpartLoc.Phat idx cutoff

abbrev gtH (idx cutoff : Nat) : SplitAssumption :=
  gtAt SubpartLoc.Phat idx cutoff

abbrev leF1 (idx cutoff : Nat) : SplitAssumption :=
  leAt SubpartLoc.Pfan1 idx cutoff

abbrev gtF1 (idx cutoff : Nat) : SplitAssumption :=
  gtAt SubpartLoc.Pfan1 idx cutoff

abbrev leF2 (idx cutoff : Nat) : SplitAssumption :=
  leAt SubpartLoc.Pfan2 idx cutoff

abbrev gtF2 (idx cutoff : Nat) : SplitAssumption :=
  gtAt SubpartLoc.Pfan2 idx cutoff

abbrev leF3 (idx cutoff : Nat) : SplitAssumption :=
  leAt SubpartLoc.Pfan3 idx cutoff

abbrev gtF3 (idx cutoff : Nat) : SplitAssumption :=
  gtAt SubpartLoc.Pfan3 idx cutoff

abbrev hub1 (i : Nat) (b : Int) : Discharge.Hubcap :=
  Presentation.HubcapSyntax.one i b

abbrev hub2 (i j : Nat) (b : Int) : Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b

abbrev hub11 (i : Nat) (b : Int) (j : Nat) (c : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.one i b
    (Presentation.HubcapSyntax.one j c)

abbrev hub12 (i : Nat) (b : Int) (j k : Nat) (c : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.one i b
    (Presentation.HubcapSyntax.two j k c)

abbrev hub21 (i j : Nat) (b : Int) (k : Nat) (c : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b
    (Presentation.HubcapSyntax.one k c)

abbrev hub22 (i j : Nat) (b : Int) (k l : Nat) (c : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b
    (Presentation.HubcapSyntax.two k l c)

abbrev hub111
    (i : Nat) (b : Int) (j : Nat) (c : Int) (k : Nat) (d : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.one i b
    (Presentation.HubcapSyntax.one j c
      (Presentation.HubcapSyntax.one k d))

abbrev hub122
    (i : Nat) (b : Int) (j k : Nat) (c : Int)
    (l m : Nat) (d : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.one i b
    (Presentation.HubcapSyntax.two j k c
      (Presentation.HubcapSyntax.two l m d))

abbrev hub212
    (i j : Nat) (b : Int) (k : Nat) (c : Int)
    (l m : Nat) (d : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b
    (Presentation.HubcapSyntax.one k c
      (Presentation.HubcapSyntax.two l m d))

abbrev hub221
    (i j : Nat) (b : Int) (k l : Nat) (c : Int)
    (m : Nat) (d : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b
    (Presentation.HubcapSyntax.two k l c
      (Presentation.HubcapSyntax.one m d))

abbrev hub222
    (i j : Nat) (b : Int) (k l : Nat) (c : Int)
    (m n : Nat) (d : Int) :
    Discharge.Hubcap :=
  Presentation.HubcapSyntax.two i j b
    (Presentation.HubcapSyntax.two k l c
      (Presentation.HubcapSyntax.two m n d))

theorem arityGeFiveOfPentagonal
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u}) :
    ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y :=
  fun G _x hx y =>
    Hypermap.arity_ge_five_of_pentagonal
      (G := G) (hpentagonal G hx.1) y

theorem pcase
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y)
    (a : SplitAssumption) {p0 p : Part}
    (hgood : a.good p = true)
    (hl : SucceedsIn.{u}
      (if a.good p0 then a.apply p0 else a.apply p) (a.apply p))
    (hr : Successful.{u}
        (if a.good p0 then a.apply p0 else a.apply p) →
      SucceedsIn.{u} p0 (a.complement.apply p)) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_splitGoal_good_of_arity_ge_five hge hgood hl hr

theorem reducibleLeaf
    (hredpart : RedpartSound.{u})
    {p0 p : Part}
    (hcheck : reducibilityCheck { p0 := p0, p := p } = true) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_reducibilityCheck_sound hredpart hcheck

theorem hubcapLeaf
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hc : Discharge.Hubcap) {p0 p : Part}
    (hcheck : hubcapCheck { p0 := p0, p := p } hc = true) :
    SucceedsIn.{u} p0 p :=
  Unavoidability.succeedsIn_of_hubcapCheck_minimalGeometry
    hcubic hpentagonal hredpart hcheck

theorem smallLeaf
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    {p0 p : Part}
    (hsize : p.size < 5) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_pentagonal_size_lt_five
    (fun G _x hx => hpentagonal G hx.1) hsize

theorem rotateGoal
    (n : Nat) {p0 p : Part}
    (h : SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p)) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_rotate n h

theorem rotateGoalForward
    (n : Nat) {p0 p : Part}
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p) :=
  succeedsIn_rotate n h

theorem rotateGoalIff
    (n : Nat) {p0 p : Part} :
    SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_rotate_iff n

theorem mirrorGoal
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (h : SucceedsIn.{u} (Part.mirror p0) (Part.mirror p)) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_mirror hvalid hfitMirror h

theorem mirrorGoalForward
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) :=
  succeedsIn_mirror hvalid hfitMirror h

theorem mirrorGoalIff
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part} :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_mirror_iff hvalid hfitMirror

theorem mirrorGoalUpTo
    (n : Nat)
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (h : SucceedsIn.{u} (Part.mirror p0) (Part.mirror p)) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_mirror_upTo hvalid hfitMirror hsize0 hsize h

theorem mirrorGoalForwardUpTo
    (n : Nat)
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) :=
  succeedsIn_mirror_upTo hvalid hfitMirror hsize0 hsize h

theorem mirrorGoalIffUpTo
    (n : Nat)
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_mirror_iff_upTo hvalid hfitMirror hsize0 hsize

theorem mirrorGoalPentagonalUpToFour
    (hvalid : MirrorValidHubTransport.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    {p0 p : Part}
    (hsize0 : p0.size ≤ 4)
    (hsize : p.size ≤ 4)
    (h : SucceedsIn.{u} (Part.mirror p0) (Part.mirror p)) :
    SucceedsIn.{u} p0 p :=
  mirrorGoalUpTo 4 hvalid
    (mirrorExactFitTransportUpTo_four_of_minimalCounterexample_pentagonal
      (fun G hG => hpentagonal G hG))
    hsize0 hsize h

theorem mirrorGoalIffLocal
    (hscore2 : MirrorDscore2Transport.{u})
    (hfit : MirrorFitTransport.{u})
    {p0 p : Part} :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_mirror_iff
    (mirrorValidHubTransport_of_dscore2_mirror hscore2)
    (mirrorExactFitTransport_of_fit_mirror hfit)

theorem similarLeaf
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (hps : Successful.{u} ps)
    (hcheck : similarityCheck ps p j mir = true) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_similarityCheck_successful_of_validHubTransport
    hvalid hfitMirror hcheck hps

theorem similarLeafUpTo
    (n : Nat)
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (hsize : p.size ≤ n)
    (hps : Successful.{u} ps)
    (hcheck : similarityCheck ps p j mir = true) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_similarityCheck_successful_upTo
    hvalid hfitMirror hsize hcheck hps

theorem similarLeafPentagonalUpToFour
    (hvalid : MirrorValidHubTransport.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (hsize : p.size ≤ 4)
    (hps : Successful.{u} ps)
    (hcheck : similarityCheck ps p j mir = true) :
    SucceedsIn.{u} p0 p :=
  similarLeafUpTo 4 hvalid
    (mirrorExactFitTransportUpTo_four_of_minimalCounterexample_pentagonal
      (fun G hG => hpentagonal G hG))
    hsize hps hcheck

theorem similarLeafLocal
    (hscore2 : MirrorDscore2Transport.{u})
    (hfit : MirrorFitTransport.{u})
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (hps : Successful.{u} ps)
    (hcheck : similarityCheck ps p j mir = true) :
    SucceedsIn.{u} p0 p :=
  similarLeaf
    (mirrorValidHubTransport_of_dscore2_mirror hscore2)
    (mirrorExactFitTransport_of_fit_mirror hfit)
    hps hcheck

end

end PresentationScripts

end FourColor

end Schematic.Math.GraphTheory
