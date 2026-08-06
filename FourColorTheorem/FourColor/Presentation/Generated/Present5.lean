import FourColorTheorem.FourColor.Presentation.ScriptCombinators

/-!
Arity-5 presentation script.

This ports the shape of Coq `present5.v` into the lightweight Lean
presentation layer.  The executable leaf checks are discharged by computation;
the theorem remains parameterized by the semantic redpart and mirror bridges
that are still being connected below the full four-colour theorem.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace PresentationScripts

open Presentation

noncomputable section

universe u

private abbrev hc_0_m6_m4 : Discharge.Hubcap :=
  hub221 1 2 0 3 4 (-6) 5 (-4)

private abbrev hc_0_m7_m3 : Discharge.Hubcap :=
  hub221 1 2 0 3 4 (-7) 5 (-3)

private abbrev hc_0_m5_m5 : Discharge.Hubcap :=
  hub221 1 2 0 3 4 (-5) 5 (-5)

private abbrev hc_m4_m2_m4 : Discharge.Hubcap :=
  hub221 1 2 (-4) 3 4 (-2) 5 (-4)

private abbrev hc_m4_m3_m3 : Discharge.Hubcap :=
  hub221 1 2 (-4) 3 4 (-3) 5 (-3)

private abbrev hc_m3_m4_m3 : Discharge.Hubcap :=
  hub221 1 2 (-3) 3 4 (-4) 5 (-3)

private abbrev hc_m3_m5_m2 : Discharge.Hubcap :=
  hub221 1 2 (-3) 3 4 (-5) 5 (-2)

private abbrev hc_m2_m6_m2 : Discharge.Hubcap :=
  hub221 1 2 (-2) 3 4 (-6) 5 (-2)

private abbrev hc_m4_m4_m2 : Discharge.Hubcap :=
  hub221 1 2 (-4) 3 4 (-4) 5 (-2)

theorem present5UpTo
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} 5) :
    SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5) := by
  let hge := arityGeFiveOfPentagonal hpentagonal
  refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
  · refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    · refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      · refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        · exact reducibleLeaf hredpart (by fct_decide)
        · intro _
          refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          · exact reducibleLeaf hredpart (by fct_decide)
          · intro _
            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            · exact hubcapLeaf hcubic hpentagonal hredpart
                hc_0_m6_m4 (by fct_decide)
            · intro _
              refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              · exact hubcapLeaf hcubic hpentagonal hredpart
                  hc_0_m7_m3 (by fct_decide)
              · intro _
                exact reducibleLeaf hredpart (by fct_decide)
      · intro L2_1
        refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        · exact similarLeafUpTo 5 hvalid hfitMirror
            (by fct_decide)
            (j := 3) (mir := true) L2_1 (by fct_decide)
        · intro _
          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          · exact hubcapLeaf hcubic hpentagonal hredpart
              hc_0_m6_m4 (by fct_decide)
          · intro _
            exact hubcapLeaf hcubic hpentagonal hredpart
              hc_0_m5_m5 (by fct_decide)
    · intro L1_1
      refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      · exact similarLeafUpTo 5 hvalid hfitMirror
          (by fct_decide)
          (j := 4) (mir := false) L1_1 (by fct_decide)
      · intro _
        refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        · refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          · exact reducibleLeaf hredpart (by fct_decide)
          · intro _
            refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            · exact similarLeafUpTo 5 hvalid hfitMirror
                (by fct_decide)
                (j := 2) (mir := false) L1_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              · refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                · exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    hc_m4_m2_m4 (by fct_decide)
              · intro L2_1
                refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                · exact similarLeafUpTo 5 hvalid hfitMirror
                    (by fct_decide)
                    (j := 2) (mir := true) L2_1 (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    hc_m4_m3_m3 (by fct_decide)
        · intro L1_2
          refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          · exact similarLeafUpTo 5 hvalid hfitMirror
              (by fct_decide)
              (j := 4) (mir := true) L1_2 (by fct_decide)
          · intro _
            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            · refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              · exact hubcapLeaf hcubic hpentagonal hredpart
                  hc_m3_m4_m3 (by fct_decide)
              · intro _
                exact hubcapLeaf hcubic hpentagonal hredpart
                  hc_m3_m5_m2 (by fct_decide)
            · intro L1_3
              refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              · exact similarLeafUpTo 5 hvalid hfitMirror
                  (by fct_decide)
                  (j := 4) (mir := true) L1_3 (by fct_decide)
              · intro _
                exact hubcapLeaf hcubic hpentagonal hredpart
                  hc_m2_m6_m2 (by fct_decide)
  · intro L0_1
    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    · exact similarLeafUpTo 5 hvalid hfitMirror
        (by fct_decide)
        (j := 1) (mir := false) L0_1 (by fct_decide)
    · intro _
      refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      · exact similarLeafUpTo 5 hvalid hfitMirror
          (by fct_decide)
          (j := 2) (mir := false) L0_1 (by fct_decide)
      · intro _
        refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        · exact similarLeafUpTo 5 hvalid hfitMirror
            (by fct_decide)
            (j := 3) (mir := false) L0_1 (by fct_decide)
        · intro _
          refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          · exact similarLeafUpTo 5 hvalid hfitMirror
              (by fct_decide)
              (j := 4) (mir := false) L0_1 (by fct_decide)
          · intro _
            exact hubcapLeaf hcubic hpentagonal hredpart
              hc_m4_m4_m2 (by fct_decide)

theorem present5
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u}) :
    SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5) :=
  present5UpTo hcubic hpentagonal hredpart hvalid
    (mirrorExactFitTransportUpTo_of_mirrorExactFitTransport hfitMirror)

end

end PresentationScripts

end FourColor

end Schematic.Math.GraphTheory
