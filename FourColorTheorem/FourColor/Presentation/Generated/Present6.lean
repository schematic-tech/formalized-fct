import FourColorTheorem.FourColor.Presentation.ScriptCombinators

/-!
Arity-6 presentation script, mechanically ported from Coq `present6.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace PresentationScripts

open Presentation

noncomputable section

universe u

set_option maxHeartbeats 10000000 in
theorem present6UpTo
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} 6) :
    SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6) := by
  let hge := arityGeFiveOfPentagonal hpentagonal
  refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
  ·
    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    ·
      refine pcase hge (gtS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
          · intro _
            refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (-3 : Int) (Presentation.HubcapSyntax.two 4 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
        · intro _
          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact hubcapLeaf hcubic hpentagonal hredpart
                  (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro _
                exact hubcapLeaf hcubic hpentagonal hredpart
                  (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (2 : Int) (Presentation.HubcapSyntax.two 4 6 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro _
                refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
          · intro L3_1
            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 3) (mir := true) L3_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.two 2 3 (-1 : Int) (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro _
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro L3_2
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 6 hvalid hfitMirror
                    (by fct_decide)
                    (j := 3) (mir := true) L3_2 (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro L4_1
                      refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact similarLeafUpTo 6 hvalid hfitMirror
                          (by fct_decide)
                          (j := 3) (mir := true) L4_1 (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 2 3 (-1 : Int) (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 2 (-2 : Int) (Presentation.HubcapSyntax.two 3 5 (2 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (-2 : Int) (Presentation.HubcapSyntax.two 3 5 (2 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
      · intro _
        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
          · intro _
            refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-3 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              exact hubcapLeaf hcubic hpentagonal hredpart
                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-4 : Int) (Presentation.HubcapSyntax.two 4 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
        · intro _
          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact hubcapLeaf hcubic hpentagonal hredpart
                  (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro _
                exact hubcapLeaf hcubic hpentagonal hredpart
                  (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
            · intro _
              refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro _
                refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                · intro _
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
          · intro L3_1
            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 3) (mir := true) L3_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro _
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.two 2 3 (1 : Int) (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro L3_2
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 6 hvalid hfitMirror
                    (by fct_decide)
                    (j := 3) (mir := true) L3_2 (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro L4_1
                      refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact similarLeafUpTo 6 hvalid hfitMirror
                          (by fct_decide)
                          (j := 3) (mir := true) L4_1 (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
    · intro L1_1
      refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        exact similarLeafUpTo 6 hvalid hfitMirror
          (by fct_decide)
          (j := 4) (mir := false) L1_1 (by fct_decide)
      · intro _
        refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 6 hvalid hfitMirror
              (by fct_decide)
              (j := 1) (mir := false) L1_1 (by fct_decide)
          · intro _
            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 3) (mir := false) L1_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (-3 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (-2 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (-4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (-3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro L4_1
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 6 hvalid hfitMirror
                        (by fct_decide)
                        (j := 2) (mir := true) L4_1 (by fct_decide)
                    · intro _
                      refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 5 (-3 : Int) (Presentation.HubcapSyntax.two 4 6 (-3 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 3 (-4 : Int) (Presentation.HubcapSyntax.two 2 4 (-2 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (-2 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro _
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-4 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 5 (-3 : Int) (Presentation.HubcapSyntax.two 4 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro L2_1
                refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 6 hvalid hfitMirror
                    (by fct_decide)
                    (j := 2) (mir := true) L2_1 (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 6 hvalid hfitMirror
                      (by fct_decide)
                      (j := 3) (mir := false) L2_1 (by fct_decide)
                  · intro _
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 6 hvalid hfitMirror
                        (by fct_decide)
                        (j := 5) (mir := true) L2_1 (by fct_decide)
                    · intro _
                      refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro L3_1
                            refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 6 hvalid hfitMirror
                                (by fct_decide)
                                (j := 2) (mir := true) L3_1 (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro L2_2
                            refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 6 hvalid hfitMirror
                                (by fct_decide)
                                (j := 2) (mir := true) L2_2 (by fct_decide)
                            · intro _
                              refine pcase hge (gtF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro L2_3
                                refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 6 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 2) (mir := true) L2_3 (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro L2_4
                                    refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 6 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 2) (mir := true) L2_4 (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
        · intro _
          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 5) (mir := false) L1_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact reducibleLeaf hredpart (by fct_decide)
                  · intro _
                    refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 1 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 1 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro L2_1
                refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 6 hvalid hfitMirror
                    (by fct_decide)
                    (j := 4) (mir := true) L2_1 (by fct_decide)
                · intro _
                  refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.two 1 2 (-2 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 4 2 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 1 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro L2_2
                    refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 6 hvalid hfitMirror
                        (by fct_decide)
                        (j := 4) (mir := true) L2_2 (by fct_decide)
                    · intro _
                      refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro L2_3
                        refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact similarLeafUpTo 6 hvalid hfitMirror
                            (by fct_decide)
                            (j := 4) (mir := true) L2_3 (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro L2_4
                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 6 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 4) (mir := true) L2_4 (by fct_decide)
                              · intro _
                                refine pcase hge (gtF1 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro L2_5
                                  refine pcase hge (gtF1 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := true) L2_5 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
          · intro L1_2
            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 5) (mir := true) L1_2 (by fct_decide)
            · intro _
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact reducibleLeaf hredpart (by fct_decide)
                  · intro _
                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact reducibleLeaf hredpart (by fct_decide)
                    · intro _
                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact reducibleLeaf hredpart (by fct_decide)
                      · intro _
                        refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
              · intro L1_3
                refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 6 hvalid hfitMirror
                    (by fct_decide)
                    (j := 5) (mir := true) L1_3 (by fct_decide)
                · intro _
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact reducibleLeaf hredpart (by fct_decide)
                    · intro _
                      refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 3 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                  · intro L1_4
                    refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 6 hvalid hfitMirror
                        (by fct_decide)
                        (j := 5) (mir := true) L1_4 (by fct_decide)
                    · intro _
                      refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 2 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro _
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                      · intro _
                        refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro _
                              refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                        · intro L1_5
                          refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact similarLeafUpTo 6 hvalid hfitMirror
                              (by fct_decide)
                              (j := 5) (mir := true) L1_5 (by fct_decide)
                          · intro _
                            refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (-1 : Int) (Presentation.HubcapSyntax.two 4 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-3 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (1 : Int) (Presentation.HubcapSyntax.two 4 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro L1_6
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 6 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 5) (mir := true) L1_6 (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 5 (0 : Int) (Presentation.HubcapSyntax.two 2 3 (0 : Int) (Presentation.HubcapSyntax.two 4 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro L3_1
                                      refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 6 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 5) (mir := true) L3_1 (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro L1_7
                                  refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 5) (mir := true) L1_7 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 5 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro L1_8
                                      refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 6 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 5) (mir := true) L1_8 (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 5 6 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
  · intro L0_1
    refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    ·
      exact similarLeafUpTo 6 hvalid hfitMirror
        (by fct_decide)
        (j := 1) (mir := false) L0_1 (by fct_decide)
    · intro _
      refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        exact similarLeafUpTo 6 hvalid hfitMirror
          (by fct_decide)
          (j := 2) (mir := false) L0_1 (by fct_decide)
      · intro _
        refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          exact similarLeafUpTo 6 hvalid hfitMirror
            (by fct_decide)
            (j := 3) (mir := false) L0_1 (by fct_decide)
        · intro _
          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 6 hvalid hfitMirror
              (by fct_decide)
              (j := 4) (mir := false) L0_1 (by fct_decide)
          · intro _
            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 6 hvalid hfitMirror
                (by fct_decide)
                (j := 5) (mir := false) L0_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact reducibleLeaf hredpart (by fct_decide)
              · intro _
                refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact reducibleLeaf hredpart (by fct_decide)
                  · intro _
                    refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact reducibleLeaf hredpart (by fct_decide)
                    · intro _
                      refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact reducibleLeaf hredpart (by fct_decide)
                      · intro _
                        refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact reducibleLeaf hredpart (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 6 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (-2 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 6 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro L3_1
                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 0) (mir := true) L3_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (2 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (2 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 6 (2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 6 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro L3_2
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 6 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 0) (mir := true) L3_2 (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro L3_3
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 6 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 0) (mir := true) L3_3 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (2 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro L3_4
                                              refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 6 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 0) (mir := true) L3_4 (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-2 : Int) (Presentation.HubcapSyntax.two 4 5 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-3 : Int) (Presentation.HubcapSyntax.two 2 6 (1 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (1 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (1 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (1 : Int) (Presentation.HubcapSyntax.two 4 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-2 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro L2_1
                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := true) L2_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (-2 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (1 : Int) (Presentation.HubcapSyntax.two 2 6 (-2 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 3 (1 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro L2_2
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 6 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 4) (mir := true) L2_2 (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-2 : Int) (Presentation.HubcapSyntax.two 4 5 (3 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro L2_3
                                          refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 6 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 4) (mir := true) L2_3 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (-1 : Int) (Presentation.HubcapSyntax.two 2 6 (-1 : Int) (Presentation.HubcapSyntax.two 4 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 3 (0 : Int) (Presentation.HubcapSyntax.two 2 6 (0 : Int) (Presentation.HubcapSyntax.two 4 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                            · intro L1_1
                              refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 6 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 4) (mir := false) L1_1 (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 1) (mir := false) L1_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 6 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 5) (mir := false) L1_1 (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-2 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 5 (-1 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.two 4 6 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro L3_1
                                        refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 6 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 5) (mir := true) L3_1 (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (2 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                          · intro L3_2
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 6 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 5) (mir := true) L3_2 (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                · intro L1_2
                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 0) (mir := true) L1_2 (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (2 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (2 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                    · intro L1_3
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 6 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 0) (mir := true) L1_3 (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                        · intro L1_4
                                          refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 6 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 0) (mir := true) L1_4 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (-2 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (-1 : Int) (Presentation.HubcapSyntax.two 2 4 (1 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                            · intro L1_5
                                              refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 6 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 0) (mir := true) L1_5 (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                          · intro L0_2
                            refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 6 hvalid hfitMirror
                                (by fct_decide)
                                (j := 1) (mir := false) L0_2 (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 6 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 2) (mir := false) L0_2 (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 6 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 3) (mir := false) L0_2 (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 6 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := false) L0_2 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 6 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 5) (mir := false) L0_2 (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.two 1 6 (2 : Int) (Presentation.HubcapSyntax.two 2 4 (-1 : Int) (Presentation.HubcapSyntax.two 3 5 (-1 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)
                                      · intro L0_3
                                        refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 6 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 1) (mir := false) L0_3 (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 6 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 2) (mir := false) L0_3 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 6 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 3) (mir := false) L0_3 (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 6 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 4) (mir := false) L0_3 (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact similarLeafUpTo 6 hvalid hfitMirror
                                                    (by fct_decide)
                                                    (j := 5) (mir := false) L0_3 (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.two 1 6 (0 : Int) (Presentation.HubcapSyntax.two 2 4 (0 : Int) (Presentation.HubcapSyntax.two 3 5 (0 : Int) Presentation.HubcapSyntax.nil))) (by fct_decide)

theorem present6
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u}) :
    SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6) :=
  present6UpTo hcubic hpentagonal hredpart hvalid
    (mirrorExactFitTransportUpTo_of_mirrorExactFitTransport hfitMirror)

end

end PresentationScripts

end FourColor

end Schematic.Math.GraphTheory
