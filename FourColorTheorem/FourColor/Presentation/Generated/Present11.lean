import FourColorTheorem.FourColor.Presentation.ScriptCombinators

/-!
Arity-11 presentation script, mechanically ported from Coq `present11.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace PresentationScripts

open Presentation

noncomputable section

universe u

set_option maxHeartbeats 10000000 in
theorem present11UpTo
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} 11) :
    SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11) := by
  let hge := arityGeFiveOfPentagonal hpentagonal
  refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
  ·
    exact hubcapLeaf hcubic hpentagonal hredpart
      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
  · intro L0_1
    refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    ·
      exact similarLeafUpTo 11 hvalid hfitMirror
        (by fct_decide)
        (j := 1) (mir := false) L0_1 (by fct_decide)
    · intro _
      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        exact similarLeafUpTo 11 hvalid hfitMirror
          (by fct_decide)
          (j := 2) (mir := false) L0_1 (by fct_decide)
      · intro _
        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          exact similarLeafUpTo 11 hvalid hfitMirror
            (by fct_decide)
            (j := 3) (mir := false) L0_1 (by fct_decide)
        · intro _
          refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 11 hvalid hfitMirror
              (by fct_decide)
              (j := 4) (mir := false) L0_1 (by fct_decide)
          · intro _
            refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 11 hvalid hfitMirror
                (by fct_decide)
                (j := 5) (mir := false) L0_1 (by fct_decide)
            · intro _
              refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 11 hvalid hfitMirror
                  (by fct_decide)
                  (j := 6) (mir := false) L0_1 (by fct_decide)
              · intro _
                refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 11 hvalid hfitMirror
                    (by fct_decide)
                    (j := 7) (mir := false) L0_1 (by fct_decide)
                · intro _
                  refine pcase hge (gtS 9 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 11 hvalid hfitMirror
                      (by fct_decide)
                      (j := 8) (mir := false) L0_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 10 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 11 hvalid hfitMirror
                        (by fct_decide)
                        (j := 9) (mir := false) L0_1 (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 11 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact similarLeafUpTo 11 hvalid hfitMirror
                          (by fct_decide)
                          (j := 10) (mir := false) L0_1 (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (gtS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                          · intro L1_1
                            refine pcase hge (gtS 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 11 hvalid hfitMirror
                                (by fct_decide)
                                (j := 10) (mir := true) L1_1 (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 2) (mir := false) L1_1 (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                              · intro L1_2
                                refine pcase hge (gtS 10 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 9) (mir := false) L1_2 (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 7) (mir := true) L1_1 (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 3) (mir := false) L1_1 (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 3) (mir := false) L1_2 (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                  · intro L1_3
                                    refine pcase hge (gtS 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 8) (mir := false) L1_3 (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 6) (mir := true) L1_1 (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 4) (mir := false) L1_1 (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 4) (mir := false) L1_2 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 4) (mir := false) L1_3 (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                      · intro L1_4
                                        refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 7) (mir := false) L1_4 (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 5) (mir := true) L1_1 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 5) (mir := false) L1_1 (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                          · intro L1_5
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 6) (mir := false) L1_5 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 8 9 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (9 : Int) (Presentation.HubcapSyntax.two 9 10 (9 : Int) Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro L0_2
                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact similarLeafUpTo 11 hvalid hfitMirror
                              (by fct_decide)
                              (j := 1) (mir := false) L0_2 (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 11 hvalid hfitMirror
                                (by fct_decide)
                                (j := 2) (mir := false) L0_2 (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 11 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 3) (mir := false) L0_2 (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 4) (mir := false) L0_2 (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 5) (mir := false) L0_2 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 6) (mir := false) L0_2 (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 7) (mir := false) L0_2 (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 8) (mir := false) L0_2 (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 10 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 9) (mir := false) L0_2 (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 11 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 10) (mir := false) L0_2 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (gtS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  refine pcase hge (gtS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 5 6 (9 : Int) Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 8 9 (9 : Int) Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro L1_1
                                                  refine pcase hge (gtS 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                      (by fct_decide)
                                                      (j := 10) (mir := false) L1_1 (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              refine pcase hge (leS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                refine pcase hge (leS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 8) (mir := false) L1_1 (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 10 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (leF1 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                · intro _
                                                                                  refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                  ·
                                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                                  · intro _
                                                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                    ·
                                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                            ·
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                            · intro _
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                                    · intro L7_1
                                                                                      refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                          (by fct_decide)
                                                                                          (j := 2) (mir := true) L7_1 (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                            ·
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                            · intro _
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 7) (mir := false) L1_1 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.two 9 11 (7 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (leF1 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                · intro _
                                                                                  refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                  ·
                                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                                  · intro _
                                                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                    ·
                                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                            ·
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                            · intro _
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 6 10 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                                    · intro L6_1
                                                                                      refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                          (by fct_decide)
                                                                                          (j := 3) (mir := true) L6_1 (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                              (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 6) (mir := false) L1_1 (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (leF1 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                · intro _
                                                                                  refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                  ·
                                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                                  · intro _
                                                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                    ·
                                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                            ·
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                                            · intro _
                                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 7 10 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                                    · intro L5_1
                                                                                      refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                          (by fct_decide)
                                                                                          (j := 4) (mir := true) L5_1 (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (leH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                                          · intro _
                                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 3 5 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro L4_1
                                                            refine pcase hge (gtS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 5) (mir := false) L1_1 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) (Presentation.HubcapSyntax.two 9 10 (9 : Int) Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 5) (mir := false) L4_1 (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                        · intro L3_1
                                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                                              (by fct_decide)
                                                              (j := 4) (mir := false) L1_1 (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              refine pcase hge (leS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                refine pcase hge (leS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 4) (mir := false) L3_1 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 8) (mir := false) L1_1 (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (4 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                              · intro L4_1
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 7) (mir := false) L1_1 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 7) (mir := false) L4_1 (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                            · intro L3_2
                                                              refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 6) (mir := false) L1_1 (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 6) (mir := true) L3_2 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 8) (mir := false) L1_1 (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                      · intro L2_1
                                                        refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 3) (mir := false) L1_1 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 3) (mir := false) L2_1 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 6) (mir := false) L1_1 (by fct_decide)
                                                              · intro _
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (5 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                          · intro L2_2
                                                            refine pcase hge (gtS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 5) (mir := false) L1_1 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 5) (mir := false) L2_2 (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 7) (mir := false) L1_1 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 7) (mir := false) L2_1 (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.one 10 (5 : Int) (Presentation.HubcapSyntax.one 11 (4 : Int) Presentation.HubcapSyntax.nil))))))))))) (by fct_decide)
                                                    · intro L1_2
                                                      refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 2) (mir := false) L1_1 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 2) (mir := false) L1_2 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                                              (by fct_decide)
                                                              (j := 4) (mir := false) L1_1 (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 4) (mir := false) L1_2 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 6) (mir := false) L1_1 (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 8) (mir := false) L1_2 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                                                        (by fct_decide)
                                                                        (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                                          (by fct_decide)
                                                                          (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                                                            (by fct_decide)
                                                                            (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                                                              (by fct_decide)
                                                                              (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                (by fct_decide)
                                                                                (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                  (by fct_decide)
                                                                                  (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                    (by fct_decide)
                                                                                    (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                · intro _
                                                                                  refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                  ·
                                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                      (by fct_decide)
                                                                                      (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                  · intro _
                                                                                    refine pcase hge (gtH 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                    ·
                                                                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                        (by fct_decide)
                                                                                        (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                    · intro _
                                                                                      refine pcase hge (gtH 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                      ·
                                                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                          (by fct_decide)
                                                                                          (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                      · intro _
                                                                                        refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                        ·
                                                                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                            (by fct_decide)
                                                                                            (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                        · intro _
                                                                                          refine pcase hge (gtF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                          ·
                                                                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                              (by fct_decide)
                                                                                              (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                          · intro _
                                                                                            refine pcase hge (gtF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                            ·
                                                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                                (by fct_decide)
                                                                                                (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                            · intro _
                                                                                              refine pcase hge (gtF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                              ·
                                                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                                  (by fct_decide)
                                                                                                  (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                              · intro _
                                                                                                refine pcase hge (gtF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                                ·
                                                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                                                    (by fct_decide)
                                                                                                    (j := 6) (mir := false) L1_2 (by fct_decide)
                                                                                                · intro _
                                                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                              · intro L0_3
                                                refine pcase hge (gtS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                    (by fct_decide)
                                                    (j := 1) (mir := false) L0_3 (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                      (by fct_decide)
                                                      (j := 2) (mir := false) L0_3 (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact similarLeafUpTo 11 hvalid hfitMirror
                                                        (by fct_decide)
                                                        (j := 3) (mir := false) L0_3 (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 11 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 4) (mir := false) L0_3 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 11 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 5) (mir := false) L0_3 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact similarLeafUpTo 11 hvalid hfitMirror
                                                              (by fct_decide)
                                                              (j := 6) (mir := false) L0_3 (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 11 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 7) (mir := false) L0_3 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact similarLeafUpTo 11 hvalid hfitMirror
                                                                  (by fct_decide)
                                                                  (j := 8) (mir := false) L0_3 (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 10 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 11 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 9) (mir := false) L0_3 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 11 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact similarLeafUpTo 11 hvalid hfitMirror
                                                                      (by fct_decide)
                                                                      (j := 10) (mir := false) L0_3 (by fct_decide)
                                                                  · intro _
                                                                    exact reducibleLeaf hredpart (by fct_decide)

theorem present11
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u}) :
    SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11) :=
  present11UpTo hcubic hpentagonal hredpart hvalid
    (mirrorExactFitTransportUpTo_of_mirrorExactFitTransport hfitMirror)

end

end PresentationScripts

end FourColor

end Schematic.Math.GraphTheory
