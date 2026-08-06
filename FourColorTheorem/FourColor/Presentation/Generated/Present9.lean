import FourColorTheorem.FourColor.Presentation.ScriptCombinators

/-!
Arity-9 presentation script, mechanically ported from Coq `present9.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace PresentationScripts

open Presentation

noncomputable section

universe u

set_option maxHeartbeats 30000000 in
theorem present9UpTo
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} 9) :
    SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9) := by
  let hge := arityGeFiveOfPentagonal hpentagonal
  refine pcase hge (leS 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
  ·
    refine pcase hge (leS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    ·
      refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact reducibleLeaf hredpart (by fct_decide)
            · intro _
              refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact reducibleLeaf hredpart (by fct_decide)
              · intro _
                refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                · intro _
                  refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact reducibleLeaf hredpart (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                          · intro L6_1
                            refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 9 hvalid hfitMirror
                                (by fct_decide)
                                (j := 5) (mir := true) L6_1 (by fct_decide)
                            · intro _
                              refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro L5_1
                      refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact similarLeafUpTo 9 hvalid hfitMirror
                          (by fct_decide)
                          (j := 5) (mir := true) L5_1 (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 2 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (2 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro L5_2
                              refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 9 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 5) (mir := true) L5_2 (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro L6_1
                                            refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 9 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 5) (mir := true) L6_1 (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro L5_3
                                  refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 5) (mir := true) L5_3 (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
          · intro L4_1
            refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 9 hvalid hfitMirror
                (by fct_decide)
                (j := 1) (mir := false) L4_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact reducibleLeaf hredpart (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact reducibleLeaf hredpart (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 5 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
              · intro L4_2
                refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 9 hvalid hfitMirror
                    (by fct_decide)
                    (j := 4) (mir := true) L4_2 (by fct_decide)
                · intro _
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro L5_1
                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 4) (mir := true) L5_1 (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro L4_3
                                  refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := true) L4_3 (by fct_decide)
                                  · intro _
                                    refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
        · intro L3_1
          refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 9 hvalid hfitMirror
              (by fct_decide)
              (j := 1) (mir := false) L3_1 (by fct_decide)
          · intro _
            refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact reducibleLeaf hredpart (by fct_decide)
                · intro _
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact similarLeafUpTo 9 hvalid hfitMirror
                        (by fct_decide)
                        (j := 5) (mir := false) L3_1 (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro L6_1
                            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact similarLeafUpTo 9 hvalid hfitMirror
                                (by fct_decide)
                                (j := 7) (mir := true) L6_1 (by fct_decide)
                            · intro _
                              exact reducibleLeaf hredpart (by fct_decide)
                  · intro _
                    refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact reducibleLeaf hredpart (by fct_decide)
                          · intro _
                            refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (9 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 6 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
              · intro L4_1
                refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 3) (mir := true) L4_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 7 (7 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 7 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 7 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.two 3 7 (7 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 7 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 5 9 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 9 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 9 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 5 (5 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                · intro _
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 6 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 5 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro L6_1
                                  refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 6 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 6 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 6 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 6 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 3) (mir := true) L6_1 (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (8 : Int) (Presentation.HubcapSyntax.two 3 7 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (7 : Int) (Presentation.HubcapSyntax.two 3 7 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                    · intro L5_1
                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact similarLeafUpTo 9 hvalid hfitMirror
                          (by fct_decide)
                          (j := 3) (mir := true) L5_1 (by fct_decide)
                      · intro _
                        refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact reducibleLeaf hredpart (by fct_decide)
                        · intro _
                          refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact reducibleLeaf hredpart (by fct_decide)
                          · intro _
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.two 1 6 (9 : Int) (Presentation.HubcapSyntax.two 1 8 (9 : Int) (Presentation.HubcapSyntax.two 6 8 (9 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 6 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                · intro _
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 2 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF2 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.two 2 4 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 8 (9 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                    · intro _
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
            · intro L3_2
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 9 hvalid hfitMirror
                  (by fct_decide)
                  (j := 3) (mir := true) L3_2 (by fct_decide)
              · intro _
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                        · intro L5_1
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 3) (mir := true) L5_1 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                · intro L3_3
                  refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 3) (mir := true) L3_3 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 8 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                          · intro _
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro L3_4
                                          refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 3) (mir := true) L3_4 (by fct_decide)
                                          · intro _
                                            exact reducibleLeaf hredpart (by fct_decide)
      · intro L2_1
        refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          exact similarLeafUpTo 9 hvalid hfitMirror
            (by fct_decide)
            (j := 1) (mir := false) L2_1 (by fct_decide)
        · intro _
          refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 9 hvalid hfitMirror
                  (by fct_decide)
                  (j := 5) (mir := false) L2_1 (by fct_decide)
              · intro _
                refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 9 hvalid hfitMirror
                    (by fct_decide)
                    (j := 6) (mir := false) L2_1 (by fct_decide)
                · intro _
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact reducibleLeaf hredpart (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (leS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                        · intro L5_1
                          refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact similarLeafUpTo 9 hvalid hfitMirror
                              (by fct_decide)
                              (j := 6) (mir := true) L5_1 (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro L5_2
                                  refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 6) (mir := true) L5_2 (by fct_decide)
                                  · intro _
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro L5_1
                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 6) (mir := true) L5_1 (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro L4_1
                                refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact similarLeafUpTo 9 hvalid hfitMirror
                                    (by fct_decide)
                                    (j := 6) (mir := true) L4_1 (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                  · intro L4_2
                                    refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 6) (mir := true) L4_2 (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                · intro _
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
            · intro _
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact reducibleLeaf hredpart (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (7 : Int) (Presentation.HubcapSyntax.two 3 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 5 (7 : Int) (Presentation.HubcapSyntax.two 4 8 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 3 7 (8 : Int) (Presentation.HubcapSyntax.two 4 9 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 7 (5 : Int) (Presentation.HubcapSyntax.two 4 8 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro L5_1
                      refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 5 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro L7_1
                                  refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.two 6 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 3) (mir := false) L7_1 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 6) (mir := false) L5_1 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 9 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 3) (mir := false) L5_1 (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact similarLeafUpTo 9 hvalid hfitMirror
                                  (by fct_decide)
                                  (j := 3) (mir := false) L5_1 (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 4 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                · intro L4_1
                  refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 6) (mir := false) L4_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 2 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
              · intro L3_1
                refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 5) (mir := true) L3_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 3 7 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 5 (8 : Int) (Presentation.HubcapSyntax.two 2 4 (8 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (leS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 9 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 4 8 (8 : Int) (Presentation.HubcapSyntax.two 4 9 (8 : Int) (Presentation.HubcapSyntax.two 5 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact reducibleLeaf hredpart (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (8 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (5 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (1 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                · intro _
                  refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 4 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 5 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                            · intro _
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro L3_2
                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 5) (mir := true) L3_2 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                        · intro L3_3
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                                              (by fct_decide)
                                                              (j := 5) (mir := true) L3_3 (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 5) (mir := true) L3_2 (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                                        (by fct_decide)
                                                        (j := 5) (mir := true) L3_3 (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 5) (mir := true) L3_2 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                          · intro _
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro L3_4
                                                                      refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                                          (by fct_decide)
                                                                          (j := 5) (mir := true) L3_4 (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 3 (1 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                                · intro _
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
          · intro L2_2
            refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 9 hvalid hfitMirror
                (by fct_decide)
                (j := 2) (mir := true) L2_2 (by fct_decide)
            · intro _
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact hubcapLeaf hcubic hpentagonal hredpart
                    (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (9 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                · intro _
                  refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 7 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 8 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 2 8 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 5 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact reducibleLeaf hredpart (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact reducibleLeaf hredpart (by fct_decide)
                            · intro _
                              refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 7 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 2 5 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (8 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 5 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (4 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 2 5 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 5 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.two 1 4 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 1 5 (7 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 5 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                            · intro _
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                  · intro L3_1
                    refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 5 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 6 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 9 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 2) (mir := true) L3_1 (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro L4_1
                                      refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (8 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                                        (by fct_decide)
                                                        (j := 2) (mir := true) L3_1 (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 2) (mir := true) L4_1 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                        · intro _
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (leH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact reducibleLeaf hredpart (by fct_decide)
                              · intro _
                                refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact reducibleLeaf hredpart (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 7 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 6 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (3 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro L4_1
                                              refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (8 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 2) (mir := true) L3_1 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 2) (mir := true) L4_1 (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                          · intro _
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 2) (mir := true) L3_1 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 2) (mir := true) L4_1 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 7 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro L3_2
                                      refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.two 6 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 8 (7 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                · intro _
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 2) (mir := true) L3_2 (by fct_decide)
                                          · intro _
                                            refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                (by fct_decide)
                                                (j := 2) (mir := true) L3_1 (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro L3_3
                                                            refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                                (by fct_decide)
                                                                (j := 2) (mir := true) L3_3 (by fct_decide)
                                                            · intro _
                                                              exact reducibleLeaf hredpart (by fct_decide)
              · intro L2_3
                refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 9 hvalid hfitMirror
                    (by fct_decide)
                    (j := 2) (mir := true) L2_3 (by fct_decide)
                · intro _
                  refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact reducibleLeaf hredpart (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                refine pcase hge (leS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                              · intro _
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                              · intro L3_1
                                                                refine pcase hge (leH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact similarLeafUpTo 9 hvalid hfitMirror
                                                                    (by fct_decide)
                                                                    (j := 2) (mir := true) L3_1 (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                            · intro _
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                          · intro L3_2
                                                                            refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact similarLeafUpTo 9 hvalid hfitMirror
                                                                                (by fct_decide)
                                                                                (j := 2) (mir := true) L3_2 (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                                              · intro _
                                                                                refine pcase hge (leF1 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                                ·
                                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                                · intro _
                                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                    (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
    · intro L1_1
      refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        exact similarLeafUpTo 9 hvalid hfitMirror
          (by fct_decide)
          (j := 1) (mir := false) L1_1 (by fct_decide)
      · intro _
        refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 9 hvalid hfitMirror
              (by fct_decide)
              (j := 6) (mir := false) L1_1 (by fct_decide)
          · intro _
            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 9 hvalid hfitMirror
                (by fct_decide)
                (j := 7) (mir := false) L1_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 9 hvalid hfitMirror
                    (by fct_decide)
                    (j := 3) (mir := false) L1_1 (by fct_decide)
                · intro _
                  refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 4) (mir := false) L1_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (0 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (1 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                · intro L3_1
                                  refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := true) L3_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                        (by fct_decide)
                                        (j := 3) (mir := false) L3_1 (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                          (by fct_decide)
                                          (j := 1) (mir := true) L3_1 (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 9 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                            (by fct_decide)
                                            (j := 6) (mir := false) L3_1 (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact similarLeafUpTo 9 hvalid hfitMirror
                                              (by fct_decide)
                                              (j := 7) (mir := true) L3_1 (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 6 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro L3_2
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 9 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 7) (mir := true) L3_2 (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact similarLeafUpTo 9 hvalid hfitMirror
                                                    (by fct_decide)
                                                    (j := 3) (mir := false) L3_2 (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                                      (by fct_decide)
                                                      (j := 4) (mir := true) L3_2 (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact similarLeafUpTo 9 hvalid hfitMirror
                                                        (by fct_decide)
                                                        (j := 6) (mir := false) L3_2 (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact similarLeafUpTo 9 hvalid hfitMirror
                                                          (by fct_decide)
                                                          (j := 1) (mir := true) L3_2 (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.two 2 6 (6 : Int) (Presentation.HubcapSyntax.two 3 7 (7 : Int) (Presentation.HubcapSyntax.two 4 8 (7 : Int) (Presentation.HubcapSyntax.two 5 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 5 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
              · intro _
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (gtS 1 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.two 6 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 3 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (8 : Int) (Presentation.HubcapSyntax.two 6 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 5 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (0 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 3 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (0 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 2 9 (7 : Int) (Presentation.HubcapSyntax.two 3 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 1 9 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 2 9 (7 : Int) (Presentation.HubcapSyntax.two 3 5 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 1 3 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.two 2 9 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                          · intro _
                                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                              · intro _
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 7 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (0 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.two 1 4 (8 : Int) (Presentation.HubcapSyntax.two 2 5 (8 : Int) (Presentation.HubcapSyntax.two 3 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 8 (0 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 5 (8 : Int) (Presentation.HubcapSyntax.two 3 6 (8 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (leS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.two 2 9 (6 : Int) (Presentation.HubcapSyntax.two 3 5 (8 : Int) (Presentation.HubcapSyntax.two 4 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 2 9 (5 : Int) (Presentation.HubcapSyntax.two 3 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.two 2 3 (8 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF2 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                  · intro _
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 8 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 5 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.two 8 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 3 5 (6 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.two 3 5 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.two 2 4 (5 : Int) (Presentation.HubcapSyntax.two 3 5 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.two 2 6 (6 : Int) (Presentation.HubcapSyntax.two 4 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.two 3 5 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.two 8 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leF2 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.two 4 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                · intro _
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro L4_1
                                            refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact similarLeafUpTo 9 hvalid hfitMirror
                                                  (by fct_decide)
                                                  (j := 4) (mir := true) L4_1 (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 8 9 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 2 4 (6 : Int) (Presentation.HubcapSyntax.two 8 9 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      refine pcase hge (leH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact reducibleLeaf hredpart (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.two 3 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                        · intro _
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                      · intro L4_2
                                                        refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact similarLeafUpTo 9 hvalid hfitMirror
                                                            (by fct_decide)
                                                            (j := 4) (mir := true) L4_2 (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (leH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (4 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leH 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro _
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (5 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (5 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (1 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                · intro L3_1
                                  refine pcase hge (leS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 4) (mir := true) L3_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                          · intro _
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (5 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                · intro L2_1
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 4) (mir := true) L2_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro _
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 1 5 (7 : Int) (Presentation.HubcapSyntax.two 2 5 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
        · intro L1_2
          refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 9 hvalid hfitMirror
              (by fct_decide)
              (j := 3) (mir := false) L1_2 (by fct_decide)
          · intro _
            refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 9 hvalid hfitMirror
                  (by fct_decide)
                  (j := 7) (mir := false) L1_2 (by fct_decide)
              · intro _
                refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 5) (mir := false) L1_2 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (0 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (0 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (0 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (0 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 8 8) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (0 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (3 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                · intro L3_1
                                  refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact similarLeafUpTo 9 hvalid hfitMirror
                                      (by fct_decide)
                                      (j := 5) (mir := true) L3_1 (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        refine pcase hge (leH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (2 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (leH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (1 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                    · intro _
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          refine pcase hge (leH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact reducibleLeaf hredpart (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (1 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (2 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (leF1 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.two 2 7 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.two 1 9 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.two 5 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (4 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 3 7 (7 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 7 (6 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 8 (9 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 9 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 5 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                      · intro _
                                                                        refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                        ·
                                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                        · intro _
                                                                          refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                          ·
                                                                            exact reducibleLeaf hredpart (by fct_decide)
                                                                          · intro _
                                                                            refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                            ·
                                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                            · intro _
                                                                              refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                              ·
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                              · intro _
                                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.two 1 2 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 3 7 (5 : Int) (Presentation.HubcapSyntax.two 4 7 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtS 6 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (2 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtS 8 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (5 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (2 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 7 (6 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                                            (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 8 (8 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (7 : Int) (Presentation.HubcapSyntax.two 5 9 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 5 9 (7 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (leF1 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact reducibleLeaf hredpart (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 5 (6 : Int) (Presentation.HubcapSyntax.two 3 4 (6 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (2 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (leH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                    · intro _
                                                                      refine pcase hge (gtH 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                      ·
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                                      · intro _
                                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 6 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                · intro L2_1
                  refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 2) (mir := false) L2_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 3 4 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (2 : Int) (Presentation.HubcapSyntax.one 3 (2 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 4 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (gtH 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact hubcapLeaf hcubic hpentagonal hredpart
                                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (2 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.two 4 5 (4 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact hubcapLeaf hcubic hpentagonal hredpart
                                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                            · intro _
                                              refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact reducibleLeaf hredpart (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 7 (3 : Int) (Presentation.HubcapSyntax.one 8 (5 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                        (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.two 1 7 (7 : Int) (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 8 9 (8 : Int) (Presentation.HubcapSyntax.nil)))))) (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.two 3 4 (5 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.two 1 2 (7 : Int) (Presentation.HubcapSyntax.two 1 8 (8 : Int) (Presentation.HubcapSyntax.two 2 8 (8 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                      · intro _
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.two 2 8 (7 : Int) (Presentation.HubcapSyntax.two 4 5 (5 : Int) (Presentation.HubcapSyntax.two 7 9 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
            · intro L1_3
              refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 9 hvalid hfitMirror
                  (by fct_decide)
                  (j := 2) (mir := false) L1_3 (by fct_decide)
              · intro _
                refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 5) (mir := false) L1_1 (by fct_decide)
                  · intro _
                    refine pcase hge (gtS 1 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                    ·
                      exact hubcapLeaf hcubic hpentagonal hredpart
                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                    · intro _
                      refine pcase hge (gtS 2 7) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                      ·
                        exact hubcapLeaf hcubic hpentagonal hredpart
                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (0 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 6 (4 : Int) (Presentation.HubcapSyntax.one 7 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.nil)))))))))) (by fct_decide)
                      · intro _
                        refine pcase hge (gtS 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                        ·
                          exact hubcapLeaf hcubic hpentagonal hredpart
                            (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                        · intro _
                          refine pcase hge (gtS 5 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                          ·
                            exact hubcapLeaf hcubic hpentagonal hredpart
                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                          · intro _
                            refine pcase hge (gtS 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                            ·
                              exact hubcapLeaf hcubic hpentagonal hredpart
                                (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                            · intro _
                              refine pcase hge (gtS 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                              ·
                                exact hubcapLeaf hcubic hpentagonal hredpart
                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                              · intro _
                                refine pcase hge (gtS 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                ·
                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                · intro _
                                  refine pcase hge (gtH 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                  ·
                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                      (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                  · intro _
                                    refine pcase hge (gtH 3 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                    ·
                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                        (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 1 2 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                    · intro _
                                      refine pcase hge (gtH 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                      ·
                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                          (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                      · intro _
                                        refine pcase hge (leF1 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                        ·
                                          exact reducibleLeaf hredpart (by fct_decide)
                                        · intro _
                                          refine pcase hge (gtH 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                          ·
                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                              (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (3 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.one 6 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                          · intro _
                                            refine pcase hge (leF1 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                            ·
                                              exact reducibleLeaf hredpart (by fct_decide)
                                            · intro _
                                              refine pcase hge (gtH 7 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                              ·
                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                  (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 5 6 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                              · intro _
                                                refine pcase hge (gtH 8 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                ·
                                                  exact hubcapLeaf hcubic hpentagonal hredpart
                                                    (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 8 (3 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 5 7 (5 : Int) (Presentation.HubcapSyntax.two 6 7 (5 : Int) (Presentation.HubcapSyntax.nil))))))))) (by fct_decide)
                                                · intro _
                                                  refine pcase hge (gtH 6 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                  ·
                                                    exact hubcapLeaf hcubic hpentagonal hredpart
                                                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (3 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 6 9 (5 : Int) (Presentation.HubcapSyntax.two 7 8 (7 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                  · intro _
                                                    refine pcase hge (leF1 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                    ·
                                                      exact reducibleLeaf hredpart (by fct_decide)
                                                    · intro _
                                                      refine pcase hge (gtS 2 6) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                      ·
                                                        exact hubcapLeaf hcubic hpentagonal hredpart
                                                          (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (3 : Int) (Presentation.HubcapSyntax.one 3 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 5 (4 : Int) (Presentation.HubcapSyntax.two 6 9 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                      · intro _
                                                        refine pcase hge (leF1 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                        ·
                                                          exact reducibleLeaf hredpart (by fct_decide)
                                                        · intro _
                                                          refine pcase hge (gtH 9 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                          ·
                                                            exact hubcapLeaf hcubic hpentagonal hredpart
                                                              (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                          · intro _
                                                            refine pcase hge (leF1 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                            ·
                                                              exact reducibleLeaf hredpart (by fct_decide)
                                                            · intro _
                                                              refine pcase hge (gtH 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                              ·
                                                                exact hubcapLeaf hcubic hpentagonal hredpart
                                                                  (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (3 : Int) (Presentation.HubcapSyntax.two 5 6 (7 : Int) (Presentation.HubcapSyntax.two 7 8 (5 : Int) (Presentation.HubcapSyntax.nil)))))))) (by fct_decide)
                                                              · intro _
                                                                refine pcase hge (leF1 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                ·
                                                                  exact reducibleLeaf hredpart (by fct_decide)
                                                                · intro _
                                                                  refine pcase hge (leF1 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                  ·
                                                                    exact reducibleLeaf hredpart (by fct_decide)
                                                                  · intro _
                                                                    refine pcase hge (gtH 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                                                                    ·
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (3 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (7 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                                                                    · intro _
                                                                      exact hubcapLeaf hcubic hpentagonal hredpart
                                                                        (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 4 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 5 6 (6 : Int) (Presentation.HubcapSyntax.two 7 8 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
                · intro L1_4
                  refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 5) (mir := false) L1_4 (by fct_decide)
                  · intro _
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 8 (4 : Int) (Presentation.HubcapSyntax.one 9 (4 : Int) (Presentation.HubcapSyntax.two 2 3 (6 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)
  · intro L0_1
    refine pcase hge (leS 1 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
    ·
      exact similarLeafUpTo 9 hvalid hfitMirror
        (by fct_decide)
        (j := 1) (mir := false) L0_1 (by fct_decide)
    · intro _
      refine pcase hge (leS 2 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
      ·
        exact similarLeafUpTo 9 hvalid hfitMirror
          (by fct_decide)
          (j := 2) (mir := false) L0_1 (by fct_decide)
      · intro _
        refine pcase hge (leS 3 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
        ·
          exact similarLeafUpTo 9 hvalid hfitMirror
            (by fct_decide)
            (j := 3) (mir := false) L0_1 (by fct_decide)
        · intro _
          refine pcase hge (leS 4 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
          ·
            exact similarLeafUpTo 9 hvalid hfitMirror
              (by fct_decide)
              (j := 4) (mir := false) L0_1 (by fct_decide)
          · intro _
            refine pcase hge (leS 5 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
            ·
              exact similarLeafUpTo 9 hvalid hfitMirror
                (by fct_decide)
                (j := 5) (mir := false) L0_1 (by fct_decide)
            · intro _
              refine pcase hge (leS 6 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
              ·
                exact similarLeafUpTo 9 hvalid hfitMirror
                  (by fct_decide)
                  (j := 6) (mir := false) L0_1 (by fct_decide)
              · intro _
                refine pcase hge (leS 7 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                ·
                  exact similarLeafUpTo 9 hvalid hfitMirror
                    (by fct_decide)
                    (j := 7) (mir := false) L0_1 (by fct_decide)
                · intro _
                  refine pcase hge (leS 8 5) (by set_option maxRecDepth 100000 in rfl) ?_ ?_
                  ·
                    exact similarLeafUpTo 9 hvalid hfitMirror
                      (by fct_decide)
                      (j := 8) (mir := false) L0_1 (by fct_decide)
                  · intro _
                    exact hubcapLeaf hcubic hpentagonal hredpart
                      (Presentation.HubcapSyntax.one 1 (4 : Int) (Presentation.HubcapSyntax.one 2 (4 : Int) (Presentation.HubcapSyntax.one 3 (4 : Int) (Presentation.HubcapSyntax.two 4 5 (6 : Int) (Presentation.HubcapSyntax.two 6 7 (6 : Int) (Presentation.HubcapSyntax.two 8 9 (6 : Int) (Presentation.HubcapSyntax.nil))))))) (by fct_decide)

theorem present9
    (hcubic : Unavoidability.CubicMinimalCounterexamples.{u})
    (hpentagonal : Unavoidability.PentagonalMinimalCounterexamples.{u})
    (hredpart : RedpartSound.{u})
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u}) :
    SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9) :=
  present9UpTo hcubic hpentagonal hredpart hvalid
    (mirrorExactFitTransportUpTo_of_mirrorExactFitTransport hfitMirror)

end

end PresentationScripts

end FourColor

end Schematic.Math.GraphTheory
