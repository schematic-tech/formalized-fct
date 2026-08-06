import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding
import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension

/-!
Embedding geometry of compiled configurations.

This is the Lean counterpart of Coq `cfquiz.v`'s `embeddable_cfquiz`.  It
packages the construction-program invariants and the two executable quiz
guards into the exact `Embeddable` interface consumed by `embed.v`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Config

noncomputable section

/-- The semantic quiz kernel is exactly Coq's complement of the reversed
configuration perimeter. -/
theorem kernelSet_eq_kernel_reducibilityRingDarts
    {cf : Config}
    (hcf : cf.WellFormed) :
    cf.kernelSet = cf.map.map.Kernel cf.reducibilityRingDarts := by
  funext x
  apply propext
  have hpartition :
      cf.kernelSet x ↔ ¬ cf.map.map.FaceBand cf.ringDarts x := by
    simpa [Config.map, Config.ringDarts, Config.kernelDarts,
      Config.kernelSet] using
      (PointedHypermap.cpKernel_faceBand_iff_not_cpRing_faceBand
        (PointedHypermap.cpMapSimple_of_config hcf)
        (PointedHypermap.cpMapCover_of_config hcf) x)
  have hreverse :
      cf.map.map.FaceBand cf.reducibilityRingDarts x ↔
        cf.map.map.FaceBand cf.ringDarts x := by
    simpa [Config.reducibilityRingDarts] using
      (Hypermap.FaceBand.perm (G := cf.map.map)
        (List.reverse_perm cf.ringDarts) (u := x))
  simp only [Hypermap.Kernel]
  rw [hpartition, hreverse]

/-- Coq `embeddable_cfquiz`: every well-formed, right-rooted compiled
configuration is embeddable along the `C_reducible` perimeter orientation. -/
theorem embeddable_of_wellFormed_configQuiz_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (CFQuiz.configQuiz cf).isQuizR = true) :
    cf.map.map.Embeddable cf.reducibilityRingDarts := by
  have hcycle :=
    PointedHypermap.cpRingCycle_of_config (cp := cf.program) hcf
  have hsimpleFull :
      cf.map.map.FaceSimple (cf.ringDarts ++ cf.kernelDarts) := by
    simpa [Config.map, Config.ringDarts, Config.kernelDarts,
      PointedHypermap.cpMapSimple] using
      PointedHypermap.cpMapSimple_of_config (cp := cf.program) hcf
  have hsimpleRing : cf.map.map.FaceSimple cf.ringDarts :=
    (List.pairwise_append.mp hsimpleFull).1
  have hrawR : (CFQuiz.rawConfigQuiz cf).isQuizR = true :=
    CFQuiz.rawConfigQuiz_isQuizR_of_configQuiz_isQuizR hR
  have hradius : cf.map.map.RadiusTwo cf.kernelSet :=
    CFQuiz.config_radiusTwo_kernelSet_of_configQuiz_isQuizR hcf hR
      (fun m hm => PointedHypermap.cpMaskAdjSound_of_config hcf hm)
  refine {
    cycle := ?_
    faceSimple := ?_
    planar := ?_
    bridgeless := Config.map_bridgeless_of_wellFormed hcf
    plain := Config.map_plain_of_wellFormed hcf
    quasicubic := ?_
    connected := Config.map_connected_of_wellFormed hcf
    ringArity := ?_
    kernelRadiusTwo := ?_
  }
  · simpa [Config.map, Config.reducibilityRingDarts,
      Config.ringDarts] using
      (Birkhoff.functionCycle_reverse_of_symm
        (Birkhoff.ringCycle_functionCycleNodeSymm hcycle)
        hcycle.nodup)
  · simpa [Config.reducibilityRingDarts] using
      (Hypermap.FaceSimple.perm (G := cf.map.map)
        (List.reverse_perm cf.ringDarts).symm hsimpleRing)
  · simpa [Config.map] using
      PointedHypermap.cpmap_eulerPlanar_of_cubic
        (Config.wellFormed_cubicProgram hcf)
  · intro x hx
    have hxRing : x ∉ cf.ringDarts := by
      simpa [Config.reducibilityRingDarts] using hx
    apply Config.map_quasicubic_of_wellFormed hcf x
    intro hxOnRing
    exact hxRing
      (by
        simpa [Config.map, Config.ringDarts] using
          hcycle.mem_ringDarts_of_onRing
            (CProg.ringSize_pos cf.program) hxOnRing)
  · intro x hx
    apply CFQuiz.goodRingArity_of_mem_ringDarts_of_rawConfigQuiz_isQuizR
      hcf hrawR
    simpa [Config.reducibilityRingDarts] using hx
  · rw [← kernelSet_eq_kernel_reducibilityRingDarts hcf]
    exact hradius

/-- Source-validity form of `embeddable_cfquiz`. -/
theorem embeddable_of_wellFormed_sourceValid
    {cf : Config}
    (hcf : cf.WellFormed)
    (hsource : CFQuiz.ConfigQuizSourceValid cf) :
    cf.map.map.Embeddable cf.reducibilityRingDarts := by
  rcases hsource with ⟨_x0, hvalid⟩
  exact embeddable_of_wellFormed_configQuiz_isQuizR hcf hvalid.rightRooted

end

end Config

end FourColor

end Schematic.Math.GraphTheory
