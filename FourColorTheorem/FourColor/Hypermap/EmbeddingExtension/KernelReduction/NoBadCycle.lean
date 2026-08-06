import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.KernelReduction.Descent

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- There is no kernel-contained bad cycle.  This is the well-founded core of
Coq `embed_functor`, with `diskCard` replacing MathComp's `#|diskN ...|`. -/
theorem noKernelBadCycle
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h) :
    ¬ Nonempty (KernelBadCycle G H r h) := by
  rintro ⟨B⟩
  exact (measure KernelBadCycle.diskCard).wf.induction
      (C := fun _ => False) B (fun B ih => by
    have hnotBoth := hG.badCycle_not_both_nodeCentral hH hembed B
    by_cases hcentralN : EdgeCentral G H h (G.node B.head)
    · have hnotCentralNN :
          ¬ EdgeCentral G H h (G.node (G.node B.head)) := by
        intro hcentralNN
        exact hnotBoth ⟨hcentralN, hcentralNN⟩
      rcases hG.badCycle_secondNode_smaller hH.plain B hcentralN
          hnotCentralNN with ⟨B', hsmaller⟩
      exact ih B' hsmaller
    · rcases hG.badCycle_firstNode_smaller hH.plain hembed B
          hcentralN with ⟨B', hsmaller⟩
      exact ih B' hsmaller)

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
