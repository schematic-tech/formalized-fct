import FourColorTheorem.FourColor.Hypermap.Patch.Boundary

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

namespace Patch

/-- An injective image, restricted away from a source predicate, is equivalent
to the codomain outside an overlapping predicate when the two images cover the
codomain. -/
noncomputable def offImageEquiv
    {A X : Type*} (f : A → X) (boundary : A → Prop) (other : X → Prop)
    (hf : Function.Injective f)
    (hoverlap : ∀ a, boundary a ↔ other (f a))
    (hcover : ∀ x, (∃ a, f a = x) ∨ other x) :
    {a : A // ¬ boundary a} ≃ {x : X // ¬ other x} :=
  Equiv.ofBijective
    (fun a => ⟨f a, fun h => a.2 ((hoverlap a).2 h)⟩)
    ⟨by
        intro a b hab
        exact Subtype.ext (hf (congrArg Subtype.val hab)),
      by
        rintro ⟨x, hx⟩
        rcases hcover x with ⟨a, ha⟩ | hother
        · have haOff : ¬ boundary a := by
            intro hboundary
            apply hx
            rw [← ha]
            exact (hoverlap a).1 hboundary
          exact ⟨⟨a, haOff⟩, Subtype.ext ha⟩
        · exact False.elim (hx hother)⟩

end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
