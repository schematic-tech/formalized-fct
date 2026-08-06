import FourColorTheorem.FourColor.Discharging.PartGeometry
import FourColorTheorem.FourColor.Presentation.Language

/-!
Fast semantic closing lemmas for presentation goals.

This file deliberately depends only on the named reducibility proposition and
the lightweight part soundness facts.  It does not import the job/task
aggregates that execute the 0--633 certificate checks.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Presentation

noncomputable section

universe u

/-- The full free part for arity `n` fits every valid hub of arity `n`.
This isolates the geometric side condition needed by the arity-exclusion
presentation steps. -/
def FullPartFitsValidHub (n : Nat) : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    ValidHub G x →
      G.arity x = n →
        Part.exactFitp G x (Part.pconsN n) = true

theorem fullPartFitsValidHub_of_arity_ge_five
    {n : Nat}
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → ∀ y : G.Dart, 5 ≤ G.arity y) :
    FullPartFitsValidHub.{u} n := by
  intro G x hx harity
  exact Part.exactFitp_pconsN_of_arity_ge_five (G := G)
    (hge G x hx) harity

theorem fullPartFitsValidHub_of_pentagonal
    {n : Nat}
    (hPentagonal : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.Pentagonal) :
    FullPartFitsValidHub.{u} n := by
  intro G x hx harity
  exact Part.exactFitp_pconsN_of_pentagonal
    (G := G) (hPentagonal G x hx) harity

theorem successful_of_pentagonal_size_lt_five
    (hPentagonal : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.Pentagonal)
    {p : Part}
    (hsize : p.size < 5) :
    Successful.{u} p := by
  intro G x hx
  exact Part.exactFitp_eq_false_of_pentagonal_size_lt_five
    (G := G) (hPentagonal G x hx) (p := p) (x := x) hsize

theorem succeedsIn_of_pentagonal_size_lt_five
    (hPentagonal : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.Pentagonal)
    {p0 p : Part}
    (hsize : p.size < 5) :
    SucceedsIn.{u} p0 p :=
  succeedsIn_of_successful
    (successful_of_pentagonal_size_lt_five hPentagonal hsize)

theorem excludedArity_of_arity_ge_five
    (hge : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → 5 ≤ G.arity x)
    {n : Nat}
    (hn : n < 5) :
    ExcludedArity.{u} n := by
  intro _ G x hx harity
  have hbound : 5 ≤ G.arity x := hge G x hx
  omega

theorem excludedArity_of_pentagonal_lt_five
    (hPentagonal : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.Pentagonal)
    {n : Nat}
    (hn : n < 5) :
    ExcludedArity.{u} n :=
  excludedArity_of_arity_ge_five
    (fun G x hx =>
      Hypermap.arity_ge_five_of_pentagonal (hPentagonal G x hx) x)
    hn

theorem excludedArity_of_arity_le_eleven
    (hupper : ∀ (G : Hypermap.{u}) (x : G.Dart),
      ValidHub G x → G.arity x ≤ 11)
    {n : Nat}
    (hn : 11 < n) :
    ExcludedArity.{u} n := by
  intro _ G x hx harity
  have hbound : G.arity x ≤ 11 := hupper G x hx
  omega

/-- Valid-hub status is invariant along the face orbit. -/
theorem validHub_face_iter
    {G : Hypermap.{u}} {x : G.Dart}
    (n : Nat)
    (hx : ValidHub G x) :
    ValidHub G ((G.face : G.Dart → G.Dart)^[n] x) := by
  constructor
  · exact hx.1
  · have hreach :
        PermReachable G.face x ((G.face : G.Dart → G.Dart)^[n] x) :=
      permReachable_of_iterate_eq G.face rfl
    have hscore :
        G.dscore x =
          G.dscore ((G.face : G.Dart → G.Dart)^[n] x) :=
      G.dscore_cface hreach
    simpa [← hscore] using hx.2

/-- The face orbit period used by rotation-style presentation similarity. -/
def FacePeriodForValidHubs : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    (G.face : G.Dart → G.Dart)^[G.arity x] x = x

/-- The face-period dependency follows from the cardinal definition of
`Hypermap.arity`. -/
theorem facePeriodForValidHubs : FacePeriodForValidHubs.{u} := by
  intro G x
  exact G.face_iterate_arity x

end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
