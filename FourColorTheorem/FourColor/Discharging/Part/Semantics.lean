import FourColorTheorem.FourColor.Discharging.Part.Operations

/-! Hypermap semantics and update combinators for discharging parts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PRange Part SubpartLoc

namespace SubpartLoc

/-- The dart selected by a subpart location relative to a hub dart. -/
def move (i : SubpartLoc) (G : Hypermap) (x : G.Dart) : G.Dart :=
  match i with
  | Pspoke => G.edge x
  | Phat => G.edge (G.face (G.face (G.edge x)))
  | Pfan1 => G.edge (G.face (G.face (G.face (G.edge x))))
  | Pfan2 => G.edge (G.face (G.face (G.face (G.face (G.edge x)))))
  | Pfan3 => G.edge (G.face (G.face (G.face (G.face (G.face (G.edge x))))))

/-- In a plain hypermap, the spoke selected in the mirror at `x` has the same
face arity as the original spoke one face-step before `x`. -/
theorem arity_mirror_spoke
    {G : Hypermap} (hG : G.Plain) (x : G.Dart) :
    G.mirror.arity (move Pspoke G.mirror x) =
      G.arity (move Pspoke G (G.face.symm x)) := by
  simp [move]
  rw [G.arity_mirror]
  rw [Hypermap.Plain.mirror_edge_eq_face_edge_face_symm (G := G) hG x]
  exact G.arity_face (G.edge (G.face.symm x))

end SubpartLoc

namespace Part

/-- Semantic fit of a pointed hypermap against a sector part. -/
noncomputable def fitp (G : Hypermap) (x : G.Dart) : Part → Bool
  | Pnil => true
  | Pcons s h p =>
      s (G.arity (SubpartLoc.move Pspoke G x)) &&
        h (G.arity (SubpartLoc.move Phat G x)) &&
          fitp G (G.face x) p
  | Pcons6 h f1 p =>
      Pr66 (G.arity (SubpartLoc.move Pspoke G x)) &&
        h (G.arity (SubpartLoc.move Phat G x)) &&
          f1 (G.arity (SubpartLoc.move Pfan1 G x)) &&
            fitp G (G.face x) p
  | Pcons7 h f1 f2 p =>
      Pr77 (G.arity (SubpartLoc.move Pspoke G x)) &&
        h (G.arity (SubpartLoc.move Phat G x)) &&
          f1 (G.arity (SubpartLoc.move Pfan1 G x)) &&
            f2 (G.arity (SubpartLoc.move Pfan2 G x)) &&
              fitp G (G.face x) p
  | Pcons8 h f1 f2 f3 p =>
      Pr88 (G.arity (SubpartLoc.move Pspoke G x)) &&
        h (G.arity (SubpartLoc.move Phat G x)) &&
          f1 (G.arity (SubpartLoc.move Pfan1 G x)) &&
            f2 (G.arity (SubpartLoc.move Pfan2 G x)) &&
              f3 (G.arity (SubpartLoc.move Pfan3 G x)) &&
                fitp G (G.face x) p

/-- Exact fit additionally fixes the hub arity to the number of subparts. -/
noncomputable def exactFitp (G : Hypermap) (x : G.Dart) (p : Part) : Bool :=
  (G.arity x == p.size) && fitp G x p

/-- Fit with an explicit range constraint on the hub arity. -/
noncomputable def tightFitp (G : Hypermap) (x : G.Dart)
    (up : PRange × Part) : Bool :=
  let (u, p) := up
  u (G.arity x) && fitp G x p

universe u

/-- A constructor function is valid for a subpart location when replacing its
range slot only changes the semantic constraint at that location.  This is the
Lean counterpart of Coq `part_update`. -/
def PartUpdate (pc : PRange → Part → Part) (i : SubpartLoc) : Prop :=
  ∀ (r : PRange) (p : Part),
    size (pc r p) = size p + 1 ∧
      ∀ (G : Hypermap.{u}) (x : G.Dart),
        fitp G x (pc r p) = true →
          PRange.contains r (G.arity (SubpartLoc.move i G x)) = true ∧
            ∀ r' : PRange,
              PRange.contains r' (G.arity (SubpartLoc.move i G x)) = true →
                fitp G x (pc r' p) = true

theorem updatePs (h : PRange) :
    PartUpdate (fun r p => Pcons r h p) SubpartLoc.Pspoke := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact ⟨hfit.1.1, fun _ hr' => ⟨⟨hr', hfit.1.2⟩, hfit.2⟩⟩

theorem updatePh (s : PRange) :
    PartUpdate (fun r p => Pcons s r p) SubpartLoc.Phat := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact ⟨hfit.1.2, fun _ hr' => ⟨⟨hfit.1.1, hr'⟩, hfit.2⟩⟩

theorem updateP6h (f1 : PRange) :
    PartUpdate (fun r p => Pcons6 r f1 p) SubpartLoc.Phat := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.2,
        fun _ hr' => ⟨⟨⟨hfit.1.1.1, hr'⟩, hfit.1.2⟩, hfit.2⟩⟩

theorem updateP6f1 (h : PRange) :
    PartUpdate (fun r p => Pcons6 h r p) SubpartLoc.Pfan1 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.2,
        fun _ hr' => ⟨⟨⟨hfit.1.1.1, hfit.1.1.2⟩, hr'⟩, hfit.2⟩⟩

theorem updateP7h (f1 f2 : PRange) :
    PartUpdate (fun r p => Pcons7 r f1 f2 p) SubpartLoc.Phat := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨hfit.1.1.1.1, hr'⟩, hfit.1.1.2⟩, hfit.1.2⟩,
            hfit.2⟩⟩

theorem updateP7f1 (h f2 : PRange) :
    PartUpdate (fun r p => Pcons7 h r f2 p) SubpartLoc.Pfan1 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨hfit.1.1.1.1, hfit.1.1.1.2⟩, hr'⟩, hfit.1.2⟩,
            hfit.2⟩⟩

theorem updateP7f2 (h f1 : PRange) :
    PartUpdate (fun r p => Pcons7 h f1 r p) SubpartLoc.Pfan2 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨hfit.1.1.1.1, hfit.1.1.1.2⟩, hfit.1.1.2⟩, hr'⟩,
            hfit.2⟩⟩

theorem updateP8h (f1 f2 f3 : PRange) :
    PartUpdate (fun r p => Pcons8 r f1 f2 f3 p) SubpartLoc.Phat := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.1.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨⟨hfit.1.1.1.1.1, hr'⟩, hfit.1.1.1.2⟩,
              hfit.1.1.2⟩, hfit.1.2⟩,
            hfit.2⟩⟩

theorem updateP8f1 (h f2 f3 : PRange) :
    PartUpdate (fun r p => Pcons8 h r f2 f3 p) SubpartLoc.Pfan1 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨⟨hfit.1.1.1.1.1, hfit.1.1.1.1.2⟩, hr'⟩,
              hfit.1.1.2⟩, hfit.1.2⟩,
            hfit.2⟩⟩

theorem updateP8f2 (h f1 f3 : PRange) :
    PartUpdate (fun r p => Pcons8 h f1 r f3 p) SubpartLoc.Pfan2 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨⟨hfit.1.1.1.1.1, hfit.1.1.1.1.2⟩, hfit.1.1.1.2⟩,
              hr'⟩, hfit.1.2⟩,
            hfit.2⟩⟩

theorem updateP8f3 (h f1 f2 : PRange) :
    PartUpdate (fun r p => Pcons8 h f1 f2 r p) SubpartLoc.Pfan3 := by
  intro r p
  constructor
  · simp [size]
  · intro G x hfit
    simp [fitp] at hfit ⊢
    exact
      ⟨hfit.1.2,
        fun _ hr' =>
          ⟨⟨⟨⟨⟨hfit.1.1.1.1.1, hfit.1.1.1.1.2⟩, hfit.1.1.1.2⟩,
              hfit.1.1.2⟩, hr'⟩,
            hfit.2⟩⟩

end Part

end FourColor

end Schematic.Math.GraphTheory
