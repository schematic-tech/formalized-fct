import FourColorTheorem.FourColor.Hypermap.Embedding.FaceSimplification

/-! Radius-two adjacency of selected face classes. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

/-- Coq `at_radius2`: `x` and `y` have adjacent representatives with the
intermediate edge dart in the selected face-closed set. -/
def AtRadiusTwo (A : G.Dart → Prop) (x y : G.Dart) : Prop :=
  ∃ x' y' : G.Dart,
    PermReachable G.face x x' ∧
      PermReachable G.face y y' ∧
        A (G.edge x') ∧
          PermReachable G.face (G.edge x') (G.edge y')

/-- Coq `radius2`: some selected face is radius-two adjacent to every selected
face. -/
def RadiusTwo (A : G.Dart → Prop) : Prop :=
  ∃ x : G.Dart, A x ∧ ∀ y : G.Dart, A y → G.AtRadiusTwo A x y

variable {G}

theorem AtRadiusTwo.of_faceReachable_left
    {A : G.Dart → Prop} {x x' y : G.Dart}
    (hxx' : PermReachable G.face x x')
    (hxy : G.AtRadiusTwo A x' y) :
    G.AtRadiusTwo A x y := by
  rcases hxy with ⟨u, v, hx'u, hyv, hAu, huv⟩
  exact ⟨u, v, PermReachable.trans G.face hxx' hx'u, hyv, hAu, huv⟩

theorem AtRadiusTwo.of_faceReachable_right
    {A : G.Dart → Prop} {x y y' : G.Dart}
    (hxy : G.AtRadiusTwo A x y)
    (hyy' : PermReachable G.face y y') :
    G.AtRadiusTwo A x y' := by
  rcases hxy with ⟨u, v, hxu, hyv, hAu, huv⟩
  exact ⟨u, v, hxu,
    PermReachable.trans G.face (PermReachable.symm G.face hyy') hyv, hAu, huv⟩

theorem AtRadiusTwo.of_ringAdj_chain
    {A : G.Dart → Prop}
    (hPlain : G.Plain)
    (hAface :
      ∀ ⦃u v : G.Dart⦄, A u → PermReachable G.face u v → A v)
    {center x y : G.Dart}
    (hy : A y)
    (hxy : G.RingAdj x y)
    (hyc : G.RingAdj y center) :
    G.AtRadiusTwo A center x := by
  rcases hxy with ⟨z, hxz, hzy⟩
  rcases hyc with ⟨t, hyt, htc⟩
  refine ⟨G.edge t, z, ?_, hxz, ?_, ?_⟩
  · exact PermReachable.symm G.face htc
  · have hAt : A t := hAface hy hyt
    simpa [hPlain t |>.1] using hAt
  · have hzt : PermReachable G.face (G.edge z) t :=
      PermReachable.trans G.face hzy hyt
    simpa [hPlain t |>.1] using PermReachable.symm G.face hzt

theorem GoodRingArity.bounds
    {x : G.Dart}
    (hx : G.GoodRingArity x) :
    3 ≤ G.arity x ∧ G.arity x ≤ 6 := by
  rcases hx with h | h | h | h <;> omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
