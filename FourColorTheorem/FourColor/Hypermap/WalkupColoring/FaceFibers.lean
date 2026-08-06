
import Schematic.Math.GraphTheory.Embedding.Coloring
import Schematic.Math.GraphTheory.Embedding.WalkupGeometry

/-!
Colouring transport facts for Walkup deletions.

These are the coloring-facing forms of the `fconnect_skip` facts used in
Coq's `minimal_counter_example_is_cubic`: after one or two `WalkupE`
deletions, face and node reachability of projected darts is exactly the
original reachability relation, so colour constancy along those orbits can be
used without re-expanding the skip construction.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

theorem Coloring.eq_of_walkupE_face_project_reachable
    {z : G.Dart} {k : (G.walkupE z).Dart → Color}
    (hk : (G.walkupE z).Coloring k)
    {x y : (G.walkupE z).Dart}
    (hxy : PermReachable G.face x.1 y.1) :
    k y = k x :=
  Coloring.eq_of_face_reachable (G := G.walkupE z) hk
    (G.walkupE_facePermReachable_iff.mpr hxy)

theorem Coloring.eq_of_walkupE_walkupE_face_project_reachable
    {z : G.Dart} {u : (G.walkupE z).Dart}
    {k : ((G.walkupE z).walkupE u).Dart → Color}
    (hk : ((G.walkupE z).walkupE u).Coloring k)
    {x y : ((G.walkupE z).walkupE u).Dart}
    (hxy : PermReachable G.face x.1.1 y.1.1) :
    k y = k x :=
  Coloring.eq_of_face_reachable (G := (G.walkupE z).walkupE u) hk
    (G.walkupE_walkupE_facePermReachable_iff.mpr hxy)

theorem GraphColoring.eq_of_walkupE_node_project_reachable
    {z : G.Dart} {k : (G.walkupE z).Dart → Color}
    (hk : (G.walkupE z).GraphColoring k)
    {x y : (G.walkupE z).Dart}
    (hxy : PermReachable G.node x.1 y.1) :
    k y = k x :=
  GraphColoring.eq_of_node_reachable (G := G.walkupE z) hk
    (G.walkupE_nodePermReachable_iff.mpr hxy)

theorem GraphColoring.eq_of_walkupE_walkupE_node_project_reachable
    {z : G.Dart} {u : (G.walkupE z).Dart}
    {k : ((G.walkupE z).walkupE u).Dart → Color}
    (hk : ((G.walkupE z).walkupE u).GraphColoring k)
    {x y : ((G.walkupE z).walkupE u).Dart}
    (hxy : PermReachable G.node x.1.1 y.1.1) :
    k y = k x :=
  GraphColoring.eq_of_node_reachable (G := (G.walkupE z).walkupE u) hk
    (G.walkupE_walkupE_nodePermReachable_iff.mpr hxy)

/-- Lift an original dart outside the two deleted darts into a twice-deleted
`WalkupE` map. -/
def walkupE_walkupE_lift
    {z : G.Dart} (u : (G.walkupE z).Dart)
    (x : G.Dart) (hxz : x ≠ z) (hxu : x ≠ u.1) :
    ((G.walkupE z).walkupE u).Dart :=
  ⟨⟨x, hxz⟩, by
    intro hx
    exact hxu (congrArg Subtype.val hx)⟩

@[simp]
theorem walkupE_walkupE_lift_coe
    {z : G.Dart} (u : (G.walkupE z).Dart)
    (x : G.Dart) (hxz : x ≠ z) (hxu : x ≠ u.1) :
    (G.walkupE_walkupE_lift u x hxz hxu).1.1 = x :=
  rfl

/-- Lift outside `z` and `node z`, the pair deleted in the cubicity proof. -/
def walkupE_walkupE_liftTwoNode
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (x : G.Dart) (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart :=
  G.walkupE_walkupE_lift
    (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart) x hxz hxnode

@[simp]
theorem walkupE_walkupE_liftTwoNode_coe
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (x : G.Dart) (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    (G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode).1.1 = x :=
  rfl

/-- The original face orbit of `x`, restricted to the two-node deleted
Walkup map.  This is the Prop-valued analogue of the `a'` predicate in Coq's
`minimal_counter_example_is_cubic` proof. -/
def walkupE_walkupE_twoNodeFaceFiber
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (x : G.Dart)
    (w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart) : Prop :=
  PermReachable G.face x w.1.1

theorem walkupE_walkupE_twoNodeFaceFiber_nonempty_of_ne
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    ∃ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
      G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w := by
  refine ⟨G.walkupE_walkupE_liftTwoNode hz_ne x hxz hxnode, ?_⟩
  exact PermReachable.refl G.face x

theorem walkupE_walkupE_twoNodeFaceFiber_deleted_or
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    (hempty : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w) :
    x = z ∨ x = G.node z := by
  by_cases hxz : x = z
  · exact Or.inl hxz
  · by_cases hxnode : x = G.node z
    · exact Or.inr hxnode
    · exfalso
      rcases G.walkupE_walkupE_twoNodeFaceFiber_nonempty_of_ne
        hz_ne hxz hxnode with ⟨w, hw⟩
      exact hempty w hw

theorem walkupE_walkupE_twoNodeFaceFiber_target_deleted_or_of_reachable
    {z x y : G.Dart} (hz_ne : G.node z ≠ z)
    (hempty : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w)
    (hxy : PermReachable G.face x y) :
    y = z ∨ y = G.node z := by
  apply G.walkupE_walkupE_twoNodeFaceFiber_deleted_or hz_ne
  intro w hyw
  exact hempty w (PermReachable.trans G.face hxy hyw)

theorem walkupE_walkupE_twoNodeFaceFiber_eq_of_empty_of_reachable
    (hG : G.Bridgeless)
    {z x y : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (hempty : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w)
    (hxy : PermReachable G.face x y) :
    x = y := by
  have hxdel :
      x = z ∨ x = G.node z :=
    G.walkupE_walkupE_twoNodeFaceFiber_deleted_or hz_ne hempty
  have hydel :
      y = z ∨ y = G.node z :=
    G.walkupE_walkupE_twoNodeFaceFiber_target_deleted_or_of_reachable
      hz_ne hempty hxy
  rcases hxdel with hx | hx
  · rcases hydel with hy | hy
    · exact hx.trans hy.symm
    · exfalso
      subst x
      subst y
      exact Bridgeless.not_faceReachable_node (G := G) hG z hxy
  · rcases hydel with hy | hy
    · exfalso
      subst x
      subst y
      have hbad : PermReachable G.face (G.node z) (G.node (G.node z)) := by
        simpa [hzz] using hxy
      exact Bridgeless.not_faceReachable_node (G := G) hG (G.node z) hbad
    · exact hx.trans hy.symm

/-- Extend a twice-deleted colouring by selecting the colour of an arbitrary
surviving dart in the same original face orbit.  When the face orbit is
entirely deleted, use the supplied fallback. -/
noncomputable def walkupE_walkupE_faceClassColor
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (fallback : G.Dart → Color) (x : G.Dart) : Color :=
  by
    classical
    exact if h : ∃ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w then
      k (Classical.choose h)
    else
      fallback x

/-- Coq's default colour choice for the two deleted darts, expressed with the
Lean colour constructors: `z` gets `Color.one`, all other empty face classes
get `Color.zero`. -/
def walkupE_walkupE_twoNodeFallback
    (z x : G.Dart) : Color :=
  Color.cons false (decide (x = z))

@[simp]
theorem walkupE_walkupE_twoNodeFallback_self
    (z : G.Dart) :
    G.walkupE_walkupE_twoNodeFallback z z = Color.one := by
  simp [walkupE_walkupE_twoNodeFallback]
  rfl

theorem walkupE_walkupE_twoNodeFallback_node
    {z : G.Dart} (hz_ne : G.node z ≠ z) :
    G.walkupE_walkupE_twoNodeFallback z (G.node z) = Color.zero := by
  simp [walkupE_walkupE_twoNodeFallback, hz_ne]
  rfl

theorem walkupE_walkupE_twoNodeFallback_self_ne_node
    {z : G.Dart} (hz_ne : G.node z ≠ z) :
    G.walkupE_walkupE_twoNodeFallback z z ≠
      G.walkupE_walkupE_twoNodeFallback z (G.node z) := by
  simp [G.walkupE_walkupE_twoNodeFallback_node hz_ne]

theorem walkupE_walkupE_faceClassColor_eq_fallback_of_empty
    {z x : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (fallback : G.Dart → Color)
    (hempty : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w) :
    G.walkupE_walkupE_faceClassColor hz_ne k fallback x = fallback x := by
  classical
  have hnot : ¬ ∃ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        G.walkupE_walkupE_twoNodeFaceFiber hz_ne x w := by
    rintro ⟨w, hw⟩
    exact hempty w hw
  simp [walkupE_walkupE_faceClassColor, hnot]

theorem walkupE_walkupE_faceClassColor_twoNodeFallback_self_ne_node_of_empty
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (k : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart → Color)
    (hempty_z : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne z w)
    (hempty_node : ∀ w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart,
        ¬ G.walkupE_walkupE_twoNodeFaceFiber hz_ne (G.node z) w) :
    G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) z ≠
      G.walkupE_walkupE_faceClassColor hz_ne k
        (G.walkupE_walkupE_twoNodeFallback z) (G.node z) := by
  rw [G.walkupE_walkupE_faceClassColor_eq_fallback_of_empty
      hz_ne k (G.walkupE_walkupE_twoNodeFallback z) hempty_z,
    G.walkupE_walkupE_faceClassColor_eq_fallback_of_empty
      hz_ne k (G.walkupE_walkupE_twoNodeFallback z) hempty_node]
  exact G.walkupE_walkupE_twoNodeFallback_self_ne_node hz_ne

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
