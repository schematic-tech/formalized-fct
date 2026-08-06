import FourColorTheorem.FourColor.Reducibility.ProgramMap.Support

/-!
# Old-dart transport

Generic list and adjacency transport used by construction-map embeddings.
-/

namespace Schematic.Math.GraphTheory.FourColor

namespace OldDartTransport

theorem faceBand_map_iff
    {G : Hypermap} {H : Hypermap}
    (old : G.Dart → H.Dart)
    (hface : ∀ {x y : G.Dart},
      PermReachable H.face (old x) (old y) ↔
        PermReachable G.face x y)
    (r : List G.Dart) (x : G.Dart) :
    H.FaceBand (r.map old) (old x) ↔ G.FaceBand r x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact ⟨z, hz, hface.mp hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨old y, List.mem_map.mpr ⟨y, hy, rfl⟩, hface.mpr hyx⟩

theorem exists_mem_map_iff
    {α β : Type*} {R : β → β → Prop} {S : α → α → Prop}
    (old : α → β)
    (hrel : ∀ {x y : α}, R (old x) (old y) ↔ S x y)
    (r : List α) (x : α) :
    (∃ y : β, y ∈ r.map old ∧ R (old x) y) ↔
      ∃ y : α, y ∈ r ∧ S x y := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact ⟨z, hz, hrel.mp hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨old y, List.mem_map.mpr ⟨y, hy, rfl⟩, hrel.mpr hxy⟩

theorem exists_selectMask_map_iff
    {α β : Type*} {R : β → β → Prop} {S : α → α → Prop}
    (old : α → β)
    (hrel : ∀ {x y : α}, R (old x) (old y) ↔ S x y)
    (m : CfMask) (ring kernel : List α) (x : α) :
    (∃ y : β,
      y ∈ CfMask.selectMask m (ring.map old) (kernel.map old) ∧
        R (old x) y) ↔
      ∃ y : α,
        y ∈ CfMask.selectMask m ring kernel ∧ S x y := by
  rw [CfMask.selectMask_map]
  exact exists_mem_map_iff old hrel _ x

theorem liftFaceBandRingAdj
    {G : Hypermap} {H : Hypermap}
    (old : G.Dart → H.Dart)
    (hface : ∀ (r : List G.Dart) {x : G.Dart},
      H.FaceBand (r.map old) (old x) ↔ G.FaceBand r x)
    (hring : ∀ {x y : G.Dart},
      H.RingAdj (old x) (old y) ↔ G.RingAdj x y)
    {adj orig : List G.Dart}
    (hsound : ∀ x : G.Dart,
      G.FaceBand adj x ↔
        ∃ y : G.Dart, y ∈ orig ∧ G.RingAdj x y)
    {x : G.Dart} :
    H.FaceBand (adj.map old) (old x) ↔
      ∃ y : H.Dart, y ∈ orig.map old ∧ H.RingAdj (old x) y := by
  rw [hface, hsound]
  exact (exists_mem_map_iff old hring orig x).symm

end OldDartTransport

end Schematic.Math.GraphTheory.FourColor
