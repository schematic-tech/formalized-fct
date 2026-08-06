
import Schematic.Math.GraphTheory.Embedding.Coloring

/-!
Contract colourings for hypermaps.

This is the first Lean-side piece corresponding to the `cc_coloring` and
`cc_colorable` layer of Gonthier's `coloring.v`.  A contract is represented by
a finite set of selected darts; its edge closure contains those darts and their
edge mates.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Edge closure of a finite contract set: selected darts together with their
edge partners. -/
def contractClosure (cc : Finset G.Dart) : Finset G.Dart :=
  cc ∪ cc.image G.edge

theorem mem_contractClosure_self
    {cc : Finset G.Dart} {x : G.Dart}
    (hx : x ∈ cc) :
    x ∈ G.contractClosure cc := by
  exact Finset.mem_union_left _ hx

theorem mem_contractClosure_edge
    {cc : Finset G.Dart} {x : G.Dart}
    (hx : x ∈ cc) :
    G.edge x ∈ G.contractClosure cc := by
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)

theorem mem_contractClosure_iff
    {cc : Finset G.Dart} {x : G.Dart} :
    x ∈ G.contractClosure cc ↔
      x ∈ cc ∨ ∃ y ∈ cc, G.edge y = x := by
  constructor
  · intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl hx
    · rcases Finset.mem_image.1 hx with ⟨y, hy, hyx⟩
      exact Or.inr ⟨y, hy, hyx⟩
  · intro hx
    rcases hx with hx | ⟨y, hy, hyx⟩
    · exact G.mem_contractClosure_self hx
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hy, hyx⟩)

theorem mem_contractClosure_iff_self_or_edge_of_plain
    (hplain : G.Plain) {cc : Finset G.Dart} {x : G.Dart} :
    x ∈ G.contractClosure cc ↔ x ∈ cc ∨ G.edge x ∈ cc := by
  constructor
  · intro hx
    rcases (G.mem_contractClosure_iff).1 hx with hx | ⟨y, hy, hyx⟩
    · exact Or.inl hx
    · right
      have : G.edge x = y := by
        calc
          G.edge x = G.edge (G.edge y) := by rw [hyx]
          _ = y := Plain.edge_edge (G := G) hplain y
      simpa [this] using hy
  · rintro (hx | hedge)
    · exact G.mem_contractClosure_self hx
    · have := G.mem_contractClosure_edge hedge
      simpa [Plain.edge_edge (G := G) hplain x] using this

theorem subset_contractClosure
    (cc : Finset G.Dart) :
    cc ⊆ G.contractClosure cc := by
  intro x hx
  exact G.mem_contractClosure_self hx

theorem edge_image_subset_contractClosure
    (cc : Finset G.Dart) :
    cc.image G.edge ⊆ G.contractClosure cc := by
  intro x hx
  exact Finset.mem_union_right _ hx

theorem contractClosure_mono
    {cc dd : Finset G.Dart}
    (hcc : cc ⊆ dd) :
    G.contractClosure cc ⊆ G.contractClosure dd := by
  intro x hx
  rcases (G.mem_contractClosure_iff).1 hx with hx | ⟨y, hy, hyx⟩
  · exact G.mem_contractClosure_self (hcc hx)
  · have hmem : G.edge y ∈ G.contractClosure dd :=
      G.mem_contractClosure_edge (hcc hy)
    simpa [hyx] using hmem

theorem contractClosure_edge_mem_of_plain
    (hG : G.Plain)
    {cc : Finset G.Dart} {x : G.Dart}
    (hx : x ∈ G.contractClosure cc) :
    G.edge x ∈ G.contractClosure cc := by
  rcases Finset.mem_union.1 hx with hx | hx
  · exact G.mem_contractClosure_edge hx
  · rcases Finset.mem_image.1 hx with ⟨y, hy, hyx⟩
    exact G.mem_contractClosure_self (by
      rw [← hyx, (hG y).1]
      exact hy)

theorem contractClosure_edge_mem_iff_of_plain
    (hG : G.Plain)
    {cc : Finset G.Dart} {x : G.Dart} :
    G.edge x ∈ G.contractClosure cc ↔ x ∈ G.contractClosure cc := by
  constructor
  · intro hx
    have hxx : G.edge (G.edge x) ∈ G.contractClosure cc :=
      G.contractClosure_edge_mem_of_plain hG hx
    simpa [(hG x).1] using hxx
  · exact G.contractClosure_edge_mem_of_plain hG

theorem contractClosure_empty :
    G.contractClosure ∅ = ∅ := by
  ext x
  simp [contractClosure]

theorem not_mem_contractClosure_empty
    (x : G.Dart) :
    x ∉ G.contractClosure ∅ := by
  simp [contractClosure]

/-- A contract colouring: selected contract edges have equal colours, all other
edge-neighbours have distinct colours, and faces remain monochromatic. -/
def ContractColoring (cc : Finset G.Dart) (k : G.Dart → Color) : Prop :=
  (∀ x : G.Dart, x ∈ G.contractClosure cc → k (G.edge x) = k x) ∧
    (∀ x : G.Dart, x ∉ G.contractClosure cc → k (G.edge x) ≠ k x) ∧
      (∀ x : G.Dart, k (G.face x) = k x)

/-- A hypermap admits a colouring of the contract `cc`. -/
def ContractColorable (cc : Finset G.Dart) : Prop :=
  Exists fun k : G.Dart → Color => G.ContractColoring cc k

theorem contractColoring_of_injective_color_map
    {cc : Finset G.Dart}
    {k : G.Dart → Color}
    {f : Color → Color}
    (hf : Function.Injective f)
    (hk : G.ContractColoring cc k) :
    G.ContractColoring cc (f ∘ k) := by
  constructor
  · intro x hx
    exact congrArg f (hk.1 x hx)
  · constructor
    · intro x hx hsame
      exact hk.2.1 x hx (hf hsame)
    · intro x
      exact congrArg f (hk.2.2 x)

theorem ContractColoring.perm
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    (g : EdgePerm) :
    G.ContractColoring cc (g ∘ k) :=
  G.contractColoring_of_injective_color_map (EdgePerm.injective g) hk

theorem contractColoring_perm_iff
    {cc : Finset G.Dart}
    (g : EdgePerm) (k : G.Dart → Color) :
    G.ContractColoring cc (g ∘ k) ↔ G.ContractColoring cc k := by
  constructor
  · intro hk
    have h := G.contractColoring_of_injective_color_map
      (EdgePerm.injective (EdgePerm.inv g)) hk
    convert h using 1
    funext x
    simp [Function.comp]
  · intro hk
    exact ContractColoring.perm (G := G) hk g

instance contractColoringDecidable
    (cc : Finset G.Dart) (k : G.Dart → Color) :
    Decidable (G.ContractColoring cc k) := by
  unfold ContractColoring
  infer_instance

instance contractColorableDecidable
    (cc : Finset G.Dart) :
    Decidable (G.ContractColorable cc) := by
  unfold ContractColorable
  infer_instance

theorem ContractColoring.edge_eq
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    (x : G.Dart)
    (hx : x ∈ G.contractClosure cc) :
    k (G.edge x) = k x :=
  hk.1 x hx

theorem ContractColoring.edge_ne
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    (x : G.Dart)
    (hx : x ∉ G.contractClosure cc) :
    k (G.edge x) ≠ k x :=
  hk.2.1 x hx

theorem ContractColoring.face_eq
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    (x : G.Dart) :
    k (G.face x) = k x :=
  hk.2.2 x

theorem ContractColoring.eq_face
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    (x : G.Dart) :
    k x = k (G.face x) :=
  (ContractColoring.face_eq (G := G) hk x).symm

theorem contractColoring_empty_iff
    (k : G.Dart → Color) :
    G.ContractColoring ∅ k ↔ G.Coloring k := by
  constructor
  · intro hk
    constructor
    · intro x
      exact hk.2.1 x (G.not_mem_contractClosure_empty x)
    · exact hk.2.2
  · intro hk
    constructor
    · intro x hx
      simp [contractClosure] at hx
    · constructor
      · intro x _
        exact hk.1 x
      · exact hk.2

theorem contractColorable_empty_iff :
    G.ContractColorable ∅ ↔ G.FourColorable := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (G.contractColoring_empty_iff k).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (G.contractColoring_empty_iff k).mpr hk⟩

theorem ContractColoring.edge_eq_of_edge_mem_contractClosure
    (hG : G.Plain)
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart}
    (hx : G.edge x ∈ G.contractClosure cc) :
    k (G.edge x) = k x :=
  hk.1 x ((G.contractClosure_edge_mem_iff_of_plain hG).1 hx)

theorem ContractColoring.edge_ne_of_edge_not_mem_contractClosure
    (hG : G.Plain)
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart}
    (hx : G.edge x ∉ G.contractClosure cc) :
    k (G.edge x) ≠ k x := by
  exact hk.2.1 x (by
    intro hxmem
    exact hx ((G.contractClosure_edge_mem_iff_of_plain hG).2 hxmem))

theorem ContractColoring.eq_edge_of_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart}
    (hx : x ∈ G.contractClosure cc) :
    k x = k (G.edge x) :=
  (hk.1 x hx).symm

theorem ContractColoring.ne_edge_of_not_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart}
    (hx : x ∉ G.contractClosure cc) :
    k x ≠ k (G.edge x) := by
  intro h
  exact hk.2.1 x hx h.symm

theorem ContractColoring.edge_eq_iff_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart} :
    k (G.edge x) = k x ↔ x ∈ G.contractClosure cc := by
  constructor
  · intro h
    by_contra hx
    exact hk.2.1 x hx h
  · exact hk.1 x

theorem ContractColoring.edge_ne_iff_not_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart} :
    k (G.edge x) ≠ k x ↔ x ∉ G.contractClosure cc := by
  constructor
  · intro h hx
    exact h (hk.1 x hx)
  · exact hk.2.1 x

theorem ContractColoring.eq_edge_iff_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart} :
    k x = k (G.edge x) ↔ x ∈ G.contractClosure cc := by
  constructor
  · intro h
    exact (ContractColoring.edge_eq_iff_mem_contractClosure
      (G := G) hk).1 h.symm
  · intro hx
    exact (hk.1 x hx).symm

theorem ContractColoring.ne_edge_iff_not_mem_contractClosure
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x : G.Dart} :
    k x ≠ k (G.edge x) ↔ x ∉ G.contractClosure cc := by
  constructor
  · intro h hx
    exact h (hk.1 x hx).symm
  · intro hx
    exact ContractColoring.ne_edge_of_not_mem_contractClosure (G := G) hk hx

theorem ContractColoring.eq_of_face_link
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    k y = k x := by
  cases hxy with
  | forward => exact hk.2.2 x
  | backward =>
      have h := hk.2.2 (G.face.symm x)
      simpa using h.symm

theorem ContractColoring.eq_of_face_reachable
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k)
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    k y = k x := by
  induction hxy with
  | refl => rfl
  | tail hxb hbc ih =>
      exact (ContractColoring.eq_of_face_link (G := G) hk hbc).trans ih

namespace Iso

universe u

variable {G H : Hypermap.{u}} (φ : Iso G H)

theorem mem_image_iff_symm
    (s : Finset G.Dart) (y : H.Dart) :
    y ∈ s.image φ.toEquiv ↔ φ.toEquiv.symm y ∈ s := by
  constructor
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    simpa using hx
  · intro hx
    exact Finset.mem_image.2
      ⟨φ.toEquiv.symm y, hx, by simp⟩

theorem mem_contractClosure_image_iff
    (cc : Finset G.Dart) (y : H.Dart) :
    y ∈ H.contractClosure (cc.image φ.toEquiv) ↔
      φ.toEquiv.symm y ∈ G.contractClosure cc := by
  unfold contractClosure
  constructor
  · intro hy
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
      exact Or.inl (by simpa using hx)
    · rcases Finset.mem_image.1 hy with ⟨z, hz, hzedge⟩
      rcases Finset.mem_image.1 hz with ⟨x, hx, rfl⟩
      exact Or.inr (Finset.mem_image.2 ⟨x, hx, by
        have hyx : φ.toEquiv.symm y = G.edge x := by
          calc
            φ.toEquiv.symm y =
                φ.toEquiv.symm (H.edge (φ.toEquiv x)) := by rw [hzedge]
            _ = G.edge x := by
              simpa [Iso.symm] using φ.symm.map_edge (φ.toEquiv x)
        exact hyx.symm⟩)
  · intro hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Finset.mem_image.2 ⟨φ.toEquiv.symm y, hx, by simp⟩)
    · rcases Finset.mem_image.1 hx with ⟨x, hx, hxedge⟩
      exact Or.inr (Finset.mem_image.2
        ⟨φ.toEquiv x, Finset.mem_image.2 ⟨x, hx, rfl⟩, by
          calc
            H.edge (φ.toEquiv x) = φ.toEquiv (G.edge x) :=
              (φ.map_edge x).symm
            _ = y := by rw [hxedge]; simp⟩)

theorem contractClosure_image
    (cc : Finset G.Dart) :
    H.contractClosure (cc.image φ.toEquiv) =
      (G.contractClosure cc).image φ.toEquiv := by
  ext y
  rw [φ.mem_contractClosure_image_iff,
    φ.mem_image_iff_symm]

theorem contractColoring_image
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k) :
    H.ContractColoring (cc.image φ.toEquiv) (k ∘ φ.toEquiv.symm) := by
  constructor
  · intro y hy
    have hx :
        φ.toEquiv.symm y ∈ G.contractClosure cc :=
      (φ.mem_contractClosure_image_iff cc y).1 hy
    have h := hk.1 (φ.toEquiv.symm y) hx
    have hEdge :
        φ.toEquiv.symm (H.edge y) =
          G.edge (φ.toEquiv.symm y) := by
      simpa [Iso.symm] using φ.symm.map_edge y
    simpa [Function.comp, hEdge] using h
  · constructor
    · intro y hy hsame
      have hx :
          φ.toEquiv.symm y ∉ G.contractClosure cc := by
        intro hx
        exact hy ((φ.mem_contractClosure_image_iff cc y).2 hx)
      have hEdge :
          φ.toEquiv.symm (H.edge y) =
            G.edge (φ.toEquiv.symm y) := by
        simpa [Iso.symm] using φ.symm.map_edge y
      exact hk.2.1 (φ.toEquiv.symm y) hx (by
        simpa [Function.comp, hEdge] using hsame)
    · intro y
      have h := hk.2.2 (φ.toEquiv.symm y)
      have hFace :
          φ.toEquiv.symm (H.face y) =
            G.face (φ.toEquiv.symm y) := by
        simpa [Iso.symm] using φ.symm.map_face y
      simpa [Function.comp, hFace] using h

theorem contractColoring_of_image
    {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : H.ContractColoring (cc.image φ.toEquiv)
      (k ∘ φ.toEquiv.symm)) :
    G.ContractColoring cc k := by
  constructor
  · intro x hx
    have hy :
        φ.toEquiv x ∈ H.contractClosure (cc.image φ.toEquiv) := by
      exact (φ.mem_contractClosure_image_iff cc (φ.toEquiv x)).2
        (by simpa using hx)
    have h := hk.1 (φ.toEquiv x) hy
    have hEdge :
        φ.toEquiv.symm (H.edge (φ.toEquiv x)) = G.edge x := by
      simpa [Iso.symm] using φ.symm.map_edge (φ.toEquiv x)
    simpa [Function.comp, hEdge] using h
  · constructor
    · intro x hx hsame
      have hy :
          φ.toEquiv x ∉ H.contractClosure (cc.image φ.toEquiv) := by
        intro hy
        exact hx (by
          have hx' :=
            (φ.mem_contractClosure_image_iff cc (φ.toEquiv x)).1
              (by simpa using hy)
          simpa using hx')
      have hEdge :
          φ.toEquiv.symm (H.edge (φ.toEquiv x)) = G.edge x := by
        simpa [Iso.symm] using φ.symm.map_edge (φ.toEquiv x)
      exact hk.2.1 (φ.toEquiv x) hy (by
        simpa [Function.comp, hEdge] using hsame)
    · intro x
      have h := hk.2.2 (φ.toEquiv x)
      have hFace :
          φ.toEquiv.symm (H.face (φ.toEquiv x)) = G.face x := by
        simpa [Iso.symm] using φ.symm.map_face (φ.toEquiv x)
      simpa [Function.comp, hFace] using h

theorem contractColoring_image_iff
    (cc : Finset G.Dart) (k : G.Dart → Color) :
    H.ContractColoring (cc.image φ.toEquiv) (k ∘ φ.toEquiv.symm) ↔
      G.ContractColoring cc k := by
  constructor
  · exact φ.contractColoring_of_image
  · exact φ.contractColoring_image

theorem contractColorable_image
    {cc : Finset G.Dart}
    (hcolor : G.ContractColorable cc) :
    H.ContractColorable (cc.image φ.toEquiv) := by
  rcases hcolor with ⟨k, hk⟩
  exact ⟨k ∘ φ.toEquiv.symm, φ.contractColoring_image hk⟩

theorem contractColorable_of_image
    {cc : Finset G.Dart}
    (hcolor : H.ContractColorable (cc.image φ.toEquiv)) :
    G.ContractColorable cc := by
  rcases hcolor with ⟨k, hk⟩
  refine ⟨k ∘ φ.toEquiv, ?_⟩
  exact φ.contractColoring_of_image (by
    convert hk using 1
    funext y
    simp [Function.comp])

theorem contractColorable_image_iff
    (cc : Finset G.Dart) :
    H.ContractColorable (cc.image φ.toEquiv) ↔ G.ContractColorable cc := by
  constructor
  · exact φ.contractColorable_of_image
  · exact φ.contractColorable_image

end Iso

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
