
import FourColorTheorem.FourColor.Reducibility.Contract
import Schematic.Math.GraphTheory.Embedding.Trace

/-!
Ring traces for map and contract colourings.

This corresponds to the `ring_trace` and `cc_ring_trace` predicates from
Gonthier's `coloring.v`.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- The colour sequence obtained by reading a colouring along a dart list. -/
def colorsOn (k : G.Dart → Color) (r : List G.Dart) : ColSeq :=
  r.map k

theorem length_colorsOn
    (k : G.Dart → Color) (r : List G.Dart) :
    (G.colorsOn k r).length = r.length := by
  simp [colorsOn]

/-- A ring trace witnessed by an ordinary map colouring. -/
def RingTrace (r : List G.Dart) (et : ColSeq) : Prop :=
  ∃ k : G.Dart → Color,
    G.Coloring k ∧ et = ColSeq.trace (G.colorsOn k r)

/-- A ring trace witnessed by a contract colouring. -/
def ContractRingTrace
    (cc : Finset G.Dart) (r : List G.Dart) (et : ColSeq) : Prop :=
  ∃ k : G.Dart → Color,
    G.ContractColoring cc k ∧ et = ColSeq.trace (G.colorsOn k r)

instance ringTraceDecidable
    (r : List G.Dart) (et : ColSeq) :
    Decidable (G.RingTrace r et) := by
  unfold RingTrace
  infer_instance

instance contractRingTraceDecidable
    (cc : Finset G.Dart) (r : List G.Dart) (et : ColSeq) :
    Decidable (G.ContractRingTrace cc r et) := by
  unfold ContractRingTrace
  infer_instance

theorem RingTrace.fourColorable
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    G.FourColorable := by
  rcases htrace with ⟨k, hk, _⟩
  exact ⟨k, hk⟩

theorem RingTrace.exists_coloring
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    ∃ k : G.Dart → Color, G.Coloring k ∧ ColSeq.trace (G.colorsOn k r) = et :=
  by
    rcases htrace with ⟨k, hk, htrace⟩
    exact ⟨k, hk, htrace.symm⟩

theorem ContractRingTrace.contractColorable
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    G.ContractColorable cc := by
  rcases htrace with ⟨k, hk, _⟩
  exact ⟨k, hk⟩

theorem ContractRingTrace.exists_coloring
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    ∃ k : G.Dart → Color,
      G.ContractColoring cc k ∧ ColSeq.trace (G.colorsOn k r) = et :=
  by
    rcases htrace with ⟨k, hk, htrace⟩
    exact ⟨k, hk, htrace.symm⟩

theorem RingTrace.perm
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et)
    (g : EdgePerm) :
    G.RingTrace r (ColSeq.perm g et) := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨g ∘ k, G.coloring_of_injective_color_map (EdgePerm.injective g) hk, ?_⟩
  rw [← ColSeq.perm_trace]
  simp [colorsOn]

/-- Reversing the boundary reverses its cyclic trace and rotates it once.
This is the ring-trace form of Coq `trace_rev`. -/
theorem RingTrace.reverse_boundary
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    G.RingTrace r.reverse (ColSeq.rot1 et.reverse) := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  simp only [colorsOn, List.map_reverse, ColSeq.trace_reverse]

theorem ContractRingTrace.perm
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et)
    (g : EdgePerm) :
    G.ContractRingTrace cc r (ColSeq.perm g et) := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine
    ⟨g ∘ k,
      G.contractColoring_of_injective_color_map (EdgePerm.injective g) hk, ?_⟩
  rw [← ColSeq.perm_trace]
  simp [colorsOn]

theorem RingTrace.perm_iff
    (g : EdgePerm) {r : List G.Dart} {et : ColSeq} :
    G.RingTrace r (ColSeq.perm g et) ↔ G.RingTrace r et := by
  constructor
  · intro htrace
    have htrace' := RingTrace.perm (G := G) htrace (EdgePerm.inv g)
    simpa [ColSeq.perm_inv] using htrace'
  · intro htrace
    exact RingTrace.perm (G := G) htrace g

theorem ContractRingTrace.perm_iff
    (g : EdgePerm) {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq} :
    G.ContractRingTrace cc r (ColSeq.perm g et) ↔
      G.ContractRingTrace cc r et := by
  constructor
  · intro htrace
    have htrace' :=
      ContractRingTrace.perm (G := G) htrace (EdgePerm.inv g)
    simpa [ColSeq.perm_inv] using htrace'
  · intro htrace
    exact ContractRingTrace.perm (G := G) htrace g

theorem RingTrace.etrace
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    G.RingTrace r (ColSeq.etrace et) := by
  simpa [ColSeq.etrace] using
    (RingTrace.perm (G := G) htrace (ColSeq.etracePerm et))

theorem ContractRingTrace.etrace
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    G.ContractRingTrace cc r (ColSeq.etrace et) := by
  simpa [ColSeq.etrace] using
    (ContractRingTrace.perm (G := G) htrace (ColSeq.etracePerm et))

theorem RingTrace.etrace_iff
    {r : List G.Dart} {et : ColSeq} :
    G.RingTrace r (ColSeq.etrace et) ↔ G.RingTrace r et := by
  simpa [ColSeq.etrace] using
    (RingTrace.perm_iff (G := G) (ColSeq.etracePerm et)
      (r := r) (et := et))

theorem ContractRingTrace.etrace_iff
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq} :
    G.ContractRingTrace cc r (ColSeq.etrace et) ↔
      G.ContractRingTrace cc r et := by
  simpa [ColSeq.etrace] using
    (ContractRingTrace.perm_iff (G := G) (ColSeq.etracePerm et)
      (cc := cc) (r := r) (et := et))

theorem RingTrace.even_etrace
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    G.RingTrace r (ColSeq.etrace et) ∧
      ColSeq.evenTrace (ColSeq.etrace et) = true :=
  ⟨htrace.etrace, ColSeq.even_etrace et⟩

theorem ContractRingTrace.even_etrace
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    G.ContractRingTrace cc r (ColSeq.etrace et) ∧
      ColSeq.evenTrace (ColSeq.etrace et) = true :=
  ⟨htrace.etrace, ColSeq.even_etrace et⟩

theorem RingTrace.length
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    et.length = r.length := by
  rcases htrace with ⟨k, _hk, rfl⟩
  simp [ColSeq.length_trace, length_colorsOn]

theorem ContractRingTrace.length
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    et.length = r.length := by
  rcases htrace with ⟨k, _hk, rfl⟩
  simp [ColSeq.length_trace, length_colorsOn]

theorem RingTrace.sum_zero
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    ColSeq.sum et = Color.zero := by
  rcases htrace with ⟨k, _hk, rfl⟩
  exact ColSeq.sum_trace (G.colorsOn k r)

theorem ContractRingTrace.sum_zero
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    ColSeq.sum et = Color.zero := by
  rcases htrace with ⟨k, _hk, rfl⟩
  exact ColSeq.sum_trace (G.colorsOn k r)

theorem RingTrace.length_etrace
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    (ColSeq.etrace et).length = r.length := by
  rw [ColSeq.length_etrace, RingTrace.length (G := G) htrace]

theorem ContractRingTrace.length_etrace
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    (ColSeq.etrace et).length = r.length := by
  rw [ColSeq.length_etrace, ContractRingTrace.length (G := G) htrace]

theorem contractRingTrace_empty_iff
    (r : List G.Dart) (et : ColSeq) :
    G.ContractRingTrace ∅ r et ↔ G.RingTrace r et := by
  constructor
  · rintro ⟨k, hk, htrace⟩
    exact ⟨k, (G.contractColoring_empty_iff k).mp hk, htrace⟩
  · rintro ⟨k, hk, htrace⟩
    exact ⟨k, (G.contractColoring_empty_iff k).mpr hk, htrace⟩

namespace Iso

universe u

variable {G H : Hypermap.{u}} (φ : Iso G H)

theorem colorsOn_map
  (k : H.Dart → Color) (r : List G.Dart) :
    H.colorsOn k (r.map φ.toEquiv) =
      G.colorsOn (k ∘ φ.toEquiv) r := by
  simp [colorsOn, List.map_map]

theorem colorsOn_map_symm
    (k : G.Dart → Color) (r : List G.Dart) :
    H.colorsOn (k ∘ φ.toEquiv.symm) (r.map φ.toEquiv) =
      G.colorsOn k r := by
  simp [colorsOn, List.map_map, Function.comp]

theorem ringTrace_map
    {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    H.RingTrace (r.map φ.toEquiv) et := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k ∘ φ.toEquiv.symm, φ.symm.coloring_pull hk, ?_⟩
  rw [colorsOn_map_symm]

theorem ringTrace_of_map
    {r : List G.Dart} {et : ColSeq}
    (htrace : H.RingTrace (r.map φ.toEquiv) et) :
    G.RingTrace r et := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k ∘ φ.toEquiv, φ.coloring_pull hk, ?_⟩
  rw [colorsOn_map]

theorem ringTrace_map_iff
    (r : List G.Dart) (et : ColSeq) :
    H.RingTrace (r.map φ.toEquiv) et ↔ G.RingTrace r et := by
  constructor
  · exact φ.ringTrace_of_map
  · exact φ.ringTrace_map

theorem contractRingTrace_map
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace : G.ContractRingTrace cc r et) :
    H.ContractRingTrace (cc.image φ.toEquiv) (r.map φ.toEquiv) et := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k ∘ φ.toEquiv.symm, φ.contractColoring_image hk, ?_⟩
  rw [colorsOn_map_symm]

theorem contractRingTrace_of_map
    {cc : Finset G.Dart} {r : List G.Dart} {et : ColSeq}
    (htrace :
      H.ContractRingTrace (cc.image φ.toEquiv) (r.map φ.toEquiv) et) :
    G.ContractRingTrace cc r et := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k ∘ φ.toEquiv, ?_, ?_⟩
  · exact φ.contractColoring_of_image (by
      convert hk using 1
      funext y
      simp [Function.comp])
  · rw [colorsOn_map]

theorem contractRingTrace_map_iff
    (cc : Finset G.Dart) (r : List G.Dart) (et : ColSeq) :
    H.ContractRingTrace (cc.image φ.toEquiv) (r.map φ.toEquiv) et ↔
      G.ContractRingTrace cc r et := by
  constructor
  · exact φ.contractRingTrace_of_map
  · exact φ.contractRingTrace_map

end Iso

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
