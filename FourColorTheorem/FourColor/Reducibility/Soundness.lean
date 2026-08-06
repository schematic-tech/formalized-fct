
import FourColorTheorem.FourColor.Coloring.Kempe
import FourColorTheorem.FourColor.Coloring.RingTrace

/-!
Contract reducibility interface.

This ports the statement layer around `valid_contract` and `C_reducible` from
Gonthier's `coloring.v`.  The computational certificate checker will later
prove these predicates for the 633 configurations.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Face-orbit form of Coq `triad`: a center has at least three distinct
adjacent faces represented in the boundary set, but is not adjacent to every
boundary face.  Under the surrounding `Sparse` hypothesis this is the
semantic form extracted from Coq's incidence count. -/
def TriadFor (p : Finset G.Dart) (x : G.Dart) : Prop :=
  (∃ a ∈ p, ∃ b ∈ p, ∃ c ∈ p,
    ¬ PermReachable G.face a b ∧
      ¬ PermReachable G.face a c ∧
        ¬ PermReachable G.face b c ∧
      G.RingAdj x a ∧ G.RingAdj x b ∧ G.RingAdj x c) ∧
    ∃ y ∈ p, ¬ G.RingAdj x y

/-- A finite set has a triad. -/
def HasTriad (p : Finset G.Dart) : Prop :=
  ∃ x : G.Dart, G.TriadFor p x

/-- A finite set of darts is node-sparse: no two distinct selected darts lie in
the same node orbit. -/
def Sparse (p : Finset G.Dart) : Prop :=
  ∀ ⦃x y : G.Dart⦄,
    x ∈ p → y ∈ p → PermReachable G.node x y → x = y

/-- The contract closure is disjoint from the ring. -/
def ContractOffRing (r : List G.Dart) (cc : Finset G.Dart) : Prop :=
  ∀ ⦃x : G.Dart⦄, x ∈ r → x ∉ G.contractClosure cc

/-- Valid contracts are small, off-ring, sparse after edge closure, and have a
triad when they contain four selected contract darts. -/
structure ValidContract (r : List G.Dart) (cc : Finset G.Dart) : Prop where
  offRing : G.ContractOffRing r cc
  sparse : G.Sparse (G.contractClosure cc)
  size_pos : 0 < cc.card
  size_le_four : cc.card ≤ 4
  triad_of_card_four : cc.card = 4 →
    ∃ x : G.Dart, G.Kernel r x ∧
      G.TriadFor (G.contractClosure cc) x

/-- Configuration reducibility for a ring and contract: every contract trace on
the reversed ring belongs to the Kempe co-closure of ordinary ring traces on
that reversed ring. -/
structure CReducible (r : List G.Dart) (cc : Finset G.Dart) : Prop where
  valid : G.ValidContract r cc
  closure :
    ∀ et : ColSeq,
      G.ContractRingTrace cc r.reverse et →
        Chromogram.KempeCoclosure (G.RingTrace r.reverse) et

namespace ValidContract

theorem not_mem_contractClosure_of_mem_ring
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    x ∉ G.contractClosure cc :=
  hvalid.offRing hx

theorem not_mem_contract_of_mem_ring
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    x ∉ cc := by
  intro hcc
  exact hvalid.offRing hx (G.mem_contractClosure_self hcc)

theorem edge_not_mem_contractClosure_of_mem_ring
    (hplain : G.Plain)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    G.edge x ∉ G.contractClosure cc := by
  intro hedge
  exact hvalid.offRing hx
    ((G.contractClosure_edge_mem_iff_of_plain hplain).1 hedge)

theorem edge_not_mem_contract_of_mem_ring
    (hplain : G.Plain)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    G.edge x ∉ cc := by
  intro hcc
  exact edge_not_mem_contractClosure_of_mem_ring
    (G := G) hplain hvalid hx (G.mem_contractClosure_self hcc)

theorem eq_of_mem_contractClosure_of_node_reachable
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    {x y : G.Dart}
    (hx : x ∈ G.contractClosure cc)
    (hy : y ∈ G.contractClosure cc)
    (hxy : PermReachable G.node x y) :
    x = y :=
  hvalid.sparse hx hy hxy

theorem size_le_three_of_card_ne_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    (hfour : cc.card ≠ 4) :
    cc.card ≤ 3 := by
  have hlt : cc.card < 4 :=
    Nat.lt_of_le_of_ne hvalid.size_le_four hfour
  exact Nat.le_of_lt_succ hlt

theorem size_eq_four_or_le_three
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc) :
    cc.card = 4 ∨ cc.card ≤ 3 := by
  by_cases hfour : cc.card = 4
  · exact Or.inl hfour
  · exact Or.inr (size_le_three_of_card_ne_four
      (G := G) hvalid hfour)

theorem hasTriad_of_card_ge_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc)
    (hge : 4 ≤ cc.card) :
    G.HasTriad (G.contractClosure cc) := by
  have hcard : cc.card = 4 :=
    Nat.le_antisymm hvalid.size_le_four hge
  rcases hvalid.triad_of_card_four hcard with ⟨x, _hxKernel, hx⟩
  exact ⟨x, hx⟩

end ValidContract

namespace Iso

universe u

variable {G H : Hypermap.{u}} (φ : Iso G H)

theorem ringAdj_map
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    H.RingAdj (φ.toEquiv x) (φ.toEquiv y) := by
  rcases hxy with ⟨z, hxz, hzy⟩
  refine ⟨φ.toEquiv z, ?_, ?_⟩
  · exact (φ.faceReachable_iff).mp hxz
  · have hmap := (φ.faceReachable_iff).mp hzy
    simpa [φ.map_edge z] using hmap

theorem ringAdj_iff
    {x y : G.Dart} :
    H.RingAdj (φ.toEquiv x) (φ.toEquiv y) ↔ G.RingAdj x y := by
  constructor
  · intro hxy
    have hback := φ.symm.ringAdj_map hxy
    simpa [Iso.symm] using hback
  · exact φ.ringAdj_map

theorem sparse_contractClosure_image
    {cc : Finset G.Dart}
    (hsparse : G.Sparse (G.contractClosure cc)) :
    H.Sparse (H.contractClosure (cc.image φ.toEquiv)) := by
  intro y z hy hz hyz
  have hyG :
      φ.toEquiv.symm y ∈ G.contractClosure cc :=
    (φ.mem_contractClosure_image_iff cc y).1 hy
  have hzG :
      φ.toEquiv.symm z ∈ G.contractClosure cc :=
    (φ.mem_contractClosure_image_iff cc z).1 hz
  have hyzG :
      PermReachable G.node (φ.toEquiv.symm y) (φ.toEquiv.symm z) :=
    (φ.symm.nodeReachable_iff).mp hyz
  have hEq := hsparse hyG hzG hyzG
  exact φ.toEquiv.symm.injective hEq

theorem contractOffRing_image
    {r : List G.Dart} {cc : Finset G.Dart}
    (hoff : G.ContractOffRing r cc) :
    H.ContractOffRing (r.map φ.toEquiv) (cc.image φ.toEquiv) := by
  intro y hy hyc
  rcases List.mem_map.1 hy with ⟨x, hx, rfl⟩
  exact hoff hx (by
    have hx' :=
      (φ.mem_contractClosure_image_iff cc (φ.toEquiv x)).1
        (by simpa using hyc)
    simpa using hx')

theorem triadFor_contractClosure_image
    {cc : Finset G.Dart} {x : G.Dart}
    (htriad : G.TriadFor (G.contractClosure cc) x) :
    H.TriadFor (H.contractClosure (cc.image φ.toEquiv))
      (φ.toEquiv x) := by
  rcases htriad.1 with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hxa, hxb, hxc⟩
  rcases htriad.2 with ⟨y, hy, hxy⟩
  refine ⟨?_, ?_⟩
  · refine
      ⟨φ.toEquiv a,
        (φ.mem_contractClosure_image_iff cc (φ.toEquiv a)).2
          (by simpa using ha),
        φ.toEquiv b,
        (φ.mem_contractClosure_image_iff cc (φ.toEquiv b)).2
          (by simpa using hb),
        φ.toEquiv c,
        (φ.mem_contractClosure_image_iff cc (φ.toEquiv c)).2
          (by simpa using hc),
        ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hab ((φ.faceReachable_iff).mpr h)
    · intro h
      exact hac ((φ.faceReachable_iff).mpr h)
    · intro h
      exact hbc ((φ.faceReachable_iff).mpr h)
    · exact φ.ringAdj_map hxa
    · exact φ.ringAdj_map hxb
    · exact φ.ringAdj_map hxc
  · refine
      ⟨φ.toEquiv y,
        (φ.mem_contractClosure_image_iff cc (φ.toEquiv y)).2
          (by simpa using hy),
        ?_⟩
    intro hadj
    exact hxy ((φ.ringAdj_iff).1 hadj)

theorem hasTriad_contractClosure_image
    {cc : Finset G.Dart}
    (htriad : G.HasTriad (G.contractClosure cc)) :
    H.HasTriad (H.contractClosure (cc.image φ.toEquiv)) := by
  rcases htriad with ⟨x, hx⟩
  exact ⟨φ.toEquiv x, φ.triadFor_contractClosure_image hx⟩

theorem kernel_map
    {r : List G.Dart} {x : G.Dart}
    (hx : G.Kernel r x) :
    H.Kernel (r.map φ.toEquiv) (φ.toEquiv x) := by
  intro hxBand
  rcases hxBand with ⟨y, hy, hyx⟩
  rcases List.mem_map.1 hy with ⟨z, hz, rfl⟩
  exact hx ⟨z, hz, (φ.faceReachable_iff).mpr hyx⟩

theorem validContract_image
    {r : List G.Dart} {cc : Finset G.Dart}
    (hvalid : G.ValidContract r cc) :
    H.ValidContract (r.map φ.toEquiv) (cc.image φ.toEquiv) where
  offRing := φ.contractOffRing_image hvalid.offRing
  sparse := φ.sparse_contractClosure_image hvalid.sparse
  size_pos := by
    rw [Finset.card_image_of_injective _ φ.toEquiv.injective]
    exact hvalid.size_pos
  size_le_four := by
    rw [Finset.card_image_of_injective _ φ.toEquiv.injective]
    exact hvalid.size_le_four
  triad_of_card_four := by
    intro hcard
    have hcardG : cc.card = 4 := by
      rwa [Finset.card_image_of_injective _ φ.toEquiv.injective] at hcard
    rcases hvalid.triad_of_card_four hcardG with
      ⟨x, hxKernel, hxTriad⟩
    exact ⟨φ.toEquiv x, φ.kernel_map hxKernel,
      φ.triadFor_contractClosure_image hxTriad⟩

theorem validContract_image_iff
    {r : List G.Dart} {cc : Finset G.Dart} :
    H.ValidContract (r.map φ.toEquiv) (cc.image φ.toEquiv) ↔
      G.ValidContract r cc := by
  constructor
  · intro hvalid
    have hback := φ.symm.validContract_image hvalid
    convert hback using 1
    · symm
      simp [List.map_map, Iso.symm]
    · ext x
      constructor
      · intro hx
        refine Finset.mem_image.2
          ⟨φ.toEquiv x, Finset.mem_image.2 ⟨x, hx, rfl⟩, by
            simp [Iso.symm]⟩
      · intro hx
        rcases Finset.mem_image.1 hx with ⟨y, hy, hyx⟩
        rcases Finset.mem_image.1 hy with ⟨z, hz, rfl⟩
        have hzx : z = x := by
          simpa [Iso.symm] using hyx
        simpa [← hzx] using hz
  · exact φ.validContract_image

end Iso

namespace CReducible

universe u

variable {G : Hypermap.{u}}

theorem validContract
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc) :
    G.ValidContract r cc :=
  hred.valid

theorem contract_size_le_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc) :
    cc.card ≤ 4 :=
  hred.valid.size_le_four

theorem not_mem_contractClosure_of_mem_ring
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    x ∉ G.contractClosure cc :=
  ValidContract.not_mem_contractClosure_of_mem_ring (G := G)
    hred.valid hx

theorem not_mem_contract_of_mem_ring
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    x ∉ cc :=
  ValidContract.not_mem_contract_of_mem_ring (G := G)
    hred.valid hx

theorem edge_not_mem_contractClosure_of_mem_ring
    (hplain : G.Plain)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    G.edge x ∉ G.contractClosure cc :=
  ValidContract.edge_not_mem_contractClosure_of_mem_ring (G := G)
    hplain hred.valid hx

theorem edge_not_mem_contract_of_mem_ring
    (hplain : G.Plain)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {x : G.Dart}
    (hx : x ∈ r) :
    G.edge x ∉ cc :=
  ValidContract.edge_not_mem_contract_of_mem_ring (G := G)
    hplain hred.valid hx

theorem eq_of_mem_contractClosure_of_node_reachable
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {x y : G.Dart}
    (hx : x ∈ G.contractClosure cc)
    (hy : y ∈ G.contractClosure cc)
    (hxy : PermReachable G.node x y) :
    x = y :=
  ValidContract.eq_of_mem_contractClosure_of_node_reachable (G := G)
    hred.valid hx hy hxy

theorem contract_size_le_three_of_card_ne_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    (hfour : cc.card ≠ 4) :
    cc.card ≤ 3 :=
  ValidContract.size_le_three_of_card_ne_four (G := G)
    hred.valid hfour

theorem contract_size_eq_four_or_le_three
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc) :
    cc.card = 4 ∨ cc.card ≤ 3 :=
  ValidContract.size_eq_four_or_le_three (G := G) hred.valid

theorem triad_of_contract_card_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    (hcard : cc.card = 4) :
    G.HasTriad (G.contractClosure cc) :=
  let ⟨x, _hxKernel, hx⟩ := hred.valid.triad_of_card_four hcard
  ⟨x, hx⟩

theorem triad_of_contract_card_ge_four
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    (hge : 4 ≤ cc.card) :
    G.HasTriad (G.contractClosure cc) :=
  ValidContract.hasTriad_of_card_ge_four (G := G) hred.valid hge

theorem contract_trace_coclosure
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    Chromogram.KempeCoclosure (G.RingTrace r.reverse) et :=
  hred.closure et htrace

theorem contract_trace_length
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    et.length = r.length := by
  rw [ContractRingTrace.length (G := G) htrace]
  simp

theorem contract_trace_etrace_length
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    (ColSeq.etrace et).length = r.length := by
  rw [ContractRingTrace.length_etrace (G := G) htrace]
  simp

theorem contract_trace_sum_zero
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    ColSeq.sum et = Color.zero :=
  ContractRingTrace.sum_zero (G := G) htrace

theorem contract_trace_etrace_sum_zero
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    ColSeq.sum (ColSeq.etrace et) = Color.zero :=
  ContractRingTrace.sum_zero (G := G)
    (ContractRingTrace.etrace (G := G) htrace)

theorem contract_trace_etrace_coclosure
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {et : ColSeq}
    (htrace : G.ContractRingTrace cc r.reverse et) :
    Chromogram.KempeCoclosure
      (G.RingTrace r.reverse) (ColSeq.etrace et) :=
  hred.closure (ColSeq.etrace et)
    (ContractRingTrace.etrace (G := G) htrace)

theorem contract_trace_map_coclosure
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {et : ColSeq}
    (htrace :
      H.ContractRingTrace (cc.image φ.toEquiv)
        (r.map φ.toEquiv).reverse et) :
    Chromogram.KempeCoclosure
      (H.RingTrace (r.map φ.toEquiv).reverse) et := by
  have htraceG : G.ContractRingTrace cc r.reverse et := by
    have htrace' :
        H.ContractRingTrace (cc.image φ.toEquiv)
          (r.reverse.map φ.toEquiv) et := by
      simpa [List.map_reverse] using htrace
    exact φ.contractRingTrace_of_map htrace'
  exact Chromogram.KempeCoclosure.mono
    (P := G.RingTrace r.reverse)
    (Q := H.RingTrace (r.map φ.toEquiv).reverse)
    (fun et hring => by
      have hmap :
          H.RingTrace (r.reverse.map φ.toEquiv) et :=
        φ.ringTrace_map hring
      simpa [List.map_reverse] using hmap)
    (contract_trace_coclosure (G := G) hred htraceG)

theorem contract_trace_map_length
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace :
      H.ContractRingTrace (cc.image φ.toEquiv)
        (r.map φ.toEquiv).reverse et) :
    et.length = r.length := by
  rw [ContractRingTrace.length (G := H) htrace]
  simp

theorem contract_trace_map_etrace_length
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart}
    {et : ColSeq}
    (htrace :
      H.ContractRingTrace (cc.image φ.toEquiv)
        (r.map φ.toEquiv).reverse et) :
    (ColSeq.etrace et).length = r.length := by
  rw [ContractRingTrace.length_etrace (G := H) htrace]
  simp

theorem contract_trace_map_etrace_coclosure
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc)
    {et : ColSeq}
    (htrace :
      H.ContractRingTrace (cc.image φ.toEquiv)
        (r.map φ.toEquiv).reverse et) :
    Chromogram.KempeCoclosure
      (H.RingTrace (r.map φ.toEquiv).reverse) (ColSeq.etrace et) :=
  contract_trace_map_coclosure (G := G) φ hred
    (ContractRingTrace.etrace (G := H) htrace)

theorem map
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart}
    (hred : G.CReducible r cc) :
    H.CReducible (r.map φ.toEquiv) (cc.image φ.toEquiv) where
  valid := φ.validContract_image hred.valid
  closure := by
    intro et htrace
    exact contract_trace_map_coclosure (G := G) (H := H) φ hred htrace

theorem map_iff
    {H : Hypermap.{u}} (φ : Iso G H)
    {r : List G.Dart} {cc : Finset G.Dart} :
    H.CReducible (r.map φ.toEquiv) (cc.image φ.toEquiv) ↔
      G.CReducible r cc := by
  constructor
  · intro hred
    have hback := map (G := H) (H := G) φ.symm hred
    convert hback using 1
    · symm
      simp [List.map_map, Iso.symm]
    · ext x
      constructor
      · intro hx
        refine Finset.mem_image.2
          ⟨φ.toEquiv x, Finset.mem_image.2 ⟨x, hx, rfl⟩, by
            simp [Iso.symm]⟩
      · intro hx
        rcases Finset.mem_image.1 hx with ⟨y, hy, hyx⟩
        rcases Finset.mem_image.1 hy with ⟨z, hz, rfl⟩
        have hzx : z = x := by
          simpa [Iso.symm] using hyx
        simpa [← hzx] using hz
  · exact map (G := G) (H := H) φ

end CReducible

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
