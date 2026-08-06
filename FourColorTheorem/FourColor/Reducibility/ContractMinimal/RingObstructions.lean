
import FourColorTheorem.FourColor.Coloring.Birkhoff
import FourColorTheorem.FourColor.Reducibility.Soundness
import FourColorTheorem.FourColor.Hypermap.WalkupMinimal

/-!
Contract colourings in a minimal counterexample.

This ports `fourcolor-coq/theories/proof/contract.v`.  The central theorem is
Coq `contract_coloring`: every valid contract in a minimal counterexample has
a contract colouring.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

/-- Coq `contract_ring`: a proper simple ring whose tail is contained in the
edge closure of the selected contract. -/
structure ContractRing (G : Hypermap.{u}) (cc : Finset G.Dart)
    (p : List G.Dart) : Prop where
  cycle : G.SimpleRLinkCycle p
  proper : G.ProperRing p
  tail_contract : ∀ x : G.Dart, x ∈ p.tail → x ∈ G.contractClosure cc

namespace ContractRing

variable {G : Hypermap.{u}} {cc : Finset G.Dart} {p : List G.Dart}

private theorem exists_tailRepresentative
    (hp : G.ContractRing cc p)
    (y : {y : G.Dart // y ∈ p.tail}) :
    ∃ x : G.Dart, x ∈ cc ∧ (x = y.1 ∨ G.edge x = y.1) := by
  have hy := hp.tail_contract y.1 y.2
  rcases (G.mem_contractClosure_iff).1 hy with hy | ⟨x, hx, hxy⟩
  · exact ⟨y.1, hy, Or.inl rfl⟩
  · exact ⟨x, hx, Or.inr hxy⟩

private noncomputable def tailRepresentative
    (hp : G.ContractRing cc p)
    (y : {y : G.Dart // y ∈ p.tail}) : {x : G.Dart // x ∈ cc} :=
  ⟨Classical.choose (exists_tailRepresentative hp y),
    (Classical.choose_spec (exists_tailRepresentative hp y)).1⟩

private theorem tailRepresentative_eq_or_edge_eq
    (hp : G.ContractRing cc p)
    (y : {y : G.Dart // y ∈ p.tail}) :
    (tailRepresentative hp y).1 = y.1 ∨
      G.edge (tailRepresentative hp y).1 = y.1 := by
  exact (Classical.choose_spec (exists_tailRepresentative hp y)).2

private theorem tailRepresentative_injective
    (hplain : G.Plain)
    (hp : G.ContractRing cc p) :
    Function.Injective (tailRepresentative hp) := by
  intro y z hyz
  apply Subtype.ext
  have hy := tailRepresentative_eq_or_edge_eq hp y
  have hz := tailRepresentative_eq_or_edge_eq hp z
  have hrep : (tailRepresentative hp y).1 =
      (tailRepresentative hp z).1 := congrArg Subtype.val hyz
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact hy.symm.trans (hrep.trans hz)
  · have hyMem : y.1 ∈ p := List.mem_of_mem_tail y.2
    have hzMem : z.1 ∈ p := List.mem_of_mem_tail z.2
    exfalso
    have hedgeEq : G.edge y.1 = z.1 := by
      calc
      G.edge y.1 = G.edge (tailRepresentative hp y).1 := by rw [hy]
      _ = G.edge (tailRepresentative hp z).1 := by rw [hrep]
      _ = z.1 := hz
    exact False.elim
      ((hp.cycle.not_mem_edge_of_proper_plain (G := G) hplain hp.proper hyMem)
        (by rw [hedgeEq]; exact hzMem))
  · have hyMem : y.1 ∈ p := List.mem_of_mem_tail y.2
    have hzMem : z.1 ∈ p := List.mem_of_mem_tail z.2
    exfalso
    have hedgeEq : G.edge z.1 = y.1 := by
      calc
        G.edge z.1 = G.edge (tailRepresentative hp z).1 := by rw [hz]
        _ = G.edge (tailRepresentative hp y).1 := by rw [hrep]
        _ = y.1 := hy
    exact False.elim
      ((hp.cycle.not_mem_edge_of_proper_plain (G := G) hplain hp.proper hzMem)
        (by rw [hedgeEq]; exact hyMem))
  · exact hy.symm.trans ((congrArg G.edge hrep).trans hz)

/-- Coq `contract_ring_max`: every tail dart consumes a distinct selected
contract edge. -/
theorem length_le_card_add_one
    (hplain : G.Plain)
    (hp : G.ContractRing cc p) :
    p.length ≤ cc.card + 1 := by
  classical
  letI : Fintype {y : G.Dart // y ∈ p.tail} := Fintype.ofFinite _
  letI : Fintype {x : G.Dart // x ∈ cc} := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective
    (tailRepresentative hp) (tailRepresentative_injective hplain hp)
  have htailNodup : p.tail.Nodup := hp.cycle.faceSimple.nodup.tail
  have htailCard : Fintype.card {y : G.Dart // y ∈ p.tail} = p.tail.length := by
    calc
      Fintype.card {y : G.Dart // y ∈ p.tail} =
          Fintype.card {y : G.Dart // y ∈ p.tail.toFinset} :=
        Fintype.card_congr
          (Equiv.subtypeEquivRight (fun y : G.Dart => by simp))
      _ = p.tail.toFinset.card := Fintype.card_coe _
      _ = p.tail.length := List.toFinset_card_of_nodup htailNodup
  have hccCard : Fintype.card {x : G.Dart // x ∈ cc} = cc.card := by
    simp
  rw [htailCard, hccCard] at hcard
  cases p with
  | nil => simp
  | cons x xs =>
      simpa using Nat.add_le_add_right hcard 1

/-- Equality case of `contract_ring_max`: if the ring tail and selected
contract have the same size, every dart in the edge-closure of the contract
lies in the ring face band.  This is the finite-bijection content of the
rotation argument in Coq `triad_valid`. -/
theorem contractClosure_subset_faceBand_of_length_eq_card_add_one
    (hplain : G.Plain)
    (hp : G.ContractRing cc p)
    (hlength : p.length = cc.card + 1) :
    ∀ z : G.Dart, z ∈ G.contractClosure cc → G.FaceBand p z := by
  classical
  letI : Fintype {y : G.Dart // y ∈ p.tail} := Fintype.ofFinite _
  letI : Fintype {x : G.Dart // x ∈ cc} := Fintype.ofFinite _
  have htailNodup : p.tail.Nodup := hp.cycle.faceSimple.nodup.tail
  have htailCard :
      Fintype.card {y : G.Dart // y ∈ p.tail} = p.tail.length := by
    calc
      Fintype.card {y : G.Dart // y ∈ p.tail} =
          Fintype.card {y : G.Dart // y ∈ p.tail.toFinset} :=
        Fintype.card_congr
          (Equiv.subtypeEquivRight (fun y : G.Dart => by simp))
      _ = p.tail.toFinset.card := Fintype.card_coe _
      _ = p.tail.length := List.toFinset_card_of_nodup htailNodup
  have hcardEq :
      Fintype.card {y : G.Dart // y ∈ p.tail} =
        Fintype.card {x : G.Dart // x ∈ cc} := by
    rw [htailCard]
    simp only [Fintype.card_coe]
    cases p with
    | nil => simp at hlength
    | cons x xs =>
        simp only [List.tail_cons, List.length_cons] at hlength ⊢
        omega
  have hrepBijective : Function.Bijective (tailRepresentative hp) :=
    (Fintype.bijective_iff_injective_and_card
      (tailRepresentative hp)).2
      ⟨tailRepresentative_injective hplain hp, hcardEq⟩
  have hedgeBand : ∀ y : G.Dart, y ∈ p → G.FaceBand p (G.edge y) := by
    intro y hy
    rcases RLinkCycle.exists_outgoing (G := G) hp.cycle.cycle hy with
      ⟨w, hw, hyw⟩
    exact ⟨w, hw, PermReachable.symm G.face hyw⟩
  have hselected : ∀ x : G.Dart, x ∈ cc →
      G.FaceBand p x ∧ G.FaceBand p (G.edge x) := by
    intro x hx
    rcases hrepBijective.2 ⟨x, hx⟩ with ⟨y, hy⟩
    have hrepEq : (tailRepresentative hp y).1 = x :=
      congrArg Subtype.val hy
    have hyFull : y.1 ∈ p := List.mem_of_mem_tail y.2
    have hyBand : G.FaceBand p y.1 :=
      FaceBand.of_mem (G := G) hyFull (PermReachable.refl G.face y.1)
    have hyEdgeBand : G.FaceBand p (G.edge y.1) := hedgeBand y.1 hyFull
    rcases tailRepresentative_eq_or_edge_eq hp y with hxy | hxy
    · have hyEq : y.1 = x := hxy.symm.trans hrepEq
      constructor
      · rw [← hyEq]
        exact hyBand
      · rw [← hyEq]
        exact hyEdgeBand
    · have hyEq : y.1 = G.edge x := by rw [← hrepEq, hxy]
      refine ⟨?_, ?_⟩
      · have hedgeEq : G.edge y.1 = x := by
          rw [hyEq, Plain.edge_edge (G := G) hplain]
        rw [← hedgeEq]
        exact hyEdgeBand
      · rw [← hyEq]
        exact hyBand
  intro z hz
  rcases (G.mem_contractClosure_iff).1 hz with hz | ⟨x, hx, hxz⟩
  · exact (hselected z hz).1
  · simpa [hxz] using (hselected x hx).2

end ContractRing

variable {G : Hypermap.{u}} {cc : Finset G.Dart}

private theorem not_faceReachable_edge_node_of_bridgeless_cubic
    (hbridgeless : G.Bridgeless)
    (hcubic : G.Cubic)
    (x : G.Dart) :
    ¬ PermReachable G.face (G.edge x) (G.node x) := by
  intro hedgeNode
  have hnodeNodeEdge :
      PermReachable G.face (G.node (G.node x)) (G.edge x) := by
    rw [Cubic.node_node_eq_face_edge (G := G) hcubic x]
    simpa using PermReachable.backward G.face (G.face (G.edge x))
  have hnodeEdge :
      PermReachable G.face (G.node x)
        (G.edge (G.node (G.node x))) := by
    rw [edge_node_eq_face_symm]
    exact PermReachable.backward G.face (G.node x)
  exact hbridgeless (G.node (G.node x))
    (PermReachable.trans G.face hnodeNodeEdge
      (PermReachable.trans G.face hedgeNode hnodeEdge))

/-- First chord descent in Coq `sparse_contract_ring`: if the interior of a
contract ring is empty, the next dart around its first node must itself occur
on the ring. -/
private theorem ContractRing.head_node_mem_of_no_diskF
    [Fintype G.Dart]
    (hconnected : G.Connected)
    (hJ : G.Jordan)
    (hplain : G.Plain)
    (hbridgeless : G.Bridgeless)
    (hcubic : G.Cubic)
    {x x₁ : G.Dart} {p₀ : List G.Dart}
    (hp : G.ContractRing cc (x :: x₁ :: p₀))
    (hnoDisk : ∀ u : G.Dart, ¬ G.DiskF (x :: x₁ :: p₀) u)
    (ih : ∀ q : List G.Dart,
      q.length < (x :: x₁ :: p₀).length →
      G.ContractRing cc q → ∃ u : G.Dart, G.DiskF q u) :
    G.node x ∈ x :: x₁ :: p₀ := by
  classical
  by_contra hnodeMem
  have hxDisk : G.DiskN (x :: x₁ :: p₀) x :=
    G.diskN_of_mem (by simp)
  have hnodeDisk : G.DiskN (x :: x₁ :: p₀) (G.node x) :=
    (G.diskN_node_iff (r := x :: x₁ :: p₀)).2 hxDisk
  have hnodeBand : G.FaceBand (x :: x₁ :: p₀) (G.node x) := by
    by_contra hnotBand
    exact hnoDisk (G.node x) ⟨hnodeDisk, hnotBand⟩
  rcases hnodeBand with ⟨z, hzMem, hzNode⟩
  have hzx : z ≠ x := by
    intro hzx
    subst z
    exact Bridgeless.not_faceReachable_node (G := G) hbridgeless x hzNode
  have hzx₁ : z ≠ x₁ := by
    intro hzx₁
    subst z
    have hxx₁ : G.RLink x x₁ := hp.cycle.cycle.path.1
    exact not_faceReachable_edge_node_of_bridgeless_cubic
      (G := G) hbridgeless hcubic x
      (PermReachable.trans G.face hxx₁ hzNode)
  have hzP₀ : z ∈ p₀ := by
    simpa [hzx, hzx₁] using hzMem
  rcases (List.mem_iff_append).1 hzP₀ with ⟨pre, post, hp₀⟩
  let n := (x :: x₁ :: pre).length
  let parent : List G.Dart := z :: post ++ x :: x₁ :: pre
  let chord := G.edge (G.node x)
  let q : List G.Dart := chord :: z :: post
  have hdecomp : (x :: x₁ :: p₀).rotate n = parent := by
    dsimp [n, parent]
    rw [hp₀]
    change ((x :: x₁ :: pre) ++ z :: post).rotate
        (x :: x₁ :: pre).length = z :: post ++ x :: x₁ :: pre
    rw [List.rotate_append_length_eq]
  have hparentCycle : G.SimpleRLinkCycle parent := by
    have hrot := SimpleRLinkCycle.rotate (G := G) n hp.cycle
    simpa [hdecomp] using hrot
  have hparentProper : G.ProperRing parent := by
    have hrot :=
      (properRing_rotate_iff_of_plain (G := G) hplain n
        (x :: x₁ :: p₀)).2 hp.proper
    simpa [hdecomp] using hrot
  have hnodeE : G.DiskE (x :: x₁ :: p₀) (G.node x) :=
    ⟨hnodeDisk, hnodeMem⟩
  have hnodeParentE : G.DiskE parent (G.node x) := by
    have hrot := (DiskE.rotate (G := G) n).2 hnodeE
    simpa [hdecomp] using hrot
  have hchordParentE : G.DiskE parent chord := by
    dsimp [chord]
    exact (G.diskE_edge_iff hJ hplain hparentCycle).2 hnodeParentE
  have hxChord : PermReachable G.face x chord := by
    dsimp [chord]
    rw [edge_node_eq_face_symm]
    exact PermReachable.backward G.face x
  have hzEdgeChord : PermReachable G.face z (G.edge chord) := by
    dsimp [chord]
    simpa [Plain.edge_edge (G := G) hplain] using hzNode
  have hchordZ : G.RLink chord z := by
    unfold RLink
    exact PermReachable.symm G.face hzEdgeChord
  have hqCycle : G.SimpleRLinkCycle q := by
    dsimp [q, parent] at hparentCycle ⊢
    exact SimpleRLinkCycle.chord_prefix_of_decomposition
      (G := G) hparentCycle hchordZ hxChord
  have hotherCycle :
      G.SimpleRLinkCycle (G.edge chord :: x :: x₁ :: pre) := by
    dsimp [parent] at hparentCycle
    exact SimpleRLinkCycle.edge_chord_suffix_of_decomposition
      (G := G) hplain hparentCycle hxChord hzEdgeChord
  have hqProper : G.ProperRing q := by
    dsimp [q]
    apply G.properRing_chord_prefix_of_diskE_edge
    · simpa [chord, Plain.edge_edge (G := G) hplain] using hnodeParentE
    · simp [parent]
  have hqContract : G.ContractRing cc q := by
    refine ⟨hqCycle, hqProper, ?_⟩
    intro y hy
    apply hp.tail_contract y
    dsimp [q] at hy
    rw [hp₀]
    simp only [List.tail_cons]
    simp only [List.mem_cons, List.mem_append] at hy ⊢
    tauto
  have hqLength : q.length < (x :: x₁ :: p₀).length := by
    dsimp [q, chord]
    apply G.length_chord_prefix_lt_of_decomposition
      (r := x :: x₁ :: p₀) (x := G.edge (G.node x))
      (y₁ := x) (y₂ := z)
      (p₁ := post) (p₂ := x₁ :: pre) (i := n)
    · simpa [parent] using hdecomp
    · simp
  have hnoQ : ∀ u : G.Dart, ¬ G.DiskF q u := by
    intro u hu
    have huSplit :=
      (G.diskF_chord_prefix hconnected hJ hplain
        hparentCycle hparentProper hchordParentE
        (by simp) (by simp)
        hxChord hzEdgeChord hqCycle hotherCycle).1
        (by simpa [q] using hu)
    have huRot : G.DiskF ((x :: x₁ :: p₀).rotate n) u := by
      simpa [hdecomp, parent] using huSplit.1
    exact hnoDisk u ((DiskF.rotate (G := G) n).1 huRot)
  rcases ih q hqLength hqContract with ⟨u, hu⟩
  exact hnoQ u hu

/-- Second chord descent in Coq `sparse_contract_ring`.  Once `node x` is on
the ring it is its displayed predecessor of `x`; a second chord descent then
forces `node (node x)` onto the ring as well. -/
private theorem ContractRing.head_node_node_mem_of_no_diskF
    [Fintype G.Dart]
    (hconnected : G.Connected)
    (hJ : G.Jordan)
    (hplain : G.Plain)
    (hbridgeless : G.Bridgeless)
    (hcubic : G.Cubic)
    {x x₁ : G.Dart} {p₀ : List G.Dart}
    (hp : G.ContractRing cc (x :: x₁ :: p₀))
    (hnoDisk : ∀ u : G.Dart, ¬ G.DiskF (x :: x₁ :: p₀) u)
    (ih : ∀ q : List G.Dart,
      q.length < (x :: x₁ :: p₀).length →
      G.ContractRing cc q → ∃ u : G.Dart, G.DiskF q u)
    (hnodeMem : G.node x ∈ x :: x₁ :: p₀) :
    G.node (G.node x) ∈ x :: x₁ :: p₀ := by
  classical
  have hnodeNeX : G.node x ≠ x := (hcubic x).2
  have hnodeTail : G.node x ∈ x₁ :: p₀ := by
    simpa [hnodeNeX] using hnodeMem
  rcases (List.mem_iff_append).1 hnodeTail with
    ⟨pre, post, htail⟩
  have hpostNil : post = [] := by
    cases post with
    | nil => rfl
    | cons y ys =>
        have hpath : G.RLinkPath x (pre ++ G.node x :: y :: ys) := by
          simpa [htail] using hp.cycle.cycle.path
        have hnodeY : G.RLink (G.node x) y :=
          (RLinkPath.suffix_of_append_cons (G := G) hpath).1
        have hyMem : y ∈ x :: x₁ :: p₀ := by
          rw [htail]
          simp
        have hyEqX : y = x :=
          SimpleRLinkCycle.eq_of_same_rlink_source
            (G := G) hp.cycle hyMem (by simp) hnodeY
              (RLink.node_self (G := G) x)
        have hxNotTail : x ∉ x₁ :: p₀ :=
          (List.nodup_cons.mp hp.cycle.faceSimple.nodup).1
        exact False.elim (hxNotTail (by rw [htail]; simp [hyEqX]))
  subst post
  have htailFinal : x₁ :: p₀ = pre ++ [G.node x] := by
    simpa using htail
  by_contra hnodeNodeMem
  have hxDisk : G.DiskN (x :: x₁ :: p₀) x :=
    G.diskN_of_mem (by simp)
  have hnodeNodeDisk :
      G.DiskN (x :: x₁ :: p₀) (G.node (G.node x)) := by
    exact (G.diskN_node_iff (r := x :: x₁ :: p₀)).2
      ((G.diskN_node_iff (r := x :: x₁ :: p₀)).2 hxDisk)
  have hnodeNodeBand :
      G.FaceBand (x :: x₁ :: p₀) (G.node (G.node x)) := by
    by_contra hnotBand
    exact hnoDisk (G.node (G.node x))
      ⟨hnodeNodeDisk, hnotBand⟩
  rcases hnodeNodeBand with ⟨z, hzMem, hzNodeNode⟩
  have hzNode : z ≠ G.node x := by
    intro hzNode
    subst z
    exact Bridgeless.not_faceReachable_node
      (G := G) hbridgeless (G.node x) hzNodeNode
  have hzx : z ≠ x := by
    intro hzx
    subst z
    have hxFaceEdge :
        PermReachable G.face x (G.face (G.edge x)) := by
      simpa [Cubic.node_node_eq_face_edge (G := G) hcubic x] using
        hzNodeNode
    exact hbridgeless x
      (PermReachable.trans G.face hxFaceEdge
        (by simpa using
          PermReachable.backward G.face (G.face (G.edge x))))
  have hzPre : z ∈ pre := by
    rw [htailFinal] at hzMem
    simpa [hzx, hzNode] using hzMem
  rcases (List.mem_iff_append).1 hzPre with
    ⟨pre₁, post₁, hpre⟩
  let t := G.node (G.node x)
  let n := (x :: pre₁).length
  let parent : List G.Dart := z :: post₁ ++ G.node x :: x :: pre₁
  let chord := G.edge t
  let q : List G.Dart := chord :: z :: post₁
  have hdecomp : (x :: x₁ :: p₀).rotate n = parent := by
    have hbase :
        x :: x₁ :: p₀ =
          (x :: pre₁) ++ (z :: post₁ ++ [G.node x]) := by
      rw [htailFinal, hpre]
      simp [List.append_assoc]
    rw [hbase]
    change (((x :: pre₁) ++ (z :: post₁ ++ [G.node x])).rotate
      (x :: pre₁).length) = parent
    rw [List.rotate_append_length_eq]
    dsimp [parent]
    simp [List.append_assoc]
  have hparentCycle : G.SimpleRLinkCycle parent := by
    have hrot := SimpleRLinkCycle.rotate (G := G) n hp.cycle
    simpa [hdecomp] using hrot
  have hparentProper : G.ProperRing parent := by
    have hrot :=
      (properRing_rotate_iff_of_plain (G := G) hplain n
        (x :: x₁ :: p₀)).2 hp.proper
    simpa [hdecomp] using hrot
  have htE : G.DiskE (x :: x₁ :: p₀) t := by
    exact ⟨hnodeNodeDisk, hnodeNodeMem⟩
  have htParentE : G.DiskE parent t := by
    have hrot := (DiskE.rotate (G := G) n).2 htE
    simpa [hdecomp] using hrot
  have hchordParentE : G.DiskE parent chord := by
    dsimp [chord]
    exact (G.diskE_edge_iff hJ hplain hparentCycle).2 htParentE
  have hnodeChord : PermReachable G.face (G.node x) chord := by
    dsimp [chord, t]
    rw [edge_node_eq_face_symm]
    exact PermReachable.backward G.face (G.node x)
  have hzEdgeChord : PermReachable G.face z (G.edge chord) := by
    dsimp [chord]
    simpa [Plain.edge_edge (G := G) hplain] using hzNodeNode
  have hchordZ : G.RLink chord z := by
    unfold RLink
    exact PermReachable.symm G.face hzEdgeChord
  have hqCycle : G.SimpleRLinkCycle q := by
    dsimp [q, parent] at hparentCycle ⊢
    exact SimpleRLinkCycle.chord_prefix_of_decomposition
      (G := G) hparentCycle hchordZ hnodeChord
  have hotherCycle :
      G.SimpleRLinkCycle (G.edge chord :: G.node x :: x :: pre₁) := by
    dsimp [parent] at hparentCycle
    exact SimpleRLinkCycle.edge_chord_suffix_of_decomposition
      (G := G) hplain hparentCycle hnodeChord hzEdgeChord
  have hqProper : G.ProperRing q := by
    dsimp [q]
    apply G.properRing_chord_prefix_of_diskE_edge
    · simpa [chord, Plain.edge_edge (G := G) hplain] using htParentE
    · simp [parent]
  have hqContract : G.ContractRing cc q := by
    refine ⟨hqCycle, hqProper, ?_⟩
    intro y hy
    apply hp.tail_contract y
    dsimp [q] at hy
    rw [htailFinal, hpre]
    simp only [List.tail_cons]
    simp only [List.mem_cons, List.mem_append] at hy ⊢
    tauto
  have hqLength : q.length < (x :: x₁ :: p₀).length := by
    dsimp [q, chord]
    apply G.length_chord_prefix_lt_of_decomposition
      (r := x :: x₁ :: p₀) (x := G.edge (G.node (G.node x)))
      (y₁ := G.node x) (y₂ := z)
      (p₁ := post₁) (p₂ := x :: pre₁) (i := n)
    · simpa [parent, t] using hdecomp
    · simp
  have hnoQ : ∀ u : G.Dart, ¬ G.DiskF q u := by
    intro u hu
    have huSplit :=
      (G.diskF_chord_prefix hconnected hJ hplain
        hparentCycle hparentProper hchordParentE
        (by simp) (by simp)
        hnodeChord hzEdgeChord hqCycle hotherCycle).1
        (by simpa [q] using hu)
    have huRot : G.DiskF ((x :: x₁ :: p₀).rotate n) u := by
      simpa [hdecomp, parent] using huSplit.1
    exact hnoDisk u ((DiskF.rotate (G := G) n).1 huRot)
  rcases ih q hqLength hqContract with ⟨u, hu⟩
  exact hnoQ u hu

/-- The interior half of Coq `sparse_contract_ring`.  A sparse contract ring
has a strict face on the displayed side. -/
theorem ContractRing.exists_diskF_of_sparse
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected)
    (hcubic : G.Cubic)
    (hsparse : G.Sparse (G.contractClosure cc))
    {p : List G.Dart}
    (hp : G.ContractRing cc p) :
    ∃ u : G.Dart, G.DiskF p u := by
  classical
  have hJ : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hG.planar
  let P : Nat → Prop := fun n =>
    ∀ p : List G.Dart, p.length = n →
      G.ContractRing cc p → ∃ u : G.Dart, G.DiskF p u
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p hpLength hpRing
        by_contra hnone
        push Not at hnone
        have ihCurrent : ∀ q : List G.Dart,
            q.length < p.length → G.ContractRing cc q →
              ∃ u : G.Dart, G.DiskF q u := by
          intro q hqLength hq
          exact ih q.length (by omega) q rfl hq
        cases p with
        | nil =>
            have hproper := hpRing.proper
            simp [ProperRing] at hproper
        | cons x xs =>
            cases xs with
            | nil =>
                have hproper := hpRing.proper
                simp [ProperRing, EdgePath] at hproper
            | cons x₁ p₀ =>
                have hnodeMem : G.node x ∈ x :: x₁ :: p₀ :=
                  hpRing.head_node_mem_of_no_diskF
                    hconnected hJ hG.plain hG.bridgeless hcubic hnone
                    ihCurrent
                have hnodeNodeMem :
                    G.node (G.node x) ∈ x :: x₁ :: p₀ :=
                  hpRing.head_node_node_mem_of_no_diskF
                    hconnected hJ hG.plain hG.bridgeless hcubic hnone
                    ihCurrent hnodeMem
                have hnodeNeX : G.node x ≠ x := (hcubic x).2
                have hnodeTail : G.node x ∈ (x :: x₁ :: p₀).tail := by
                  simpa [hnodeNeX] using hnodeMem
                have hnodeNodeNeX : G.node (G.node x) ≠ x := by
                  intro hbad
                  have hperiod := (hcubic x).1
                  rw [hbad] at hperiod
                  exact hnodeNeX hperiod
                have hnodeNodeTail :
                    G.node (G.node x) ∈ (x :: x₁ :: p₀).tail := by
                  simpa [hnodeNodeNeX] using hnodeNodeMem
                have hnodeContract :
                    G.node x ∈ G.contractClosure cc :=
                  hpRing.tail_contract (G.node x) hnodeTail
                have hnodeNodeContract :
                    G.node (G.node x) ∈ G.contractClosure cc :=
                  hpRing.tail_contract (G.node (G.node x)) hnodeNodeTail
                have hEq : G.node x = G.node (G.node x) :=
                  hsparse hnodeContract hnodeNodeContract
                    (PermReachable.forward G.node (G.node x))
                exact hnodeNeX (G.node.injective hEq.symm)
  exact hP p.length p rfl hp

/-- Coq's `rev_ring (rot 1 p)` preserves the contract-ring condition: after
the reversal, every tail dart is the crossed edge of an original tail dart. -/
theorem ContractRing.revRing_rotate_one
    (hplain : G.Plain)
    {p : List G.Dart}
    (hp : G.ContractRing cc p) :
    G.ContractRing cc (G.RevRing (p.rotate 1)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact SimpleRLinkCycle.revRing_of_plain (G := G) hplain
      (SimpleRLinkCycle.rotate (G := G) 1 hp.cycle)
  · exact (properRing_revRing_iff_of_plain
      (G := G) hplain (p.rotate 1)).2
      ((properRing_rotate_iff_of_plain (G := G) hplain 1 p).2 hp.proper)
  · cases p with
    | nil =>
        simp [RevRing]
    | cons x xs =>
        intro y hy
        have hshape :
            G.RevRing ((x :: xs).rotate 1) =
              G.edge x :: (xs.map G.edge).reverse := by
          simp [RevRing, List.rotate_cons_succ, List.map_append]
        rw [hshape] at hy
        have hyMap : y ∈ xs.map G.edge := by
          simpa using hy
        rcases List.mem_map.1 hyMap with ⟨z, hz, rfl⟩
        exact (G.contractClosure_edge_mem_iff_of_plain hplain).2
          (hp.tail_contract z (by simpa using hz))

/-- Coq `sparse_contract_ring`: a sparse contract ring has at least one face
orbit on each side. -/
theorem sparse_contract_ring
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected)
    (hcubic : G.Cubic)
    (hsparse : G.Sparse (G.contractClosure cc))
    {p : List G.Dart}
    (hp : G.ContractRing cc p) :
    G.NontrivialRing 0 p := by
  classical
  have hJ : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hG.planar
  rcases hp.exists_diskF_of_sparse hG hconnected hcubic hsparse with
    ⟨u, hu⟩
  let pRot := p.rotate 1
  have hpRotCycle : G.SimpleRLinkCycle pRot :=
    SimpleRLinkCycle.rotate (G := G) 1 hp.cycle
  have hpRotProper : G.ProperRing pRot :=
    (properRing_rotate_iff_of_plain (G := G) hG.plain 1 p).2 hp.proper
  have hpRev : G.ContractRing cc (G.RevRing pRot) := by
    simpa [pRot] using hp.revRing_rotate_one hG.plain
  rcases hpRev.exists_diskF_of_sparse hG hconnected hcubic hsparse with
    ⟨v, hv⟩
  have hvOutsideRot : G.DiskFC pRot v := by
    exact (G.diskF_rev_ring hconnected hJ hG.plain
      hpRotCycle hpRotProper v).1 hv
  have hvOutside : G.DiskFC p v := by
    exact (DiskFC.rotate (G := G) 1).1 (by simpa [pRot] using hvOutsideRot)
  exact (G.nontrivialRing_zero_iff).2 ⟨⟨u, hu⟩, ⟨v, hvOutside⟩⟩

/-- Coq `contract3_valid`: a sparse contract with at most three selected
darts admits no contract ring. -/
theorem no_contractRing_of_card_le_three
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected)
    (hcubic : G.Cubic)
    (hsparse : G.Sparse (G.contractClosure cc))
    (hcard : cc.card ≤ 3)
    {p : List G.Dart}
    (hp : G.ContractRing cc p) :
    False := by
  have hpLength : p.length ≤ 4 := by
    exact (hp.length_le_card_add_one hG.plain).trans (by omega)
  have hnt : G.NontrivialRing 0 p :=
    sparse_contract_ring hG hconnected hcubic hsparse hp
  have hnot := Schematic.Math.GraphTheory.FourColor.Birkhoff.Birkhoff
    hG hconnected hcubic p (by omega) hp.cycle
  have hpNotFive : p.length ≠ 5 := by omega
  have hnotZero : ¬ G.NontrivialRing 0 p := by
    simpa [hpNotFive] using hnot
  exact hnotZero hnt

/-- Coq `contract.v::triad_valid`: a sparse four-dart contract with a triad
admits no contract ring. -/
theorem no_contractRing_of_card_four_of_triad
    (hG : G.MinimalCounterexample)
    (hconnected : G.Connected)
    (hcubic : G.Cubic)
    (hsparse : G.Sparse (G.contractClosure cc))
    (hcard : cc.card = 4)
    {center : G.Dart}
    (htriad : G.TriadFor (G.contractClosure cc) center)
    {p : List G.Dart}
    (hp : G.ContractRing cc p) : False := by
  classical
  have hpLength : p.length ≤ 5 := by
    have := hp.length_le_card_add_one hG.plain
    omega
  have hntZero : G.NontrivialRing 0 p :=
    sparse_contract_ring hG hconnected hcubic hsparse hp
  have hBirkhoff := Schematic.Math.GraphTheory.FourColor.Birkhoff.Birkhoff
    hG hconnected hcubic p hpLength hp.cycle
  have hpFive : p.length = 5 := by
    by_contra hpNotFive
    have hnotZero : ¬ G.NontrivialRing 0 p := by
      simpa [hpNotFive] using hBirkhoff
    exact hnotZero hntZero
  have hnotOne : ¬ G.NontrivialRing 1 p := by
    simpa [hpFive] using hBirkhoff
  have hJordan : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hG.planar
  have hproper := hp.proper
  have strictCompanion
      {w : G.Dart} (hwBand : ¬ G.FaceBand p w)
      (hwInside : G.DiskF p w) :
      ∀ z : G.Dart, G.RingAdj w z → ¬ G.FaceBand p z →
        ∃ t : G.Dart, G.DiskF p t ∧
          ¬ PermReachable G.face w t := by
    intro z hwz hzBand
    rcases hwz with ⟨t, hwt, hedgeTZ⟩
    have htInside : G.DiskF p t :=
      G.diskF_of_faceReachable hwt hwInside
    have htE : G.DiskE p t := ⟨htInside.1, fun htMem =>
      htInside.2 (Hypermap.FaceBand.of_mem (G := G) htMem
        (PermReachable.refl G.face t))⟩
    have hedgeTE : G.DiskE p (G.edge t) :=
      (G.diskE_edge_iff hJordan hG.plain hp.cycle).2 htE
    have hedgeTBand : ¬ G.FaceBand p (G.edge t) := by
      intro hband
      apply hzBand
      rcases hband with ⟨s, hs, hsEdgeT⟩
      exact ⟨s, hs, PermReachable.trans G.face hsEdgeT hedgeTZ⟩
    refine ⟨G.edge t, ⟨hedgeTE.1, hedgeTBand⟩, ?_⟩
    intro hwEdgeT
    exact hG.bridgeless t
      (PermReachable.trans G.face
        (PermReachable.symm G.face hwt) hwEdgeT)
  have strictCompanionOutside
      {w : G.Dart} (hwOutside : G.DiskFC p w) :
      ∀ z : G.Dart, G.RingAdj w z → ¬ G.FaceBand p z →
        ∃ t : G.Dart, G.DiskFC p t ∧
          ¬ PermReachable G.face w t := by
    intro z hwz hzBand
    rcases hwz with ⟨t, hwt, hedgeTZ⟩
    have htOutside : G.DiskFC p t :=
      G.diskFC_of_faceReachable hwt hwOutside
    have hedgeTNotDisk : ¬ G.DiskN p (G.edge t) := by
      intro hedgeTN
      have hedgeTE : G.DiskE p (G.edge t) := ⟨hedgeTN, fun hedgeTMem =>
        hzBand ⟨G.edge t, hedgeTMem, hedgeTZ⟩⟩
      have htE : G.DiskE p t :=
        (G.diskE_edge_iff hJordan hG.plain hp.cycle).1 hedgeTE
      exact htOutside.1 htE.1
    have hedgeTBand : ¬ G.FaceBand p (G.edge t) := by
      intro hband
      apply hzBand
      rcases hband with ⟨s, hs, hsEdgeT⟩
      exact ⟨s, hs, PermReachable.trans G.face hsEdgeT hedgeTZ⟩
    refine ⟨G.edge t, ⟨hedgeTNotDisk, hedgeTBand⟩, ?_⟩
    intro hwEdgeT
    exact hG.bridgeless t
      (PermReachable.trans G.face
        (PermReachable.symm G.face hwt) hwEdgeT)
  have hUniversal : ∃ hub : G.Dart,
      ∀ z : G.Dart, G.RingAdj hub z → G.FaceBand p z := by
    by_contra hnone
    push Not at hnone
    rcases (G.nontrivialRing_zero_iff).1 hntZero with
      ⟨⟨u, huInside⟩, v, hvOutside⟩
    rcases hnone u with ⟨u₁, huu₁, hu₁Band⟩
    rcases hnone v with ⟨v₁, hvv₁, hv₁Band⟩
    rcases strictCompanion huInside.2 huInside u₁ huu₁ hu₁Band with
      ⟨u₂, hu₂Inside, huu₂⟩
    rcases strictCompanionOutside hvOutside v₁ hvv₁ hv₁Band with
      ⟨v₂, hv₂Outside, hvv₂⟩
    apply hnotOne
    rw [G.nontrivialRing_one_iff]
    exact ⟨⟨u, huInside, u₂, hu₂Inside, huu₂⟩,
      ⟨v, hvOutside, v₂, hv₂Outside, hvv₂⟩⟩
  rcases hUniversal with ⟨hub, hhub⟩
  let s := Schematic.Math.GraphTheory.FourColor.Birkhoff.spokeRing G hub
  have hsCycle : G.SimpleRLinkCycle s := by
    simpa [s] using Schematic.Math.GraphTheory.FourColor.Birkhoff.spokeRing_simpleRLinkCycle
      hG hconnected hcubic hub
  have hbandSSubsetP : ∀ z : G.Dart,
      G.FaceBand s z → G.FaceBand p z := by
    intro z hz
    apply hhub z
    exact (Schematic.Math.GraphTheory.FourColor.Birkhoff.faceBand_spokeRing_iff_ringAdj hub z).1
      (by simpa [s] using hz)
  let orbit := PermOrbit.of G.face
  let S : Finset G.FaceOrbit := (s.map orbit).toFinset
  let P : Finset G.FaceOrbit := (p.map orbit).toFinset
  have hSP : S ⊆ P := by
    intro o ho
    rcases List.mem_toFinset.mp ho with ho
    rcases List.mem_map.mp ho with ⟨z, hzS, rfl⟩
    have hzBandS : G.FaceBand s z :=
      Hypermap.FaceBand.of_mem (G := G) hzS
        (PermReachable.refl G.face z)
    have hzBandP := hbandSSubsetP z hzBandS
    have hzOrbitP := (G.faceBand_iff_mem_faceOrbit_map).1 hzBandP
    exact List.mem_toFinset.mpr hzOrbitP
  have hSCard : S.card = s.length := by
    simpa [S] using List.toFinset_card_of_nodup
      ((G.faceSimple_iff_nodup_faceOrbit_map).1 hsCycle.faceSimple)
  have hPCard : P.card = p.length := by
    simpa [P] using List.toFinset_card_of_nodup
      ((G.faceSimple_iff_nodup_faceOrbit_map).1 hp.cycle.faceSimple)
  have hsLengthMin : 5 ≤ s.length := by
    change 5 ≤ (Schematic.Math.GraphTheory.FourColor.Birkhoff.spokeRing G hub).length
    rw [Schematic.Math.GraphTheory.FourColor.Birkhoff.length_spokeRing]
    exact Schematic.Math.GraphTheory.FourColor.Birkhoff.minArity hG hconnected hcubic hub
  have hPS : P ⊆ S := by
    have hcardLe : P.card ≤ S.card := by
      rw [hPCard, hSCard, hpFive]
      exact hsLengthMin
    have hEq : S = P := Finset.eq_of_subset_of_card_le hSP hcardLe
    simp [hEq]
  have hbandPSubsetAdj : ∀ z : G.Dart,
      G.FaceBand p z → G.RingAdj hub z := by
    intro z hz
    have hzP : orbit z ∈ P := by
      exact List.mem_toFinset.mpr
        ((G.faceBand_iff_mem_faceOrbit_map).1 hz)
    have hzS := hPS hzP
    have hzBandS : G.FaceBand s z := by
      apply (G.faceBand_iff_mem_faceOrbit_map).2
      exact List.mem_toFinset.mp hzS
    exact (Schematic.Math.GraphTheory.FourColor.Birkhoff.faceBand_spokeRing_iff_ringAdj hub z).1
      (by simpa [s] using hzBandS)
  have hclosureBand : ∀ z : G.Dart,
      z ∈ G.contractClosure cc → G.FaceBand p z := by
    apply hp.contractClosure_subset_faceBand_of_length_eq_card_add_one hG.plain
    omega
  rcases htriad with
    ⟨⟨a, ha, b, hb, c, hc, hab, hac, hbc,
      hcenterA, hcenterB, hcenterC⟩,
      y, hy, hcenterNotY⟩
  by_cases hcenterHub : PermReachable G.face center hub
  · apply hcenterNotY
    exact Hypermap.RingAdj.of_faceReachable_left (G := G) hcenterHub
      (hbandPSubsetAdj y (hclosureBand y hy))
  · exact Schematic.Math.GraphTheory.FourColor.Birkhoff.not_three_common_ringAdj
      hG hconnected hcubic
      (Schematic.Math.GraphTheory.FourColor.Birkhoff.minArity hG hconnected hcubic hub)
      (fun h => hcenterHub (PermReachable.symm G.face h))
      hab hac hbc
      (hbandPSubsetAdj a (hclosureBand a ha))
      (hbandPSubsetAdj b (hclosureBand b hb))
      (hbandPSubsetAdj c (hclosureBand c hc))
      hcenterA hcenterB hcenterC


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
