import FourColorTheorem.FourColor.Coloring.CFColorMap
import FourColorTheorem.FourColor.Reducibility.Certificate
import FourColorTheorem.FourColor.Reducibility.Soundness

namespace Schematic.Math.GraphTheory





namespace FourColor

@[simp]
theorem extDart_old_eq_old_iff {α : Type _} {x y : α} :
    (ExtDart.old x : ExtDart α) = ExtDart.old y ↔ x = y := by
  constructor
  · intro h
    exact ExtDart.old_injective h
  · exact congrArg ExtDart.old

theorem tail_map_eq_map_tail {α β : Type _} (f : α → β) (xs : List α) :
    (xs.map f).tail = xs.tail.map f := by
  cases xs <;> rfl

namespace Hypermap

/-- Coq `insertE`: interleave every selected dart with the opposite dart of
its edge. -/
def insertEdges (G : Hypermap) : List G.Dart → List G.Dart
  | [] => []
  | x :: xs => x :: G.edge x :: G.insertEdges xs

@[simp]
theorem insertEdges_nil (G : Hypermap) : G.insertEdges [] = [] :=
  rfl

@[simp]
theorem insertEdges_cons (G : Hypermap) (x : G.Dart) (xs : List G.Dart) :
    G.insertEdges (x :: xs) = x :: G.edge x :: G.insertEdges xs :=
  rfl

@[simp]
theorem insertEdges_append (G : Hypermap) (xs ys : List G.Dart) :
    G.insertEdges (xs ++ ys) = G.insertEdges xs ++ G.insertEdges ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem insertEdges_perm (G : Hypermap) {xs ys : List G.Dart}
    (h : xs.Perm ys) :
    (G.insertEdges xs).Perm (G.insertEdges ys) := by
  induction h with
  | nil => rfl
  | cons x _ ih => simpa using List.Perm.cons x (List.Perm.cons (G.edge x) ih)
  | swap x y xs =>
      have h :=
        (List.perm_append_comm :
          ([y, G.edge y] ++ [x, G.edge x]).Perm
            ([x, G.edge x] ++ [y, G.edge y])).append_right
          (G.insertEdges xs)
      simpa [List.append_assoc] using h
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem insertEdges_perm_append_map (G : Hypermap) :
    ∀ xs : List G.Dart,
      (G.insertEdges xs).Perm (xs ++ xs.map G.edge)
  | [] => by simp
  | x :: xs => by
      rw [insertEdges_cons, List.map_cons, List.cons_append]
      have ih := insertEdges_perm_append_map G xs
      have htail :
          (G.edge x :: G.insertEdges xs).Perm
            (G.edge x :: xs ++ xs.map G.edge) :=
        ih.cons (G.edge x)
      have hmove :
          (G.edge x :: xs ++ xs.map G.edge).Perm
            (xs ++ G.edge x :: xs.map G.edge) := by
        simpa [List.cons_append, List.append_assoc] using
          (List.perm_middle (a := G.edge x)
            (l₁ := xs) (l₂ := xs.map G.edge)).symm
      exact (htail.trans hmove).cons x

theorem disjoint_self_map_edge_of_nodup_insertEdges
    (G : Hypermap) {xs : List G.Dart}
    (h : (G.insertEdges xs).Nodup) :
    xs.Disjoint (xs.map G.edge) := by
  exact List.disjoint_of_nodup_append
    ((G.insertEdges_perm_append_map xs).nodup_iff.mp h)

theorem insertEdges_map
    {G H : Hypermap} (f : G.Dart → H.Dart)
    (hedge : ∀ x, f (G.edge x) = H.edge (f x))
    (xs : List G.Dart) :
    H.insertEdges (xs.map f) = (G.insertEdges xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [hedge, ih]

theorem sublist_insertEdges (G : Hypermap) :
    ∀ xs : List G.Dart, List.Sublist xs (G.insertEdges xs)
  | [] => .slnil
  | x :: xs =>
      (sublist_insertEdges G xs).cons (G.edge x) |>.cons_cons x

theorem mem_insertEdges_self (G : Hypermap)
    {xs : List G.Dart} {x : G.Dart}
    (hx : x ∈ xs) :
    x ∈ G.insertEdges xs :=
  List.Sublist.mem hx (G.sublist_insertEdges xs)

theorem mem_insertEdges_edge (G : Hypermap)
    {xs : List G.Dart} {x : G.Dart}
    (hx : x ∈ xs) :
    G.edge x ∈ G.insertEdges xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · simp only [insertEdges_cons, List.mem_cons]
        exact Or.inr (Or.inr (ih hx))

theorem mem_insertEdges_iff (G : Hypermap) :
    ∀ {xs : List G.Dart} {z : G.Dart},
      z ∈ G.insertEdges xs ↔
        z ∈ xs ∨ ∃ x ∈ xs, G.edge x = z
  | [], z => by simp
  | x :: xs, z => by
      rw [insertEdges_cons]
      simp only [List.mem_cons, mem_insertEdges_iff]
      aesop

theorem mem_contractClosure_toFinset_iff_insertEdges
    (G : Hypermap) (xs : List G.Dart) (z : G.Dart) :
    z ∈ G.contractClosure xs.toFinset ↔ z ∈ G.insertEdges xs := by
  rw [G.mem_contractClosure_iff, G.mem_insertEdges_iff]
  simp

theorem contractClosure_image_of_edge_commute
    {G H : Hypermap} (f : G.Dart → H.Dart)
    (hedge : ∀ x, f (G.edge x) = H.edge (f x))
    (s : Finset G.Dart) :
    H.contractClosure (s.image f) =
      (G.contractClosure s).image f := by
  ext y
  simp only [contractClosure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨z, ⟨x, hx, rfl⟩, hEq⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨G.edge x, Or.inr ⟨x, hx, rfl⟩,
        by simpa [hedge] using hEq⟩
  · rintro ⟨x, hx | ⟨z, hz, rfl⟩, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨f z, ⟨z, hz, rfl⟩, (hedge z).symm⟩

theorem contractClosure_union
    (G : Hypermap) (s t : Finset G.Dart) :
    G.contractClosure (s ∪ t) =
      G.contractClosure s ∪ G.contractClosure t := by
  unfold contractClosure
  rw [Finset.image_union]
  ac_rfl

theorem image_edge_image_of_edge_commute
    {G H : Hypermap} (f : G.Dart → H.Dart)
    (hedge : ∀ x, f (G.edge x) = H.edge (f x))
    (s : Finset G.Dart) :
    (s.image f).image H.edge = (s.image G.edge).image f := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨G.edge x, ⟨x, hx, rfl⟩, hedge x⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, (hedge x).symm⟩

/-- Pull a contract coloring back along an old-dart injection.  Constructor
cases only need to identify the selected edge closure. -/
theorem ContractColoring.pullback
    {G H : Hypermap}
    {ccG : Finset G.Dart} {ccH : Finset H.Dart}
    {k : H.Dart → Color} (f : G.Dart → H.Dart)
    (hedge : ∀ x, f (G.edge x) = H.edge (f x))
    (hface : ∀ x, PermReachable H.face (f x) (f (G.face x)))
    (hmem : ∀ x, f x ∈ H.contractClosure ccH ↔
      x ∈ G.contractClosure ccG)
    (hk : H.ContractColoring ccH k) :
    G.ContractColoring ccG (k ∘ f) := by
  constructor
  · intro x hx
    change k (f (G.edge x)) = k (f x)
    rw [hedge]
    exact hk.1 (f x) ((hmem x).2 hx)
  · constructor
    · intro x hx
      change k (f (G.edge x)) ≠ k (f x)
      rw [hedge]
      exact hk.2.1 (f x) (by
        intro hfx
        exact hx ((hmem x).1 hfx))
    · intro x
      change k (f (G.face x)) = k (f x)
      exact ContractColoring.eq_of_face_reachable (G := H) hk (hface x)

/-- Along a backwards node path, contracting every masked prefix edge makes
the first unmasked face color equal to the color at the path head.  This is
the list induction used for `h'nGc` inside Coq `cfctr_correct`. -/
theorem ContractColoring.eq_first_unselected_of_isChain
    {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k) :
    ∀ {mask : List Bool} {x : G.Dart} {xs : List G.Dart}
      {y : G.Dart} {ys : List G.Dart},
      List.IsChain (fun a b => G.node.symm a = b) (x :: xs) →
      (∀ z, z ∈ CfMask.select mask (x :: xs) →
        z ∈ G.contractClosure cc) →
      CfMask.select (mask.map Bool.not) (x :: xs) = y :: ys →
      k y = k x := by
  intro mask
  induction mask with
  | nil =>
      intro x xs y ys _hpath _hselected hsurvive
      simp [CfMask.select] at hsurvive
  | cons b bs ih =>
      intro x xs y ys hpath hselected hsurvive
      cases b with
      | false =>
          simp only [List.map_cons, Bool.not_false, CfMask.select, if_true]
            at hsurvive
          have hxy : x = y := (List.cons.inj hsurvive).1
          simp [hxy]
      | true =>
          cases xs with
          | nil =>
              simp [CfMask.select] at hsurvive
          | cons z zs =>
              cases hpath with
              | cons_cons hxz hpath =>
                  have hxcontract : x ∈ G.contractClosure cc :=
                    hselected x (by simp [CfMask.select])
                  have hkzx : k z = k x := by
                    rw [← hxz, ← G.face_edge_eq_node_symm]
                    exact
                      (Hypermap.ContractColoring.face_eq (G := G) hk
                        (G.edge x)).trans
                      (Hypermap.ContractColoring.edge_eq (G := G) hk x
                        hxcontract)
                  have hselectedTail :
                      ∀ w, w ∈ CfMask.select bs (z :: zs) →
                        w ∈ G.contractClosure cc := by
                    intro w hw
                    exact hselected w (by simp [CfMask.select, hw])
                  simp only [List.map_cons, Bool.not_true, CfMask.select] at hsurvive
                  exact (ih hpath hselectedTail hsurvive).trans hkzx

/-- If an aligned mask selects every dart on a backwards-node path, a
contract coloring identifies the path's initial dart with its terminal dart.
This is the terminating branch of Coq's selected-prefix induction. -/
theorem ContractColoring.eq_terminal_of_all_selected_of_isChain
    {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : G.ContractColoring cc k) :
    ∀ {mask : List Bool} {x : G.Dart} {xs : List G.Dart} {y : G.Dart},
      mask.length = (x :: xs).length →
      List.IsChain (fun a b => G.node.symm a = b)
        ((x :: xs) ++ [y]) →
      (∀ z, z ∈ CfMask.select mask (x :: xs) →
        z ∈ G.contractClosure cc) →
      CfMask.select (mask.map Bool.not) (x :: xs) = [] →
      k y = k x := by
  intro mask
  induction mask with
  | nil =>
      intro x xs y hlen
      simp at hlen
  | cons b bs ih =>
      intro x xs y hlen hpath hselected hnone
      cases b with
      | false =>
          simp [CfMask.select] at hnone
      | true =>
          have hxcontract : x ∈ G.contractClosure cc :=
            hselected x (by simp [CfMask.select])
          have hstep {z : G.Dart} (hxz : G.node.symm x = z) :
              k z = k x := by
            rw [← hxz, ← G.face_edge_eq_node_symm]
            exact
              (Hypermap.ContractColoring.face_eq (G := G) hk
                (G.edge x)).trans
              (Hypermap.ContractColoring.edge_eq (G := G) hk x hxcontract)
          cases xs with
          | nil =>
              have hxy : G.node.symm x = y := by
                simpa using hpath
              exact hstep hxy
          | cons z zs =>
              have hlenTail : bs.length = (z :: zs).length := by
                simpa using hlen
              have hpathTail :
                  List.IsChain (fun a b => G.node.symm a = b)
                    ((z :: zs) ++ [y]) := by
                cases hpath with
                | cons_cons _ htail => exact htail
              have hxz : G.node.symm x = z := by
                cases hpath with
                | cons_cons h _ => exact h
              have hselectedTail :
                  ∀ w, w ∈ CfMask.select bs (z :: zs) →
                    w ∈ G.contractClosure cc := by
                intro w hw
                exact hselected w (by simp [CfMask.select, hw])
              have hnoneTail :
                  CfMask.select (bs.map Bool.not) (z :: zs) = [] := by
                simpa [CfMask.select] using hnone
              exact (ih hlenTail hpathTail hselectedTail hnoneTail).trans
                (hstep hxz)

end Hypermap

namespace CfMask

theorem select_sublist {α : Type _} :
    ∀ (mask : List Bool) (xs : List α), List.Sublist (select mask xs) xs
  | [], xs => List.nil_sublist xs
  | _ :: _, [] => .slnil
  | b :: bs, x :: xs => by
      cases b
      · exact (select_sublist bs xs).cons x
      · exact (select_sublist bs xs).cons_cons x

theorem nodup_select {α : Type _}
    (mask : List Bool) {xs : List α}
    (hxs : xs.Nodup) :
    (select mask xs).Nodup :=
  hxs.sublist (select_sublist mask xs)

theorem toFinset_select_map {α β : Type _}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (mask : List Bool) (xs : List α) :
    (select mask (xs.map f)).toFinset =
      (select mask xs).toFinset.image f := by
  rw [select_map]
  ext y
  simp

end CfMask

namespace PointedHypermap

namespace CFContract.Internal

theorem insertEdges_y_fresh
    (P : PointedHypermap) (xs : List P.map.Dart)
    (hxs : (P.map.insertEdges xs).Nodup) :
    (P.y.map.insertEdges
      (P.y.map.node P.y.point :: P.y.point :: xs.map P.yOld)).Nodup := by
  rw [Hypermap.insertEdges_cons, Hypermap.insertEdges_cons,
    Hypermap.insertEdges_map P.yOld P.yOld_edge]
  change
    (ExtDart.old ExtDart.newEdge :: ExtDart.old ExtDart.new ::
      ExtDart.new :: ExtDart.newEdge ::
        (P.map.insertEdges xs).map P.yOld).Nodup
  have holdNewEdge (x : P.map.Dart) :
      P.yOld x ≠ ExtDart.old ExtDart.newEdge := by
    intro h
    injection h with h'
    cases h'
  have holdNew (x : P.map.Dart) :
      P.yOld x ≠ ExtDart.old ExtDart.new := by
    intro h
    injection h with h'
    cases h'
  have hnew (x : P.map.Dart) :
      P.yOld x ≠ P.y.point := P.yOld_ne_point x
  have hnewEdge (x : P.map.Dart) :
      P.yOld x ≠ (ExtDart.newEdge : P.y.map.Dart) := by
    change ExtDart.old (ExtDart.old x) ≠ ExtDart.newEdge
    simp
  let ys := (P.map.insertEdges xs).map P.yOld
  have hys : ys.Nodup := List.Nodup.map P.yOld_injective hxs
  have hnotOldNewEdge : ExtDart.old ExtDart.newEdge ∉ ys := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, _hx, hx⟩
    exact holdNewEdge x hx
  have hnotOldNew : ExtDart.old ExtDart.new ∉ ys := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, _hx, hx⟩
    exact holdNew x hx
  have hnotNew : (ExtDart.new : P.y.map.Dart) ∉ ys := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, _hx, hx⟩
    exact hnew x hx
  have hnotNewEdge : (ExtDart.newEdge : P.y.map.Dart) ∉ ys := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, _hx, hx⟩
    exact hnewEdge x hx
  have htailOldNewEdge :
      ExtDart.old ExtDart.newEdge ∉
        ExtDart.old ExtDart.new :: ExtDart.new :: ExtDart.newEdge :: ys := by
    intro hm
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    exact hnotOldNewEdge hm
  have htailOldNew :
      ExtDart.old ExtDart.new ∉ ExtDart.new :: ExtDart.newEdge :: ys := by
    intro hm
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    exact hnotOldNew hm
  have htailNew :
      (ExtDart.new : P.y.map.Dart) ∉ ExtDart.newEdge :: ys := by
    intro hm
    rcases List.mem_cons.mp hm with h | hm
    · cases h
    exact hnotNew hm
  exact List.Nodup.cons
    htailOldNewEdge
    (List.Nodup.cons
      htailOldNew
      (List.Nodup.cons
        htailNew
        (List.Nodup.cons hnotNewEdge hys)))

private def hFreshTag {α : Type _} :
    ExtDart (ExtDart (ExtDart α)) → Nat
  | ExtDart.new => 0
  | ExtDart.newEdge => 1
  | ExtDart.old ExtDart.new => 2
  | ExtDart.old ExtDart.newEdge => 3
  | ExtDart.old (ExtDart.old ExtDart.new) => 4
  | ExtDart.old (ExtDart.old ExtDart.newEdge) => 5
  | ExtDart.old (ExtDart.old (ExtDart.old _)) => 6

theorem insertEdges_h_fresh
    (P : PointedHypermap) (xs : List P.map.Dart)
    (hproper : P.ProperRingHead)
    (hxs : (P.map.insertEdges xs).Nodup) :
    (P.h.map.insertEdges
      (P.h.map.node P.h.point :: P.h.point ::
        P.h.map.face P.h.point :: xs.map P.hOld)).Nodup := by
  rw [Hypermap.insertEdges_cons, Hypermap.insertEdges_cons,
    Hypermap.insertEdges_cons,
    Hypermap.insertEdges_map P.hOld P.hOld_edge]
  have hyLong : P.y.LongRingHead := P.y_longRingHead_of_proper hproper
  have hyLong' :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new := by
    simpa [PointedHypermap.y] using hyLong
  have hnode :
      P.h.map.node P.h.point =
        ExtDart.old (ExtDart.old ExtDart.newEdge) := by
    change (Hypermap.extensionH P.map P.point).node ExtDart.new = _
    unfold Hypermap.extensionH Hypermap.extensionN
    rw [Hypermap.ExtensionN.node_new, if_pos hyLong']
    exact congrArg ExtDart.old
      (Hypermap.extensionY_node_new P.map P.point)
  have hedgeNode :
      P.h.map.edge (P.h.map.node P.h.point) =
        ExtDart.old (ExtDart.old ExtDart.new) := by
    rw [hnode]
    rfl
  have hface :
      P.h.map.face P.h.point = ExtDart.old ExtDart.new := by
    exact Hypermap.extensionH_face_new P.map P.point
  have hedgeFace :
      P.h.map.edge (P.h.map.face P.h.point) =
        ExtDart.old ExtDart.newEdge := by
    rw [hface]
    rfl
  have hedgePoint :
      P.h.map.edge P.h.point = ExtDart.newEdge := rfl
  rw [hedgeNode, hnode, hedgeFace, hface, hedgePoint]
  change
    (([ExtDart.old (ExtDart.old ExtDart.newEdge),
        ExtDart.old (ExtDart.old ExtDart.new),
        ExtDart.new, ExtDart.newEdge,
        ExtDart.old ExtDart.new, ExtDart.old ExtDart.newEdge] :
          List P.h.map.Dart) ++
      (P.map.insertEdges xs).map P.hOld).Nodup
  let fresh : List P.h.map.Dart :=
    [ExtDart.old (ExtDart.old ExtDart.newEdge),
      ExtDart.old (ExtDart.old ExtDart.new),
      ExtDart.new, ExtDart.newEdge,
      ExtDart.old ExtDart.new, ExtDart.old ExtDart.newEdge]
  let ys := (P.map.insertEdges xs).map P.hOld
  have hfresh : fresh.Nodup := by
    apply List.Nodup.of_map hFreshTag
    change ([5, 4, 0, 1, 2, 3] : List Nat).Nodup
    decide
  have hys : ys.Nodup := List.Nodup.map P.hOld_injective hxs
  have hold (x : P.map.Dart) : P.hOld x ∉ fresh := by
    intro hx
    have htag : hFreshTag (P.hOld x) ∈ fresh.map hFreshTag :=
      List.mem_map_of_mem hx
    change (6 : Nat) ∈ [5, 4, 0, 1, 2, 3] at htag
    simp at htag
  have hdisjoint :
      ∀ a ∈ fresh, ∀ b ∈ ys, a ≠ b := by
    intro a ha b hb hab
    rcases List.mem_map.mp hb with ⟨x, _hx, hx⟩
    exact hold x ((hx.trans hab.symm) ▸ ha)
  exact List.nodup_append.mpr ⟨hfresh, hys, hdisjoint⟩

end CFContract.Internal

/-- Coq `ctrenum`: one representative for every edge that becomes internal
during a configuration construction. -/
noncomputable def cpContractDarts :
    (cp : CProg) → List (cpmap cp).map.Dart
  | [] => []
  | CpStep.rotate n :: cp =>
      (cpContractDarts cp).map
        (oldStep (CpStep.rotate n) (cpmap cp))
  | CpStep.y :: cp =>
      if cp = [] then []
      else
        ((cpmap cp).map.node (cpmap cp).point ::
            cpContractDarts cp).map
          (oldStep CpStep.y (cpmap cp))
  | CpStep.h :: cp =>
      (cpmap (CpStep.h :: cp)).map.face
          (cpmap (CpStep.h :: cp)).point ::
        ((cpmap cp).map.node (cpmap cp).point ::
            (cpmap cp).point :: cpContractDarts cp).map
          (oldStep CpStep.h (cpmap cp))
  | _ :: _ => []

@[simp]
theorem cpContractDarts_nil :
    cpContractDarts [] = [] :=
  by simp [cpContractDarts]

@[simp]
theorem cpContractDarts_rotate (n : Nat) (cp : CProg) :
    cpContractDarts (CpStep.rotate n :: cp) = cpContractDarts cp :=
  by
    rw [cpContractDarts]
    change (cpContractDarts cp).map id = cpContractDarts cp
    simp

@[simp]
theorem cpContractDarts_y_nil :
    cpContractDarts [CpStep.y] = [] :=
  by simp [cpContractDarts]

theorem cpContractDarts_y_cons (s : CpStep) (cp : CProg) :
    cpContractDarts (CpStep.y :: s :: cp) =
      ((cpmap (s :: cp)).map.node (cpmap (s :: cp)).point ::
          cpContractDarts (s :: cp)).map (cpmap (s :: cp)).yOld :=
  by simp [cpContractDarts, oldStep]

@[simp]
theorem cpContractDarts_h (cp : CProg) :
    cpContractDarts (CpStep.h :: cp) =
      (cpmap (CpStep.h :: cp)).map.face
          (cpmap (CpStep.h :: cp)).point ::
        ((cpmap cp).map.node (cpmap cp).point ::
            (cpmap cp).point :: cpContractDarts cp).map
          (cpmap cp).hOld :=
  by simp [cpContractDarts, oldStep]

/-- Coq `size_ctrenum`. -/
@[simp]
theorem length_cpContractDarts :
    ∀ cp : CProg,
      (cpContractDarts cp).length = CProg.contractEdgeSize cp
  | [] => rfl
  | CpStep.rotate n :: cp => by
      simpa [CProg.contractEdgeSize] using length_cpContractDarts cp
  | CpStep.reverseRotate :: cp => by
      simp [cpContractDarts, CProg.contractEdgeSize]
  | CpStep.y :: [] => by simp [cpContractDarts, CProg.contractEdgeSize]
  | CpStep.y :: s :: cp => by
      rw [cpContractDarts]
      simp only [if_neg (List.cons_ne_nil s cp), List.length_map,
        List.length_cons,
        CProg.contractEdgeSize]
      rw [length_cpContractDarts (s :: cp)]
  | CpStep.h :: cp => by
      simp [cpContractDarts, CProg.contractEdgeSize,
        length_cpContractDarts cp]
  | CpStep.u :: cp => by
      simp [cpContractDarts, CProg.contractEdgeSize]
  | CpStep.k :: cp => by
      simp [cpContractDarts, CProg.contractEdgeSize]
  | CpStep.a :: cp => by
      simp [cpContractDarts, CProg.contractEdgeSize]

/-- The recursive `cfctr` contract selection: ring edges followed by kernel
edges, exactly as in Coq `cfctr_correct`. -/
noncomputable def cpContractSelection
    (mr mc : List Bool) (cp : CProg) : List (cpmap cp).map.Dart :=
  CfMask.select mr (cpRing cp) ++
    CfMask.select mc (cpContractDarts cp)

noncomputable def cpContractFinset
    (mr mc : List Bool) (cp : CProg) : Finset (cpmap cp).map.Dart :=
  (cpContractSelection mr mc cp).toFinset

/-- Semantic postcondition of Coq `cfctr_correct`: a successful executable
contract produces an ordinary coloring whose surviving boundary colors are
exactly the uncontracted source boundary colors. -/
def ContractProgramCorrect
    (mr mc : List Bool) (cp cpc : CProg) : Prop :=
  ∀ k : (cpmap cp).map.Dart → Color,
    (cpmap cp).map.ContractColoring (cpContractFinset mr mc cp) k →
      ∃ k' : (cpmap cpc).map.Dart → Color,
        (cpmap cpc).map.Coloring k' ∧
          cpRingCycle cpc ∧
            (cpmap cpc).map.colorsOn k' (cpRing cpc) =
            (cpmap cp).map.colorsOn k
              (CfMask.select (mr.map Bool.not) (cpRing cp))

/-- Set-based form of the tail in Coq `sparse_cfctr`: opposite ring darts and
both orientations of selected kernel edges. -/
noncomputable def cpSparseTail
    (mr mc : List Bool) (cp : CProg) : Finset (cpmap cp).map.Dart :=
  ((CfMask.select mr (cpRing cp)).toFinset.image (cpmap cp).map.edge) ∪
    (cpmap cp).map.contractClosure
      ((CfMask.select mc (cpContractDarts cp)).toFinset)

/-- Duplicate-sensitive pointed version of Coq `sparse (G :: cc)`. -/
def RootSparse (P : PointedHypermap) (s : Finset P.map.Dart) : Prop :=
  P.point ∉ s ∧ P.map.Sparse (insert P.point s)

theorem RootSparse.sparse
    {P : PointedHypermap} {s : Finset P.map.Dart}
    (h : RootSparse P s) :
    P.map.Sparse s := by
  intro x y hx hy hxy
  exact h.2 (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy

theorem RootSparse.mono
    {P : PointedHypermap} {s t : Finset P.map.Dart}
    (h : RootSparse P t) (hst : s ⊆ t) :
    RootSparse P s := by
  constructor
  · exact fun hs => h.1 (hst hs)
  · intro x y hx hy hxy
    rw [Finset.mem_insert] at hx hy
    exact h.2
      (hx.elim (fun hEq => hEq ▸ Finset.mem_insert_self _ _)
        (fun hs => Finset.mem_insert_of_mem (hst hs)))
      (hy.elim (fun hEq => hEq ▸ Finset.mem_insert_self _ _)
        (fun hs => Finset.mem_insert_of_mem (hst hs)))
      hxy

theorem Hypermap.rootSparse_replace
    {G : Hypermap} {s : Finset G.Dart} {a b : G.Dart}
    (h : a ∉ s ∧ G.Sparse (insert a s))
    (hab : PermReachable G.node a b) :
    b ∉ s ∧ G.Sparse (insert b s) := by
  have hba := PermReachable.symm G.node hab
  have hbnot : b ∉ s := by
    intro hb
    have habEq := h.2 (by simp) (Finset.mem_insert_of_mem hb) hab
    exact h.1 (habEq ▸ hb)
  refine ⟨hbnot, ?_⟩
  intro x y hx hy hxy
  rw [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · have hay : PermReachable G.node a y :=
        PermReachable.trans G.node hab hxy
      have hayEq := h.2 (by simp) (Finset.mem_insert_of_mem hy) hay
      rw [← hayEq] at hy
      exact (h.1 hy).elim
  · rcases hy with rfl | hy
    · have hxa : PermReachable G.node x a :=
        PermReachable.trans G.node hxy hba
      have hxaEq := h.2 (Finset.mem_insert_of_mem hx) (by simp) hxa
      rw [hxaEq] at hx
      exact (h.1 hx).elim
    · exact h.2 (Finset.mem_insert_of_mem hx)
        (Finset.mem_insert_of_mem hy) hxy

theorem cpSparseTail_rotate_eq
    {cp : CProg} {n : Nat} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : mr.length = CProg.ringSize cp) :
    cpSparseTail mr mc (CpStep.rotate n :: cp) =
      cpSparseTail (CProg.rotateRight n mr) mc cp := by
  have hring :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle
      (n := n) (cpRingCycle_of_config hcfg)
  have hselected :
      (CfMask.select mr (cpRing (CpStep.rotate n :: cp))).toFinset =
        (CfMask.select (CProg.rotateRight n mr) (cpRing cp)).toFinset := by
    ext x
    rw [hring]
    have hmem :=
      (CfMask.mem_select_rotateRight_mask_rotateLeft_values_iff_of_length
        (α := (cpmap cp).map.Dart) n
        (mask := mr) (xs := cpRing cp) (x := x)
        (by simpa [length_cpRing] using hmr.symm)).symm
    constructor
    · intro hx
      exact List.mem_toFinset.mpr
        (hmem.mp (List.mem_toFinset.mp hx))
    · intro hx
      exact List.mem_toFinset.mpr
        (hmem.mpr (List.mem_toFinset.mp hx))
  unfold cpSparseTail
  rw [hselected, cpContractDarts_rotate]
  rfl

theorem cpContractFinset_rotate_eq
    {cp : CProg} {n : Nat} {mr mc : List Bool}
    (hcfg : CProg.config cp = true)
    (hmr : mr.length = CProg.ringSize cp) :
    cpContractFinset mr mc (CpStep.rotate n :: cp) =
      cpContractFinset (CProg.rotateRight n mr) mc cp := by
  have hring :
      cpRing (CpStep.rotate n :: cp) = CProg.rotateLeft n (cpRing cp) :=
    cpRing_rotate_of_ringCycle
      (n := n) (cpRingCycle_of_config hcfg)
  unfold cpContractFinset cpContractSelection
  ext x
  simp only [List.mem_toFinset, List.mem_append]
  rw [hring, cpContractDarts_rotate]
  have hsel :=
    CfMask.mem_select_rotateRight_mask_rotateLeft_values_iff_of_length
      (α := (cpmap cp).map.Dart) n
      (mask := mr) (xs := cpRing cp) (x := x)
      (by simpa [length_cpRing] using hmr.symm)
  constructor
  · intro hx
    exact List.mem_toFinset.mpr
      (List.mem_append.mpr (hx.imp hsel.mpr id))
  · intro hx
    have hx' := List.mem_toFinset.mp hx
    have hx'' := List.mem_append.mp hx'
    exact hx''.imp hsel.mp id


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
