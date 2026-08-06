import FourColorTheorem.FourColor.Coloring.KempeMap.Chromograms

/-!
The two-dart Kempe reduction and its spliced node cycle.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- A map coloring rules out fixed points of the node permutation.  This is
Coq `n'id` at the start of `Kempe_map`. -/
theorem Coloring.node_ne_self
    (G : Hypermap.{u}) {k : G.Dart -> Color}
    (hk : G.Coloring k) (x : G.Dart) :
    G.node x ≠ x := by
  intro hnode
  have hface := Coloring.face_eq (G := G) hk (G.edge (G.node x))
  rw [G.face_edge_node, hnode] at hface
  exact Coloring.ne_edge (G := G) hk x hface

/-- The first deleted-map dart corresponding to Coq `ez' : WalkupN z`. -/
def kempeEdgeDart
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    (G.walkupN z).Dart :=
  ⟨G.edge z, Plain.edge_ne (G := G) hplain z⟩

/-- Coq's map `H := WalkupE ez'` after first deleting `z` by `WalkupN`. -/
def kempeReduction
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) : Hypermap.{u} :=
  (G.walkupN z).walkupE (G.kempeEdgeDart z hplain)

/-- Projection of the two-dart Kempe reduction into the original map. -/
def kempeProjection
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    (G.kempeReduction z hplain).Dart -> G.Dart :=
  fun x => x.1.1

/-- The original darts that survive the two-dart Kempe reduction. -/
abbrev KempeRemaining
    (G : Hypermap.{u}) (z : G.Dart) :=
  {x : G.Dart // x ≠ z ∧ x ≠ G.edge z}

/-- The nested Walkup carrier is exactly the complement of `z` and
`edge z`, not merely an injection into that complement. -/
def kempeRemainingEquiv
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain) :
    (G.kempeReduction z hplain).Dart ≃ G.KempeRemaining z where
  toFun x :=
    ⟨G.kempeProjection z hplain x,
      x.1.2,
      by
        intro hx
        apply x.2
        apply Subtype.ext
        exact hx⟩
  invFun x :=
    ⟨⟨x.1, x.2.1⟩,
      by
        intro hx
        exact x.2.2 (congrArg Subtype.val hx)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp]
theorem kempeRemainingEquiv_val
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : (G.kempeReduction z hplain).Dart) :
    (G.kempeRemainingEquiv z hplain x).1 =
      G.kempeProjection z hplain x :=
  rfl

@[simp]
theorem kempeRemainingEquiv_symm_projection
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (x : G.KempeRemaining z) :
    G.kempeProjection z hplain
      ((G.kempeRemainingEquiv z hplain).symm x) = x.1 :=
  rfl

/-- Lift a list all of whose darts survive the two-dart reduction. -/
def kempeLiftList
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (q : List G.Dart)
    (hq : forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z) :
    List (G.kempeReduction z hplain).Dart :=
  q.attach.map fun x =>
    (G.kempeRemainingEquiv z hplain).symm ⟨x.1, hq x.1 x.2⟩

@[simp]
theorem kempeLiftList_projection
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (q : List G.Dart)
    (hq : forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z) :
    (G.kempeLiftList z hplain q hq).map
        (G.kempeProjection z hplain) = q := by
  simp [kempeLiftList, Function.comp_def]

theorem kempeLiftList_nodup
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (q : List G.Dart)
    (hq : forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z)
    (hqn : q.Nodup) :
    (G.kempeLiftList z hplain q hq).Nodup := by
  apply List.Nodup.of_map (G.kempeProjection z hplain)
  rw [G.kempeLiftList_projection z hplain q hq]
  exact hqn

/-- Reflect a function cycle through an injective list map. -/
theorem functionCycle_of_map_injective
    {α β : Type _} [DecidableEq α] [DecidableEq β]
    {f : α -> α} {g : β -> β} {e : α -> β} {s : List α}
    (he : Function.Injective e)
    (hsn : s.Nodup)
    (hc : FunctionCycle g (s.map e))
    (hcomm : forall x, x ∈ s -> e (f x) = g (e x)) :
    FunctionCycle f s := by
  apply FunctionCycle.of_eq_next hsn
  intro x hx
  apply he
  calc
    e (f x) = g (e x) := hcomm x hx
    _ = (s.map e).next (e x) (List.mem_map_of_mem hx) :=
      FunctionCycle.eq_next hc (hsn.map he) (e x)
        (List.mem_map_of_mem hx)
    _ = e (s.next x hx) :=
      List.next_map_injective e he s hsn x hx

/-- The node permutation seen through the Kempe reduction projection. -/
def kempeSpliceNode
    (G : Hypermap.{u}) (z x : G.Dart) : G.Dart :=
  if G.node x = z then G.node (G.edge z)
  else if G.node x = G.edge z then G.node z
  else G.node x

theorem functionPath_kempeSpliceNode
    (G : Hypermap.{u}) (z a : G.Dart) (p : List G.Dart)
    (hp : FunctionPath G.node a p)
    (hsurvive : forall x, x ∈ a :: p -> x ≠ z ∧ x ≠ G.edge z) :
    FunctionPath (G.kempeSpliceNode z) a p := by
  induction p generalizing a with
  | nil => trivial
  | cons b p ih =>
      rcases hp with ⟨hab, hp⟩
      constructor
      · have hb := hsurvive b (by simp)
        simp [kempeSpliceNode, hab, hb.1, hb.2]
      · apply ih b hp
        intro x hx
        exact hsurvive x (by simp only [List.mem_cons] at hx ⊢; tauto)

/-- Coq's fixed-face branch of `invh_r1`: when `face z = z`, deleting the
first two darts of an aligned node cycle leaves a node cycle for the spliced
node action. -/
theorem kempeSpliceCycle_of_face_fixed
    (G : Hypermap.{u}) (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hface : G.face z = z) :
    FunctionCycle (G.kempeSpliceNode z) p ∧
      p.Nodup ∧
      (forall x, x ∈ p -> x ≠ z ∧ x ≠ G.edge z) := by
  have hnodeEdge : G.node z = G.edge z := by
    rw [← Plain.node_face_eq_edge (G := G) hplain z, hface]
  have hzmem : z ∉ G.node z :: p := (List.nodup_cons.mp hnodup).1
  have htailNodup : (G.node z :: p).Nodup :=
    (List.nodup_cons.mp hnodup).2
  have hnodeNotMem : G.node z ∉ p :=
    (List.nodup_cons.mp htailNodup).1
  have hpNodup : p.Nodup := (List.nodup_cons.mp htailNodup).2
  have hsurvive : forall x, x ∈ p -> x ≠ z ∧ x ≠ G.edge z := by
    intro x hx
    constructor
    · intro hxz
      subst x
      exact hzmem (by simp [hx])
    · intro hxe
      rw [← hnodeEdge] at hxe
      subst x
      exact hnodeNotMem hx
  refine ⟨?_, hpNodup, hsurvive⟩
  cases p with
  | nil => trivial
  | cons a q =>
      have hpath0 := hcycle.1
      rcases hpath0 with ⟨_, hpath1⟩
      rcases hpath1 with ⟨hfirst, hpath⟩
      have hsurviveA :
          forall x, x ∈ a :: q -> x ≠ z ∧ x ≠ G.edge z := by
        intro x hx
        exact hsurvive x hx
      have hpathSplice :=
        G.functionPath_kempeSpliceNode z a q hpath hsurviveA
      constructor
      · exact hpathSplice
      · have hclose : G.node ((a :: q).getLastD a) = z := by
          simpa [List.getLastD] using hcycle.2
        change G.kempeSpliceNode z ((a :: q).getLastD a) = a
        rw [kempeSpliceNode, if_pos hclose, ← hnodeEdge, hfirst]

/-- Coq's non-fixed-face branch of `invh_r1`: the two darts inserted before
the old tail are `node (edge z)` and `face z`.  Quasicubicity at the latter
is precisely what makes this a cycle. -/
theorem kempeSpliceCycle_of_face_not_mem
    (G : Hypermap.{u}) (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hquasi : G.Quasicubic (z :: G.node z :: p))
    (hfaceOut : G.face z ∉ z :: G.node z :: p) :
    let q := G.node (G.edge z) :: G.face z :: G.node z :: p
    FunctionCycle (G.kempeSpliceNode z) q ∧
      q.Nodup ∧
      (forall x, x ∈ q -> x ≠ z ∧ x ≠ G.edge z) := by
  let fz := G.face z
  let ez := G.edge z
  let nz := G.node z
  let nez := G.node ez
  have hnodeFz : G.node fz = ez := by
    exact Plain.node_face_eq_edge (G := G) hplain z
  have hcubicFz := hquasi fz hfaceOut
  have hnodeNez : G.node nez = fz := by
    change G.node (G.node ez) = fz
    rw [← hnodeFz]
    exact hcubicFz.1
  have hfzNez : fz ≠ nez := by
    intro h
    exact hnode nez (hnodeNez.trans h)
  have hfzZ : fz ≠ z := by
    intro h
    apply hfaceOut
    simp only [List.mem_cons]
    left
    exact h
  have hfzEz : fz ≠ ez := by
    intro h
    exact hnode fz (hnodeFz.trans h.symm)
  have hnezEz : nez ≠ ez := hnode ez
  have hnezZ : nez ≠ z := by
    intro h
    have hnzFz : nz = fz := by
      change G.node z = fz
      rw [← h, hnodeNez]
    apply hfaceOut
    simp only [List.mem_cons]
    right
    left
    exact hnzFz.symm
  have hzmem : z ∉ nz :: p := by
    simpa [nz] using (List.nodup_cons.mp hnodup).1
  have htailNodup : (nz :: p).Nodup := by
    simpa [nz] using (List.nodup_cons.mp hnodup).2
  have hfzNotTail : fz ∉ nz :: p := by
    intro h
    exact hfaceOut (by simp [fz, nz, h])
  have hnezNotTail : nez ∉ nz :: p := by
    intro hnezMem
    have hnezMemR : nez ∈ z :: G.node z :: p := by
      simpa [nz] using List.mem_cons_of_mem z hnezMem
    have hfzMemR : fz ∈ z :: G.node z :: p := by
      rw [← hnodeNez]
      exact hcycle.image_mem hnezMemR
    exact hfaceOut (by simpa [fz] using hfzMemR)
  have hezNotTail : ez ∉ nz :: p := by
    intro hezMem
    have hezMemR : ez ∈ z :: G.node z :: p := by
      simpa [nz] using List.mem_cons_of_mem z hezMem
    have hfzMemR : fz ∈ z :: G.node z :: p := by
      have himage :=
        (FunctionCycle.image_mem_iff hcycle G.node.injective fz).1
      apply himage
      simpa [hnodeFz] using hezMemR
    exact hfaceOut (by simpa [fz] using hfzMemR)
  have htailSurvive :
      forall x, x ∈ nz :: p -> x ≠ z ∧ x ≠ ez := by
    intro x hx
    constructor
    · intro hxz
      subst x
      exact hzmem hx
    · intro hxe
      subst x
      exact hezNotTail hx
  have hqSurvive :
      forall x, x ∈ nez :: fz :: nz :: p -> x ≠ z ∧ x ≠ ez := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨hnezZ, hnezEz⟩
    · exact ⟨hfzZ, hfzEz⟩
    · exact htailSurvive x (by simpa only [List.mem_cons] using hx)
  have hqNodup : (nez :: fz :: nz :: p).Nodup := by
    simp only [List.nodup_cons]
    exact ⟨by
      simpa only [List.mem_cons, not_or] using
        And.intro hfzNez.symm hnezNotTail,
      hfzNotTail, (List.nodup_cons.mp htailNodup).1,
      (List.nodup_cons.mp htailNodup).2⟩
  have hpath0 := hcycle.1
  rcases hpath0 with ⟨_, htailPath⟩
  have htailSplice :=
    G.functionPath_kempeSpliceNode z nz p htailPath htailSurvive
  have hstepNez : G.kempeSpliceNode z nez = fz := by
    rw [kempeSpliceNode, hnodeNez, if_neg hfzZ, if_neg hfzEz]
  have hstepFz : G.kempeSpliceNode z fz = nz := by
    have hezZ : ez ≠ z := Plain.edge_ne (G := G) hplain z
    rw [kempeSpliceNode, hnodeFz, if_neg hezZ, if_pos rfl]
  have hclose : G.node ((nz :: p).getLastD nz) = z := by
    simpa [List.getLastD, nz] using hcycle.2
  refine ⟨?_, hqNodup, hqSurvive⟩
  constructor
  · exact ⟨hstepNez, hstepFz, htailSplice⟩
  · change G.kempeSpliceNode z ((nz :: p).getLastD nz) = nez
    rw [kempeSpliceNode, if_pos hclose]


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
