import FourColorTheorem.FourColor.Hypermap.Patch.Topology

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

private def ReachableClosure
    (H : Hypermap) (p : H.Dart → Prop) (x : H.Dart) : Prop :=
  ∃ y, p y ∧ H.Reachable y x

private theorem reachableClosure_congr
    (H : Hypermap) (p : H.Dart → Prop) {x y : H.Dart}
    (hxy : H.Reachable x y) :
    ReachableClosure H p x ↔ ReachableClosure H p y := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx.trans hxy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, hzy.trans (H.reachable_symm hxy)⟩

private theorem card_eq_subtype_add_compl
    {A : Type*} [Finite A] (p : A → Prop) :
    Nat.card A = Nat.card {a : A // p a} + Nat.card {a : A // ¬ p a} := by
  classical
  rw [← Nat.card_sum]
  exact (Nat.card_congr (Equiv.sumCompl p)).symm

/-- Disk reachability maps to host reachability even across the patch
boundary. -/
theorem mapD_link_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart} (hxy : Gd.Link xd yd) :
    G.Reachable (hd xd) (hd yd) := by
  rcases hxy with rfl | rfl | rfl
  · have hedge : G.Reachable (hd xd) (G.edge (hd xd)) :=
      G.reachable_edge (hd xd)
    have hface : G.Reachable (hd (Gd.edge xd)) (G.edge (hd xd)) :=
      G.facePermReachable_reachable
        (P.map_edgeD_face_reachable_host_edge xd)
    exact hedge.trans (G.reachable_symm hface)
  · rw [P.map_nodeD]
    exact G.reachable_node (hd xd)
  · exact G.facePermReachable_reachable
      (P.map_faceD_reachable xd)

theorem mapD_reachable_host
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart} (hxy : Gd.Reachable xd yd) :
    G.Reachable (hd xd) (hd yd) := by
  induction hxy with
  | refl => exact G.reachable_refl _
  | tail _ hstep ih => exact ih.trans (P.mapD_link_reachable hstep)

theorem mapR_link_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart} (hxy : Gr.Link xr yr) :
    G.Reachable (hr xr) (hr yr) := by
  rcases hxy with rfl | rfl | rfl
  · rw [P.map_edgeR]
    exact G.reachable_edge (hr xr)
  · by_cases hxr : xr ∈ bGr
    · have hnxr : Gr.node xr ∈ bGr :=
        (P.remainder_boundary_node_iff xr).2 hxr
      rcases (P.remainder_boundary_iff_disk_overlap xr).1 hxr with
        ⟨xd, hxd⟩
      rcases (P.remainder_boundary_iff_disk_overlap (Gr.node xr)).1 hnxr with
        ⟨yd, hyd⟩
      have hxdBoundary : xd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap xd).2 ⟨xr, hxd.symm⟩
      have hydBoundary : yd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap yd).2
          ⟨Gr.node xr, hyd.symm⟩
      have hdisk : Gd.Reachable xd yd :=
        Gd.edgePermReachable_reachable
          (P.cycleD.permReachable_of_mem_mem hxdBoundary hydBoundary)
      simpa [hxd, hyd] using P.mapD_reachable_host hdisk
    · rw [P.map_nodeR xr hxr]
      exact G.reachable_node (hr xr)
  · exact G.facePermReachable_reachable
      (P.map_faceR_reachable_of_reachable
        (PermReachable.forward Gr.face xr))

theorem mapR_reachable_host
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart} (hxy : Gr.Reachable xr yr) :
    G.Reachable (hr xr) (hr yr) := by
  induction hxy with
  | refl => exact G.reachable_refl _
  | tail _ hstep ih => exact ih.trans (P.mapR_link_reachable hstep)

theorem reachableR_of_map_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr yr : Gr.Dart}
    (hxy : G.Reachable (hr xr) (hr yr)) :
    Gr.Reachable xr yr := by
  rcases P.componentLiftState_of_reachable hxy with
    ⟨zr, hzrMap, hxrZr⟩ |
      ⟨zr, yd, xd, hxrZr, hydMap, _hydXd, hxdMap⟩
  · simpa [P.injr hzrMap] using hxrZr
  · have hzrBoundary : zr ∈ bGr :=
      (P.remainder_boundary_iff_disk_overlap zr).2 ⟨yd, hydMap⟩
    have hyrBoundary : yr ∈ bGr :=
      (P.remainder_boundary_iff_disk_overlap yr).2 ⟨xd, hxdMap⟩
    exact hxrZr.trans
      (P.reachableR_of_boundary_mem hzrBoundary hyrBoundary)

/-- Host components meeting the remainder image. -/
def RemainderClosure
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) : Prop :=
  ReachableClosure G P.InRemainderImage x

/-- Disk components meeting the boundary cycle. -/
def DiskBoundaryComponent
    (_P : Patch G Gd Gr hd hr bGd bGr) (xd : Gd.Dart) : Prop :=
  ReachableClosure Gd (fun yd => yd ∈ bGd) xd

theorem remainderClosure_congr_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x y : G.Dart} (hxy : G.Reachable x y) :
    P.RemainderClosure x ↔ P.RemainderClosure y :=
  reachableClosure_congr G P.InRemainderImage hxy

theorem diskBoundaryComponent_congr_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart} (hxy : Gd.Reachable xd yd) :
    P.DiskBoundaryComponent xd ↔ P.DiskBoundaryComponent yd :=
  reachableClosure_congr Gd (fun zd => zd ∈ bGd) hxy

/-- Lift a component-invariant dart predicate to generated components. -/
def ComponentPred
    (H : Hypermap) (p : H.Dart → Prop)
    (hp : ∀ x y, H.Reachable x y → (p x ↔ p y)) :
    H.Component → Prop :=
  Quotient.lift p (by
    intro x y hxy
    exact propext (hp x y hxy))

@[simp]
theorem componentPred_componentOf
    (H : Hypermap) (p : H.Dart → Prop)
    (hp : ∀ x y, H.Reachable x y → (p x ↔ p y))
    (x : H.Dart) :
    ComponentPred H p hp (H.componentOf x) = p x :=
  rfl

theorem remainderClosure_mapD_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (xd : Gd.Dart) :
    P.RemainderClosure (hd xd) ↔ P.DiskBoundaryComponent xd := by
  constructor
  · rintro ⟨y, ⟨xr, hxr⟩, hyx⟩
    have hreach : G.Reachable (hr xr) (hd xd) := by
      rw [hxr]
      exact hyx
    rcases P.componentLiftState_of_reachable hreach with
      ⟨yr, hyrMap, _⟩ |
        ⟨yr, yd, zd, _, hydMap, hydZd, hzdMap⟩
    · have hxdBoundary : xd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap xd).2
          ⟨yr, hyrMap⟩
      exact ⟨xd, hxdBoundary, Gd.reachable_refl xd⟩
    · have hydBoundary : yd ∈ bGd :=
        (P.disk_boundary_iff_remainder_overlap yd).2
          ⟨yr, hydMap.symm⟩
      have hzdEq : zd = xd := P.injd hzdMap
      exact ⟨yd, hydBoundary, hzdEq ▸ hydZd⟩
  · rintro ⟨yd, hydBoundary, hydXd⟩
    refine ⟨hd yd, ?_, P.mapD_reachable_host hydXd⟩
    exact (P.disk_boundary_iff_remainder_overlap yd).1 hydBoundary

set_option linter.unusedVariables false in
/-- A host path outside the remainder closure lifts uniquely to the disk. -/
def DiskComponentLiftState
    (P : Patch G Gd Gr hd hr bGd bGr)
    (root : Gd.Dart) (x : G.Dart) : Prop :=
  ∃ yd : Gd.Dart, Gd.Reachable root yd ∧ hd yd = x

theorem diskComponentLiftState_link
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gd.Dart} {x y : G.Dart}
    (hrootOff : ¬ P.RemainderClosure (hd root))
    (hs : P.DiskComponentLiftState root x)
    (hxy : G.Link x y) :
    P.DiskComponentLiftState root y := by
  rcases hs with ⟨yd, hrootYd, hydMap⟩
  have hydOff : yd ∉ bGd := by
    intro hydBoundary
    apply hrootOff
    have hclosureYd : P.RemainderClosure (hd yd) :=
      (P.remainderClosure_mapD_iff yd).2
        ⟨yd, hydBoundary, Gd.reachable_refl yd⟩
    exact (P.remainderClosure_congr_reachable
      (P.mapD_reachable_host hrootYd)).2 hclosureYd
  rcases hxy with rfl | rfl | rfl
  · exact ⟨Gd.edge yd, hrootYd.trans (Gd.reachable_edge yd), by
      calc
        hd (Gd.edge yd) = G.edge (hd yd) := P.map_edgeD yd hydOff
        _ = G.edge x := congrArg G.edge hydMap⟩
  · exact ⟨Gd.node yd, hrootYd.trans (Gd.reachable_node yd), by
      calc
        hd (Gd.node yd) = G.node (hd yd) := P.map_nodeD yd
        _ = G.node x := congrArg G.node hydMap⟩
  · exact ⟨Gd.face yd, hrootYd.trans (Gd.reachable_face yd), by
      calc
        hd (Gd.face yd) = G.face (hd yd) :=
          P.map_faceD_of_not_boundary yd hydOff
        _ = G.face x := congrArg G.face hydMap⟩

theorem diskComponentLiftState_of_reachable
    (P : Patch G Gd Gr hd hr bGd bGr)
    {root : Gd.Dart} {x : G.Dart}
    (hrootOff : ¬ P.RemainderClosure (hd root))
    (hreach : G.Reachable (hd root) x) :
    P.DiskComponentLiftState root x := by
  induction hreach with
  | refl => exact ⟨root, Gd.reachable_refl root, rfl⟩
  | tail _ hstep ih =>
      exact P.diskComponentLiftState_link hrootOff ih hstep

theorem reachableD_of_map_reachable_of_not_boundaryComponent
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd yd : Gd.Dart}
    (hxdOff : ¬ P.DiskBoundaryComponent xd)
    (hxy : G.Reachable (hd xd) (hd yd)) :
    Gd.Reachable xd yd := by
  have hclosureOff : ¬ P.RemainderClosure (hd xd) := by
    simpa [P.remainderClosure_mapD_iff xd] using hxdOff
  rcases P.diskComponentLiftState_of_reachable hclosureOff hxy with
    ⟨zd, hxdZd, hzdMap⟩
  exact hxdZd.trans (by rw [P.injd hzdMap])

noncomputable def remainderComponentMap
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.Component →
      {c : G.Component // ComponentPred G P.RemainderClosure
        (fun _ _ h => P.remainderClosure_congr_reachable h) c} :=
  Quotient.lift
    (fun xr => ⟨G.componentOf (hr xr),
      ⟨hr xr, ⟨xr, rfl⟩, G.reachable_refl (hr xr)⟩⟩)
    (by
      intro xr yr hxy
      apply Subtype.ext
      exact G.componentOf_eq_componentOf
        (P.mapR_reachable_host hxy))

theorem remainderComponentMap_injective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Injective P.remainderComponentMap := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d ?_ hcd
  intro xr yr hxy
  have hhost : G.componentOf (hr xr) = G.componentOf (hr yr) :=
    congrArg Subtype.val hxy
  exact Quot.sound
    (P.reachableR_of_map_reachable
      (G.reachable_of_componentOf_eq hhost))

theorem remainderComponentMap_surjective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Surjective P.remainderComponentMap := by
  rintro ⟨c, hc⟩
  refine Quotient.inductionOn c ?_ hc
  intro x hx
  rcases hx with ⟨y, ⟨xr, hxr⟩, hyx⟩
  refine ⟨Gr.componentOf xr, ?_⟩
  apply Subtype.ext
  apply G.componentOf_eq_componentOf
  rw [hxr]
  exact hyx

noncomputable def remainderComponentEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.Component ≃
      {c : G.Component // ComponentPred G P.RemainderClosure
        (fun _ _ h => P.remainderClosure_congr_reachable h) c} :=
  Equiv.ofBijective P.remainderComponentMap
    ⟨P.remainderComponentMap_injective,
      P.remainderComponentMap_surjective⟩

noncomputable def diskComponentMap
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.Component → G.Component :=
  Quotient.lift (fun xd => G.componentOf (hd xd)) (by
    intro xd yd hxy
    exact G.componentOf_eq_componentOf
      (P.mapD_reachable_host hxy))

@[simp]
theorem diskComponentMap_componentOf
    (P : Patch G Gd Gr hd hr bGd bGr) (xd : Gd.Dart) :
    P.diskComponentMap (Gd.componentOf xd) = G.componentOf (hd xd) :=
  rfl

theorem remainderClosure_diskComponentMap_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (c : Gd.Component) :
    ComponentPred G P.RemainderClosure
        (fun _ _ h => P.remainderClosure_congr_reachable h)
        (P.diskComponentMap c) ↔
      ComponentPred Gd P.DiskBoundaryComponent
        (fun _ _ h => P.diskBoundaryComponent_congr_reachable h) c := by
  refine Quotient.inductionOn c ?_
  intro xd
  exact P.remainderClosure_mapD_iff xd

noncomputable def diskComponentOffMap
    (P : Patch G Gd Gr hd hr bGd bGr) :
    {c : Gd.Component // ¬ ComponentPred Gd P.DiskBoundaryComponent
      (fun _ _ h => P.diskBoundaryComponent_congr_reachable h) c} →
    {c : G.Component // ¬ ComponentPred G P.RemainderClosure
      (fun _ _ h => P.remainderClosure_congr_reachable h) c} :=
  fun c => ⟨P.diskComponentMap c.1, fun h =>
    c.2 ((P.remainderClosure_diskComponentMap_iff c.1).1 h)⟩

theorem diskComponentOffMap_injective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Injective P.diskComponentOffMap := by
  rintro ⟨c, hc⟩ ⟨d, hd'⟩ hcd
  apply Subtype.ext
  revert hc hd' hcd
  refine Quotient.inductionOn₂ c d ?_
  intro xd yd hxdOff _hydOff hmap
  have hhostComp : G.componentOf (hd xd) = G.componentOf (hd yd) :=
    congrArg Subtype.val hmap
  have hhostReach : G.Reachable (hd xd) (hd yd) :=
    G.reachable_of_componentOf_eq hhostComp
  exact Quot.sound
    (P.reachableD_of_map_reachable_of_not_boundaryComponent
      hxdOff hhostReach)

theorem diskComponentOffMap_surjective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Surjective P.diskComponentOffMap := by
  rintro ⟨c, hc⟩
  refine Quotient.inductionOn c ?_ hc
  intro x hx
  rcases P.cover x with ⟨xd, hxd⟩ | hxr
  · have hxdOff : ¬ P.DiskBoundaryComponent xd := by
      intro hboundary
      apply hx
      have hclosure : P.RemainderClosure (hd xd) :=
        (P.remainderClosure_mapD_iff xd).2 hboundary
      simpa [hxd] using hclosure
    refine ⟨⟨Gd.componentOf xd, hxdOff⟩, ?_⟩
    apply Subtype.ext
    apply G.componentOf_eq_componentOf
    rw [hxd]
    exact G.reachable_refl x
  · exact False.elim (hx
      ⟨x, hxr, G.reachable_refl x⟩)

noncomputable def diskComponentOffEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    {c : Gd.Component // ¬ ComponentPred Gd P.DiskBoundaryComponent
      (fun _ _ h => P.diskBoundaryComponent_congr_reachable h) c} ≃
    {c : G.Component // ¬ ComponentPred G P.RemainderClosure
      (fun _ _ h => P.remainderClosure_congr_reachable h) c} :=
  Equiv.ofBijective P.diskComponentOffMap
    ⟨P.diskComponentOffMap_injective,
      P.diskComponentOffMap_surjective⟩

theorem diskBoundaryComponentCount
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Nat.card {c : Gd.Component //
        ComponentPred Gd P.DiskBoundaryComponent
          (fun _ _ h => P.diskBoundaryComponent_congr_reachable h) c} =
      if bGd = [] then 0 else 1 := by
  classical
  by_cases hb : bGd = []
  · rw [if_pos hb]
    apply Nat.card_eq_zero.mpr
    left
    constructor
    rintro ⟨c, hc⟩
    refine Quotient.inductionOn c ?_ hc
    intro xd hxd
    rcases hxd with ⟨yd, hyd, _⟩
    simp [hb] at hyd
  · rw [if_neg hb]
    rcases List.exists_cons_of_ne_nil hb with ⟨z, zs, rfl⟩
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      rintro ⟨c, hc⟩ ⟨d, hd'⟩
      apply Subtype.ext
      revert hc hd'
      refine Quotient.inductionOn₂ c d ?_
      intro xd yd hxd hyd
      rcases hxd with ⟨sx, hsx, hsxXd⟩
      rcases hyd with ⟨sy, hsy, hsyYd⟩
      have hsxSy : Gd.Reachable sx sy :=
        Gd.edgePermReachable_reachable
          (P.cycleD.permReachable_of_mem_mem hsx hsy)
      exact Quot.sound
        ((Gd.reachable_symm hsxXd).trans (hsxSy.trans hsyYd))
    · exact ⟨⟨Gd.componentOf z,
        ⟨z, by simp, Gd.reachable_refl z⟩⟩⟩

/-- The generated-component identity used in Coq `genus_patch`. -/
theorem componentCount_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.componentCount + Gr.componentCount =
      G.componentCount + (if bGd = [] then 0 else 1) := by
  classical
  let diskPred : Gd.Component → Prop :=
    ComponentPred Gd P.DiskBoundaryComponent
      (fun _ _ h => P.diskBoundaryComponent_congr_reachable h)
  let hostPred : G.Component → Prop :=
    ComponentPred G P.RemainderClosure
      (fun _ _ h => P.remainderClosure_congr_reachable h)
  letI : Finite Gd.Component :=
    Finite.of_surjective Gd.componentOf (by
      intro c
      refine Quotient.inductionOn c ?_
      intro xd
      exact ⟨xd, rfl⟩)
  letI : Finite G.Component :=
    Finite.of_surjective G.componentOf (by
      intro c
      refine Quotient.inductionOn c ?_
      intro x
      exact ⟨x, rfl⟩)
  have hDiskSplit : Gd.componentCount =
      Nat.card {c : Gd.Component // diskPred c} +
        Nat.card {c : Gd.Component // ¬ diskPred c} := by
    change Nat.card Gd.Component = _
    exact card_eq_subtype_add_compl diskPred
  have hHostSplit : G.componentCount =
      Nat.card {c : G.Component // hostPred c} +
        Nat.card {c : G.Component // ¬ hostPred c} := by
    change Nat.card G.Component = _
    exact card_eq_subtype_add_compl hostPred
  have hBoundary := P.diskBoundaryComponentCount
  have hR : Gr.componentCount =
      Nat.card {c : G.Component // hostPred c} :=
    Nat.card_congr P.remainderComponentEquiv
  have hOff : Nat.card {c : Gd.Component // ¬ diskPred c} =
      Nat.card {c : G.Component // ¬ hostPred c} :=
    Nat.card_congr P.diskComponentOffEquiv
  change Nat.card {c : Gd.Component // diskPred c} =
    (if bGd = [] then 0 else 1) at hBoundary
  omega
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
