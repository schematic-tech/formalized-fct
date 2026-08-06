import FourColorTheorem.FourColor.Hypermap.Patch.ImageEquiv

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

theorem diskImage_node
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x : G.Dart} (hx : P.InDiskImage x) :
    P.InDiskImage (G.node x) := by
  rcases hx with ⟨xd, rfl⟩
  exact ⟨Gd.node xd, P.map_nodeD xd⟩

theorem remainderImage_edge
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x : G.Dart} (hx : P.InRemainderImage x) :
    P.InRemainderImage (G.edge x) := by
  rcases hx with ⟨xr, rfl⟩
  exact ⟨Gr.edge xr, P.map_edgeR xr⟩

theorem remainderImage_edge_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.InRemainderImage (G.edge x) ↔ P.InRemainderImage x := by
  constructor
  · rintro ⟨xr, hxr⟩
    let yr := Gr.edge.symm xr
    refine ⟨yr, G.edge.injective ?_⟩
    calc
      G.edge (hr yr) = hr (Gr.edge yr) := (P.map_edgeR yr).symm
      _ = hr xr := by simp [yr]
      _ = G.edge x := hxr
  · exact P.remainderImage_edge

theorem diskImage_node_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.InDiskImage (G.node x) ↔ P.InDiskImage x := by
  constructor
  · rintro ⟨xd, hxd⟩
    let yd := Gd.node.symm xd
    refine ⟨yd, G.node.injective ?_⟩
    calc
      G.node (hd yd) = hd (Gd.node yd) := (P.map_nodeD yd).symm
      _ = hd xd := by simp [yd]
      _ = G.node x := hxd
  · exact P.diskImage_node

noncomputable def remainderDartEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.Dart ≃ {x : G.Dart // P.InRemainderImage x} :=
  Equiv.ofInjective hr P.injr

noncomputable def diskDartEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.Dart ≃ {x : G.Dart // P.InDiskImage x} :=
  Equiv.ofInjective hd P.injd

noncomputable def diskOffBoundaryEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    {xd : Gd.Dart // xd ∉ bGd} ≃
      {x : G.Dart // ¬ P.InRemainderImage x} :=
  offImageEquiv hd (fun xd => xd ∈ bGd) P.InRemainderImage
    P.injd P.disk_boundary_iff_remainder_overlap P.cover

noncomputable def remainderOffBoundaryEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    {xr : Gr.Dart // xr ∉ bGr} ≃
      {x : G.Dart // ¬ P.InDiskImage x} :=
  offImageEquiv hr (fun xr => xr ∈ bGr) P.InDiskImage
    P.injr P.remainder_boundary_iff_disk_overlap
    (fun x => (P.cover x).symm)

theorem edgeOrbitCount_remainderImage
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.edgeOrbitCount =
      Nat.card (PermOrbit
        (G.edge.subtypePerm
          (p := fun x => P.InRemainderImage x)
          P.remainderImage_edge_iff)) := by
  let e := P.remainderDartEquiv
  have hcomm (xr : Gr.Dart) :
      e (Gr.edge xr) =
        (G.edge.subtypePerm
          (p := fun x => P.InRemainderImage x)
          P.remainderImage_edge_iff) (e xr) := by
    apply Subtype.ext
    exact P.map_edgeR xr
  exact Nat.card_congr
    (permOrbitEquivOfConj e Gr.edge
      (G.edge.subtypePerm P.remainderImage_edge_iff) hcomm)

theorem edgeOrbitCount_diskOffBoundary
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Nat.card (PermOrbit
        (Gd.edge.subtypePerm
          (p := fun xd => xd ∉ bGd)
          (fun xd => not_congr (P.disk_boundary_edge_iff xd)))) =
      Nat.card (PermOrbit
        (G.edge.subtypePerm
          (p := fun x => ¬ P.InRemainderImage x)
          (fun x => not_congr (P.remainderImage_edge_iff x)))) := by
  let e := P.diskOffBoundaryEquiv
  have hcomm (xd : {xd : Gd.Dart // xd ∉ bGd}) :
      e ((Gd.edge.subtypePerm
          (p := fun yd => yd ∉ bGd)
          (fun yd => not_congr (P.disk_boundary_edge_iff yd))) xd) =
        (G.edge.subtypePerm
          (p := fun x => ¬ P.InRemainderImage x)
          (fun x => not_congr (P.remainderImage_edge_iff x))) (e xd) := by
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    exact P.map_edgeD xd xd.2
  exact Nat.card_congr
    (permOrbitEquivOfConj e
      (Gd.edge.subtypePerm
        (fun xd => not_congr (P.disk_boundary_edge_iff xd)))
      (G.edge.subtypePerm
        (fun x => not_congr (P.remainderImage_edge_iff x))) hcomm)

theorem nodeOrbitCount_diskImage
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.nodeOrbitCount =
      Nat.card (PermOrbit
        (G.node.subtypePerm
          (p := fun x => P.InDiskImage x)
          P.diskImage_node_iff)) := by
  let e := P.diskDartEquiv
  have hcomm (xd : Gd.Dart) :
      e (Gd.node xd) =
        (G.node.subtypePerm
          (p := fun x => P.InDiskImage x)
          P.diskImage_node_iff) (e xd) := by
    apply Subtype.ext
    exact P.map_nodeD xd
  exact Nat.card_congr
    (permOrbitEquivOfConj e Gd.node
      (G.node.subtypePerm P.diskImage_node_iff) hcomm)

theorem nodeOrbitCount_remainderOffBoundary
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Nat.card (PermOrbit
        (Gr.node.subtypePerm
          (p := fun xr => xr ∉ bGr)
          (fun xr => not_congr (P.remainder_boundary_node_iff xr)))) =
      Nat.card (PermOrbit
        (G.node.subtypePerm
          (p := fun x => ¬ P.InDiskImage x)
          (fun x => not_congr (P.diskImage_node_iff x)))) := by
  let e := P.remainderOffBoundaryEquiv
  have hcomm (xr : {xr : Gr.Dart // xr ∉ bGr}) :
      e ((Gr.node.subtypePerm
          (p := fun yr => yr ∉ bGr)
          (fun yr => not_congr (P.remainder_boundary_node_iff yr))) xr) =
        (G.node.subtypePerm
          (p := fun x => ¬ P.InDiskImage x)
          (fun x => not_congr (P.diskImage_node_iff x))) (e xr) := by
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    exact P.map_nodeR xr xr.2
  exact Nat.card_congr
    (permOrbitEquivOfConj e
      (Gr.node.subtypePerm
        (fun xr => not_congr (P.remainder_boundary_node_iff xr)))
      (G.node.subtypePerm
        (fun x => not_congr (P.diskImage_node_iff x))) hcomm)

theorem boundary_length_eq
    (P : Patch G Gd Gr hd hr bGd bGr) :
    bGr.length = bGd.length := by
  have h := congrArg List.length P.map_boundaryR
  simpa using h

theorem remainderBoundary_empty_iff
    (P : Patch G Gd Gr hd hr bGd bGr) :
    bGr = [] ↔ bGd = [] := by
  rw [List.eq_nil_iff_length_eq_zero, List.eq_nil_iff_length_eq_zero,
    P.boundary_length_eq]

/-- The edge-orbit identity used in Coq `genus_patch`.  Cutting contributes
one disk boundary edge orbit exactly when the boundary is nonempty. -/
theorem edgeOrbitCount_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.edgeOrbitCount + Gr.edgeOrbitCount =
      G.edgeOrbitCount + (if bGd = [] then 0 else 1) := by
  classical
  let hDb : ∀ xd, Gd.edge xd ∈ bGd ↔ xd ∈ bGd :=
    P.disk_boundary_edge_iff
  let hRi : ∀ x, P.InRemainderImage (G.edge x) ↔
      P.InRemainderImage x := P.remainderImage_edge_iff
  have hD := PermOrbit.card_eq_restricted_add_compl
    Gd.edge (fun xd => xd ∈ bGd) hDb
  have hG := PermOrbit.card_eq_restricted_add_compl
    G.edge P.InRemainderImage hRi
  have hBoundary :=
    FunctionCycle.restrictedOrbitCount Gd.edge bGd P.cycleD
  have hOff := P.edgeOrbitCount_diskOffBoundary
  have hR := P.edgeOrbitCount_remainderImage
  change Gd.edgeOrbitCount = _ + _ at hD
  change G.edgeOrbitCount = _ + _ at hG
  omega

/-- The node-orbit identity used in Coq `genus_patch`.  The dual boundary
contribution is the single remainder node orbit. -/
theorem nodeOrbitCount_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.nodeOrbitCount + Gr.nodeOrbitCount =
      G.nodeOrbitCount + (if bGd = [] then 0 else 1) := by
  classical
  let hDi : ∀ x, P.InDiskImage (G.node x) ↔ P.InDiskImage x :=
    P.diskImage_node_iff
  let hRb : ∀ xr, Gr.node xr ∈ bGr ↔ xr ∈ bGr :=
    P.remainder_boundary_node_iff
  have hG := PermOrbit.card_eq_restricted_add_compl
    G.node P.InDiskImage hDi
  have hR := PermOrbit.card_eq_restricted_add_compl
    Gr.node (fun xr => xr ∈ bGr) hRb
  have hBoundary :=
    FunctionCycle.restrictedOrbitCount Gr.node bGr P.cycleR
  have hOff := P.nodeOrbitCount_remainderOffBoundary
  have hD := P.nodeOrbitCount_diskImage
  have hEmpty := P.remainderBoundary_empty_iff
  change G.nodeOrbitCount = _ + _ at hG
  change Gr.nodeOrbitCount = _ + _ at hR
  by_cases hdEmpty : bGd = []
  · have hrEmpty : bGr = [] := hEmpty.mpr hdEmpty
    rw [if_pos hrEmpty] at hBoundary
    simp [hdEmpty]
    omega
  · have hrNonempty : bGr ≠ [] := fun h => hdEmpty (hEmpty.mp h)
    rw [if_neg hrNonempty] at hBoundary
    simp [hdEmpty]
    omega
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
