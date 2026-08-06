
import FourColorTheorem.FourColor.Hypermap.Patch
import Mathlib.Data.List.NodupEquivFin

/-!
Sewing two hypermaps along oppositely oriented boundary cycles.

This ports the construction from Gonthier's `sew.v`.  The common boundary is
represented once, by the disk darts; remainder darts off the boundary form the
other summand.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u v

variable {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

private theorem prev_congr_list
    {α : Type _} [DecidableEq α]
    {l₁ l₂ : List α} (hl : l₁ = l₂)
    {x : α} (hx₁ : x ∈ l₁) (hx₂ : x ∈ l₂) :
    l₁.prev x hx₁ = l₂.prev x hx₂ := by
  subst l₂
  rfl

/-- The hypotheses of Coq `sew_map`. -/
structure SewBoundary
    (Gd : Hypermap.{u}) (Gr : Hypermap.{v})
    (bGd : List Gd.Dart) (bGr : List Gr.Dart) : Prop where
  cycleD : FunctionCycle Gd.edge bGd
  faceSimpleD : Gd.FaceSimple bGd
  cycleR : FunctionCycle Gr.node bGr
  nodupR : bGr.Nodup
  length_eq : bGd.length = bGr.length

namespace SewBoundary

variable (S : SewBoundary Gd Gr bGd bGr)

include S

theorem nodupD : bGd.Nodup :=
  FaceSimple.nodup (G := Gd) S.faceSimpleD

private def reverseMembershipEquiv :
    {x : Gr.Dart // x ∈ bGr.reverse} ≃ {x : Gr.Dart // x ∈ bGr} where
  toFun x := ⟨x.1, List.mem_reverse.mp x.2⟩
  invFun x := ⟨x.1, List.mem_reverse.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coq's `hdr`/`hrd` indexing, as one boundary equivalence.  Disk order is
matched with reversed remainder order. -/
noncomputable def boundaryEquiv :
    {x : Gd.Dart // x ∈ bGd} ≃ {x : Gr.Dart // x ∈ bGr} :=
  ((nodupD S).getEquiv bGd).symm |>.trans
    ((finCongr (by simpa using S.length_eq)).trans
      ((List.nodup_reverse.mpr S.nodupR).getEquiv bGr.reverse |>.trans
        reverseMembershipEquiv))

theorem boundaryEquiv_apply_val
    (i : Fin bGd.length) :
    ((boundaryEquiv S) ((nodupD S).getEquiv bGd i)).1 =
      bGr.reverse.get (finCongr (by simpa using S.length_eq) i) := by
  simp [boundaryEquiv, reverseMembershipEquiv]

theorem map_boundaryEquiv_attach :
    bGd.attach.map (fun x => ((boundaryEquiv S) x).1) = bGr.reverse := by
  apply List.ext_getElem
  · simp [S.length_eq]
  · intro i hi₁ hi₂
    have hiD : i < bGd.length := by simpa using hi₁
    have hiAttach : i < bGd.attach.length := by simpa using hiD
    let j : Fin bGd.length := ⟨i, hiD⟩
    have hgetD : bGd.attach[i]'(hiAttach) =
        (nodupD S).getEquiv bGd j := by
      apply Subtype.ext
      simp [j]
    rw [List.getElem_map, hgetD, boundaryEquiv_apply_val]
    rfl

theorem map_boundaryEquiv_attach_subtype :
    bGd.attach.map (boundaryEquiv S) =
      bGr.reverse.attach.map reverseMembershipEquiv := by
  apply List.ext_getElem
  · simp [S.length_eq]
  · intro i hi₁ hi₂
    have hiD : i < bGd.length := by simpa using hi₁
    have hiAttach : i < bGd.attach.length := by simpa using hiD
    let j : Fin bGd.length := ⟨i, hiD⟩
    have hgetD : bGd.attach[i]'(hiAttach) =
        (nodupD S).getEquiv bGd j := by
      apply Subtype.ext
      simp [j]
    apply Subtype.ext
    rw [List.getElem_map, List.getElem_map, hgetD,
      boundaryEquiv_apply_val]
    simp [j, reverseMembershipEquiv]

theorem map_boundaryEquiv_symm_attach :
    bGr.attach.map (boundaryEquiv S).symm = bGd.attach.reverse := by
  have h := congrArg
    (fun l : List {x : Gr.Dart // x ∈ bGr} =>
      l.reverse.map (boundaryEquiv S).symm)
    (map_boundaryEquiv_attach_subtype S)
  simpa [List.map_map, Function.comp_def, reverseMembershipEquiv] using h.symm

theorem boundaryEquiv_prev_val
    (xd : Gd.Dart) (hxd : xd ∈ bGd) :
    ((boundaryEquiv S)
        ⟨bGd.prev xd hxd, List.prev_mem bGd xd hxd⟩).1 =
      Gr.node ((boundaryEquiv S) ⟨xd, hxd⟩).1 := by
  let d : {x : Gd.Dart // x ∈ bGd} := ⟨xd, hxd⟩
  let f : {x : Gd.Dart // x ∈ bGd} → Gr.Dart :=
    fun z => ((boundaryEquiv S) z).1
  have hf : Function.Injective f := by
    intro x y hxy
    apply (boundaryEquiv S).injective
    exact Subtype.ext hxy
  have hdAttach : d ∈ bGd.attach := by simp [d]
  have hAttachNodup : bGd.attach.Nodup := (nodupD S).attach
  have hMapPrev := List.prev_map_injective f hf bGd.attach
    hAttachNodup d hdAttach
  have hfdRev : f d ∈ bGr.reverse := by
    exact List.mem_reverse.mpr ((boundaryEquiv S) d).2
  have hMapPrev' :
      bGr.reverse.prev (f d) hfdRev =
        f (bGd.attach.prev d hdAttach) := by
    have hfdMap : f d ∈ bGd.attach.map f :=
      List.mem_map_of_mem hdAttach
    have htransport := prev_congr_list
      (map_boundaryEquiv_attach S) hfdMap hfdRev
    exact htransport.symm.trans hMapPrev
  have hValPrev := List.prev_map_injective
    (fun z : {x : Gd.Dart // x ∈ bGd} => z.1)
    Subtype.val_injective bGd.attach hAttachNodup d hdAttach
  have hValPrev' :
      bGd.prev xd hxd = (bGd.attach.prev d hdAttach).1 := by
    simpa [d] using hValPrev
  have hdPrev :
      (⟨bGd.prev xd hxd, List.prev_mem bGd xd hxd⟩ :
        {x : Gd.Dart // x ∈ bGd}) = bGd.attach.prev d hdAttach :=
    Subtype.ext hValPrev'
  have hReverse := List.prev_reverse_eq_next bGr S.nodupR
    (f d) ((boundaryEquiv S) d).2
  have hNode := S.cycleR.eq_next S.nodupR
    (f d) ((boundaryEquiv S) d).2
  calc
    ((boundaryEquiv S)
        ⟨bGd.prev xd hxd, List.prev_mem bGd xd hxd⟩).1 =
        f (bGd.attach.prev d hdAttach) := by rw [hdPrev]
    _ = bGr.reverse.prev (f d) hfdRev := hMapPrev'.symm
    _ = bGr.next (f d) ((boundaryEquiv S) d).2 := hReverse
    _ = Gr.node (f d) := hNode.symm

private theorem edge_prev_eq
    (xd : Gd.Dart) (hxd : xd ∈ bGd) :
    Gd.edge (bGd.prev xd hxd) = xd := by
  have hprevMem := List.prev_mem bGd xd hxd
  calc
    Gd.edge (bGd.prev xd hxd) =
        bGd.next (bGd.prev xd hxd) hprevMem :=
      S.cycleD.eq_next (nodupD S) _ hprevMem
    _ = xd := List.next_prev bGd (nodupD S) xd hxd

def boundaryBackD
    (d : {x : Gd.Dart // x ∈ bGd}) : {x : Gd.Dart // x ∈ bGd} :=
  ⟨Gd.node (Gd.face d.1), by
    have hEq : Gd.node (Gd.face d.1) = bGd.prev d.1 d.2 := by
      apply Gd.edge.injective
      rw [edge_prev_eq S]
      exact Gd.edge_node_face d.1
    rw [hEq]
    exact List.prev_mem bGd d.1 d.2⟩

theorem boundaryBackD_eq_prev
    (d : {x : Gd.Dart // x ∈ bGd}) :
    (boundaryBackD S d).1 = bGd.prev d.1 d.2 := by
  apply Gd.edge.injective
  rw [edge_prev_eq S]
  exact Gd.edge_node_face d.1

/-- Coq `node_hdr`. -/
theorem node_boundaryEquiv
    (d : {x : Gd.Dart // x ∈ bGd}) :
    Gr.node ((boundaryEquiv S) d).1 =
      ((boundaryEquiv S) (boundaryBackD S d)).1 := by
  have hback : boundaryBackD S d =
      ⟨bGd.prev d.1 d.2, List.prev_mem bGd d.1 d.2⟩ :=
    Subtype.ext (boundaryBackD_eq_prev S d)
  rw [hback]
  exact (boundaryEquiv_prev_val S d.1 d.2).symm

/-- Dart type of Coq `sew_map`: all disk darts plus the remainder darts off
the identified boundary. -/
def SewDart
    (Gd : Hypermap.{u}) (Gr : Hypermap.{v}) (bGr : List Gr.Dart) :=
  Gd.Dart ⊕ {xr : Gr.Dart // xr ∉ bGr}

noncomputable instance sewDartFintype :
    Fintype (SewDart Gd Gr bGr) := by
  unfold SewDart
  letI : Finite {xr : Gr.Dart // xr ∉ bGr} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype {xr : Gr.Dart // xr ∉ bGr} := Fintype.ofFinite _
  infer_instance

noncomputable instance sewDartDecidableEq :
    DecidableEq (SewDart Gd Gr bGr) :=
  Classical.decEq _

/-- Coq `sewd`. -/
def sewd (xd : Gd.Dart) : SewDart Gd Gr bGr :=
  Sum.inl xd

/-- Coq `sewr`: boundary darts are represented by their matching disk dart. -/
noncomputable def sewr (xr : Gr.Dart) : SewDart Gd Gr bGr :=
  if hxr : xr ∈ bGr then
    sewd ((boundaryEquiv S).symm ⟨xr, hxr⟩).1
  else
    Sum.inr ⟨xr, hxr⟩

omit S in
theorem sewd_injective :
    Function.Injective (sewd : Gd.Dart → SewDart Gd Gr bGr) :=
  Sum.inl_injective

theorem sewr_boundary
    (xr : Gr.Dart) (hxr : xr ∈ bGr) :
    sewr S xr = sewd ((boundaryEquiv S).symm ⟨xr, hxr⟩).1 := by
  simp [sewr, hxr]

theorem sewr_offBoundary
    (xr : Gr.Dart) (hxr : xr ∉ bGr) :
    sewr S xr = Sum.inr ⟨xr, hxr⟩ := by
  simp [sewr, hxr]

theorem sewr_boundaryEquiv
    (d : {xd : Gd.Dart // xd ∈ bGd}) :
    sewr S ((boundaryEquiv S) d).1 = sewd d.1 := by
  rw [sewr_boundary S _ ((boundaryEquiv S) d).2]
  congr
  exact (boundaryEquiv S).symm_apply_apply d

theorem sewr_injective :
    Function.Injective (sewr S : Gr.Dart → SewDart Gd Gr bGr) := by
  intro x y hxy
  by_cases hx : x ∈ bGr
  · by_cases hy : y ∈ bGr
    · rw [sewr_boundary S x hx, sewr_boundary S y hy] at hxy
      have hval :
          ((boundaryEquiv S).symm ⟨x, hx⟩).1 =
            ((boundaryEquiv S).symm ⟨y, hy⟩).1 :=
        Sum.inl_injective hxy
      have hsub :
          (boundaryEquiv S).symm ⟨x, hx⟩ =
            (boundaryEquiv S).symm ⟨y, hy⟩ := Subtype.ext hval
      exact congrArg Subtype.val ((boundaryEquiv S).symm.injective hsub)
    · rw [sewr_boundary S x hx, sewr_offBoundary S y hy] at hxy
      cases hxy
  · by_cases hy : y ∈ bGr
    · rw [sewr_offBoundary S x hx, sewr_boundary S y hy] at hxy
      cases hxy
    · rw [sewr_offBoundary S x hx, sewr_offBoundary S y hy] at hxy
      exact congrArg (fun z => z.1) (Sum.inr_injective hxy)

theorem edge_mem_boundaryD_iff (xd : Gd.Dart) :
    Gd.edge xd ∈ bGd ↔ xd ∈ bGd :=
  FunctionCycle.image_mem_iff S.cycleD Gd.edge.injective xd

theorem node_mem_boundaryR_iff (xr : Gr.Dart) :
    Gr.node xr ∈ bGr ↔ xr ∈ bGr :=
  FunctionCycle.image_mem_iff S.cycleR Gr.node.injective xr

theorem node_symm_mem_boundaryR_iff (xr : Gr.Dart) :
    Gr.node.symm xr ∈ bGr ↔ xr ∈ bGr := by
  have h := node_mem_boundaryR_iff S (Gr.node.symm xr)
  simpa using h.symm

private noncomputable def sewEdgeFn :
    SewDart Gd Gr bGr → SewDart Gd Gr bGr
  | Sum.inl xd =>
      if hxd : xd ∈ bGd then
        sewr S (Gr.edge ((boundaryEquiv S) ⟨xd, hxd⟩).1)
      else
        sewd (Gd.edge xd)
  | Sum.inr xr =>
      sewr S (Gr.edge xr.1)

private noncomputable def sewFaceR
    (xr : Gr.Dart) : SewDart Gd Gr bGr :=
  match sewr S (Gr.face xr) with
  | Sum.inl xd => sewd (Gd.face xd)
  | Sum.inr yr => Sum.inr yr

private noncomputable def sewFaceFn :
    SewDart Gd Gr bGr → SewDart Gd Gr bGr
  | Sum.inl xd =>
      if hxd : xd ∈ bGd then
        sewFaceR S ((boundaryEquiv S) ⟨xd, hxd⟩).1
      else
        sewd (Gd.face xd)
  | Sum.inr xr =>
      sewFaceR S xr.1

private noncomputable def sewNodeFn :
    SewDart Gd Gr bGr → SewDart Gd Gr bGr
  | Sum.inl xd => sewd (Gd.node xd)
  | Sum.inr xr => sewr S (Gr.node xr.1)

private theorem sewFace_sewr
    (xr : Gr.Dart) :
    sewFaceFn S (sewr S xr) = sewFaceR S xr := by
  by_cases hxr : xr ∈ bGr
  · rw [sewr_boundary S xr hxr]
    simp only [sewd, sewFaceFn]
    have hdisk : ((boundaryEquiv S).symm ⟨xr, hxr⟩).1 ∈ bGd :=
      ((boundaryEquiv S).symm ⟨xr, hxr⟩).2
    rw [dif_pos hdisk]
    have hEq :
        (boundaryEquiv S)
            ((boundaryEquiv S).symm ⟨xr, hxr⟩) = ⟨xr, hxr⟩ :=
      (boundaryEquiv S).apply_symm_apply ⟨xr, hxr⟩
    congr
    exact congrArg Subtype.val hEq
  · rw [sewr_offBoundary S xr hxr]
    rfl

private theorem sewNode_faceR_edge_boundary
    (d : {xd : Gd.Dart // xd ∈ bGd}) :
    sewNodeFn S
        (sewFaceR S (Gr.edge ((boundaryEquiv S) d).1)) =
      sewd d.1 := by
  let xr : Gr.Dart := ((boundaryEquiv S) d).1
  have hxr : xr ∈ bGr := ((boundaryEquiv S) d).2
  have hfaceEq : Gr.face (Gr.edge xr) = Gr.node.symm xr :=
    Gr.face_edge_eq_node_symm xr
  have hfaceMem : Gr.face (Gr.edge xr) ∈ bGr := by
    rw [hfaceEq, node_symm_mem_boundaryR_iff S]
    exact hxr
  rw [sewFaceR, sewr_boundary S _ hfaceMem]
  simp only [sewd, sewNodeFn]
  let y : {xd : Gd.Dart // xd ∈ bGd} :=
    (boundaryEquiv S).symm ⟨Gr.face (Gr.edge xr), hfaceMem⟩
  have hEy : (boundaryEquiv S) y =
      ⟨Gr.face (Gr.edge xr), hfaceMem⟩ :=
    (boundaryEquiv S).apply_symm_apply _
  have hcompat := node_boundaryEquiv S y
  have hbackImage : (boundaryEquiv S) (boundaryBackD S y) =
      (boundaryEquiv S) d := by
    apply Subtype.ext
    calc
      ((boundaryEquiv S) (boundaryBackD S y)).1 =
          Gr.node ((boundaryEquiv S) y).1 := hcompat.symm
      _ = Gr.node (Gr.face (Gr.edge xr)) := by rw [hEy]
      _ = xr := Gr.node_face_edge xr
      _ = ((boundaryEquiv S) d).1 := rfl
  have hback : boundaryBackD S y = d :=
    (boundaryEquiv S).injective hbackImage
  exact congrArg (fun z => sewd z.1) hback

private theorem sewNode_faceR_edge_offBoundary
    (xr : Gr.Dart) (hxr : xr ∉ bGr) :
    sewNodeFn S (sewFaceR S (Gr.edge xr)) = Sum.inr ⟨xr, hxr⟩ := by
  have hfaceEq : Gr.face (Gr.edge xr) = Gr.node.symm xr :=
    Gr.face_edge_eq_node_symm xr
  have hfaceOff : Gr.face (Gr.edge xr) ∉ bGr := by
    rw [hfaceEq, node_symm_mem_boundaryR_iff S]
    exact hxr
  rw [sewFaceR, sewr_offBoundary S _ hfaceOff]
  simp only [sewNodeFn]
  rw [Gr.node_face_edge, sewr_offBoundary S xr hxr]

private theorem sew_cancel3 :
    ∀ w : SewDart Gd Gr bGr,
      sewNodeFn S (sewFaceFn S (sewEdgeFn S w)) = w := by
  intro w
  cases w with
  | inl xd =>
      by_cases hxd : xd ∈ bGd
      · simp only [sewEdgeFn, dif_pos hxd]
        rw [sewFace_sewr]
        exact sewNode_faceR_edge_boundary S ⟨xd, hxd⟩
      · have hedgeOff : Gd.edge xd ∉ bGd := by
          exact mt (edge_mem_boundaryD_iff S xd).1 hxd
        simp [sewEdgeFn, hxd, sewFaceFn, hedgeOff,
          sewNodeFn, sewd]
  | inr xr =>
      simp only [sewEdgeFn]
      rw [sewFace_sewr]
      exact sewNode_faceR_edge_offBoundary S xr.1 xr.2

/-- Coq `sew_map`. -/
noncomputable def sewMap : Hypermap.{max u v} :=
  Hypermap.ofCancel3 (sewEdgeFn S) (sewNodeFn S) (sewFaceFn S)
    (sew_cancel3 S)

@[simp]
theorem sewMap_edge_apply (w : SewDart Gd Gr bGr) :
    (sewMap S).edge w = sewEdgeFn S w := by
  unfold sewMap
  exact ofCancel3_edge_apply _ _ _ _ w

@[simp]
theorem sewMap_node_apply (w : SewDart Gd Gr bGr) :
    (sewMap S).node w = sewNodeFn S w := by
  unfold sewMap
  exact ofCancel3_node_apply _ _ _ _ w

private theorem sewEdge_sewr (xr : Gr.Dart) :
    sewEdgeFn S (sewr S xr) = sewr S (Gr.edge xr) := by
  by_cases hxr : xr ∈ bGr
  · rw [sewr_boundary S xr hxr]
    simp only [sewd, sewEdgeFn]
    have hdisk : ((boundaryEquiv S).symm ⟨xr, hxr⟩).1 ∈ bGd :=
      ((boundaryEquiv S).symm ⟨xr, hxr⟩).2
    rw [dif_pos hdisk]
    congr
    exact congrArg Subtype.val
      ((boundaryEquiv S).apply_symm_apply ⟨xr, hxr⟩)
  · rw [sewr_offBoundary S xr hxr]
    rfl

theorem map_sewr_boundary :
    bGr.map (sewr S) = (bGd.map sewd).reverse := by
  calc
    bGr.map (sewr S) =
        bGr.attach.map (fun x => sewr S x.1) := by
      rw [List.attach_map_val]
    _ = bGr.attach.map
        (fun x => sewd ((boundaryEquiv S).symm x).1) := by
      apply List.map_congr_left
      intro x _hx
      exact sewr_boundary S x.1 x.2
    _ = (bGr.attach.map (boundaryEquiv S).symm).map
        (fun x => sewd x.1) := by simp [List.map_map]
    _ = bGd.attach.reverse.map (fun x => sewd x.1) := by
      rw [map_boundaryEquiv_symm_attach S]
    _ = (bGd.map sewd).reverse := by
      simp [List.map_reverse]

private theorem remainderImage_inl_iff
    (xd : Gd.Dart) :
    (∃ xr : Gr.Dart, sewr S xr = sewd xd) ↔ xd ∈ bGd := by
  constructor
  · rintro ⟨xr, hxr⟩
    by_cases hmem : xr ∈ bGr
    · rw [sewr_boundary S xr hmem] at hxr
      have hval : ((boundaryEquiv S).symm ⟨xr, hmem⟩).1 = xd :=
        Sum.inl_injective hxr
      rw [← hval]
      exact ((boundaryEquiv S).symm ⟨xr, hmem⟩).2
    · rw [sewr_offBoundary S xr hmem] at hxr
      cases hxr
  · intro hxd
    let d : {z : Gd.Dart // z ∈ bGd} := ⟨xd, hxd⟩
    exact ⟨((boundaryEquiv S) d).1, by
      simpa [d] using sewr_boundaryEquiv S d⟩

omit S in
private theorem diskImage_inr_false
    (xr : {z : Gr.Dart // z ∉ bGr}) :
    ¬ ∃ xd : Gd.Dart, sewd xd = (Sum.inr xr : SewDart Gd Gr bGr) := by
  rintro ⟨xd, hxd⟩
  cases hxd

private theorem remainderImage_inr
    (xr : {z : Gr.Dart // z ∉ bGr}) :
    ∃ yr : Gr.Dart, sewr S yr = (Sum.inr xr : SewDart Gd Gr bGr) :=
  ⟨xr.1, sewr_offBoundary S xr.1 xr.2⟩

/-- Coq `sew_map_patch`. -/
theorem sewMapPatch :
    Patch (sewMap S) Gd Gr sewd (sewr S) bGd bGr := by
  classical
  refine {
    injd := sewd_injective
    injr := sewr_injective S
    cycleD := S.cycleD
    boundaryD_faceSimple := S.faceSimpleD
    cycleR := S.cycleR
    boundaryR_nodup := S.nodupR
    map_boundaryR := map_sewr_boundary S
    coverR := ?_
    map_edgeD := ?_
    map_nodeD := ?_
    map_edgeR := ?_
    map_nodeR := ?_
  }
  · intro w
    cases w with
    | inl xd =>
        change (∃ xr, sewr S xr = sewd xd) ↔
          (¬ ∃ yd, sewd yd = sewd xd) ∨ sewd xd ∈ bGd.map sewd
        rw [remainderImage_inl_iff S]
        constructor
        · intro hxd
          exact Or.inr (List.mem_map.mpr ⟨xd, hxd, rfl⟩)
        · rintro (hno | hmem)
          · exact False.elim (hno ⟨xd, rfl⟩)
          · rcases List.mem_map.mp hmem with ⟨yd, hyd, hEq⟩
            exact (Sum.inl_injective hEq).symm ▸ hyd
    | inr xr =>
        change (∃ yr, sewr S yr = (Sum.inr xr : SewDart Gd Gr bGr)) ↔
          (¬ ∃ xd, sewd xd = Sum.inr xr) ∨
            (Sum.inr xr : SewDart Gd Gr bGr) ∈ bGd.map sewd
        exact iff_of_true (remainderImage_inr S xr)
          (Or.inl (diskImage_inr_false xr))
  · intro xd hxd
    have hedge : (sewMap S).edge (sewd xd) = sewd (Gd.edge xd) := by
      rw [sewMap_edge_apply]
      simp [sewd, sewEdgeFn, hxd]
    exact hedge.symm
  · intro xd
    rw [sewMap_node_apply]
    rfl
  · intro xr
    rw [sewMap_edge_apply, sewEdge_sewr S xr]
  · intro xr hxr
    rw [sewr_offBoundary S xr hxr, sewMap_node_apply]
    rfl

end SewBoundary

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
