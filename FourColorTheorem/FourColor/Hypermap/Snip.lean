
import FourColorTheorem.FourColor.Hypermap.Patch

/-!
Cutting an Euler-planar hypermap along a simple ring.

This is the concrete construction from Gonthier's `snip.v`.  The disk keeps
the node-closed `DiskN` side and replaces the edge action on the ring by its
cyclic successor.  The remainder keeps the complement of `DiskE` and replaces
the node action on the ring by its cyclic predecessor.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Dart type of Coq `snip_disk`. -/
def SnipDiskDart (G : Hypermap.{u}) (r : List G.Dart) :=
  {x : G.Dart // G.DiskN r x}

/-- Dart type of Coq `snip_rem`. -/
def SnipRemainderDart (G : Hypermap.{u}) (r : List G.Dart) :=
  {x : G.Dart // ¬ G.DiskE r x}

noncomputable instance snipDiskDartFintype :
    Fintype (SnipDiskDart G r) := by
  letI : Finite (SnipDiskDart G r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (SnipDiskDart G r)

noncomputable instance snipDiskDartDecidableEq :
    DecidableEq (SnipDiskDart G r) :=
  Classical.decEq _

noncomputable instance snipRemainderDartFintype :
    Fintype (SnipRemainderDart G r) := by
  letI : Finite (SnipRemainderDart G r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (SnipRemainderDart G r)

noncomputable instance snipRemainderDartDecidableEq :
    DecidableEq (SnipRemainderDart G r) :=
  Classical.decEq _

private theorem diskE_edge_iff_of_jordan
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) (x : G.Dart) :
    G.DiskE r (G.edge x) ↔ G.DiskE r x := by
  constructor
  · intro hx
    have hreach : PermReachable G.edge (G.edge x) x := by
      simpa using PermReachable.backward G.edge (G.edge x)
    rcases permReachable_exists_iterate G.edge hreach with ⟨n, hn⟩
    have hiter : ∀ m : Nat, ∀ y : G.Dart,
        G.DiskE r y → G.DiskE r (((G.edge : G.Dart → G.Dart)^[m]) y) := by
      intro m y hy
      induction m generalizing y with
      | zero => simpa using hy
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact G.diskE_edge hJ hr (ih y hy)
    simpa [hn] using hiter n (G.edge x) hx
  · exact G.diskE_edge hJ hr

private def snipDiskEdgeFn
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    SnipDiskDart G r → SnipDiskDart G r := fun x =>
  if hx : x.1 ∈ r then
    ⟨r.next x.1 hx, G.diskN_of_mem (List.next_mem r x.1 hx)⟩
  else
    ⟨G.edge x.1, (G.diskE_edge hJ hr ⟨x.2, hx⟩).1⟩

private def snipDiskNodeFn :
    SnipDiskDart G r → SnipDiskDart G r := fun x =>
  ⟨G.node x.1, (G.diskN_node_iff (r := r)).2 x.2⟩

private def snipDiskFaceFn
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    SnipDiskDart G r → SnipDiskDart G r := fun x =>
  if hx : x.1 ∈ r then
    ⟨G.face (G.edge (r.prev x.1 hx)), by
      rw [G.face_edge_eq_node_symm]
      exact G.diskN_node_symm_of_mem (List.prev_mem r x.1 hx)⟩
  else
    ⟨G.face x.1, by
      have hEpred : G.DiskE r (G.edge.symm x.1) :=
        (diskE_edge_iff_of_jordan hJ hr (G.edge.symm x.1)).1
          (by simpa using (show G.DiskE r x.1 from ⟨x.2, hx⟩))
      have hN : G.DiskN r (G.node.symm (G.edge.symm x.1)) :=
        G.diskN_node_symm hEpred.1
      have hface : G.face x.1 = G.node.symm (G.edge.symm x.1) := by
        apply G.node.injective
        simpa using G.node_face_edge (G.edge.symm x.1)
      simpa [hface] using hN⟩

private theorem snipDisk_cancel3
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    ∀ x : SnipDiskDart G r,
      snipDiskNodeFn
        (snipDiskFaceFn hJ hr (snipDiskEdgeFn hJ hr x)) = x := by
  intro x
  apply Subtype.ext
  by_cases hx : x.1 ∈ r
  · have hnext : r.next x.1 hx ∈ r := List.next_mem r x.1 hx
    simp only [snipDiskEdgeFn, dif_pos hx, snipDiskFaceFn, dif_pos hnext,
      snipDiskNodeFn, Subtype.coe_mk]
    rw [List.prev_next r hr.2.nodup x.1 hx]
    exact G.node_face_edge x.1
  · have hE : G.DiskE r (G.edge x.1) :=
      G.diskE_edge hJ hr ⟨x.2, hx⟩
    simp only [snipDiskEdgeFn, dif_neg hx, snipDiskFaceFn,
      dif_neg hE.2, snipDiskNodeFn, Subtype.coe_mk]
    exact G.node_face_edge x.1

/-- Coq `snip_disk`. -/
noncomputable def snipDisk
    (G : Hypermap.{u}) (r : List G.Dart)
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) : Hypermap.{u} :=
  Hypermap.ofCancel3
    (snipDiskEdgeFn (Unavoidability.eulerPlanar_jordan G hplanar) hr)
    snipDiskNodeFn
    (snipDiskFaceFn (Unavoidability.eulerPlanar_jordan G hplanar) hr)
    (snipDisk_cancel3 (Unavoidability.eulerPlanar_jordan G hplanar) hr)

/-- Coq projection `snipd`. -/
def snipd
    {G : Hypermap.{u}} {r : List G.Dart}
    {hplanar : G.EulerPlanar} {hr : G.SimpleRLinkCycle r}
    (x : (snipDisk G r hplanar hr).Dart) : G.Dart :=
  x.1

@[simp]
theorem snipDisk_edge_val
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipDisk G r hplanar hr).Dart) :
    snipd ((snipDisk G r hplanar hr).edge x) =
      if hx : snipd x ∈ r then r.next (snipd x) hx else G.edge (snipd x) :=
  by
    unfold snipd snipDisk
    rw [ofCancel3_edge_apply]
    unfold snipDiskEdgeFn
    split <;> rfl

@[simp]
theorem snipDisk_node_val
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipDisk G r hplanar hr).Dart) :
    snipd ((snipDisk G r hplanar hr).node x) = G.node (snipd x) :=
  rfl

@[simp]
theorem snipDisk_face_val
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipDisk G r hplanar hr).Dart) :
    snipd ((snipDisk G r hplanar hr).face x) =
      if hx : snipd x ∈ r then
        G.face (G.edge (r.prev (snipd x) hx))
      else G.face (snipd x) :=
  by
    unfold snipd snipDisk
    rw [ofCancel3_face_apply]
    unfold snipDiskFaceFn
    split <;> rfl

/-- Coq `snipd_ring`. -/
def snipdRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    List (snipDisk G r hplanar hr).Dart :=
  r.attach.map fun x => ⟨x.1, G.diskN_of_mem x.2⟩

@[simp]
theorem map_snipdRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipdRing hplanar hr).map snipd = r := by
  simp [snipdRing, snipd]

theorem snipd_injective
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    Function.Injective
      (snipd : (snipDisk G r hplanar hr).Dart → G.Dart) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem snipdRing_nodup
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipdRing hplanar hr).Nodup := by
  unfold snipdRing
  apply hr.2.nodup.attach.map
  intro x y hxy
  exact Subtype.ext
    (congrArg (fun z : SnipDiskDart G r => z.1) hxy)

theorem cycle_snipdRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    FunctionCycle (snipDisk G r hplanar hr).edge
      (snipdRing hplanar hr) := by
  apply FunctionCycle.of_eq_next (snipdRing_nodup hplanar hr)
  intro x hx
  apply Subtype.ext
  change snipd ((snipDisk G r hplanar hr).edge x) =
    snipd ((snipdRing hplanar hr).next x hx)
  rw [snipDisk_edge_val]
  have hxr : snipd x ∈ r := by
    have hm : snipd x ∈ (snipdRing hplanar hr).map snipd :=
      List.mem_map_of_mem hx
    simpa only [map_snipdRing] using hm
  rw [dif_pos hxr]
  have hmap := List.next_map_injective snipd
    (snipd_injective hplanar hr)
    (snipdRing hplanar hr) (snipdRing_nodup hplanar hr) x hx
  simpa only [map_snipdRing] using hmap

private theorem rLinkPath_isChain
    {x : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p) :
    List.IsChain G.RLink (x :: p) := by
  induction p generalizing x with
  | nil => exact .singleton x
  | cons y p ih =>
      exact .cons_cons hp.1 (ih hp.2)

private theorem prev_rel_of_isChain_of_ne_head
    {α : Type _} [DecidableEq α] {R : α → α → Prop}
    {a x : α} {p : List α}
    (hc : List.IsChain R (a :: p))
    (hx : x ∈ a :: p) (hxa : x ≠ a) :
    R ((a :: p).prev x hx) x := by
  induction p generalizing a with
  | nil =>
      have : x = a := by simpa using hx
      exact False.elim (hxa this)
  | cons b p ih =>
      have hxbp : x ∈ b :: p := by simpa [hxa] using hx
      by_cases hxb : x = b
      · subst x
        simpa [List.prev, hxa] using hc.rel
      · have htail : List.IsChain R (b :: p) := hc.tail
        simpa [List.prev, hxa, hxb] using ih htail hxbp hxb

private theorem RLinkCycle_prev_link
    (hc : G.RLinkCycle r) (hn : r.Nodup)
    {x : G.Dart} (hx : x ∈ r) :
    G.RLink (r.prev x hx) x := by
  cases r with
  | nil => simp at hx
  | cons a p =>
      by_cases hxa : x = a
      · subst x
        rw [List.prev_getLast_cons]
        simpa [List.getLastD] using hc.2
      · exact prev_rel_of_isChain_of_ne_head
          (rLinkPath_isChain hc.1) hx hxa

private theorem snipDisk_face_step_reachable
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipDisk G r hplanar hr).Dart) :
    PermReachable G.face (snipd x)
      (snipd ((snipDisk G r hplanar hr).face x)) := by
  rw [snipDisk_face_val]
  by_cases hx : snipd x ∈ r
  · rw [dif_pos hx]
    exact RLink.face_edge_reachable (G := G)
      (RLinkCycle_prev_link hr.1 hr.2.nodup hx)
  · rw [dif_neg hx]
    exact PermReachable.forward G.face (snipd x)

theorem snipDisk_faceReachable_projection
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    {x y : (snipDisk G r hplanar hr).Dart}
    (hxy : PermReachable (snipDisk G r hplanar hr).face x y) :
    PermReachable G.face (snipd x) (snipd y) := by
  induction hxy with
  | refl => exact PermReachable.refl G.face (snipd x)
  | tail hxb hbc ih =>
      apply PermReachable.trans G.face ih
      cases hbc with
      | forward => exact snipDisk_face_step_reachable hplanar hr _
      | backward =>
          exact PermReachable.symm G.face (by
            simpa using snipDisk_face_step_reachable hplanar hr
              ((snipDisk G r hplanar hr).face.symm _))

theorem faceSimple_snipdRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipDisk G r hplanar hr).FaceSimple (snipdRing hplanar hr) := by
  have hHost :
      ((snipdRing hplanar hr).map snipd).Pairwise
        (fun x y => ¬ PermReachable G.face x y) := by
    rw [map_snipdRing]
    exact hr.2
  have hHost' := (List.pairwise_map.mp hHost)
  unfold FaceSimple
  exact hHost'.imp (by
    intro x y hnot hxy
    exact hnot (snipDisk_faceReachable_projection hplanar hr hxy))

theorem mem_snipdRing_iff
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipDisk G r hplanar hr).Dart) :
    x ∈ snipdRing hplanar hr ↔ snipd x ∈ r := by
  constructor
  · intro hx
    have hm : snipd x ∈ (snipdRing hplanar hr).map snipd :=
      List.mem_map_of_mem hx
    simpa only [map_snipdRing] using hm
  · intro hx
    have hm : snipd x ∈ (snipdRing hplanar hr).map snipd := by
      simpa only [map_snipdRing] using hx
    rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
    exact (snipd_injective hplanar hr hyx).symm ▸ hy

private def snipRemainderEdgeFn
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    SnipRemainderDart G r → SnipRemainderDart G r := fun x =>
  ⟨G.edge x.1, by
    intro hE
    exact x.2 ((diskE_edge_iff_of_jordan hJ hr x.1).1 hE)⟩

private def snipRemainderNodeFn :
    SnipRemainderDart G r → SnipRemainderDart G r := fun x =>
  if hx : x.1 ∈ r then
    ⟨r.prev x.1 hx, fun hE => hE.2 (List.prev_mem r x.1 hx)⟩
  else
    ⟨G.node x.1, by
      intro hE
      apply x.2
      exact ⟨(G.diskN_node_iff (r := r)).1 hE.1, hx⟩⟩

private def snipRemainderFaceFn
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    SnipRemainderDart G r → SnipRemainderDart G r := fun x =>
  if hx : G.node (G.face x.1) ∈ r then
    ⟨r.next (G.node (G.face x.1)) hx,
      fun hE => hE.2 (List.next_mem r _ hx)⟩
  else
    ⟨G.face x.1, by
      intro hE
      apply x.2
      have hNodeE : G.DiskE r (G.node (G.face x.1)) :=
        ⟨(G.diskN_node_iff (r := r)).2 hE.1, hx⟩
      have hEdgeE := G.diskE_edge hJ hr hNodeE
      simpa using hEdgeE⟩

private theorem snipRemainder_cancel3
    (hJ : G.Jordan) (hr : G.SimpleRLinkCycle r) :
    ∀ x : SnipRemainderDart G r,
      snipRemainderNodeFn
        (snipRemainderFaceFn hJ hr (snipRemainderEdgeFn hJ hr x)) = x := by
  intro x
  apply Subtype.ext
  by_cases hx : x.1 ∈ r
  · have hnext : r.next x.1 hx ∈ r := List.next_mem r x.1 hx
    simp only [snipRemainderEdgeFn, snipRemainderFaceFn,
      G.node_face_edge, dif_pos hx, snipRemainderNodeFn,
      dif_pos hnext, Subtype.coe_mk]
    exact List.prev_next r hr.2.nodup x.1 hx
  · have hfaceNot : G.face (G.edge x.1) ∉ r := by
      intro hface
      apply x.2
      refine ⟨?_, hx⟩
      have hfaceN : G.DiskN r (G.face (G.edge x.1)) :=
        G.diskN_of_mem hface
      rw [G.face_edge_eq_node_symm] at hfaceN
      exact (G.diskN_node_symm_iff (r := r)).1 hfaceN
    simp [snipRemainderEdgeFn, snipRemainderFaceFn,
      snipRemainderNodeFn, hx, hfaceNot]

/-- Coq `snip_rem`. -/
noncomputable def snipRemainder
    (G : Hypermap.{u}) (r : List G.Dart)
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) : Hypermap.{u} :=
  Hypermap.ofCancel3
    (snipRemainderEdgeFn (Unavoidability.eulerPlanar_jordan G hplanar) hr)
    snipRemainderNodeFn
    (snipRemainderFaceFn (Unavoidability.eulerPlanar_jordan G hplanar) hr)
    (snipRemainder_cancel3 (Unavoidability.eulerPlanar_jordan G hplanar) hr)

/-- Coq projection `snipr`. -/
def snipr
    {G : Hypermap.{u}} {r : List G.Dart}
    {hplanar : G.EulerPlanar} {hr : G.SimpleRLinkCycle r}
    (x : (snipRemainder G r hplanar hr).Dart) : G.Dart :=
  x.1

@[simp]
theorem snipRemainder_edge_val
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipRemainder G r hplanar hr).Dart) :
    snipr ((snipRemainder G r hplanar hr).edge x) = G.edge (snipr x) :=
  rfl

@[simp]
theorem snipRemainder_node_val
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipRemainder G r hplanar hr).Dart) :
    snipr ((snipRemainder G r hplanar hr).node x) =
      if hx : snipr x ∈ r then r.prev (snipr x) hx else G.node (snipr x) :=
  by
    unfold snipr snipRemainder
    rw [ofCancel3_node_apply]
    unfold snipRemainderNodeFn
    split <;> rfl

/-- Coq `snipr_ring`. -/
def sniprRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    List (snipRemainder G r hplanar hr).Dart :=
  r.reverse.attach.map fun x =>
    ⟨x.1, fun hE => hE.2 (List.mem_reverse.mp x.2)⟩

@[simp]
theorem map_sniprRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (sniprRing hplanar hr).map snipr = r.reverse := by
  simp [sniprRing, snipr]

theorem snipr_injective
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    Function.Injective
      (snipr : (snipRemainder G r hplanar hr).Dart → G.Dart) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem sniprRing_nodup
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (sniprRing hplanar hr).Nodup := by
  unfold sniprRing
  apply (List.nodup_reverse.mpr hr.2.nodup).attach.map
  intro x y hxy
  exact Subtype.ext
    (congrArg (fun z : SnipRemainderDart G r => z.1) hxy)

theorem cycle_sniprRing
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    FunctionCycle (snipRemainder G r hplanar hr).node
      (sniprRing hplanar hr) := by
  apply FunctionCycle.of_eq_next (sniprRing_nodup hplanar hr)
  intro x hx
  apply Subtype.ext
  change snipr ((snipRemainder G r hplanar hr).node x) =
    snipr ((sniprRing hplanar hr).next x hx)
  rw [snipRemainder_node_val]
  have hxRev : snipr x ∈ r.reverse := by
    rw [← map_sniprRing hplanar hr]
    exact List.mem_map_of_mem hx
  have hxr : snipr x ∈ r := List.mem_reverse.mp hxRev
  rw [dif_pos hxr]
  have hmap := List.next_map_injective snipr
    (snipr_injective hplanar hr)
    (sniprRing hplanar hr) (sniprRing_nodup hplanar hr) x hx
  have hrev := List.next_reverse_eq_prev r hr.2.nodup (snipr x) hxr
  have hmap' :
      r.reverse.next (snipr x) hxRev =
        snipr ((sniprRing hplanar hr).next x hx) := by
    simpa only [map_sniprRing] using hmap
  exact hrev.symm.trans hmap'

theorem mem_sniprRing_iff
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : (snipRemainder G r hplanar hr).Dart) :
    x ∈ sniprRing hplanar hr ↔ snipr x ∈ r := by
  constructor
  · intro hx
    have hm : snipr x ∈ (sniprRing hplanar hr).map snipr :=
      List.mem_map_of_mem hx
    have : snipr x ∈ r.reverse := by
      simpa only [map_sniprRing] using hm
    exact List.mem_reverse.mp this
  · intro hx
    have hm : snipr x ∈ (sniprRing hplanar hr).map snipr := by
      have : snipr x ∈ r.reverse := List.mem_reverse.mpr hx
      simpa only [map_sniprRing] using this
    rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
    exact (snipr_injective hplanar hr hyx).symm ▸ hy

/-- Coq `snip_patch`. -/
theorem snipPatch
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    Patch G (snipDisk G r hplanar hr) (snipRemainder G r hplanar hr)
      snipd snipr (snipdRing hplanar hr) (sniprRing hplanar hr) := by
  classical
  refine {
    injd := snipd_injective hplanar hr
    injr := snipr_injective hplanar hr
    cycleD := cycle_snipdRing hplanar hr
    boundaryD_faceSimple := faceSimple_snipdRing hplanar hr
    cycleR := cycle_sniprRing hplanar hr
    boundaryR_nodup := sniprRing_nodup hplanar hr
    map_boundaryR := ?_
    coverR := ?_
    map_edgeD := ?_
    map_nodeD := ?_
    map_edgeR := ?_
    map_nodeR := ?_
  }
  · rw [map_sniprRing, map_snipdRing]
  · intro x
    rw [map_snipdRing]
    unfold snipd snipr
    change (∃ xr : SnipRemainderDart G r, xr.1 = x) ↔
      (¬ ∃ xd : SnipDiskDart G r, xd.1 = x) ∨ x ∈ r
    constructor
    · rintro ⟨xr, hxr⟩
      have hnotE : ¬ G.DiskE r x := by
        rw [← hxr]
        exact xr.2
      by_cases hN : G.DiskN r x
      · exact Or.inr (by
          by_contra hnotMem
          exact hnotE ⟨hN, hnotMem⟩)
      · exact Or.inl (by
          rintro ⟨xd, hxd⟩
          apply hN
          rw [← hxd]
          exact xd.2)
    · rintro (hnoDisk | hmem)
      · exact ⟨⟨x, by
          intro hE
          exact hnoDisk ⟨⟨x, hE.1⟩, rfl⟩⟩, rfl⟩
      · exact ⟨⟨x, by
          intro hE
          exact hE.2 hmem⟩, rfl⟩
  · intro xd hxd
    have hnot : snipd xd ∉ r := by
      exact mt (mem_snipdRing_iff hplanar hr xd).2 hxd
    simp [snipDisk_edge_val, hnot]
  · intro xd
    exact snipDisk_node_val hplanar hr xd
  · intro xr
    exact snipRemainder_edge_val hplanar hr xr
  · intro xr hxr
    have hnot : snipr xr ∉ r := by
      exact mt (mem_sniprRing_iff hplanar hr xr).2 hxr
    simp [snipRemainder_node_val, hnot]

/-- For the canonical snip patch, Coq's `outer` predicate is exactly the
strict outside of the disk together with the ring face band. -/
theorem snipPatch_outer_iff
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x : G.Dart) :
    (snipPatch hplanar hr).Outer x ↔
      G.DiskFC r x ∨ G.FaceBand r x := by
  constructor
  · rintro ⟨y, ⟨yr, hyr⟩, hyx⟩
    have hyrOff : ¬ G.DiskE r y := by
      intro hyE
      apply yr.2
      change G.DiskE r (snipr yr)
      rw [hyr]
      exact hyE
    by_cases hyBand : G.FaceBand r y
    · exact Or.inr (FaceBand.of_faceReachable (G := G) hyBand hyx)
    · have hyN : ¬ G.DiskN r y := by
        intro hyN
        apply hyrOff
        refine ⟨hyN, ?_⟩
        intro hyring
        exact hyBand ⟨y, hyring, PermReachable.refl G.face y⟩
      exact Or.inl (G.diskFC_of_faceReachable hyx ⟨hyN, hyBand⟩)
  · rintro (hx | hx)
    · let xr : (snipRemainder G r hplanar hr).Dart :=
        ⟨x, fun hE => hx.1 hE.1⟩
      exact ⟨x, ⟨xr, rfl⟩, PermReachable.refl G.face x⟩
    · rcases hx with ⟨y, hyring, hyx⟩
      let yr : (snipRemainder G r hplanar hr).Dart :=
        ⟨y, fun hE => hE.2 hyring⟩
      exact ⟨y, ⟨yr, rfl⟩, hyx⟩

/-- Coq's `fcard_snip_rem`: the remainder faces are the strict exterior face
orbits together with the one boundary face orbit for each ring dart. -/
theorem snipRemainder_faceOrbitCount
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipRemainder G r hplanar hr).faceOrbitCount =
      G.FaceOrbitCountOf (G.DiskFC r) + r.length := by
  classical
  calc
    (snipRemainder G r hplanar hr).faceOrbitCount =
        G.FaceOrbitCountOf (snipPatch hplanar hr).Outer :=
      (snipPatch hplanar hr).faceOrbitCount_remainderOuter_eq
    _ = G.FaceOrbitCountOf
        (fun x => G.DiskFC r x ∨ G.FaceBand r x) :=
      G.faceOrbitCountOf_congr (snipPatch_outer_iff hplanar hr)
    _ = G.FaceOrbitCountOf (G.DiskFC r) +
        G.FaceOrbitCountOf (G.FaceBand r) :=
      G.faceOrbitCountOf_or (G.DiskFC r) (G.FaceBand r)
        (fun _ _ hxy => FaceBand.congr_faceReachable (G := G) hxy)
        (fun _ hx => hx.2)
    _ = G.FaceOrbitCountOf (G.DiskFC r) + r.length := by
      rw [G.faceOrbitCountOf_faceBand_eq_length hr.faceSimple]

/-- Coq `cface_snipd`: the disk projection preserves and reflects face
orbits.  Reflection away from the boundary is the generic patch face-lifting
lemma; if both faces meet the boundary, face-simplicity of the host ring
identifies their boundary representatives. -/
theorem snipDisk_faceReachable_iff
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (x y : (snipDisk G r hplanar hr).Dart) :
    PermReachable (snipDisk G r hplanar hr).face x y ↔
      PermReachable G.face (snipd x) (snipd y) := by
  let Gd := snipDisk G r hplanar hr
  let bGd := snipdRing hplanar hr
  let P := snipPatch hplanar hr
  constructor
  · exact snipDisk_faceReachable_projection hplanar hr
  · intro hxy
    by_cases hxBand : Gd.FaceBand bGd x
    · by_cases hyBand : Gd.FaceBand bGd y
      · rcases hxBand with ⟨u, huBoundary, hux⟩
        rcases hyBand with ⟨v, hvBoundary, hvy⟩
        have hHostUX :
            PermReachable G.face (snipd u) (snipd x) :=
          snipDisk_faceReachable_projection hplanar hr hux
        have hHostVY :
            PermReachable G.face (snipd v) (snipd y) :=
          snipDisk_faceReachable_projection hplanar hr hvy
        have hHostUV :
            PermReachable G.face (snipd u) (snipd v) :=
          PermReachable.trans G.face hHostUX
            (PermReachable.trans G.face hxy
              (PermReachable.symm G.face hHostVY))
        have huRing : snipd u ∈ r :=
          (mem_snipdRing_iff hplanar hr u).1 huBoundary
        have hvRing : snipd v ∈ r :=
          (mem_snipdRing_iff hplanar hr v).1 hvBoundary
        have huvMap : snipd u = snipd v :=
          FaceSimple.eq_of_faceReachable_of_mem
            (G := G) hr.2 huRing hvRing hHostUV
        have huv : u = v := snipd_injective hplanar hr huvMap
        exact PermReachable.trans Gd.face
          (PermReachable.symm Gd.face hux) (huv ▸ hvy)
      · exact PermReachable.symm Gd.face
          (P.reachableD_of_map_face_reachable_of_not_faceBand
            hyBand (PermReachable.symm G.face hxy))
    · exact P.reachableD_of_map_face_reachable_of_not_faceBand hxBand hxy

/-- Coq `planar_snipd`. -/
theorem snipDisk_eulerPlanar
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipDisk G r hplanar hr).EulerPlanar :=
  ((snipPatch hplanar hr).eulerPlanar_iff.mp hplanar).1

/-- Coq `planar_snipr`. -/
theorem snipRemainder_eulerPlanar
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (snipRemainder G r hplanar hr).EulerPlanar :=
  ((snipPatch hplanar hr).eulerPlanar_iff.mp hplanar).2

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
