
import FourColorTheorem.FourColor.Reducibility.ContractMinimal
import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension

/-!
The reducibility contradiction after extending a configuration embedding.

This file is the common upper layer over `ContractMinimal` and
`EmbeddingExtension`; keeping it separate avoids the former import cycle
between contract coloring and patch construction.  It ports the final part of
Coq `embed.v`, from `embed_valid_contract` through `not_embed_reducible`.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

theorem functionPathMap_eq_tail_append_of_last
    {α : Type _} {f : α -> α} {x t : α} {xs : List α}
    (hp : FunctionPath f x xs)
    (hlast : f ((x :: xs).getLastD x) = t) :
    (x :: xs).map f = xs ++ [t] := by
  induction xs generalizing x with
  | nil => simpa [FunctionPath] using hlast
  | cons y ys ih =>
      rcases hp with ⟨hxy, hp⟩
      have hlast' : f ((y :: ys).getLastD y) = t := by
        simpa [List.getLastD] using hlast
      simp only [List.map_cons, hxy, List.cons_append]
      exact congrArg (List.cons y) (ih hp hlast')

theorem functionCycleMap_eq_rotate_one
    {α : Type _} {f : α -> α} {xs : List α}
    (hc : FunctionCycle f xs) :
    xs.map f = xs.rotate 1 := by
  cases xs with
  | nil => simp
  | cons x xs =>
      rcases hc with ⟨hp, hlast⟩
      simpa [List.rotate_cons_succ] using
        functionPathMap_eq_tail_append_of_last hp hlast

theorem rotateRightOne_reverse
    {α : Type _} (xs : List α) :
    rotateRightOne xs.reverse = (xs.rotate 1).reverse := by
  cases xs with
  | nil => simp [rotateRightOne]
  | cons x xs =>
      unfold rotateRightOne
      rw [show (x :: xs).reverse.length - 1 = xs.length by simp]
      rw [List.reverse_cons]
      calc
        (xs.reverse ++ [x]).rotate xs.length = [x] ++ xs.reverse := by
          simpa only [List.length_reverse] using
            List.rotate_append_length_eq xs.reverse [x]
        _ = ((x :: xs).rotate 1).reverse := by
          simp [List.rotate_cons_succ]

theorem trace_rotateRightOne_eq_trace_reverse_reverse
    (cs : ColSeq) :
    ColSeq.trace (rotateRightOne cs) =
      (ColSeq.trace cs.reverse).reverse := by
  calc
    ColSeq.trace (rotateRightOne cs) =
        rotateRightOne (ColSeq.trace cs) := by
      unfold rotateRightOne
      rw [ColSeq.trace_rotate, ColSeq.length_trace]
    _ = ((ColSeq.trace cs).reverse.rotate 1).reverse := by
      simpa using rotateRightOne_reverse (ColSeq.trace cs).reverse
    _ = (ColSeq.trace cs.reverse).reverse := by
      rw [ColSeq.trace_reverse, colSeq_rot1_eq_rotate]

/-- Removing the literal perimeter from a face cycle and skipping each removed
dart does not split the orbit on the remaining darts.  This is the source-side
content of Coq `cface_embd`. -/
theorem embeddedDisk_faceReachable_of_offRing
    (hG : G.Embeddable r) {x y : G.Dart}
    (hx : x ∉ r) (hy : y ∉ r) (hxy : PermReachable G.face x y) :
    PermReachable (embeddedDisk hG).face
      (⟨x, hx⟩ : (embeddedDisk hG).Dart)
      (⟨y, hy⟩ : (embeddedDisk hG).Dart) := by
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      cases n with
      | zero =>
          have hxyEq : x = y := by simpa using hn
          subst y
          exact PermReachable.refl (embeddedDisk hG).face ⟨x, hx⟩
      | succ n =>
          have htail :
              ((G.face : G.Dart -> G.Dart)^[n]) (G.face x) = y := by
            simpa [Function.iterate_succ_apply] using hn
          by_cases hfaceOff : G.face x ∉ r
          · let xd : (embeddedDisk hG).Dart := ⟨x, hx⟩
            let fd : (embeddedDisk hG).Dart := ⟨G.face x, hfaceOff⟩
            have hstep : (embeddedDisk hG).face xd = fd := by
              apply Subtype.ext
              change embeddedDiskVal hG ((embeddedDisk hG).face xd) =
                G.face x
              simpa [xd, embeddedDiskVal, hfaceOff] using
                embeddedDisk_face_val hG xd
            apply PermReachable.trans (embeddedDisk hG).face
              (PermReachable.forward (embeddedDisk hG).face xd)
            rw [hstep]
            exact ih n (Nat.lt_succ_self n) hfaceOff
              (permReachable_of_iterate_eq G.face htail) htail
          · cases n with
            | zero =>
                have hfaceEq : G.face x = y := by simpa using htail
                exact False.elim (hfaceOff (hfaceEq ▸ hy))
            | succ m =>
                let xd : (embeddedDisk hG).Dart := ⟨x, hx⟩
                have hfaceFaceOff : G.face (G.face x) ∉ r := by
                  have hoff := ((embeddedDisk hG).face xd).property
                  have hval : embeddedDiskVal hG
                      ((embeddedDisk hG).face xd) =
                        G.face (G.face x) := by
                    simpa [xd, embeddedDiskVal, hfaceOff] using
                      embeddedDisk_face_val hG xd
                  rw [← hval]
                  exact hoff
                let ffd : (embeddedDisk hG).Dart :=
                  ⟨G.face (G.face x), hfaceFaceOff⟩
                have hstep : (embeddedDisk hG).face xd = ffd := by
                  apply Subtype.ext
                  change embeddedDiskVal hG ((embeddedDisk hG).face xd) =
                    G.face (G.face x)
                  simpa [xd, embeddedDiskVal, hfaceOff] using
                    embeddedDisk_face_val hG xd
                have htail2 :
                    ((G.face : G.Dart -> G.Dart)^[m])
                        (G.face (G.face x)) = y := by
                  simpa [Function.iterate_succ_apply] using htail
                apply PermReachable.trans (embeddedDisk hG).face
                  (PermReachable.forward (embeddedDisk hG).face xd)
                rw [hstep]
                exact ih m (by omega) hfaceFaceOff
                  (permReachable_of_iterate_eq G.face htail2) htail2

/-- Coq `cface_h1`: the total embedding sends every source face orbit between
off-perimeter darts into a target face orbit. -/
theorem extendEmbedding_faceReachable_of_offRing
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hx : x ∉ r) (hy : y ∉ r)
    (hxy : PermReachable G.face x y) :
    PermReachable H.face (extendEmbedding r h x) (extendEmbedding r h y) := by
  let P := hG.embeddingPatch hH hembed
  exact P.map_faceD_reachable_of_reachable
    (hG.embeddedDisk_faceReachable_of_offRing hx hy hxy)

/-- A face-simple embeddable perimeter does not contain two consecutive darts
of one face. -/
theorem face_not_mem_ring_of_mem_ring
    (hG : G.Embeddable r) {x : G.Dart} (hx : x ∈ r) :
    G.face x ∉ r := by
  intro hfaceOn
  have hfixed : G.face x = x :=
    (Hypermap.FaceSimple.eq_of_faceReachable_of_mem
      (G := G) hG.faceSimple hx hfaceOn
      (PermReachable.forward G.face x)).symm
  have harity : G.arity x = 1 := by
    rw [G.arity_eq_minimalPeriod x]
    exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfixed
  have hbounds := (hG.ringArity hx).bounds
  omega

/-- On a literal perimeter dart, total edge commutation and node commutation
at the off-perimeter face successor imply exact face commutation. -/
theorem extendEmbedding_face_of_mem_ring
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} (hx : x ∈ r) :
    extendEmbedding r h (G.face x) = H.face (extendEmbedding r h x) := by
  have hfaceOff : G.face x ∉ r := hG.face_not_mem_ring_of_mem_ring hx
  apply H.node.injective
  calc
    H.node (extendEmbedding r h (G.face x)) =
        extendEmbedding r h (G.node (G.face x)) :=
      (hG.extendEmbedding_node hH hembed hfaceOff).symm
    _ = extendEmbedding r h (G.edge x) := by
      rw [Hypermap.Plain.node_face_eq_edge (G := G) hG.plain]
    _ = H.edge (extendEmbedding r h x) :=
      hG.extendEmbedding_edge hH hembed x
    _ = H.node (H.face (extendEmbedding r h x)) :=
      (Hypermap.Plain.node_face_eq_edge (G := H) hH.plain _).symm

/-- Exact global Coq `cface_h1`: total embedding preserves every source face
orbit, including the case where an endpoint is on the literal perimeter. -/
theorem extendEmbedding_faceReachable
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hxy : PermReachable G.face x y) :
    PermReachable H.face (extendEmbedding r h x) (extendEmbedding r h y) := by
  have hstep : ∀ z : G.Dart,
      PermReachable H.face (extendEmbedding r h z)
        (extendEmbedding r h (G.face z)) := by
    intro z
    by_cases hzOn : z ∈ r
    · rw [hG.extendEmbedding_face_of_mem_ring hH hembed hzOn]
      exact PermReachable.forward H.face _
    · by_cases hfaceOff : G.face z ∉ r
      · exact hG.extendEmbedding_faceReachable_of_offRing hH hembed
          hzOn hfaceOff (PermReachable.forward G.face z)
      · have hfaceOn : G.face z ∈ r := Classical.not_not.mp hfaceOff
        have hfaceFaceOff : G.face (G.face z) ∉ r :=
          hG.face_not_mem_ring_of_mem_ring hfaceOn
        have hsource : PermReachable G.face z (G.face (G.face z)) :=
          PermReachable.trans G.face (PermReachable.forward G.face z)
            (PermReachable.forward G.face (G.face z))
        have htarget : PermReachable H.face (extendEmbedding r h z)
            (extendEmbedding r h (G.face (G.face z))) :=
          hG.extendEmbedding_faceReachable_of_offRing hH hembed
            hzOn hfaceFaceOff hsource
        exact PermReachable.trans H.face htarget
          (PermReachable.symm H.face (by
            rw [hG.extendEmbedding_face_of_mem_ring hH hembed hfaceOn]
            exact PermReachable.forward H.face _))
  induction hxy with
  | refl => exact PermReachable.refl H.face _
  | @tail a b _ hab ih =>
      apply PermReachable.trans H.face ih
      cases hab with
      | forward => exact hstep a
      | backward =>
          have h := PermReachable.symm H.face (hstep (G.face.symm a))
          simpa using h

/-- A source face path wholly in the kernel is represented by the explicit
embedded disk. -/
theorem embeddedDisk_faceReachable_of_kernel
    (hG : G.Embeddable r) {x y : G.Dart}
    (hx : G.Kernel r x) (hxy : PermReachable G.face x y) :
    PermReachable (embeddedDisk hG).face
      (⟨x, G.kernel_off_ring hx⟩ : (embeddedDisk hG).Dart)
      (⟨y, G.kernel_off_ring
        (G.kernel_faceClosed r hx hxy)⟩ : (embeddedDisk hG).Dart) := by
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  let xd : (embeddedDisk hG).Dart := ⟨x, G.kernel_off_ring hx⟩
  have hkernelIter : forall m : Nat,
      G.Kernel r (((G.face : G.Dart -> G.Dart)^[m]) x) := by
    intro m
    exact G.kernel_faceClosed r hx
      (permReachable_of_iterate_eq G.face rfl)
  have hiter : forall m : Nat,
      embeddedDiskVal hG
          (((embeddedDisk hG).face : _ -> _)^[m] xd) =
        ((G.face : G.Dart -> G.Dart)^[m]) x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          embeddedDisk_face_val, ih]
        have hoff : G.face (((G.face : G.Dart -> G.Dart)^[m]) x) ∉ r := by
          apply G.kernel_off_ring
          simpa [Function.iterate_succ_apply'] using hkernelIter (m + 1)
        rw [dif_pos hoff]
  apply permReachable_of_iterate_eq (embeddedDisk hG).face
  apply Subtype.ext
  change embeddedDiskVal hG
      (((embeddedDisk hG).face : _ -> _)^[n] xd) = y
  exact (hiter n).trans hn

/-- Kernel faces do not meet the crossed perimeter face band of the explicit
embedded disk. -/
theorem embeddedDisk_not_faceBand_boundary_of_kernel
    (hG : G.Embeddable r) {x : G.Dart} (hx : G.Kernel r x) :
    ¬ (embeddedDisk hG).FaceBand (embeddedDiskBoundary hG)
      (⟨x, G.kernel_off_ring hx⟩ : (embeddedDisk hG).Dart) := by
  intro hband
  rcases hband with ⟨z, hzBoundary, hzx⟩
  have hzCrossed : embeddedDiskVal hG z ∈ G.RevRing r.reverse :=
    (mem_embeddedDiskBoundary_iff hG z).1 hzBoundary
  have hsource : PermReachable G.face (embeddedDiskVal hG z) x := by
    simpa using embeddedDisk_faceReachable_map hG hzx
  by_cases hr : r = []
  · subst r
    simp [RevRing] at hzCrossed
  · apply hx
    apply (hG.faceBand_edgePerimeter_iff hr x).1
    exact ⟨embeddedDiskVal hG z, hzCrossed, hsource⟩

/-- On the configuration kernel, the total extension reflects and preserves
face orbits.  This packages Coq `cface_ac_h1`. -/
theorem extendEmbedding_faceReachable_iff_of_kernel
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hx : G.Kernel r x) (hy : y ∉ r) :
    PermReachable H.face (extendEmbedding r h x) (extendEmbedding r h y) <->
      PermReachable G.face x y := by
  let xd : (embeddedDisk hG).Dart := ⟨x, G.kernel_off_ring hx⟩
  let yd : (embeddedDisk hG).Dart := ⟨y, hy⟩
  let P := hG.embeddingPatch hH hembed
  constructor
  · intro htarget
    have hdisk : PermReachable (embeddedDisk hG).face xd yd :=
      P.reachableD_of_map_face_reachable_of_not_faceBand
        (hG.embeddedDisk_not_faceBand_boundary_of_kernel hx) htarget
    exact embeddedDisk_faceReachable_map hG hdisk
  · intro hsource
    have hyKernel : G.Kernel r y := G.kernel_faceClosed r hx hsource
    exact P.map_faceD_reachable_of_reachable
      (hG.embeddedDisk_faceReachable_of_kernel hx hsource)

/-- A kernel dart cannot point across an edge to a literal perimeter dart. -/
theorem edge_not_mem_ring_of_kernel
    (hG : G.Embeddable r) {x : G.Dart} (hx : G.Kernel r x) :
    G.edge x ∉ r := by
  by_cases hr : r = []
  · subst r
    simp
  · intro hedgeOn
    have hxCrossed : x ∈ G.RevRing r.reverse :=
      (hG.mem_edgePerimeter_iff x).2 hedgeOn
    apply hx
    apply (hG.faceBand_edgePerimeter_iff hr x).1
    exact FaceBand.of_mem (G := G) hxCrossed
      (PermReachable.refl G.face x)

/-- Coq `adj_ac_h1`, forward half with only the hub face in the kernel. -/
theorem extendEmbedding_ringAdj_map_of_kernel
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hx : G.Kernel r x) (hy : y ∉ r)
    (hxy : G.RingAdj x y) :
    H.RingAdj (extendEmbedding r h x) (extendEmbedding r h y) := by
  rcases hxy with ⟨z, hxz, hzy⟩
  have hzKernel : G.Kernel r z := G.kernel_faceClosed r hx hxz
  have hxOff : x ∉ r := G.kernel_off_ring hx
  have hzOff : z ∉ r := G.kernel_off_ring hzKernel
  have hedgeZOff : G.edge z ∉ r := hG.edge_not_mem_ring_of_kernel hzKernel
  refine ⟨extendEmbedding r h z,
    hG.extendEmbedding_faceReachable_of_offRing hH hembed hxOff hzOff hxz,
    ?_⟩
  rw [← hG.extendEmbedding_edge hH hembed z]
  exact hG.extendEmbedding_faceReachable_of_offRing hH hembed
    hedgeZOff hy hzy

/-- Coq `adj_ac_h1`: adjacency between two kernel faces is preserved and
reflected by the total embedding. -/
theorem extendEmbedding_ringAdj_iff_of_kernel
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x y : G.Dart} (hx : G.Kernel r x) (hy : G.Kernel r y) :
    H.RingAdj (extendEmbedding r h x) (extendEmbedding r h y) <->
      G.RingAdj x y := by
  let P := hG.embeddingPatch hH hembed
  let xd : (embeddedDisk hG).Dart := ⟨x, G.kernel_off_ring hx⟩
  let yd : (embeddedDisk hG).Dart := ⟨y, G.kernel_off_ring hy⟩
  have hxdBand : ¬ (embeddedDisk hG).FaceBand
      (embeddedDiskBoundary hG) xd :=
    hG.embeddedDisk_not_faceBand_boundary_of_kernel hx
  have hydBand : ¬ (embeddedDisk hG).FaceBand
      (embeddedDiskBoundary hG) yd :=
    hG.embeddedDisk_not_faceBand_boundary_of_kernel hy
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have hxdOuter : ¬ P.Outer (embeddedDiskMap hG h xd) := by
      simpa [P.outer_mapD_iff_faceBand xd] using hxdBand
    have hzOuter : ¬ P.Outer z := by
      intro hzOuter
      exact hxdOuter (P.outer_of_reachable hzOuter
        (PermReachable.symm H.face hxz))
    have hzDisk : P.InDiskImage z := by
      rcases P.cover z with hzDisk | hzRemainder
      · exact hzDisk
      · exact False.elim (hzOuter
          ⟨z, hzRemainder, PermReachable.refl H.face z⟩)
    rcases hzDisk with ⟨zd, hzdMap⟩
    have hzdOffBoundary : zd ∉ embeddedDiskBoundary hG := by
      intro hzdBoundary
      have hzRemainder : P.InRemainderImage z := by
        rcases (P.disk_boundary_iff_remainder_overlap zd).1 hzdBoundary with
          ⟨zr, hzrMap⟩
        exact ⟨zr, hzrMap.trans hzdMap⟩
      exact hzOuter ⟨z, hzRemainder, PermReachable.refl H.face z⟩
    have hxdZd : PermReachable (embeddedDisk hG).face xd zd :=
      P.reachableD_of_map_face_reachable_of_not_faceBand hxdBand (by
        simpa [hzdMap] using hxz)
    let ezd := (embeddedDisk hG).edge zd
    have hezdYTarget : PermReachable H.face
        (embeddedDiskMap hG h ezd) (embeddedDiskMap hG h yd) := by
      rw [P.map_edgeD zd hzdOffBoundary, hzdMap]
      exact hzy
    have hydOuter : ¬ P.Outer (embeddedDiskMap hG h yd) := by
      simpa [P.outer_mapD_iff_faceBand yd] using hydBand
    have hezdBand : ¬ (embeddedDisk hG).FaceBand
        (embeddedDiskBoundary hG) ezd := by
      intro hezdBand
      have hezdOuter : P.Outer (embeddedDiskMap hG h ezd) :=
        (P.outer_mapD_iff_faceBand ezd).2 hezdBand
      exact hydOuter (P.outer_of_reachable hezdOuter hezdYTarget)
    have hezdY : PermReachable (embeddedDisk hG).face ezd yd :=
      P.reachableD_of_map_face_reachable_of_not_faceBand
        hezdBand hezdYTarget
    have hedgeZOff : G.edge (embeddedDiskVal hG zd) ∉ r := by
      intro hedgeOn
      apply hzdOffBoundary
      apply (mem_embeddedDiskBoundary_iff hG zd).2
      exact (hG.mem_edgePerimeter_iff _).2 hedgeOn
    refine ⟨embeddedDiskVal hG zd,
      embeddedDisk_faceReachable_map hG hxdZd, ?_⟩
    have hsource := embeddedDisk_faceReachable_map hG hezdY
    have hezdVal : embeddedDiskVal hG ezd =
        G.edge (embeddedDiskVal hG zd) := by
      simp [ezd, hedgeZOff]
    simpa [hezdVal] using hsource
  · exact hG.extendEmbedding_ringAdj_map_of_kernel hH hembed hx
      (G.kernel_off_ring hy)

/-- Distinct source faces adjacent to one kernel face remain distinct after
embedding.  This is the semantic form of the incidence-count inequality in
Coq `embed_valid_contract`; target `double_dart` rules out a merger. -/
theorem extendEmbedding_not_faceReachable_of_kernel_ringAdj
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {center a b : G.Dart}
    (hcenter : G.Kernel r center) (haOff : a ∉ r) (hbOff : b ∉ r)
    (hca : G.RingAdj center a) (hcb : G.RingAdj center b)
    (hab : ¬ PermReachable G.face a b) :
    ¬ PermReachable H.face (extendEmbedding r h a)
      (extendEmbedding r h b) := by
  intro habTarget
  rcases hca with ⟨za, hcenterZa, hedgeZaA⟩
  rcases hcb with ⟨zb, hcenterZb, hedgeZbB⟩
  have hzaKernel : G.Kernel r za :=
    G.kernel_faceClosed r hcenter hcenterZa
  have hzbKernel : G.Kernel r zb :=
    G.kernel_faceClosed r hcenter hcenterZb
  have hcenterOff : center ∉ r := G.kernel_off_ring hcenter
  have hzaOff : za ∉ r := G.kernel_off_ring hzaKernel
  have hzbOff : zb ∉ r := G.kernel_off_ring hzbKernel
  have hedgeZaOff : G.edge za ∉ r :=
    hG.edge_not_mem_ring_of_kernel hzaKernel
  have hedgeZbOff : G.edge zb ∉ r :=
    hG.edge_not_mem_ring_of_kernel hzbKernel
  have hzaZbTarget : PermReachable H.face
      (extendEmbedding r h za) (extendEmbedding r h zb) :=
    PermReachable.trans H.face
      (PermReachable.symm H.face
        (hG.extendEmbedding_faceReachable_of_offRing hH hembed
          hcenterOff hzaOff hcenterZa))
      (hG.extendEmbedding_faceReachable_of_offRing hH hembed
        hcenterOff hzbOff hcenterZb)
  have hedgeZaZbTarget : PermReachable H.face
      (H.edge (extendEmbedding r h za))
      (H.edge (extendEmbedding r h zb)) := by
    rw [← hG.extendEmbedding_edge hH hembed za,
      ← hG.extendEmbedding_edge hH hembed zb]
    exact PermReachable.trans H.face
      (hG.extendEmbedding_faceReachable_of_offRing hH hembed
        hedgeZaOff haOff hedgeZaA)
      (PermReachable.trans H.face habTarget
        (PermReachable.symm H.face
          (hG.extendEmbedding_faceReachable_of_offRing hH hembed
            hedgeZbOff hbOff hedgeZbB)))
  have hzaEqZb : extendEmbedding r h za = extendEmbedding r h zb :=
    Birkhoff.doubleDart hH
      (Unavoidability.connectedMinimalCounterexamples_proved H hH)
      (Unavoidability.cubicMinimalCounterexamples_proved H hH)
      hzaZbTarget hedgeZaZbTarget
  have hzaEq : za = zb :=
    hG.extendEmbedding_injective hH hembed hzaOff hzbOff hzaEqZb
  apply hab
  exact PermReachable.trans G.face
    (PermReachable.symm G.face hedgeZaA)
    (hzaEq ▸ hedgeZbB)

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
