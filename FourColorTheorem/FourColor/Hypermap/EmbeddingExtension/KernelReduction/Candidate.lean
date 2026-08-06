import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.KernelBasics

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

namespace KernelReduction
/-- Propagate membership in the selected Jordan disk along an `rlink` path
whose targets avoid the ring face band.  This is the recurring inner induction
in the two descent branches of Coq `embed_functor`. -/
theorem diskN_getLastD_of_rLinkPath_avoids_faceBand
    {q : List G.Dart}
    (hJ : G.Jordan)
    (hq : G.SimpleRLinkCycle q)
    {a : G.Dart} {s : List G.Dart}
    (haDisk : G.DiskN q a)
    (haNotMem : a ∉ q)
    (hs : G.RLinkPath a s)
    (havoid : ∀ z : G.Dart, z ∈ s → ¬ G.FaceBand q z) :
    G.DiskN q ((a :: s).getLastD a) := by
  induction s generalizing a with
  | nil => simpa [List.getLastD] using haDisk
  | cons z s ih =>
      have hs' : G.RLink a z ∧ G.RLinkPath z s := by
        simpa [RLinkPath] using hs
      have hzNotBand : ¬ G.FaceBand q z := havoid z (by simp)
      have haEdgeDisk : G.DiskE q (G.edge a) :=
        G.diskE_edge hJ hq ⟨haDisk, haNotMem⟩
      have haEdgeNotBand : ¬ G.FaceBand q (G.edge a) := by
        intro hband
        exact hzNotBand
          (FaceBand.of_faceReachable (G := G) hband hs'.1)
      have hzDisk : G.DiskN q z :=
        G.diskN_of_faceReachable_of_not_faceBand
          hs'.1 haEdgeDisk.1 haEdgeNotBand
      have hzNotMem : z ∉ q := by
        intro hzMem
        exact hzNotBand
          (FaceBand.of_mem (G := G) hzMem
            (PermReachable.refl G.face z))
      have havoidTail : ∀ w : G.Dart, w ∈ s → ¬ G.FaceBand q w := by
        intro w hw
        exact havoid w (by simp [hw])
      simpa [List.getLastD] using
        ih hzDisk hzNotMem hs'.2 havoidTail

/-- Concatenate two `rlink` paths when the displayed last dart of the first
path links to the head of the second. -/
theorem rLinkPath_append_cons
    {a b : G.Dart} {s t : List G.Dart}
    (hs : G.RLinkPath a s)
    (hab : G.RLink ((a :: s).getLastD a) b)
    (ht : G.RLinkPath b t) :
    G.RLinkPath a (s ++ b :: t) := by
  induction s generalizing a with
  | nil => simpa [RLinkPath, List.getLastD] using And.intro hab ht
  | cons z s ih =>
      have hs' : G.RLink a z ∧ G.RLinkPath z s := by
        simpa [RLinkPath] using hs
      exact ⟨hs'.1, ih hs'.2 (by simpa [List.getLastD] using hab)⟩

theorem getLastD_cons_append_cons
    {α : Type _} (a b : α) (s t : List α) :
    (a :: (s ++ b :: t)).getLastD a = (b :: t).getLastD b := by
  induction s generalizing a with
  | nil => simp [List.getLastD]
  | cons z s ih => simp [List.getLastD]

theorem dropLast_append_getLastD_cons
    {α : Type _} (a : α) (s : List α) :
    (a :: s).dropLast ++ [(a :: s).getLastD a] = a :: s := by
  induction s generalizing a with
  | nil => simp [List.getLastD]
  | cons z s ih =>
      cases s with
      | nil => simp [List.getLastD]
      | cons w ws =>
          simpa [List.getLastD] using congrArg (List.cons a) (ih z)

/-- Reverse propagation used in the spoke-splice branch of Coq
`embed_functor`: if every target of a nonempty `rlink` path avoids the selected
ring face band, disk membership of the last target propagates to the head. -/
theorem diskN_head_of_rLinkPath_avoids_faceBand
    {q : List G.Dart}
    (hJ : G.Jordan)
    (hPlain : G.Plain)
    (hq : G.SimpleRLinkCycle q)
    {a : G.Dart} {s : List G.Dart}
    (hs : G.RLinkPath a s)
    (hsne : s ≠ [])
    (hlastDisk : G.DiskN q ((a :: s).getLastD a))
    (havoid : ∀ z : G.Dart, z ∈ s → ¬ G.FaceBand q z) :
    G.DiskN q a := by
  cases s with
  | nil => exact False.elim (hsne rfl)
  | cons z s =>
      have hs' : G.RLink a z ∧ G.RLinkPath z s := by
        simpa [RLinkPath] using hs
      have hzDisk : G.DiskN q z := by
        cases s with
        | nil => simpa [List.getLastD] using hlastDisk
        | cons w ws =>
            have htailNe : w :: ws ≠ [] := by simp
            have htailLast :
                G.DiskN q ((z :: w :: ws).getLastD z) := by
              simpa [List.getLastD] using hlastDisk
            exact diskN_head_of_rLinkPath_avoids_faceBand
              hJ hPlain hq hs'.2 htailNe htailLast
              (by
                intro u hu
                exact havoid u (by simp [hu]))
      have hzNotBand : ¬ G.FaceBand q z := havoid z (by simp)
      have hedgeNotBand : ¬ G.FaceBand q (G.edge a) := by
        intro hband
        exact hzNotBand
          (FaceBand.of_faceReachable (G := G) hband hs'.1)
      have hedgeDisk : G.DiskN q (G.edge a) :=
        G.diskN_of_faceReachable_of_not_faceBand
          (PermReachable.symm G.face hs'.1) hzDisk hzNotBand
      have hedgeNotMem : G.edge a ∉ q := by
        intro hmem
        exact hedgeNotBand
          (FaceBand.of_mem (G := G) hmem
            (PermReachable.refl G.face (G.edge a)))
      have haaDisk : G.DiskN q (G.edge (G.edge a)) :=
        (G.diskE_edge hJ hq ⟨hedgeDisk, hedgeNotMem⟩).1
      simpa [Plain.edge_edge (G := G) hPlain a] using haaDisk

/-- A selected Jordan disk properly contained in the old one decreases the
bad-cycle induction measure.  The old head witnesses strictness. -/
theorem kernelBadCycle_diskCard_lt_of_diskN_subset
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (B B' : KernelBadCycle G H r h)
    (hsubset : ∀ z : G.Dart,
      G.DiskN (B'.head :: B'.tail) z →
        G.DiskN (B.head :: B.tail) z)
    (hhead : ¬ G.DiskN (B'.head :: B'.tail) B.head) :
    B'.diskCard < B.diskCard := by
  unfold KernelBadCycle.diskCard
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨B.head, ?_, ?_⟩
  · exact fun hx => hhead ((KernelBadCycle.mem_diskFinset B' B.head).1 hx)
  rw [Finset.insert_subset_iff]
  refine ⟨(KernelBadCycle.mem_diskFinset B B.head).2
    (G.diskN_of_mem (by simp)), ?_⟩
  intro z hz
  exact (KernelBadCycle.mem_diskFinset B z).2
    (hsubset z ((KernelBadCycle.mem_diskFinset B' z).1 hz))

end KernelReduction

open KernelReduction

/-- Cycle-construction half of Coq's second node-centrality case.  If
`node x` is central and `node² x` is not, rerooting the closed path at
`edge (node² x)` and erasing face repetitions yields another simple cycle
with a noncentral head and central tail. -/
theorem badCycle_secondNode_candidate
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hPlainH : H.Plain)
    (B : KernelBadCycle G H r h)
    (hcentralN : EdgeCentral G H h (G.node B.head))
    (hnotCentralNN : ¬ EdgeCentral G H h (G.node (G.node B.head))) :
    ∃ p post : List G.Dart,
      B.tail ++ [G.edge (G.node B.head)] = p ++ post ∧
        G.SimpleRLinkCycle
            (G.edge (G.node (G.node B.head)) :: p) ∧
          (∀ z : G.Dart, z ∈ p → EdgeCentral G H h z) ∧
            (∀ z : G.Dart,
              G.DiskN (G.edge (G.node (G.node B.head)) :: p) z →
                G.DiskN (B.head :: B.tail) z) ∧
              ¬ G.DiskN
                (G.edge (G.node (G.node B.head)) :: p) B.head := by
  classical
  let x := B.head
  let q : List G.Dart := x :: B.tail
  have hxDisk : G.DiskN q x := G.diskN_of_mem (by simp [q])
  have hnxDisk : G.DiskN q (G.node x) :=
    (diskN_node_iff (G := G) (r := q)).2 hxDisk
  have hnnxDisk : G.DiskN q (G.node (G.node x)) :=
    (diskN_node_iff (G := G) (r := q)).2 hnxDisk
  have hxKernel : G.Kernel r x := B.diskKernel x hxDisk
  have hxOffRing : x ∉ r := G.kernel_off_ring hxKernel
  have hcubicX := hG.quasicubic x hxOffRing
  have hpne : B.tail ≠ [] := by
    intro hp
    have hloop : G.RLink x x := by
      simpa [x, hp, List.getLastD] using B.simpleCycle.cycle.closing
    exact hG.bridgeless x (PermReachable.symm G.face hloop)
  let enx := G.edge (G.node x)
  let ennx := G.edge (G.node (G.node x))
  have hsourceFace :
      G.face (G.edge x) = G.node (G.node x) := by
    apply G.node.injective
    rw [G.node_face_edge, hcubicX.1]
  have hxEnx : PermReachable G.face x enx := by
    simpa [enx, G.edge_node_eq_face_symm] using
      PermReachable.backward G.face x
  have hlastEnx :
      G.RLink ((x :: B.tail).getLastD x) enx :=
    RLink.of_faceReachable_right (G := G)
      B.simpleCycle.cycle.closing hxEnx
  have hpathExtended : G.RLinkPath x (B.tail ++ [enx]) :=
    RLinkPath.snoc_last (G := G) B.simpleCycle.cycle.path hlastEnx
  have hpathRerooted : G.RLinkPath ennx (B.tail ++ [enx]) := by
    cases hp : B.tail with
    | nil => exact False.elim (hpne hp)
    | cons y ys =>
        have hpath' :
            G.RLink x y ∧ G.RLinkPath y (ys ++ [enx]) := by
          simpa [hp, List.cons_append] using hpathExtended
        have hfaceStep :
            PermReachable G.face (G.edge x) (G.node (G.node x)) := by
          simpa [hsourceFace] using
            PermReachable.forward G.face (G.edge x)
        have hfirst : G.RLink ennx y := by
          unfold RLink
          have hreach :
              PermReachable G.face (G.node (G.node x)) y :=
            PermReachable.trans G.face
              (PermReachable.symm G.face hfaceStep) hpath'.1
          simpa [ennx, (hG.plain (G.node (G.node x))).1] using hreach
        simpa [hp, List.cons_append] using
          (show G.RLink ennx y ∧ G.RLinkPath y (ys ++ [enx]) from
            ⟨hfirst, hpath'.2⟩)
  have hcloseRerooted : G.RLink enx ennx := by
    unfold RLink
    have hback :
        PermReachable G.face (G.node x) (G.face.symm (G.node x)) :=
      PermReachable.backward G.face (G.node x)
    have hedgeEnx : G.edge enx = G.node x := by
      simp [enx, (hG.plain (G.node x)).1]
    have hennx : ennx = G.face.symm (G.node x) := by
      exact G.edge_node_eq_face_symm (G.node x)
    simpa only [hedgeEnx, hennx] using hback
  have hfullCycle :
      G.RLinkCycle (ennx :: (B.tail ++ [enx])) := by
    refine ⟨hpathRerooted, ?_⟩
    simpa [List.getLastD, enx] using hcloseRerooted
  have htailExtendedSimple : G.FaceSimple (B.tail ++ [enx]) := by
    have hrot : G.FaceSimple (B.tail ++ [x]) := by
      simpa [q, x, List.rotate_cons_succ] using
        (SimpleRLinkCycle.rotate (G := G) 1 B.simpleCycle).faceSimple
    have horbit :
        PermOrbit.of G.face x = PermOrbit.of G.face enx :=
      PermOrbit.of_eq_of G.face hxEnx
    rw [faceSimple_iff_nodup_faceOrbit_map] at hrot ⊢
    simpa [List.map_append, horbit] using hrot
  rcases RLinkCycle.firstFaceSimplePrefix (G := G)
      hfullCycle htailExtendedSimple with
    ⟨p, post, hpDecomp, hpCycle, hpAvoid, hpost⟩
  have henxCentral : EdgeCentral G H h enx := by
    exact (edgeCentral_edge_iff G H hG.plain hPlainH h (G.node x)).2
      hcentralN
  have hpCentral : ∀ z : G.Dart, z ∈ p → EdgeCentral G H h z := by
    intro z hz
    have hz : z ∈ B.tail ++ [enx] := by
      rw [hpDecomp]
      exact List.mem_append_left post hz
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · exact (B.tailCentral z hz).2
    · simp at hz
      subst z
      exact henxCentral
  have hennxNot : ¬ EdgeCentral G H h ennx := by
    intro hcentral
    exact hnotCentralNN
      ((edgeCentral_edge_iff G H hG.plain hPlainH h
        (G.node (G.node x))).1 hcentral)
  have hproperCandidate : G.ProperRing (ennx :: p) :=
    KernelBadCycle.proper_of_simpleCycle_tail_edgeCentral
      hennxNot hpCycle hpCentral hG.bridgeless hG.plain hPlainH
  have hJordan : G.Jordan := hG.jordan
  have hedgeOutside : ¬ G.DiskN (ennx :: p) (G.edge ennx) :=
    G.diskN_edge_ring hJordan hG.plain hpCycle hproperCandidate (by simp)
  have hxOutside : ¬ G.DiskN (ennx :: p) x := by
    intro hxInside
    have hnxInside : G.DiskN (ennx :: p) (G.node x) :=
      (diskN_node_iff (G := G) (r := ennx :: p)).2 hxInside
    have hnnxInside : G.DiskN (ennx :: p) (G.node (G.node x)) :=
      (diskN_node_iff (G := G) (r := ennx :: p)).2 hnxInside
    have hedgeEq : G.edge ennx = G.node (G.node x) := by
      simp [ennx, (hG.plain (G.node (G.node x))).1]
    exact hedgeOutside (by simpa [hedgeEq] using hnnxInside)
  have hfullNodup : (B.tail ++ [enx]).Nodup :=
    htailExtendedSimple.nodup
  have hnnxNeX : G.node (G.node x) ≠ x := by
    intro hEq
    have hnodeEq : G.node x = x := by
      calc
        G.node x = G.node (G.node (G.node x)) :=
          (congrArg G.node hEq).symm
        _ = x := hcubicX.1
    exact hcubicX.2 hnodeEq
  have hnnxNotMemQ : G.node (G.node x) ∉ q := by
    intro hmem
    change G.node (G.node x) ∈ x :: B.tail at hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | htail
    · exact hnnxNeX hEq
    · exact hnotCentralNN (B.tailCentral _ htail).2
  have hennxDiskQ : G.DiskN q ennx := by
    have hnnxE : G.DiskE q (G.node (G.node x)) :=
      ⟨hnnxDisk, hnnxNotMemQ⟩
    exact (G.diskE_edge hJordan B.simpleCycle hnnxE).1
  have hfaceEnnxNodeX :
      PermReachable G.face ennx (G.node x) := by
    have hreach : PermReachable G.face (G.node x) ennx := by
      simpa [RLink, enx, (hG.plain (G.node x)).1] using hcloseRerooted
    exact PermReachable.symm G.face hreach
  have henxDiskQ_of_memP (henxP : enx ∈ p) : G.DiskN q enx := by
    have hpostNil : post = [] := by
      by_contra hpost
      have hlastPost : post.getLast hpost = enx := by
        calc
          post.getLast hpost =
              (p ++ post).getLast (List.append_ne_nil_of_right_ne_nil p hpost) :=
            (List.getLast_append_of_right_ne_nil p post hpost).symm
          _ = (B.tail ++ [enx]).getLast (by simp) := by
            apply List.getLast_congr
            exact hpDecomp.symm
          _ = enx := List.getLast_append_singleton B.tail
      have henxPost : enx ∈ post := by
        rw [← hlastPost]
        exact List.getLast_mem hpost
      have hnodupAppend : (p ++ post).Nodup := by
        simpa [hpDecomp] using hfullNodup
      have hdisjoint : p.Disjoint post :=
        List.disjoint_of_nodup_append hnodupAppend
      exact hdisjoint henxP henxPost
    have hfullEqP : B.tail ++ [enx] = p := by
      simpa [hpostNil] using hpDecomp
    have hnodeNotMemQ : G.node x ∉ q := by
      intro hmem
      change G.node x ∈ x :: B.tail at hmem
      rw [List.mem_cons] at hmem
      rcases hmem with hEq | htail
      · exact hcubicX.2 hEq
      · have hnodeP : G.node x ∈ p := by
          rw [← hfullEqP]
          exact List.mem_append_left [enx] htail
        exact (hpAvoid (G.node x) hnodeP) hfaceEnnxNodeX
    have hnodeE : G.DiskE q (G.node x) :=
      ⟨hnxDisk, hnodeNotMemQ⟩
    exact (G.diskE_edge hJordan B.simpleCycle hnodeE).1
  have hbaseOld :
      ∀ z : G.Dart, z ∈ ennx :: p → G.DiskN q (G.node.symm z) := by
    intro z hz
    apply (diskN_node_symm_iff (G := G) (r := q)).2
    rw [List.mem_cons] at hz
    rcases hz with rfl | hzP
    · exact hennxDiskQ
    · have hzFull : z ∈ B.tail ++ [enx] := by
        rw [hpDecomp]
        exact List.mem_append_left post hzP
      rw [List.mem_append] at hzFull
      rcases hzFull with hzTail | hzLast
      · exact G.diskN_of_mem (by simp [q, hzTail])
      · have hzEq : z = enx := by simpa using hzLast
        subst z
        exact henxDiskQ_of_memP hzP
  have hboundaryOutside :
      ∀ y : G.Dart, y ∈ B.tail → y ∉ ennx :: p →
        ¬ G.DiskN (ennx :: p) y := by
    intro y hyTail hyNotCandidate hyDisk
    have hyNotP : y ∉ p := by
      intro hyP
      exact hyNotCandidate (by simp [hyP])
    have hyFull : y ∈ p ++ post := by
      rw [← hpDecomp]
      exact List.mem_append_left [enx] hyTail
    have hyPost : y ∈ post := by
      rcases List.mem_append.mp hyFull with hyP | hyPost
      · exact False.elim (hyNotP hyP)
      · exact hyPost
    rcases (List.mem_iff_append).1 hyPost with
      ⟨before, after, hpostSplit⟩
    rcases hpost with hpostNil | ⟨t, ts, hpostFirst, hfaceEnnxT⟩
    · simp [hpostNil] at hyPost
    · have hfirstSplit : t :: ts = before ++ y :: after := by
        rw [← hpostFirst]
        exact hpostSplit
      have htPrefix : t ∈ before ++ [y] := by
        cases before with
        | nil =>
            have hty : t = y := (List.cons.inj (by simpa using hfirstSplit)).1
            simp [hty]
        | cons b bs =>
            have htb : t = b :=
              (List.cons.inj (by simpa using hfirstSplit)).1
            simp [htb]
      let left : List G.Dart := p ++ before ++ [y]
      have hfullSplit : B.tail ++ [enx] = left ++ after := by
        dsimp [left]
        rw [hpDecomp, hpostSplit]
        simp [List.append_assoc]
      have hnodupSplit : (left ++ after).Nodup := by
        simpa [hfullSplit] using hfullNodup
      have hdisjoint : left.Disjoint after :=
        List.disjoint_of_nodup_append hnodupSplit
      have havoidAfter :
          ∀ z : G.Dart, z ∈ after → ¬ G.FaceBand (ennx :: p) z := by
        intro z hzAfter hzBand
        rcases hzBand with ⟨a, haCandidate, haz⟩
        rw [List.mem_cons] at haCandidate
        have haLeft : ∃ a' : G.Dart,
            a' ∈ left ∧ PermReachable G.face a' z := by
          rcases haCandidate with rfl | haP
          · refine ⟨t, ?_, ?_⟩
            · dsimp [left]
              simpa [List.append_assoc] using
                (List.mem_append_right p htPrefix)
            · exact PermReachable.trans G.face
                (PermReachable.symm G.face hfaceEnnxT) haz
          · exact ⟨a, by
              dsimp [left]
              simpa [List.append_assoc] using
                (List.mem_append_left (before ++ [y]) haP), haz⟩
        rcases haLeft with ⟨a', haLeft, ha'z⟩
        have haFull : a' ∈ B.tail ++ [enx] := by
          rw [hfullSplit]
          exact List.mem_append_left after haLeft
        have hzFull : z ∈ B.tail ++ [enx] := by
          rw [hfullSplit]
          exact List.mem_append_right left hzAfter
        have hazEq : a' = z :=
          FaceSimple.eq_of_faceReachable_of_mem
            (G := G) htailExtendedSimple haFull hzFull ha'z
        exact hdisjoint haLeft (hazEq ▸ hzAfter)
      rcases (List.mem_iff_append).1 hyTail with
        ⟨beforeTail, afterTail, htailSplit⟩
      have hfullSplitTail :
          B.tail ++ [enx] = beforeTail ++ y :: (afterTail ++ [enx]) := by
        rw [htailSplit]
        simp [List.append_assoc]
      have hyNotLeft : y ∉ p ++ before := by
        have hnodup : ((p ++ before) ++ y :: after).Nodup := by
          simpa [left, List.append_assoc] using hnodupSplit
        intro hyLeft
        exact (List.nodup_append.mp hnodup).2.2
          y hyLeft y (by simp) rfl
      have hyNotAfter : y ∉ after := by
        have hnodup : ((p ++ before) ++ y :: after).Nodup := by
          simpa [left, List.append_assoc] using hnodupSplit
        exact (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
      have hafterEq : after = afterTail ++ [enx] := by
        have hEq :
            (p ++ before) ++ y :: after =
              beforeTail ++ y :: (afterTail ++ [enx]) := by
          calc
            (p ++ before) ++ y :: after = left ++ after := by
              simp [left, List.append_assoc]
            _ = B.tail ++ [enx] := hfullSplit.symm
            _ = beforeTail ++ y :: (afterTail ++ [enx]) := hfullSplitTail
        exact (List.append_cons_inj_of_notMem hyNotLeft hyNotAfter).mp hEq |>.2.2
      have hpathSuffix : G.RLinkPath y after := by
        have hpathFull : G.RLinkPath x (left ++ after) := by
          rw [← hfullSplit]
          exact hpathExtended
        have hpath : G.RLinkPath x ((p ++ before) ++ y :: after) := by
          simpa [left, List.append_assoc] using hpathFull
        exact RLinkPath.suffix_of_append_cons (G := G) hpath
      have hlastAfter : (y :: after).getLastD y = enx := by
        simp [hafterEq, List.getLastD]
      have henxDiskCandidate : G.DiskN (ennx :: p) enx := by
        rw [← hlastAfter]
        exact diskN_getLastD_of_rLinkPath_avoids_faceBand
          hJordan hpCycle hyDisk hyNotCandidate hpathSuffix havoidAfter
      have henxNotCandidate : enx ∉ ennx :: p := by
        intro henxMem
        have henxBand : G.FaceBand (ennx :: p) enx :=
          FaceBand.of_mem (G := G) henxMem
            (PermReachable.refl G.face enx)
        have henxAfter : enx ∈ after := by simp [hafterEq]
        exact havoidAfter enx henxAfter henxBand
      have hedgeEnxDisk : G.DiskN (ennx :: p) (G.edge enx) :=
        (G.diskE_edge hJordan hpCycle
          ⟨henxDiskCandidate, henxNotCandidate⟩).1
      have hedgeEnx : G.edge enx = G.node x := by
        simp [enx, (hG.plain (G.node x)).1]
      apply hxOutside
      exact (diskN_node_iff (G := G) (r := ennx :: p)).1
        (by simpa [hedgeEnx] using hedgeEnxDisk)
  have hsubset :
      ∀ z : G.Dart, G.DiskN (ennx :: p) z → G.DiskN q z := by
    intro z hz
    rcases hz with ⟨a, haCandidate, haz⟩
    induction haz with
    | refl => exact hbaseOld a haCandidate
    | @tail b c hab hbc ih =>
        have hbCandidate : G.DiskN (ennx :: p) b :=
          ⟨a, haCandidate, hab⟩
        rcases hbc.2 with hnode | hface
        · subst c
          exact G.diskN_node_symm ih
        · subst c
          by_cases hbOldRing : b ∈ q
          · change b ∈ x :: B.tail at hbOldRing
            rw [List.mem_cons] at hbOldRing
            rcases hbOldRing with hbX | hbTail
            · subst b
              exact False.elim (hxOutside hbCandidate)
            · exact False.elim
                (hboundaryOutside b hbTail hbc.1 hbCandidate)
          · exact G.diskN_face_of_not_mem ih hbOldRing
  exact ⟨p, post, by simpa [enx, x] using hpDecomp,
    by simpa [ennx, x] using hpCycle, hpCentral,
    by simpa [ennx, x, q] using hsubset,
    by simpa [ennx, x] using hxOutside⟩

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
