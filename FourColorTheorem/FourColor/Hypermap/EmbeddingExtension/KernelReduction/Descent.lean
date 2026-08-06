import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.KernelReduction.Candidate

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

open KernelReduction

/-- Pack the second-node candidate as a new bad cycle and discharge Coq's
strict finite-cardinality descent. -/
theorem badCycle_secondNode_smaller
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hPlainH : H.Plain)
    (B : KernelBadCycle G H r h)
    (hcentralN : EdgeCentral G H h (G.node B.head))
    (hnotCentralNN : ¬ EdgeCentral G H h (G.node (G.node B.head))) :
    ∃ B' : KernelBadCycle G H r h, B'.diskCard < B.diskCard := by
  classical
  rcases hG.badCycle_secondNode_candidate hPlainH B hcentralN
      hnotCentralNN with
    ⟨p, _post, _hdecomp, hcycle, hpCentral, hsubset, hxOutside⟩
  let B' : KernelBadCycle G H r h := {
    head := G.edge (G.node (G.node B.head))
    tail := p
    headNotCentral := by
      intro hcentral
      exact hnotCentralNN
        ((edgeCentral_edge_iff G H hG.plain hPlainH h
          (G.node (G.node B.head))).1 hcentral)
    simpleCycle := hcycle
    tailCentral := by
      intro z hz
      exact ⟨B.diskKernel z (hsubset z (G.diskN_of_mem (by simp [hz]))),
        hpCentral z hz⟩
    diskKernel := by
      intro z hz
      exact B.diskKernel z (hsubset z hz)
  }
  refine ⟨B', kernelBadCycle_diskCard_lt_of_diskN_subset B B' ?_ ?_⟩
  · simpa [B'] using hsubset
  · simpa [B'] using hxOutside

/-- Coq's remaining `embed_functor` branch.  When `node x` is noncentral, a
central spoke path from `edge (node x)` is cut at its first contact with the
old boundary and spliced to the boundary suffix.  The resulting bad cycle has
a strictly smaller selected disk. -/
theorem badCycle_firstNode_smaller
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hPlainH : H.Plain)
    (hembed : Preembedding G H (G.Kernel r) h)
    (B : KernelBadCycle G H r h)
    (hnotCentralN : ¬ EdgeCentral G H h (G.node B.head)) :
    ∃ B' : KernelBadCycle G H r h, B'.diskCard < B.diskCard := by
  classical
  let x := B.head
  let q : List G.Dart := x :: B.tail
  let enx := G.edge (G.node x)
  let p1 : List G.Dart := B.tail ++ [enx]
  have hxDisk : G.DiskN q x := G.diskN_of_mem (by simp [q])
  have hnxDisk : G.DiskN q (G.node x) :=
    (diskN_node_iff (G := G) (r := q)).2 hxDisk
  have hxKernel : G.Kernel r x := B.diskKernel x hxDisk
  have hxOffRing : x ∉ r := G.kernel_off_ring hxKernel
  have hcubicX := hG.quasicubic x hxOffRing
  have hnodeNotMemQ : G.node x ∉ q := by
    intro hmem
    change G.node x ∈ x :: B.tail at hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | htail
    · exact hcubicX.2 hEq
    · exact hnotCentralN (B.tailCentral _ htail).2
  have hJordan : G.Jordan := hG.jordan
  have hnodeE : G.DiskE q (G.node x) := ⟨hnxDisk, hnodeNotMemQ⟩
  have henxE : G.DiskE q enx :=
    G.diskE_edge hJordan B.simpleCycle hnodeE
  have henxDisk : G.DiskN q enx := henxE.1
  have hedgeEnx : G.edge enx = G.node x := by
    simp [enx, (hG.plain (G.node x)).1]
  have henxKernel : G.Kernel r enx := B.diskKernel enx henxDisk
  have hedgeEnxKernel : G.Kernel r (G.edge enx) := by
    rw [hedgeEnx]
    exact B.diskKernel (G.node x) hnxDisk
  rcases hembed.simplePath (G.kernel_faceClosed r)
      hedgeEnxKernel henxKernel with
    ⟨q1, hq1Path, hq1LastFace, hq1ne, hq1Simple, hq1All⟩
  have hxEnx : PermReachable G.face x enx := by
    simpa [enx, G.edge_node_eq_face_symm] using
      PermReachable.backward G.face x
  have hpathExtended : G.RLinkPath x p1 := by
    have hlastEnx : G.RLink ((x :: B.tail).getLastD x) enx :=
      RLink.of_faceReachable_right (G := G)
        B.simpleCycle.cycle.closing hxEnx
    simpa [p1] using
      RLinkPath.snoc_last (G := G) B.simpleCycle.cycle.path hlastEnx
  have hp1Simple : G.FaceSimple p1 := by
    have hrot : G.FaceSimple (B.tail ++ [x]) := by
      simpa [q, x, List.rotate_cons_succ] using
        (SimpleRLinkCycle.rotate (G := G) 1 B.simpleCycle).faceSimple
    have horbit :
        PermOrbit.of G.face x = PermOrbit.of G.face enx :=
      PermOrbit.of_eq_of G.face hxEnx
    rw [faceSimple_iff_nodup_faceOrbit_map] at hrot ⊢
    simpa [p1, List.map_append, horbit] using hrot
  have hp1Nodup : p1.Nodup := hp1Simple.nodup
  let lastQ1 : G.Dart := q1.getLast hq1ne
  have hlastQ1Mem : lastQ1 ∈ q1 := by
    exact List.getLast_mem hq1ne
  have hlastQ1Eq : (enx :: q1).getLastD enx = lastQ1 := by
    cases q1 with
    | nil => contradiction
    | cons z zs => simp [lastQ1, List.getLastD]
  have hlastBand : G.FaceBand p1 lastQ1 := by
    refine ⟨enx, by simp [p1], ?_⟩
    have hlast := hq1LastFace
    rw [hlastQ1Eq] at hlast
    exact PermReachable.symm G.face hlast
  have hcontact : ∃ z : G.Dart, z ∈ q1 ∧ G.FaceBand p1 z :=
    ⟨lastQ1, hlastQ1Mem, hlastBand⟩
  rcases list_exists_first_of_exists_mem (fun z : G.Dart => G.FaceBand p1 z)
      hcontact with
    ⟨q2, u, qrest, hq1Split, huBand, hq2Avoid⟩
  rcases huBand with ⟨y, hyP1, hyu⟩
  rcases (List.mem_iff_append).1 hyP1 with
    ⟨p2, p3, hp1Split⟩
  have hq2Path : G.RLinkPath enx q2 := by
    apply RLinkPath.prefix_of_append (G := G)
    simpa [hq1Split] using hq1Path
  have hlastQ2U : G.RLink ((enx :: q2).getLastD enx) u := by
    have hpath : G.RLinkPath enx (q2 ++ u :: qrest) := by
      simpa [hq1Split] using hq1Path
    exact RLinkPath.last_link_of_append_cons (G := G) hpath
  have hlastQ2Y : G.RLink ((enx :: q2).getLastD enx) y :=
    RLink.of_faceReachable_right (G := G) hlastQ2U
      (PermReachable.symm G.face hyu)
  have hp3Path : G.RLinkPath y p3 := by
    have hpath : G.RLinkPath x (p2 ++ y :: p3) := by
      simpa [p1, hp1Split] using hpathExtended
    exact RLinkPath.suffix_of_append_cons (G := G) hpath
  have hsplicedFull : G.RLinkPath enx (q2 ++ y :: p3) :=
    rLinkPath_append_cons hq2Path hlastQ2Y hp3Path
  have hlastP3 : (y :: p3).getLastD y = enx := by
    calc
      (y :: p3).getLastD y =
          (x :: (p2 ++ y :: p3)).getLastD x :=
        (getLastD_cons_append_cons x y p2 p3).symm
      _ = (x :: p1).getLastD x := by rw [hp1Split]
      _ = enx := by simp [p1, List.getLastD]
  let seg : List G.Dart := (y :: p3).dropLast
  have hsegAppend : seg ++ [enx] = y :: p3 := by
    dsimp [seg]
    rw [← hlastP3]
    exact dropLast_append_getLastD_cons y p3
  have htailSplit : B.tail = p2 ++ seg := by
    exact List.append_cancel_right (bs := [enx]) (by
      calc
        B.tail ++ [enx] = p1 := by rfl
        _ = p2 ++ y :: p3 := hp1Split
        _ = (p2 ++ seg) ++ [enx] := by
          rw [← hsegAppend]
          simp [List.append_assoc])
  let candTail : List G.Dart := q2 ++ seg
  have hsplicedClosed : G.RLinkPath enx (candTail ++ [enx]) := by
    dsimp [candTail]
    rw [List.append_assoc, hsegAppend]
    exact hsplicedFull
  have hcandPath : G.RLinkPath enx candTail :=
    RLinkPath.prefix_of_append (G := G) hsplicedClosed
  have hcandClose : G.RLink ((enx :: candTail).getLastD enx) enx := by
    simpa using
      (RLinkPath.last_link_of_append_cons (G := G)
        (p := candTail) (q := []) hsplicedClosed)
  have hq2SubQ1 : q2.Sublist q1 := by
    rw [hq1Split]
    exact List.sublist_append_left q2 (u :: qrest)
  have hq2Simple : G.FaceSimple q2 := by
    rw [FaceSimple] at hq1Simple ⊢
    exact List.Pairwise.sublist hq2SubQ1 hq1Simple
  have hsegSubTail : seg.Sublist B.tail := by
    rw [htailSplit]
    exact List.sublist_append_right p2 seg
  have hsegSubP1 : seg.Sublist p1 := by
    change seg.Sublist (B.tail ++ [enx])
    exact hsegSubTail.trans (List.sublist_append_left B.tail [enx])
  have hsegSimple : G.FaceSimple seg := by
    rw [FaceSimple] at hp1Simple ⊢
    exact List.Pairwise.sublist hsegSubP1 hp1Simple
  have hbandEq : ∀ z : G.Dart,
      G.FaceBand q z ↔ G.FaceBand p1 z := by
    intro z
    change G.FaceBand (x :: B.tail) z ↔
      G.FaceBand (B.tail ++ [enx]) z
    rw [FaceBand.cons, FaceBand.concat]
    have hfaceEq :
        PermReachable G.face x z ↔ PermReachable G.face enx z := by
      constructor
      · exact PermReachable.trans G.face
          (PermReachable.symm G.face hxEnx)
      · intro h
        exact PermReachable.trans G.face hxEnx h
    rw [hfaceEq]
    tauto
  have hq2AvoidQ :
      ∀ z : G.Dart, z ∈ q2 → ¬ G.FaceBand q z := by
    intro z hz hband
    exact hq2Avoid z hz ((hbandEq z).1 hband)
  have hq2OldDisk : ∀ z : G.Dart, z ∈ q2 → G.DiskN q z := by
    intro z hz
    rcases (List.mem_iff_append).1 hz with ⟨pre, post, hq2Split⟩
    have hprefixPath : G.RLinkPath enx (pre ++ [z]) := by
      apply RLinkPath.prefix_of_append (G := G)
      have hpath : G.RLinkPath enx (pre ++ z :: post) := by
        simpa [hq2Split] using hq2Path
      simpa [List.append_assoc] using hpath
    have havoidPrefix :
        ∀ w : G.Dart, w ∈ pre ++ [z] → ¬ G.FaceBand q w := by
      intro w hw
      apply hq2AvoidQ w
      have hw' : w ∈ pre ++ z :: post := by
        rw [List.mem_append] at hw ⊢
        rcases hw with hw | hw
        · exact Or.inl hw
        · simp at hw
          exact Or.inr (by simp [hw])
      simpa [hq2Split] using hw'
    have hlast : (enx :: (pre ++ [z])).getLastD enx = z := by
      simp [List.getLastD]
    rw [← hlast]
    exact diskN_getLastD_of_rLinkPath_avoids_faceBand
      hJordan B.simpleCycle henxDisk
      henxE.2
      hprefixPath havoidPrefix
  have henxNotTail : enx ∉ B.tail := by
    have hnodup : (B.tail ++ [enx]).Nodup := by simpa [p1] using hp1Nodup
    intro hmem
    exact (List.nodup_append.mp hnodup).2.2
      enx hmem enx (by simp) rfl
  have hcandSimple : G.FaceSimple (enx :: candTail) := by
    rw [FaceSimple, List.pairwise_cons]
    constructor
    · intro z hz hface
      change z ∈ q2 ++ seg at hz
      rw [List.mem_append] at hz
      rcases hz with hzQ2 | hzSeg
      · exact hq2Avoid z hzQ2
          ⟨enx, by simp [p1], hface⟩
      · have hzP1 : z ∈ p1 := hsegSubP1.subset hzSeg
        have henxP1 : enx ∈ p1 := by simp [p1]
        have hEq := FaceSimple.eq_of_faceReachable_of_mem
          (G := G) hp1Simple henxP1 hzP1 hface
        exact henxNotTail (hEq ▸ hsegSubTail.subset hzSeg)
    · change G.FaceSimple (q2 ++ seg)
      rw [FaceSimple, List.pairwise_append]
      refine ⟨hq2Simple, hsegSimple, ?_⟩
      intro a ha b hb hab
      have hbP1 : b ∈ p1 := hsegSubP1.subset hb
      exact hq2Avoid a ha
        ⟨b, hbP1, PermReachable.symm G.face hab⟩
  have hcandCycle : G.SimpleRLinkCycle (enx :: candTail) :=
    ⟨⟨hcandPath, hcandClose⟩, hcandSimple⟩
  have hsegCentral :
      ∀ z : G.Dart, z ∈ seg → EdgeCentral G H h z := by
    intro z hz
    exact (B.tailCentral z (hsegSubTail.subset hz)).2
  have hq2Central :
      ∀ z : G.Dart, z ∈ q2 → EdgeCentral G H h z := by
    intro z hz
    exact (hq1All z (hq2SubQ1.subset hz)).2
  have hcandTailCentral :
      ∀ z : G.Dart, z ∈ candTail → EdgeCentral G H h z := by
    intro z hz
    change z ∈ q2 ++ seg at hz
    rw [List.mem_append] at hz
    exact hz.elim (hq2Central z) (hsegCentral z)
  have henxNotCentral : ¬ EdgeCentral G H h enx := by
    intro hcentral
    exact hnotCentralN
      ((edgeCentral_edge_iff G H hG.plain hPlainH h (G.node x)).1 hcentral)
  have hcandProper : G.ProperRing (enx :: candTail) :=
    KernelBadCycle.proper_of_simpleCycle_tail_edgeCentral
      henxNotCentral hcandCycle hcandTailCentral hG.bridgeless
      hG.plain hPlainH
  have hxOutside : ¬ G.DiskN (enx :: candTail) x := by
    intro hxIn
    have hnxIn : G.DiskN (enx :: candTail) (G.node x) :=
      (diskN_node_iff (G := G) (r := enx :: candTail)).2 hxIn
    have hedgeOutside :=
      G.diskN_edge_ring hJordan hG.plain hcandCycle hcandProper
        (x := enx) (by simp)
    apply hedgeOutside
    rw [hedgeEnx]
    exact hnxIn
  have hbaseOld :
      ∀ z : G.Dart, z ∈ enx :: candTail → G.DiskN q (G.node.symm z) := by
    intro z hz
    apply (diskN_node_symm_iff (G := G) (r := q)).2
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact henxDisk
    · change z ∈ q2 ++ seg at hz
      rw [List.mem_append] at hz
      rcases hz with hzQ2 | hzSeg
      · exact hq2OldDisk z hzQ2
      · exact G.diskN_of_mem
          (by simp [q, hsegSubTail.subset hzSeg])
  have htailNodup : B.tail.Nodup := by
    exact (List.nodup_cons.mp B.simpleCycle.faceSimple.nodup).2
  have hdisjointP2Seg : p2.Disjoint seg := by
    apply List.disjoint_of_nodup_append
    simpa [htailSplit] using htailNodup
  have hxNotTail : x ∉ B.tail :=
    (List.nodup_cons.mp B.simpleCycle.faceSimple.nodup).1
  have hp2AvoidCandidate :
      ∀ z : G.Dart, z ∈ p2 → ¬ G.FaceBand (enx :: candTail) z := by
    intro z hzP2 hzBand
    rcases hzBand with ⟨a, haCand, haz⟩
    rw [List.mem_cons] at haCand
    rcases haCand with rfl | haTail
    · have hxz : PermReachable G.face x z :=
        PermReachable.trans G.face hxEnx haz
      have hzTail : z ∈ B.tail := by
        rw [htailSplit]
        exact List.mem_append_left seg hzP2
      have hEq := FaceSimple.eq_of_faceReachable_of_mem
        (G := G) B.simpleCycle.faceSimple (by simp [x])
          (by simp [hzTail]) hxz
      exact hxNotTail (hEq ▸ hzTail)
    · change a ∈ q2 ++ seg at haTail
      rw [List.mem_append] at haTail
      rcases haTail with haQ2 | haSeg
      · have hzP1 : z ∈ p1 := by
          rw [hp1Split]
          exact List.mem_append_left (y :: p3) hzP2
        exact hq2Avoid a haQ2
          ⟨z, hzP1, PermReachable.symm G.face haz⟩
      · have haP1 : a ∈ p1 := hsegSubP1.subset haSeg
        have hzP1 : z ∈ p1 := by
          rw [hp1Split]
          exact List.mem_append_left (y :: p3) hzP2
        have hEq := FaceSimple.eq_of_faceReachable_of_mem
          (G := G) hp1Simple haP1 hzP1 haz
        exact hdisjointP2Seg hzP2 (hEq ▸ haSeg)
  have hboundaryOutside :
      ∀ z : G.Dart, z ∈ B.tail → z ∉ enx :: candTail →
        ¬ G.DiskN (enx :: candTail) z := by
    intro z hzTail hzNotCand hzDisk
    have hzP2 : z ∈ p2 := by
      rw [htailSplit, List.mem_append] at hzTail
      rcases hzTail with hzP2 | hzSeg
      · exact hzP2
      · exact False.elim (hzNotCand (by simp [candTail, hzSeg]))
    rcases (List.mem_iff_append).1 hzP2 with
      ⟨pre, post, hp2Split⟩
    have hpathToZ : G.RLinkPath x (pre ++ [z]) := by
      apply RLinkPath.prefix_of_append (G := G)
      have hpath : G.RLinkPath x (pre ++ z :: (post ++ seg ++ [enx])) := by
        simpa [p1, htailSplit, hp2Split, List.append_assoc] using hpathExtended
      simpa [List.append_assoc] using hpath
    have hlastZ : (x :: (pre ++ [z])).getLastD x = z := by
      simp [List.getLastD]
    have htargetsAvoid :
        ∀ w : G.Dart, w ∈ pre ++ [z] →
          ¬ G.FaceBand (enx :: candTail) w := by
      intro w hw
      apply hp2AvoidCandidate w
      have hw' : w ∈ pre ++ z :: post := by
        rw [List.mem_append] at hw ⊢
        rcases hw with hw | hw
        · exact Or.inl hw
        · simp at hw
          exact Or.inr (by simp [hw])
      simpa [hp2Split] using hw'
    apply hxOutside
    exact diskN_head_of_rLinkPath_avoids_faceBand
      hJordan hG.plain hcandCycle hpathToZ (by simp)
      (by rw [hlastZ]; exact hzDisk) htargetsAvoid
  have hsubset :
      ∀ z : G.Dart, G.DiskN (enx :: candTail) z → G.DiskN q z := by
    intro z hz
    rcases hz with ⟨a, haCand, haz⟩
    induction haz with
    | refl => exact hbaseOld a haCand
    | @tail b c hab hbc ih =>
        have hbCand : G.DiskN (enx :: candTail) b :=
          ⟨a, haCand, hab⟩
        rcases hbc.2 with hnode | hface
        · subst c
          exact G.diskN_node_symm ih
        · subst c
          by_cases hbOld : b ∈ q
          · change b ∈ x :: B.tail at hbOld
            rw [List.mem_cons] at hbOld
            rcases hbOld with hbX | hbTail
            · subst b
              exact False.elim (hxOutside hbCand)
            · exact False.elim
                (hboundaryOutside b hbTail hbc.1 hbCand)
          · exact G.diskN_face_of_not_mem ih hbOld
  let B' : KernelBadCycle G H r h := {
    head := enx
    tail := candTail
    headNotCentral := henxNotCentral
    simpleCycle := hcandCycle
    tailCentral := by
      intro z hz
      exact ⟨B.diskKernel z (hsubset z (G.diskN_of_mem (by simp [hz]))),
        hcandTailCentral z hz⟩
    diskKernel := by
      intro z hz
      exact B.diskKernel z (hsubset z hz)
  }
  refine ⟨B', kernelBadCycle_diskCard_lt_of_diskN_subset B B' ?_ ?_⟩
  · simpa [B', x] using hsubset
  · simpa [B', x] using hxOutside

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
