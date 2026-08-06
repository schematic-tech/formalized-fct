import FourColorTheorem.FourColor.Coloring.Birkhoff.CertificateBoundary

/-! Trace and coloring obstructions for sewn Birkhoff basis maps. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

private theorem length_snipdRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r) :
    (Hypermap.snipdRing hplanar hr).length = r.length := by
  simpa only [List.length_map] using congrArg List.length
    (Hypermap.map_snipdRing hplanar hr)

/-- Coq `chkbP` up to coloring extraction: the basis map sewn into the snip
disk is planar, bridgeless, plain, precubic, and strictly smaller than the
minimal host. -/
theorem basisSewMap_geometry_card
    {G : Hypermap.{u}} {r : List G.Dart} {h m : Nat} {cp : CProg}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1) (hnt : G.NontrivialRing m r)
    (hshort : ∀ r' : List G.Dart,
      G.SimpleRLinkCycle r' → r'.length ≤ h →
        ¬ G.NontrivialRing 0 r')
    (hcheck : checkBasisProgram h m cp = true) :
    let S := basisSewBoundary hG.planar hr hrlen hcheck
    S.sewMap.PlanarBridgelessPlainPrecubic ∧
      Fintype.card S.sewMap.Dart < Fintype.card G.Dart := by
  let hplanar := hG.planar
  let Gd := G.snipDisk r hplanar hr
  let Grr := G.snipRemainder r hplanar hr
  let bGd := Hypermap.snipdRing hplanar hr
  let bGrr := Hypermap.sniprRing hplanar hr
  let Gr := (cpmap cp).map
  let bGr := basisBoundary cp
  let S := basisSewBoundary hplanar hr hrlen hcheck
  let Psnip := Hypermap.snipPatch hplanar hr
  let P2 := S.sewMapPatch
  change S.sewMap.PlanarBridgelessPlainPrecubic ∧
    Fintype.card S.sewMap.Dart < Fintype.card G.Dart
  have hcp := (checkBasisProgram_spec hcheck).1
  have hplainParts := Psnip.plain_iff.mp hG.plain
  have hcubicParts := Psnip.cubic_iff.mp hcubic
  have hbridgeParts := Psnip.bridgeless_parts hG.bridgeless
  have hbGrrLen : bGrr.length = r.length := by
    calc
      bGrr.length = (bGrr.map Hypermap.snipr).length := by simp
      _ = r.reverse.length := congrArg List.length
        (Hypermap.map_sniprRing hplanar hr)
      _ = r.length := List.length_reverse
  have hbGrrNe : bGrr ≠ [] := by
    intro hb
    have hbzero : bGrr.length = 0 := by simp [hb]
    have hcpLen := (checkBasisProgram_spec hcheck).2.2
    have hcpSize := CProg.one_lt_ringSize_of_cubic hcp
    simp only [length_cpRing] at hcpLen
    omega
  obtain ⟨xrr, _hxrr⟩ := List.exists_mem_of_ne_nil bGrr hbGrrNe
  have hconnectedR : Grr.Connected :=
    Psnip.connected_remainder hconnected xrr
  have hcardBasis : Fintype.card Gr.Dart < Fintype.card Grr.Dart :=
    basisMap_card_lt_snipRemainder hplanar hr hrlen hnt
      hplainParts.2 hcubicParts.2 hconnectedR hcheck
  have hchordless : Gd.Chordless bGd := by
    apply Classical.byContradiction
    intro hnot
    rcases Hypermap.ringDiskChord hplanar hconnected hG.bridgeless
        hG.plain hr hnt hnot with
      ⟨r', hr', hnt', hlen'⟩
    exact hshort r' hr' (by omega) hnt'
  have hplanar2 : S.sewMap.EulerPlanar :=
    P2.eulerPlanar_iff.mpr
      ⟨Hypermap.snipDisk_eulerPlanar hplanar hr,
        cpmap_eulerPlanar_of_cubic hcp⟩
  have hplain2 : S.sewMap.Plain :=
    P2.plain_iff.mpr
      ⟨hplainParts.1, (cpmap_cubicGeometry_of_cubic hcp).plain⟩
  have hcubic2 : S.sewMap.Cubic :=
    P2.cubic_iff.mpr
      ⟨hcubicParts.1, cpmap_quasicubic_basisBoundary hcp⟩
  have hbridge2 : S.sewMap.Bridgeless :=
    P2.bridgeless_of_parts_of_chordless hbridgeParts.1
      (cpmap_bridgeless_of_cubic hcp) hchordless
  have hgeometry : S.sewMap.PlanarBridgelessPlainPrecubic :=
    { base :=
        { base := { planar := hplanar2, bridgeless := hbridge2 }
          plain := hplain2 }
      precubic := hcubic2.precubic }
  refine ⟨hgeometry, ?_⟩
  have hcard2 := P2.card_patch
  have hcardHost := Psnip.card_patch
  change Fintype.card Gd.Dart + Fintype.card Gr.Dart =
    bGd.length + Fintype.card S.sewMap.Dart at hcard2
  change Fintype.card Gd.Dart + Fintype.card Grr.Dart =
    bGd.length + Fintype.card G.Dart at hcardHost
  change Fintype.card S.sewMap.Dart < Fintype.card G.Dart
  omega

/-- Coq `chkbP`: a basis tree disjoint from `ctu` forces an even disk trace
outside `ctu`. -/
theorem basisTree_trace_obstruction
    {G : Hypermap.{u}} {r : List G.Dart} {h m : Nat} {cp : CProg}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1) (hnt : G.NontrivialRing m r)
    (hshort : ∀ r' : List G.Dart,
      G.SimpleRLinkCycle r' → r'.length ≤ h →
        ¬ G.NontrivialRing 0 r')
    (hcheck : checkBasisProgram h m cp = true)
    (ctu : CTree)
    (hdisjoint : CTree.disjoint ctu (CProg.cpColor cp) = true) :
    ∃ et : ColSeq,
      (G.snipDisk r hG.planar hr).RingTrace
          (Hypermap.snipdRing hG.planar hr) (ColSeq.ctrace et) ∧
        CTree.mem ctu (ColSeq.etrace et) = false := by
  let S := basisSewBoundary hG.planar hr hrlen hcheck
  have hgeometry := basisSewMap_geometry_card hG hconnected hcubic hr
    hrlen hnt hshort hcheck
  have hcolor : S.sewMap.FourColorable :=
    hG.colorable_of_smaller S.sewMap hgeometry.1 hgeometry.2
  rcases S.sewMapPatch.colorable_patch.mp hcolor with
    ⟨et0, htraceD, htraceR⟩
  have hcp := (checkBasisProgram_spec hcheck).1
  have het0Len := htraceD.length
  have hbDLen :
      (Hypermap.snipdRing hG.planar hr).length = r.length :=
    length_snipdRing hG.planar hr
  have het0Pos : 0 < et0.length := by
    have hcpSize := CProg.one_lt_ringSize_of_cubic hcp
    have hcpLen := (checkBasisProgram_spec hcheck).2.2
    simp only [length_cpRing] at hcpLen
    omega
  have het0Ne : et0 ≠ [] := List.length_pos_iff_ne_nil.mp het0Pos
  let et := et0.dropLast
  let e := et0.getLast het0Ne
  have hsplit : et ++ [e] = et0 :=
    List.dropLast_append_getLast het0Ne
  have hsumZero := Hypermap.RingTrace.sum_zero
    (G := G.snipDisk r hG.planar hr) htraceD
  have hsum : ColSeq.sum et = e := by
    rw [← hsplit, ColSeq.sum_append, ColSeq.sum_singleton] at hsumZero
    exact (Color.add_eq_zero_iff_eq _ _).mp hsumZero
  have htraceDisk :
      (G.snipDisk r hG.planar hr).RingTrace
        (Hypermap.snipdRing hG.planar hr) (ColSeq.ctrace et) := by
    have hctrace : ColSeq.ctrace et = et0 := by
      unfold ColSeq.ctrace
      rw [hsum, hsplit]
    rw [hctrace]
    exact htraceD
  have hcpRingNe : cpRing cp ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    simpa only [length_cpRing] using
      (show 0 < CProg.ringSize cp from
        Nat.zero_lt_of_lt (CProg.one_lt_ringSize_of_cubic hcp))
  have htraceLen : (et ++ [e]).length = (cpRing cp).length := by
    calc
      (et ++ [e]).length = et0.length := congrArg List.length hsplit
      _ = (Hypermap.snipdRing hG.planar hr).length := het0Len
      _ = (basisBoundary cp).length := S.length_eq
      _ = (cpRing cp).length := by simp
  have htraceR' :
      (cpmap cp).map.RingTrace (basisBoundary cp)
        (ColSeq.rot1 (et ++ [e]).reverse) := by
    change (cpmap cp).map.RingTrace (basisBoundary cp)
      (ColSeq.rot1 et0.reverse) at htraceR
    simpa only [hsplit] using htraceR
  have htraceBasis :
      (cpmap cp).map.RingTrace (cpRing cp) (e :: et) :=
    ringTrace_rotateRightOne_reverse_elim hcpRingNe htraceLen htraceR'
  let g := ColSeq.etracePerm et
  have htraceNormalized := Hypermap.RingTrace.perm
    (G := (cpmap cp).map) htraceBasis g
  have hnormalized :
      ColSeq.perm g (e :: et) =
        ColSeq.sum (ColSeq.etrace et) :: ColSeq.etrace et := by
    subst g
    simp only [ColSeq.perm, List.map_cons, ColSeq.etrace]
    congr 1
    calc
      ColSeq.etracePerm et e =
          ColSeq.etracePerm et (ColSeq.sum et) := congrArg _ hsum.symm
      _ = ColSeq.sum (ColSeq.perm (ColSeq.etracePerm et) et) :=
        (ColSeq.perm_sum (ColSeq.etracePerm et) et).symm
      _ = ColSeq.sum (List.map (ColSeq.etracePerm et).apply et) := rfl
  rw [hnormalized] at htraceNormalized
  have hmemBasis :
      CTree.mem (CProg.cpColor cp) (ColSeq.etrace et) = true :=
    ctree_mem_cpColor_of_cubic hcp (ColSeq.even_etrace et) htraceNormalized
  refine ⟨et, htraceDisk, ?_⟩
  exact CTree.mem_disjoint ctu (CProg.cpColor cp) (ColSeq.etrace et)
    hdisjoint hmemBasis

theorem ringTrace_ctrace_of_etrace
    {G : Hypermap.{u}} {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r (ColSeq.ctrace (ColSeq.etrace et))) :
    G.RingTrace r (ColSeq.ctrace et) := by
  have hp := Hypermap.RingTrace.perm (G := G) htrace
    (EdgePerm.inv (ColSeq.etracePerm et))
  have heq :
      ColSeq.perm (EdgePerm.inv (ColSeq.etracePerm et))
          (ColSeq.ctrace (ColSeq.etrace et)) =
        ColSeq.ctrace et := by
    rw [ColSeq.etrace, ← ColSeq.perm_ctrace, ColSeq.perm_inv]
  rwa [heq] at hp

theorem basisTree_trace_contradiction
    {G : Hypermap.{u}} {r : List G.Dart} {h m : Nat} {cp : CProg}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1) (hnt : G.NontrivialRing m r)
    (hshort : ∀ r' : List G.Dart,
      G.SimpleRLinkCycle r' → r'.length ≤ h →
        ¬ G.NontrivialRing 0 r')
    (hpos : 0 < h)
    (hcheck : checkBasisProgram h m cp = true)
    {ctu : CTree} {gtu : GTree}
    (hvalid : KempeTree.Valid (h - 1)
      (fun cet => ¬ (G.snipDisk r hG.planar hr).RingTrace
        (Hypermap.snipdRing hG.planar hr) cet)
      ctu CTree.empty GTree.empty gtu)
    (hclosed : Chromogram.KempeClosed
      ((G.snipDisk r hG.planar hr).RingTrace
        (Hypermap.snipdRing hG.planar hr)))
    (hdisjoint : CTree.disjoint ctu (CProg.cpColor cp) = true) :
    False := by
  rcases basisTree_trace_obstruction hG hconnected hcubic hr hrlen hnt
      hshort hcheck ctu hdisjoint with ⟨et, htrace, hmem⟩
  have htraceLen := Hypermap.RingTrace.length
    (G := G.snipDisk r hG.planar hr) htrace
  have hboundaryLen :
      (Hypermap.snipdRing hG.planar hr).length = r.length :=
    length_snipdRing hG.planar hr
  have hetLen : et.length = (h - 1) + 1 := by
    rw [ColSeq.length_ctrace, hboundaryLen, hrlen] at htraceLen
    omega
  have hcoclosure := KempeTree.valid_coclosure_of_ctu_etrace_nonmem
    hvalid hetLen hmem
  rcases hcoclosure _ hclosed htrace with ⟨cet, hnot, hyes⟩
  exact hnot hyes


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
