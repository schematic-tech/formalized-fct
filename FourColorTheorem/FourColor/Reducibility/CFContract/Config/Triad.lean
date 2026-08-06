import FourColorTheorem.FourColor.Reducibility.CFContract.Config.Basic

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

/-- The four-edge branch of Coq `contract_ctreeP`: a successful executable
`cptriad` test supplies an actual triad in the edge closure of the selected
contract. -/
theorem contractFinset_hasTriad_of_card_four
    {cf : Config}
    (hcf : cf.WellFormed)
    (hmask : CfMask.validContractMask cf.contractMask cf.program = true)
    (hfour : cf.contractFinset.card = 4) :
    ∃ center : cf.map.map.Dart,
      cf.map.map.Kernel cf.reducibilityRingDarts center ∧
        cf.map.map.TriadFor
          (cf.map.map.contractClosure cf.contractFinset) center := by
  let band := CfMask.contractBand cf.contractMask cf.program
  have hbandProper : CfMask.Proper cf.program band := by
    simpa [band] using
      Config.contractBand_proper_of_program_config (cf := cf) hcf
  have hcount : CfMask.countTrue cf.contractMask = 4 := by
    rw [← card_contractFinset_of_wellFormed hcf]
    exact hfour
  rcases Config.exists_triadAtSources_count_gt_two_of_validMask_four
      hcf hmask hcount with
    ⟨i, hi, htriad, _hsources, _hbandCount⟩
  let singleton := CfMask.kernelSingleton cf.program i
  let target := CfMask.adjMask singleton cf.program
  let masks := band.ring ++ band.kernel
  let targets := target.ring ++ target.kernel
  let q := PointedHypermap.cpRing cf.program ++
    PointedHypermap.cpKernel cf.program
  let both := PointedHypermap.CFContract.Internal.selectBoth masks targets q
  have htargetProper : CfMask.Proper cf.program target := by
    simpa [target, singleton] using
      CfMask.cpadj_proper_kernelSingleton cf.program i
  have hmasksTargets : masks.length = targets.length := by
    simp only [masks, targets, List.length_append]
    rw [hbandProper.1, hbandProper.2,
      htargetProper.1, htargetProper.2]
  have hmasksQ : masks.length = q.length := by
    simp only [masks, q, List.length_append]
    rw [hbandProper.1, hbandProper.2,
      PointedHypermap.length_cpRing,
      PointedHypermap.length_cpKernel_of_config cf.program hcf]
  have hselectTargets :
      CfMask.select masks targets =
        CfMask.triadSelected band cf.program i := by
    change CfMask.select (band.ring ++ band.kernel)
        (target.ring ++ target.kernel) = _
    rw [CfMask.select_append_of_length band.ring band.kernel
      target.ring target.kernel]
    · rfl
    · rw [htargetProper.1, hbandProper.1]
  have hselectBand :
      CfMask.select masks q =
        PointedHypermap.cpMask band cf.program := by
    change CfMask.select (band.ring ++ band.kernel)
        (PointedHypermap.cpRing cf.program ++
          PointedHypermap.cpKernel cf.program) = _
    rw [CfMask.select_append_of_length band.ring band.kernel
      (PointedHypermap.cpRing cf.program)
      (PointedHypermap.cpKernel cf.program)]
    · rfl
    · rw [PointedHypermap.length_cpRing, hbandProper.1]
  have hselectTarget :
      CfMask.select targets q =
        PointedHypermap.cpMask target cf.program := by
    change CfMask.select (target.ring ++ target.kernel)
        (PointedHypermap.cpRing cf.program ++
          PointedHypermap.cpKernel cf.program) = _
    rw [CfMask.select_append_of_length target.ring target.kernel
      (PointedHypermap.cpRing cf.program)
      (PointedHypermap.cpKernel cf.program)]
    · rfl
    · rw [PointedHypermap.length_cpRing, htargetProper.1]
  have hsimple : (PointedHypermap.cpmap cf.program).map.FaceSimple q := by
    simpa [q, PointedHypermap.cpMapSimple] using
      PointedHypermap.cpMapSimple_of_config (cp := cf.program) hcf
  have hbothLength : both.length =
      CfMask.countTrue (CfMask.triadSelected band cf.program i) := by
    calc
      both.length = CfMask.countTrue (CfMask.select masks targets) :=
        PointedHypermap.CFContract.Internal.length_selectBoth_eq_countTrue_select
          masks targets q hmasksTargets hmasksQ
      _ = CfMask.countTrue (CfMask.triadSelected band cf.program i) := by
        rw [hselectTargets]
  have hbothGt : 2 < both.length := by
    rw [hbothLength]
    exact CfMask.triadAt_countTrue_gt_two htriad
  have hbothNodup : both.Nodup :=
    hsimple.nodup.sublist
      (PointedHypermap.CFContract.Internal.selectBoth_sublist masks targets q)
  rcases PointedHypermap.CFContract.Internal.exists_three_prefix_of_two_lt_length
      hbothGt with
    ⟨z0, z1, z2, rest, hboth⟩
  have hz0Both : z0 ∈ both := by rw [hboth]; exact List.Mem.head _
  have hz1Both : z1 ∈ both := by
    rw [hboth]
    exact List.Mem.tail z0 (List.Mem.head _)
  have hz2Both : z2 ∈ both := by
    rw [hboth]
    exact List.Mem.tail z0 (List.Mem.tail z1 (List.Mem.head _))
  have hbothMasks (z : (PointedHypermap.cpmap cf.program).map.Dart)
      (hz : z ∈ both) :
      z ∈ PointedHypermap.cpMask band cf.program ∧
        z ∈ PointedHypermap.cpMask target cf.program := by
    have h := PointedHypermap.CFContract.Internal.mem_selectBoth_masks
      hmasksTargets hmasksQ hz
    rwa [hselectBand, hselectTarget] at h
  have hz0Masks := hbothMasks z0 hz0Both
  have hz1Masks := hbothMasks z1 hz1Both
  have hz2Masks := hbothMasks z2 hz2Both
  have hq (z : (PointedHypermap.cpmap cf.program).map.Dart)
      (hz : z ∈ both) : z ∈ q :=
    List.Sublist.mem hz
      (PointedHypermap.CFContract.Internal.selectBoth_sublist masks targets q)
  have hz0q := hq z0 hz0Both
  have hz1q := hq z1 hz1Both
  have hz2q := hq z2 hz2Both
  have hnodupThree : (z0 :: z1 :: z2 :: rest).Nodup := by
    simpa [hboth] using hbothNodup
  have hz0ne1 : z0 ≠ z1 := by
    intro h
    apply (List.nodup_cons.mp hnodupThree).1
    simp [h]
  have hz0ne2 : z0 ≠ z2 := by
    intro h
    apply (List.nodup_cons.mp hnodupThree).1
    simp [h]
  have hz1ne2 : z1 ≠ z2 := by
    intro h
    apply (List.nodup_cons.mp (List.nodup_cons.mp hnodupThree).2).1
    simp [h]
  let center := (PointedHypermap.cpKernel cf.program).get
    ⟨i, by
      rw [PointedHypermap.length_cpKernel_of_config cf.program hcf]
      exact hi⟩
  have hsingleton :
      PointedHypermap.cpMask singleton cf.program = [center] := by
    simpa [singleton, center] using
      PointedHypermap.cpMask_cfmask1_eq_singleton_of_config
        (cp := cf.program) (i := i) hcf hi
  have hadj : PointedHypermap.cpMaskAdjSound cf.program singleton :=
    PointedHypermap.cpMaskAdjSound_of_config hcf
      (CfMask.proper_kernelSingleton cf.program i)
  have hbandCorrect :
      PointedHypermap.ContractBandCorrect cf.contractMask cf.program :=
    PointedHypermap.contractBand_correct cf.length_contractMask hcf
  have hplain : (PointedHypermap.cpmap cf.program).map.Plain :=
    (PointedHypermap.cpmap_configGeometry_of_config hcf).plain
  have liftBand
      (z : (PointedHypermap.cpmap cf.program).map.Dart)
      (hzBand : z ∈ PointedHypermap.cpMask band cf.program) :
      ∃ a : (PointedHypermap.cpmap cf.program).map.Dart,
        a ∈ (PointedHypermap.cpmap cf.program).map.contractClosure
          cf.contractFinset ∧
        PermReachable (PointedHypermap.cpmap cf.program).map.face a z := by
    have hzFace : (PointedHypermap.cpmap cf.program).map.FaceBand
        (PointedHypermap.cpMask band cf.program) z :=
      Hypermap.FaceBand.of_mem
        (G := (PointedHypermap.cpmap cf.program).map) hzBand
        (PermReachable.refl (PointedHypermap.cpmap cf.program).map.face z)
    have hzInserted := (hbandCorrect z).2 hzFace
    rcases hzInserted with ⟨a, ha, haz⟩
    refine ⟨a, ?_, haz⟩
    have ha' :=
      (Hypermap.mem_contractClosure_toFinset_iff_insertEdges
        (PointedHypermap.cpmap cf.program).map cf.contractDarts a).2
        (by simpa [Config.contractDarts] using ha)
    simpa [Config.contractFinset] using ha'
  have liftSelected
      (z : (PointedHypermap.cpmap cf.program).map.Dart)
      (hzBand : z ∈ PointedHypermap.cpMask band cf.program)
      (hzTarget : z ∈ PointedHypermap.cpMask target cf.program) :
      ∃ a : (PointedHypermap.cpmap cf.program).map.Dart,
        a ∈ (PointedHypermap.cpmap cf.program).map.contractClosure
          cf.contractFinset ∧
        PermReachable (PointedHypermap.cpmap cf.program).map.face a z ∧
        (PointedHypermap.cpmap cf.program).map.RingAdj center a := by
    rcases liftBand z hzBand with ⟨a, ha, haz⟩
    have hzFace : (PointedHypermap.cpmap cf.program).map.FaceBand
        (PointedHypermap.cpMask target cf.program) z :=
      Hypermap.FaceBand.of_mem
        (G := (PointedHypermap.cpmap cf.program).map) hzTarget
        (PermReachable.refl (PointedHypermap.cpmap cf.program).map.face z)
    rcases (hadj z).1 hzFace with ⟨y, hy, hzy⟩
    have hyc : y = center := by
      rw [hsingleton] at hy
      exact List.mem_singleton.mp hy
    subst y
    have hcz := Hypermap.RingAdj.symm_of_plain
      (G := (PointedHypermap.cpmap cf.program).map) hplain hzy
    exact ⟨a, ha, haz,
      Hypermap.RingAdj.of_faceReachable_right
        (G := (PointedHypermap.cpmap cf.program).map) hcz
        (PermReachable.symm (PointedHypermap.cpmap cf.program).map.face haz)⟩
  rcases liftSelected z0 hz0Masks.1 hz0Masks.2 with
    ⟨a0, ha0, ha0z, hca0⟩
  rcases liftSelected z1 hz1Masks.1 hz1Masks.2 with
    ⟨a1, ha1, ha1z, hca1⟩
  rcases liftSelected z2 hz2Masks.1 hz2Masks.2 with
    ⟨a2, ha2, ha2z, hca2⟩
  have lifted_ne
      {z w a b : (PointedHypermap.cpmap cf.program).map.Dart}
      (hzq : z ∈ q) (hwq : w ∈ q) (hzw : z ≠ w)
      (haz : PermReachable (PointedHypermap.cpmap cf.program).map.face a z)
      (hbw : PermReachable (PointedHypermap.cpmap cf.program).map.face b w) :
      ¬ PermReachable (PointedHypermap.cpmap cf.program).map.face a b := by
    intro hab
    apply hzw
    exact Hypermap.FaceSimple.eq_of_faceReachable_of_mem
      (G := (PointedHypermap.cpmap cf.program).map) hsimple hzq hwq
      (PermReachable.trans (PointedHypermap.cpmap cf.program).map.face
        (PermReachable.symm (PointedHypermap.cpmap cf.program).map.face haz)
        (PermReachable.trans (PointedHypermap.cpmap cf.program).map.face
          hab hbw))
  have ha0ne1 : ¬ PermReachable
      (PointedHypermap.cpmap cf.program).map.face a0 a1 :=
    lifted_ne hz0q hz1q hz0ne1 ha0z ha1z
  have ha0ne2 : ¬ PermReachable
      (PointedHypermap.cpmap cf.program).map.face a0 a2 :=
    lifted_ne hz0q hz2q hz0ne2 ha0z ha2z
  have ha1ne2 : ¬ PermReachable
      (PointedHypermap.cpmap cf.program).map.face a1 a2 :=
    lifted_ne hz1q hz2q hz1ne2 ha1z ha2z
  have hfalse : false ∈ CfMask.select masks targets := by
    rw [hselectTargets]
    exact CfMask.triadAt_exists_false htriad
  rcases PointedHypermap.CFContract.Internal.exists_mem_select_not_mem_of_false_mem
      hmasksTargets hmasksQ hsimple.nodup hfalse with
    ⟨z3, hz3BandCombined, hz3TargetCombined⟩
  have hz3Band : z3 ∈ PointedHypermap.cpMask band cf.program := by
    rwa [hselectBand] at hz3BandCombined
  have hz3Target : z3 ∉ PointedHypermap.cpMask target cf.program := by
    rwa [hselectTarget] at hz3TargetCombined
  have hz3q : z3 ∈ q :=
    CfMask.mem_of_mem_select hz3BandCombined
  have hz3NotFace : ¬ (PointedHypermap.cpmap cf.program).map.FaceBand
      (PointedHypermap.cpMask target cf.program) z3 := by
    rintro ⟨w, hwTarget, hwz⟩
    have hwq : w ∈ q := by
      have hwCombined : w ∈ CfMask.select targets q := by
        rwa [hselectTarget]
      exact CfMask.mem_of_mem_select hwCombined
    have hwEq : w = z3 :=
      Hypermap.FaceSimple.eq_of_faceReachable_of_mem
        (G := (PointedHypermap.cpmap cf.program).map) hsimple hwq hz3q hwz
    subst w
    exact hz3Target hwTarget
  rcases liftBand z3 hz3Band with ⟨a3, ha3, ha3z⟩
  have hca3 : ¬ (PointedHypermap.cpmap cf.program).map.RingAdj center a3 := by
    intro h
    have hcz := Hypermap.RingAdj.of_faceReachable_right
      (G := (PointedHypermap.cpmap cf.program).map) h ha3z
    have hzc := Hypermap.RingAdj.symm_of_plain
      (G := (PointedHypermap.cpmap cf.program).map) hplain hcz
    apply hz3NotFace
    apply (hadj z3).2
    exact ⟨center, by simp [hsingleton], hzc⟩
  have hcenterKernelList :
      center ∈ PointedHypermap.cpKernel cf.program := by
    dsimp [center]
    exact List.get_mem _ _
  have hcenterKernel :
      cf.map.map.Kernel cf.reducibilityRingDarts center := by
    intro hcenterBand
    rcases hcenterBand with ⟨y, hyRing, hyCenter⟩
    have hyCpRing : y ∈ PointedHypermap.cpRing cf.program := by
      simpa [Config.reducibilityRingDarts, Config.ringDarts] using hyRing
    have hyQ : y ∈ q :=
      List.mem_append_left _ hyCpRing
    have hcenterQ : center ∈ q :=
      List.mem_append_right _ hcenterKernelList
    have hyEq : y = center :=
      Hypermap.FaceSimple.eq_of_faceReachable_of_mem
        (G := (PointedHypermap.cpmap cf.program).map)
        hsimple hyQ hcenterQ hyCenter
    have hdisjoint := (List.nodup_append.mp hsimple.nodup).2.2
    exact hdisjoint y hyCpRing center hcenterKernelList hyEq
  refine ⟨center, hcenterKernel, ?_, a3, ha3, hca3⟩
  exact ⟨a0, ha0, a1, ha1, a2, ha2,
    ha0ne1, ha0ne2, ha1ne2, hca0, hca1, hca2⟩

theorem validContract_of_contractProgram
    {cf : Config} {cpc : CProg}
    (hcf : cf.WellFormed)
    (hrun : CProg.contractProgram cf.initialRingMask cf.contractMask cf.program =
      some cpc)
    (hmask : CfMask.validContractMask cf.contractMask cf.program = true) :
    cf.map.map.ValidContract cf.reducibilityRingDarts cf.contractFinset where
  offRing := by
    intro x hx
    exact contractOffRing_of_wellFormed hcf (List.mem_reverse.mp hx)
  sparse := contractFinset_sparse_of_contractProgram hrun
  size_pos := contractFinset_card_pos_of_validMask hcf hmask
  size_le_four := contractFinset_card_le_four_of_validMask hcf hmask
  triad_of_card_four := contractFinset_hasTriad_of_card_four hcf hmask

end Config

end FourColor

end Schematic.Math.GraphTheory
