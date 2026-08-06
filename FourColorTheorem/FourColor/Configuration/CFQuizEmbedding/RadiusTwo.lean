import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.QuizRecursion

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- The second adjacency-expansion kernel mask tested at a candidate center
by `cpradius2`. -/
def radiusTwoFirstMask (cp : CProg) (i : Nat) : CfMask :=
  CfMask.adjMask (CfMask.cfmask1 cp i) cp

def radiusTwoInputMask (cp : CProg) (i : Nat) : CfMask :=
  ⟨(CfMask.cfmask1 cp i).ring, (radiusTwoFirstMask cp i).kernel⟩

def radiusTwoSecondMask (cp : CProg) (i : Nat) : CfMask :=
  CfMask.adjMask (radiusTwoInputMask cp i) cp

def radiusTwoKernelMask (cp : CProg) (i : Nat) : List Bool :=
  (radiusTwoSecondMask cp i).kernel

/-- A syntax-level witness that the kernel entry `i` covers every kernel entry
after two adjacency-mask propagations. -/
def RadiusTwoMaskWitness (cp : CProg) (i : Nat) : Prop :=
  allTrue (radiusTwoKernelMask cp i) = true

theorem proper_radiusTwoFirstMask (cp : CProg) (i : Nat) :
    CfMask.Proper cp (radiusTwoFirstMask cp i) :=
  CfMask.cpadj_proper cp (CfMask.cfmask1 cp i)
    (CfMask.proper_cpmask1 cp i)

theorem proper_radiusTwoInputMask (cp : CProg) (i : Nat) :
    CfMask.Proper cp (radiusTwoInputMask cp i) := by
  constructor
  · exact (CfMask.proper_cpmask1 cp i).1
  · exact (proper_radiusTwoFirstMask cp i).2

theorem proper_radiusTwoSecondMask (cp : CProg) (i : Nat) :
    CfMask.Proper cp (radiusTwoSecondMask cp i) :=
  CfMask.cpadj_proper cp (radiusTwoInputMask cp i)
    (proper_radiusTwoInputMask cp i)

theorem radiusTwoKernelMask_length (cp : CProg) (i : Nat) :
    (radiusTwoKernelMask cp i).length = CProg.kernelSize cp := by
  simpa [radiusTwoKernelMask] using
    (proper_radiusTwoSecondMask cp i).2

theorem RadiusTwoMaskWitness.eq_true_of_mem
    {cp : CProg} {i : Nat} {b : Bool}
    (hw : RadiusTwoMaskWitness cp i)
    (hb : b ∈ radiusTwoKernelMask cp i) :
    b = true :=
  eq_true_of_mem_allTrue hw hb

theorem RadiusTwoMaskWitness.get_eq_true
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (k : Fin (radiusTwoKernelMask cp i).length) :
    (radiusTwoKernelMask cp i).get k = true :=
  hw.eq_true_of_mem (List.get_mem (radiusTwoKernelMask cp i) k)

theorem RadiusTwoMaskWitness.get_eq_true_of_kernel_lt
    {cp : CProg} {i k : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hk : k < CProg.kernelSize cp) :
    (radiusTwoKernelMask cp i).get
        ⟨k, by simpa [radiusTwoKernelMask_length] using hk⟩ = true :=
  hw.get_eq_true
    ⟨k, by simpa [radiusTwoKernelMask_length] using hk⟩

theorem RadiusTwoMaskWitness.false_not_mem
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i) :
    false ∉ radiusTwoKernelMask cp i :=
  false_not_mem_of_allTrue hw

theorem RadiusTwoMaskWitness.countTrue_eq_kernelSize
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i) :
    CfMask.countTrue (radiusTwoKernelMask cp i) =
      CProg.kernelSize cp := by
  rw [countTrue_eq_length_of_allTrue hw,
    radiusTwoKernelMask_length]

theorem RadiusTwoMaskWitness.select_eq_self_of_length
    {α : Type _} {cp : CProg} {i : Nat} {xs : List α}
    (hw : RadiusTwoMaskWitness cp i)
    (hlen : xs.length = CProg.kernelSize cp) :
    CfMask.select (radiusTwoKernelMask cp i) xs = xs :=
  CfMask.select_eq_self_of_all_true
    (radiusTwoKernelMask cp i) xs
    (by rw [hlen, radiusTwoKernelMask_length])
    ((allTrue_eq_true_iff).1 hw)

theorem RadiusTwoMaskWitness.select_cpKernel_eq_self_of_config
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true) :
    CfMask.select (radiusTwoKernelMask cp i)
      (PointedHypermap.cpKernel cp) =
        PointedHypermap.cpKernel cp :=
  hw.select_eq_self_of_length
    (PointedHypermap.length_cpKernel_of_config cp hcfg)

theorem RadiusTwoMaskWitness.mem_cpMask_radiusTwoSecondMask_of_mem_kernel
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpKernel cp) :
    x ∈ PointedHypermap.cpMask (radiusTwoSecondMask cp i) cp := by
  unfold PointedHypermap.cpMask CfMask.cpmask CfMask.selectMask
  apply List.mem_append_right
  change x ∈ CfMask.select (radiusTwoKernelMask cp i)
    (PointedHypermap.cpKernel cp)
  rw [hw.select_cpKernel_eq_self_of_config hcfg]
  exact hx

theorem RadiusTwoMaskWitness.faceBand_radiusTwoSecondMask_of_kernel
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpKernel cp) :
    (PointedHypermap.cpmap cp).map.FaceBand
      (PointedHypermap.cpMask (radiusTwoSecondMask cp i) cp) x :=
  Hypermap.FaceBand.of_mem
    (G := (PointedHypermap.cpmap cp).map)
    (hw.mem_cpMask_radiusTwoSecondMask_of_mem_kernel hcfg hx)
    (PermReachable.refl (PointedHypermap.cpmap cp).map.face x)

theorem RadiusTwoMaskWitness.exists_input_ringAdj_of_kernel
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    (hsound : PointedHypermap.cpMaskAdjSound cp (radiusTwoInputMask cp i))
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpKernel cp) :
    ∃ y : (PointedHypermap.cpmap cp).map.Dart,
      y ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp ∧
        (PointedHypermap.cpmap cp).map.RingAdj x y :=
  (hsound x).1 (hw.faceBand_radiusTwoSecondMask_of_kernel hcfg hx)

theorem mem_cpMask_radiusTwoFirstMask_of_mem_radiusTwoInputMask
    {cp : CProg} {i : Nat}
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp) :
    x ∈ PointedHypermap.cpMask (radiusTwoFirstMask cp i) cp := by
  unfold PointedHypermap.cpMask CfMask.cpmask CfMask.selectMask at hx ⊢
  have hring :
      CfMask.select (CfMask.cfmask1 cp i).ring
        (PointedHypermap.cpRing cp) = [] :=
    CfMask.selectMask_ring_of_kernelSingleton cp i
      (PointedHypermap.cpRing cp)
  rw [radiusTwoInputMask, hring, List.nil_append] at hx
  exact List.mem_append_right
    (CfMask.select (radiusTwoFirstMask cp i).ring
      (PointedHypermap.cpRing cp)) hx

theorem mem_cpKernel_of_mem_radiusTwoInputMask
    {cp : CProg} {i : Nat}
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp) :
    x ∈ PointedHypermap.cpKernel cp := by
  unfold PointedHypermap.cpMask CfMask.cpmask CfMask.selectMask at hx
  have hring :
      CfMask.select (CfMask.cfmask1 cp i).ring
        (PointedHypermap.cpRing cp) = [] :=
    CfMask.selectMask_ring_of_kernelSingleton cp i
      (PointedHypermap.cpRing cp)
  rw [radiusTwoInputMask, hring, List.nil_append] at hx
  exact CfMask.mem_of_mem_select hx

theorem faceBand_radiusTwoFirstMask_of_mem_radiusTwoInputMask
    {cp : CProg} {i : Nat}
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp) :
    (PointedHypermap.cpmap cp).map.FaceBand
      (PointedHypermap.cpMask (radiusTwoFirstMask cp i) cp) x :=
  Hypermap.FaceBand.of_mem
    (G := (PointedHypermap.cpmap cp).map)
    (mem_cpMask_radiusTwoFirstMask_of_mem_radiusTwoInputMask hx)
    (PermReachable.refl (PointedHypermap.cpmap cp).map.face x)

theorem exists_center_ringAdj_of_mem_radiusTwoInputMask
    {cp : CProg} {i : Nat}
    (hsound : PointedHypermap.cpMaskAdjSound cp (CfMask.cfmask1 cp i))
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp) :
    ∃ y : (PointedHypermap.cpmap cp).map.Dart,
      y ∈ PointedHypermap.cpMask (CfMask.cfmask1 cp i) cp ∧
        (PointedHypermap.cpmap cp).map.RingAdj x y :=
  (hsound x).1 (faceBand_radiusTwoFirstMask_of_mem_radiusTwoInputMask hx)

theorem ringAdj_kernelCenter_of_mem_radiusTwoInputMask
    {cp : CProg} {i : Nat}
    (hcfg : CProg.config cp = true)
    (hi : i < CProg.kernelSize cp)
    (hsound : PointedHypermap.cpMaskAdjSound cp (CfMask.cfmask1 cp i))
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp) :
    (PointedHypermap.cpmap cp).map.RingAdj x
      ((PointedHypermap.cpKernel cp).get
        ⟨i, by
          rw [PointedHypermap.length_cpKernel_of_config cp hcfg]
          exact hi⟩) := by
  rcases exists_center_ringAdj_of_mem_radiusTwoInputMask
      (cp := cp) (i := i) hsound hx with
    ⟨y, hy, hxy⟩
  have hsingleton :=
    PointedHypermap.cpMask_cfmask1_eq_singleton_of_config
      (cp := cp) (i := i) hcfg hi
  rw [hsingleton] at hy
  simp only [List.mem_singleton] at hy
  subst y
  exact hxy

theorem RadiusTwoMaskWitness.exists_twoStepRingAdj_of_kernel
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    (hi : i < CProg.kernelSize cp)
    (hsound0 : PointedHypermap.cpMaskAdjSound cp (CfMask.cfmask1 cp i))
    (hsound1 : PointedHypermap.cpMaskAdjSound cp (radiusTwoInputMask cp i))
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpKernel cp) :
    ∃ y : (PointedHypermap.cpmap cp).map.Dart,
      y ∈ PointedHypermap.cpMask (radiusTwoInputMask cp i) cp ∧
        (PointedHypermap.cpmap cp).map.RingAdj x y ∧
          (PointedHypermap.cpmap cp).map.RingAdj y
            ((PointedHypermap.cpKernel cp).get
              ⟨i, by
                rw [PointedHypermap.length_cpKernel_of_config cp hcfg]
                exact hi⟩) := by
  rcases hw.exists_input_ringAdj_of_kernel hcfg hsound1 hx with
    ⟨y, hy, hxy⟩
  exact
    ⟨y, hy, hxy,
      ringAdj_kernelCenter_of_mem_radiusTwoInputMask
        (cp := cp) (i := i) hcfg hi hsound0 hy⟩

theorem RadiusTwoMaskWitness.atRadiusTwo_kernelCenter_of_kernel
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    (hi : i < CProg.kernelSize cp)
    (hPlain : (PointedHypermap.cpmap cp).map.Plain)
    (hsound0 : PointedHypermap.cpMaskAdjSound cp (CfMask.cfmask1 cp i))
    (hsound1 : PointedHypermap.cpMaskAdjSound cp (radiusTwoInputMask cp i))
    {x : (PointedHypermap.cpmap cp).map.Dart}
    (hx : x ∈ PointedHypermap.cpKernel cp) :
    (PointedHypermap.cpmap cp).map.AtRadiusTwo
      ((PointedHypermap.cpmap cp).map.FaceBand
        (PointedHypermap.cpKernel cp))
      ((PointedHypermap.cpKernel cp).get
        ⟨i, by
          rw [PointedHypermap.length_cpKernel_of_config cp hcfg]
          exact hi⟩)
      x := by
  rcases hw.exists_twoStepRingAdj_of_kernel
      hcfg hi hsound0 hsound1 hx with
    ⟨y, hyInput, hxy, hyc⟩
  have hyKernel : y ∈ PointedHypermap.cpKernel cp :=
    mem_cpKernel_of_mem_radiusTwoInputMask hyInput
  have hyBand :
      (PointedHypermap.cpmap cp).map.FaceBand
        (PointedHypermap.cpKernel cp) y :=
    Hypermap.FaceBand.of_mem
      (G := (PointedHypermap.cpmap cp).map)
      hyKernel
      (PermReachable.refl (PointedHypermap.cpmap cp).map.face y)
  exact
    Hypermap.AtRadiusTwo.of_ringAdj_chain
      (G := (PointedHypermap.cpmap cp).map)
      (A := (PointedHypermap.cpmap cp).map.FaceBand
        (PointedHypermap.cpKernel cp))
      hPlain
      (by
        intro u v hA hface
        exact
          Hypermap.FaceBand.of_faceReachable
            (G := (PointedHypermap.cpmap cp).map) hA hface)
      hyBand hxy hyc

theorem RadiusTwoMaskWitness.radiusTwo_kernelFaceBand
    {cp : CProg} {i : Nat}
    (hw : RadiusTwoMaskWitness cp i)
    (hcfg : CProg.config cp = true)
    (hi : i < CProg.kernelSize cp)
    (hPlain : (PointedHypermap.cpmap cp).map.Plain)
    (hsound0 : PointedHypermap.cpMaskAdjSound cp (CfMask.cfmask1 cp i))
    (hsound1 : PointedHypermap.cpMaskAdjSound cp (radiusTwoInputMask cp i)) :
    (PointedHypermap.cpmap cp).map.RadiusTwo
      ((PointedHypermap.cpmap cp).map.FaceBand
        (PointedHypermap.cpKernel cp)) := by
  let center : (PointedHypermap.cpmap cp).map.Dart :=
    (PointedHypermap.cpKernel cp).get
      ⟨i, by
        rw [PointedHypermap.length_cpKernel_of_config cp hcfg]
        exact hi⟩
  refine ⟨center, ?_, ?_⟩
  · exact
      Hypermap.FaceBand.of_mem
        (G := (PointedHypermap.cpmap cp).map)
        (List.get_mem (PointedHypermap.cpKernel cp)
          ⟨i, by
            rw [PointedHypermap.length_cpKernel_of_config cp hcfg]
            exact hi⟩)
        (PermReachable.refl (PointedHypermap.cpmap cp).map.face center)
  · intro x hxBand
    rcases hxBand with ⟨x0, hx0Kernel, hx0x⟩
    have hcenterx0 :
        (PointedHypermap.cpmap cp).map.AtRadiusTwo
          ((PointedHypermap.cpmap cp).map.FaceBand
            (PointedHypermap.cpKernel cp))
          center x0 :=
      hw.atRadiusTwo_kernelCenter_of_kernel
        hcfg hi hPlain hsound0 hsound1 hx0Kernel
    exact
      Hypermap.AtRadiusTwo.of_faceReachable_right
        (G := (PointedHypermap.cpmap cp).map)
        hcenterx0 hx0x

theorem cpradius2_eq_true_iff_exists_witness
    (cp : CProg) :
    ∀ n : Nat,
      cpradius2 cp n = true ↔
        ∃ i : Nat, i < n ∧ RadiusTwoMaskWitness cp i
  | 0 => by
      simp [cpradius2]
  | n + 1 => by
      constructor
      · intro h
        by_cases hlast : RadiusTwoMaskWitness cp n
        · exact ⟨n, Nat.lt_succ_self n, hlast⟩
        · have hlast_false :
              allTrue (radiusTwoKernelMask cp n) = false := by
            cases hmask : allTrue (radiusTwoKernelMask cp n) <;>
              simp [RadiusTwoMaskWitness, hmask] at hlast ⊢
          have hrec : cpradius2 cp n = true := by
            have hsplit :
                allTrue (radiusTwoKernelMask cp n) = true ∨
                  cpradius2 cp n = true := by
              simpa [cpradius2, radiusTwoKernelMask] using h
            rcases hsplit with hmask | hrec
            · rw [hlast_false] at hmask
              cases hmask
            · exact hrec
          rcases (cpradius2_eq_true_iff_exists_witness cp n).1 hrec with
            ⟨i, hi, hw⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hw⟩
      · rintro ⟨i, hi, hw⟩
        by_cases hin : i < n
        · have hrec : cpradius2 cp n = true :=
            (cpradius2_eq_true_iff_exists_witness cp n).2 ⟨i, hin, hw⟩
          by_cases hlast : allTrue (radiusTwoKernelMask cp n) = true
          · have hsplit :
                allTrue (radiusTwoKernelMask cp n) = true ∨
                  cpradius2 cp n = true :=
              Or.inl hlast
            simpa [cpradius2, radiusTwoKernelMask] using hsplit
          · have hlast_false :
                allTrue (radiusTwoKernelMask cp n) = false := by
              cases hmask : allTrue (radiusTwoKernelMask cp n) <;>
                simp [hmask] at hlast ⊢
            have hsplit :
                allTrue (radiusTwoKernelMask cp n) = true ∨
                  cpradius2 cp n = true :=
              Or.inr hrec
            simpa [cpradius2, radiusTwoKernelMask] using hsplit
        · have hieq : i = n := by omega
          subst hieq
          have hsplit :
              allTrue (radiusTwoKernelMask cp i) = true ∨
                cpradius2 cp i = true :=
            Or.inl hw
          simpa [cpradius2, radiusTwoKernelMask,
            RadiusTwoMaskWitness] using hsplit

theorem exists_witness_of_cpradius2_eq_true
    {cp : CProg} {n : Nat}
    (h : cpradius2 cp n = true) :
    ∃ i : Nat, i < n ∧ RadiusTwoMaskWitness cp i :=
  (cpradius2_eq_true_iff_exists_witness cp n).1 h

theorem cpradius2_eq_true_of_exists_witness
    {cp : CProg} {n : Nat}
    (h : ∃ i : Nat, i < n ∧ RadiusTwoMaskWitness cp i) :
    cpradius2 cp n = true :=
  (cpradius2_eq_true_iff_exists_witness cp n).2 h

theorem radiusTwo_kernelFaceBand_of_cpradius2_eq_true
    {cp : CProg}
    (hcfg : CProg.config cp = true)
    (hradius : cpradius2 cp (CProg.kernelSize cp) = true)
    (hsound :
      ∀ m : CfMask, CfMask.Proper cp m →
        PointedHypermap.cpMaskAdjSound cp m) :
    (PointedHypermap.cpmap cp).map.RadiusTwo
      ((PointedHypermap.cpmap cp).map.FaceBand
        (PointedHypermap.cpKernel cp)) := by
  rcases exists_witness_of_cpradius2_eq_true hradius with
    ⟨i, hi, hw⟩
  exact
    hw.radiusTwo_kernelFaceBand
      hcfg hi
      (PointedHypermap.cpmap_configGeometry_of_config hcfg).plain
      (hsound (CfMask.cfmask1 cp i) (CfMask.proper_cpmask1 cp i))
      (hsound (radiusTwoInputMask cp i) (proper_radiusTwoInputMask cp i))

theorem config_radiusTwo_kernelSet_of_cpradius2_eq_true
    {cf : Config}
    (hcf : cf.WellFormed)
    (hradius : cpradius2 cf.program (CProg.kernelSize cf.program) = true)
    (hsound :
      ∀ m : CfMask, CfMask.Proper cf.program m →
        PointedHypermap.cpMaskAdjSound cf.program m) :
    cf.map.map.RadiusTwo cf.kernelSet := by
  simpa [Config.map, Config.kernelSet, Config.kernelDarts] using
    radiusTwo_kernelFaceBand_of_cpradius2_eq_true
      (cp := cf.program) hcf hradius hsound

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
