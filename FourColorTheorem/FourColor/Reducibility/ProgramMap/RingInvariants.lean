import FourColorTheorem.FourColor.Reducibility.ProgramMap.MaskSoundness

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem cpMaskAdjSound_rotate_of_cpRing
    {cp : CProg} {n : Nat} {m : CfMask}
    (hring :
      cpRing (CpStep.rotate n :: cp) =
        CProg.rotateLeft n (cpRing cp))
    (hsound :
      cpMaskAdjSound cp
        ⟨CProg.rotateRight n m.ring, m.kernel⟩)
    (hm : CfMask.Proper (CpStep.rotate n :: cp) m) :
    cpMaskAdjSound (CpStep.rotate n :: cp) m := by
  intro x
  let m₀ : CfMask := ⟨CProg.rotateRight n m.ring, m.kernel⟩
  have hm₀ : CfMask.Proper cp m₀ := by
    constructor
    · simpa [m₀, CfMask.Proper, CProg.ringSize,
        CProg.length_rotateRight] using hm.1
    · simpa [m₀, CfMask.Proper, CProg.kernelSize] using hm.2
  have hmAdj : CfMask.Proper cp (CfMask.adjMask m₀ cp) :=
    CfMask.cpadj_proper cp m₀ hm₀
  have hAdjMem :
      ∀ y : (cpmap cp).map.Dart,
        y ∈ cpMask (CfMask.adjMask m (CpStep.rotate n :: cp))
            (CpStep.rotate n :: cp) ↔
          y ∈ cpMask (CfMask.adjMask m₀ cp) cp := by
    intro y
    change
        y ∈ CfMask.selectMask
            ⟨CProg.rotateLeft n (CfMask.adjMask m₀ cp).ring,
              (CfMask.adjMask m₀ cp).kernel⟩
            (cpRing (CpStep.rotate n :: cp)) (cpKernel cp) ↔
          y ∈ CfMask.selectMask (CfMask.adjMask m₀ cp)
            (cpRing cp) (cpKernel cp)
    rw [hring]
    exact CfMask.mem_selectMask_rotateLeft_ring_iff_of_length
      (α := (cpmap cp).map.Dart) n
      (m := CfMask.adjMask m₀ cp)
      (ring := cpRing cp) (kernel := cpKernel cp)
      (x := y)
      (by rw [length_cpRing cp, hmAdj.1])
  have hOrigMem :
      ∀ y : (cpmap cp).map.Dart,
        y ∈ cpMask m (CpStep.rotate n :: cp) ↔
          y ∈ cpMask m₀ cp := by
    intro y
    change
        y ∈ CfMask.selectMask m
            (cpRing (CpStep.rotate n :: cp)) (cpKernel cp) ↔
          y ∈ CfMask.selectMask m₀ (cpRing cp) (cpKernel cp)
    rw [hring]
    exact
      (CfMask.mem_selectMask_rotateRight_ring_rotateLeft_values_iff_of_length
        (α := (cpmap cp).map.Dart) n
        (m := m) (ring := cpRing cp) (kernel := cpKernel cp)
        (x := y)
        (by
          rw [length_cpRing cp]
          simpa [CfMask.Proper, CProg.ringSize] using hm.1.symm)).symm
  have hFace :
      (cpmap cp).map.FaceBand
          (cpMask (CfMask.adjMask m (CpStep.rotate n :: cp))
            (CpStep.rotate n :: cp)) x ↔
        (cpmap cp).map.FaceBand
          (cpMask (CfMask.adjMask m₀ cp) cp) x :=
    Hypermap.FaceBand.congr_mem
      (G := (cpmap cp).map) (fun y => hAdjMem y)
  change
      (cpmap cp).map.FaceBand
          (cpMask (CfMask.adjMask m (CpStep.rotate n :: cp))
            (CpStep.rotate n :: cp)) x ↔
        ∃ y : (cpmap cp).map.Dart,
          y ∈ cpMask m (CpStep.rotate n :: cp) ∧
            (cpmap cp).map.RingAdj x y
  rw [hFace, hsound x]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, (hOrigMem y).2 hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, (hOrigMem y).1 hy, hxy⟩

theorem cpRing_rotate_of_ringCycle
    {cp : CProg} {n : Nat}
    (hcycle : RingCycle (cpmap cp) (CProg.ringSize cp)) :
    cpRing (CpStep.rotate n :: cp) =
      CProg.rotateLeft n (cpRing cp) := by
  change ringDarts ((cpmap cp).rotate n) (CProg.ringSize cp) =
    CProg.rotateLeft n (ringDarts (cpmap cp) (CProg.ringSize cp))
  exact rotate_ringDarts_eq_rotateLeft_of_ringCycle (cpmap cp) n
    (CProg.ringSize cp) hcycle

theorem cpMaskAdjSound_rotate_of_ringCycle
    {cp : CProg} {n : Nat} {m : CfMask}
    (hcycle : RingCycle (cpmap cp) (CProg.ringSize cp))
    (hsound :
      cpMaskAdjSound cp
        ⟨CProg.rotateRight n m.ring, m.kernel⟩)
    (hm : CfMask.Proper (CpStep.rotate n :: cp) m) :
    cpMaskAdjSound (CpStep.rotate n :: cp) m := by
  exact cpMaskAdjSound_rotate_of_cpRing
    (cpRing_rotate_of_ringCycle (cp := cp) (n := n) hcycle)
    hsound hm

/-- Constructor-induction invariant for semantic mask-adjacency: every proper
mask for a program has sound executable adjacency. -/
def cpMaskAdjSoundAllProper (cp : CProg) : Prop :=
  ∀ m : CfMask, CfMask.Proper cp m → cpMaskAdjSound cp m

theorem cpMaskAdjSoundAllProper_nil :
    cpMaskAdjSoundAllProper [] := by
  intro m hm
  exact cpMaskAdjSound_nil m hm

theorem cpMaskAdjSoundAllProper_rotate_of_ringCycle
    {cp : CProg} {n : Nat}
    (hcycle : RingCycle (cpmap cp) (CProg.ringSize cp))
    (htail : cpMaskAdjSoundAllProper cp) :
    cpMaskAdjSoundAllProper (CpStep.rotate n :: cp) := by
  intro m hm
  let m₀ : CfMask := ⟨CProg.rotateRight n m.ring, m.kernel⟩
  have hm₀ : CfMask.Proper cp m₀ := by
    constructor
    · simpa [m₀, CfMask.Proper, CProg.ringSize,
        CProg.length_rotateRight] using hm.1
    · simpa [m₀, CfMask.Proper, CProg.kernelSize] using hm.2
  exact cpMaskAdjSound_rotate_of_ringCycle hcycle (htail m₀ hm₀) hm

/-- Program-level ring-period invariant at the syntactic ring size. -/
def cpRingPeriod (cp : CProg) : Prop :=
  RingPeriod (cpmap cp) (CProg.ringSize cp)

theorem cpRingCycle.ringPeriod
    {cp : CProg}
    (h : cpRingCycle cp) :
    cpRingPeriod cp :=
  h.period

theorem cpRingPeriod_nil :
    cpRingPeriod [] := by
  rfl

theorem cpRingCycle_nil :
    cpRingCycle [] :=
  base_ringCycle

theorem cpRingPeriod_rotate
    {cp : CProg} {n : Nat}
    (h : cpRingPeriod cp) :
    cpRingPeriod (CpStep.rotate n :: cp) :=
  rotate_ringPeriod (r := n) h

private theorem cpRingCycle_iterate_node_symm_sub_two
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hsize : 1 < CProg.ringSize cp) :
    iteratePerm (cpmap cp).map.node.symm (CProg.ringSize cp - 2)
        (cpmap cp).point =
      (cpmap cp).map.node ((cpmap cp).map.node (cpmap cp).point) := by
  have hp := hcycle.period
  unfold RingPeriod at hp
  change iteratePerm (cpmap cp).map.node.symm (CProg.ringSize cp)
      ((cpmap cp).map.node (cpmap cp).point) =
    (cpmap cp).map.node (cpmap cp).point at hp
  have hn : CProg.ringSize cp = (CProg.ringSize cp - 1) + 1 := by omega
  rw [hn, iteratePerm_succ] at hp
  rw [(cpmap cp).map.node.symm_apply_apply] at hp
  have hn' : CProg.ringSize cp - 1 = (CProg.ringSize cp - 2) + 1 := by omega
  rw [hn', iteratePerm_succ_right] at hp
  exact (cpmap cp).map.node.injective (by
    simpa using congrArg (cpmap cp).map.node hp)

theorem cpRingPeriod_y_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hsize : 1 < CProg.ringSize cp) :
    cpRingPeriod (CpStep.y :: cp) := by
  let P := cpmap cp
  let n := CProg.ringSize cp
  have hlast :
      iteratePerm P.map.node.symm (n - 2) P.point =
        P.map.node (P.map.node P.point) :=
    cpRingCycle_iterate_node_symm_sub_two hcycle hsize
  have hprev :
      iteratePerm P.y.map.node.symm (n - 1) P.y.point =
        P.yOld (iteratePerm P.map.node.symm (n - 2) P.point) := by
    have hn : n - 1 = (n - 2) + 1 := by
      omega
    rw [hn]
    exact y_iterate_node_symm_succ_point_of_avoids_heads P hproper
      (n - 2)
      (fun k hk =>
        RingCycle.avoids_node_point_before_last hcycle (by omega))
      (fun k hk =>
        RingCycle.avoids_node_node_point_before_last hcycle (by omega))
  unfold cpRingPeriod RingPeriod
  change iteratePerm P.y.map.node.symm (n + 1)
      (P.y.map.node P.y.point) = P.y.map.node P.y.point
  rw [iteratePerm_succ]
  rw [P.y.map.node.symm_apply_apply]
  have hn : n = (n - 1) + 1 := by
    omega
  rw [hn, iteratePerm_succ_right]
  rw [hprev, hlast]
  exact yOld_node_symm_node_node_point P hproper

theorem cpRingCycle_y
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hsize : 1 < CProg.ringSize cp) :
    cpRingCycle (CpStep.y :: cp) where
  pos := by simp [CProg.ringSize]
  period := cpRingPeriod_y_of_ringCycle hcycle hproper hsize
  nodup := by
    let P := cpmap cp
    change (cpRing (CpStep.y :: cp)).Nodup
    rw [cpRing_y_eq_of_ringCycle hcycle hproper]
    have hcp : (cpRing cp).Nodup := by
      simpa [cpRing] using hcycle.nodup
    have htail : ((cpRing cp).drop 1).Nodup := hcp.drop
    simp only [List.nodup_cons, List.mem_cons, List.mem_map]
    constructor
    · rintro (h | ⟨x, _hx, hx⟩)
      · exact (y_properRingHead P) h.symm
      ·
        exact yOld_ne_node_point P x hx
    constructor
    · rintro ⟨x, _hx, hx⟩
      exact yOld_ne_point P x hx
    · exact htail.map (yOld_injective P)

theorem cpRingPeriod_h_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp) :
    cpRingPeriod (CpStep.h :: cp) := by
  let P := cpmap cp
  let n := CProg.ringSize cp
  have hlast :
      iteratePerm P.map.node.symm (n - 2) P.point =
        P.map.node (P.map.node P.point) :=
    cpRingCycle_iterate_node_symm_sub_two hcycle (by omega)
  have hprev :
      iteratePerm P.h.map.node.symm (n - 2) P.h.point =
        P.hOld (iteratePerm P.map.node.symm (n - 2) P.point) := by
    have hn : n - 2 = (n - 3) + 1 := by
      omega
    rw [hn]
    exact h_iterate_node_symm_succ_point_of_avoids_heads
      P hproper hlong (n - 3)
      (fun k hkpos hk =>
        RingCycle.avoids_point_before_last_of_pos hcycle hkpos
          (by omega))
      (fun k _hkpos hk =>
        RingCycle.avoids_node_point_before_last hcycle (by omega))
      (fun k _hkpos hk =>
        RingCycle.avoids_node_node_point_before_last hcycle (by omega))
  unfold cpRingPeriod RingPeriod
  change iteratePerm P.h.map.node.symm n
      (P.h.map.node P.h.point) = P.h.map.node P.h.point
  have hn : n = (n - 1) + 1 := by
    omega
  rw [hn, iteratePerm_succ]
  rw [P.h.map.node.symm_apply_apply]
  have hn' : n - 1 = (n - 2) + 1 := by
    omega
  rw [hn', iteratePerm_succ_right]
  rw [hprev, hlast]
  exact hOld_node_symm_node_node_point P hproper hlong

theorem cpRingCycle_h
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp) :
    cpRingCycle (CpStep.h :: cp) where
  pos := by simpa [CProg.ringSize] using hcycle.pos
  period := cpRingPeriod_h_of_ringCycle hcycle hproper hlong hsize
  nodup := by
    let P := cpmap cp
    change (cpRing (CpStep.h :: cp)).Nodup
    rw [cpRing_h_eq_of_ringCycle hcycle hproper hlong hsize]
    have hcp : (cpRing cp).Nodup := by
      simpa [cpRing] using hcycle.nodup
    have htail : ((cpRing cp).drop 2).Nodup := by
      exact hcp.drop
    simp only [List.nodup_cons, List.mem_cons, List.mem_map]
    constructor
    · rintro (h | ⟨x, _hx, hx⟩)
      · exact (h_properRingHead_of_proper P hproper) h.symm
      · exact hOld_ne_node_point P x hx
    constructor
    · rintro ⟨x, _hx, hx⟩
      exact hOld_ne_point P x hx
    · exact htail.map (hOld_injective P)

/-- The short branch of Coq `cpring_ecpH`: when the source ring has size
two, `H` again has the two-element ring headed by its fresh dart. -/
theorem cpRingCycle_h_of_ringSize_eq_two
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hsize : CProg.ringSize cp = 2) :
    cpRingCycle (CpStep.h :: cp) := by
  let P := cpmap cp
  have hyLong : P.y.LongRingHead := y_longRingHead_of_proper P hproper
  have hyCycle : RingCycle P.y 3 := by
    have h := cpRingCycle_y hcycle hproper (by omega)
    simpa [cpRingCycle, CProg.ringSize, hsize, P, cpmap_cons, step_y]
      using h
  have hyNodeThree :
      P.y.map.node (P.y.map.node (P.y.map.node P.y.point)) =
        P.y.point := by
    have hinv := RingPeriod.point_period hyCycle.period
    simp only [iteratePerm_succ, iteratePerm_zero] at hinv
    have h1 := congrArg P.y.map.node hinv
    simp only [P.y.map.node.apply_symm_apply] at h1
    have h2 := congrArg P.y.map.node h1
    simp only [P.y.map.node.apply_symm_apply] at h2
    have h3 := congrArg P.y.map.node h2
    simp only [P.y.map.node.apply_symm_apply] at h3
    exact h3.symm
  have htargetNodeTwo :
      P.h.map.node (P.h.map.node P.h.point) = P.h.point := by
    change P.y.n.map.node (P.y.n.map.node P.y.n.point) = P.y.n.point
    change (Hypermap.ExtensionN.node P.y.map P.y.point)
      ((Hypermap.ExtensionN.node P.y.map P.y.point) ExtDart.new) =
        ExtDart.new
    change P.y.map.LongRingHead P.y.point at hyLong
    rw [Hypermap.ExtensionN.node_new, if_pos hyLong]
    rw [Hypermap.ExtensionN.node_old]
    have hnewNe :
        (P.y.map.node P.y.point) ≠ P.y.point := by
      exact (y_properRingHead P) ∘ Eq.symm
    rw [if_neg hnewNe]
    rw [if_pos hyNodeThree]
  have htargetPeriod : cpRingPeriod (CpStep.h :: cp) := by
    have hp : RingPeriod P.h 2 := by
      have hsymm : P.h.map.node.symm P.h.point =
          P.h.map.node P.h.point := by
        calc
          P.h.map.node.symm P.h.point =
              P.h.map.node.symm
                (P.h.map.node (P.h.map.node P.h.point)) :=
            congrArg P.h.map.node.symm htargetNodeTwo.symm
          _ = P.h.map.node P.h.point :=
            P.h.map.node.symm_apply_apply (P.h.map.node P.h.point)
      change iteratePerm P.h.map.node.symm 2
        (P.h.map.node P.h.point) = P.h.map.node P.h.point
      simpa only [iteratePerm_succ, iteratePerm_zero,
        P.h.map.node.symm_apply_apply] using hsymm
    simpa [cpRingPeriod, CProg.ringSize, hsize, P, cpmap_cons, step_h]
      using hp
  refine ⟨by simp [CProg.ringSize, hsize], htargetPeriod, ?_⟩
  rw [show CProg.ringSize (CpStep.h :: cp) = 2 by
    simp [CProg.ringSize, hsize]]
  change (ringDarts P.h 2).Nodup
  rw [show ringDarts P.h 2 = [P.h.map.node P.h.point, P.h.point] by
    simpa using ringDarts_succ_succ P.h 0]
  have htargetProper := h_properRingHead_of_proper P hproper
  simpa [PointedHypermap.ProperRingHead, Hypermap.ProperRingHead, eq_comm]
    using htargetProper

theorem cpRingCycle_rotate
    {cp : CProg} {n : Nat}
    (h : cpRingCycle cp) :
    cpRingCycle (CpStep.rotate n :: cp) :=
  rotate_ringCycle (r := n) h

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
