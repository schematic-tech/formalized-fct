import FourColorTheorem.FourColor.Reducibility.ProgramMap.RingInvariants

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

/-- Combined constructor invariant for the executable mask-adjacency proof. -/
structure cpMaskAdjInvariant (cp : CProg) : Prop where
  ringCycle : cpRingCycle cp
  maskAdj : cpMaskAdjSoundAllProper cp

theorem cpMaskAdjInvariant.ringPeriod
    {cp : CProg}
    (h : cpMaskAdjInvariant cp) :
    cpRingPeriod cp :=
  h.ringCycle.ringPeriod

theorem cpMaskAdjInvariant_nil :
    cpMaskAdjInvariant [] where
  ringCycle := cpRingCycle_nil
  maskAdj := cpMaskAdjSoundAllProper_nil

theorem cpMaskAdjInvariant_rotate
    {cp : CProg} {n : Nat}
    (h : cpMaskAdjInvariant cp) :
    cpMaskAdjInvariant (CpStep.rotate n :: cp) where
  ringCycle := cpRingCycle_rotate h.ringCycle
  maskAdj :=
    cpMaskAdjSoundAllProper_rotate_of_ringCycle h.ringCycle h.maskAdj

theorem cpMaskAdjSound_yOld_of_cpMaskAdjInvariant
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hsize : 1 < CProg.ringSize cp)
    {b0 b1 b2 : Bool} {mr ks : List Bool}
    {a0 a2 : Bool} {mr' ks' : List Bool}
    (hm : CfMask.Proper cp (⟨b0 :: b2 :: mr, ks⟩ : CfMask))
    (hinner :
      CfMask.adjMask (⟨b0 :: b2 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a2 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).y).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
            (CpStep.y :: cp))
          (CpStep.y :: cp))
        ((cpmap cp).yOld x) ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)
          (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x) y :=
  cpMaskAdjSound_yOld_of_ringCycle
    h.ringCycle hproper hplainY hsize (h.maskAdj _ hm) hinner

theorem cpMaskAdjSound_hOld_of_cpMaskAdjInvariant_cons
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hsize : 2 < CProg.ringSize cp)
    {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 a2 : Bool} {mr' ks' : List Bool}
    (hm : CfMask.Proper cp (⟨b0 :: b1' :: mr, ks⟩ : CfMask))
    (hinner :
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).h).map.FaceBand
        (cpMask
          (CfMask.adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
            (CpStep.h :: cp))
          (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)
          (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x) y :=
  cpMaskAdjSound_hOld_of_ringCycle_cons
    h.ringCycle hproper hlong hplainH hsize (h.maskAdj _ hm) hinner

private theorem adjMask_two_ring_bits_elim
    {cp : CProg} {m : CfMask}
    (hm : CfMask.Proper cp m)
    (hsize : 1 < CProg.ringSize cp)
    (result : Prop)
    (hresult : ∀ (a0 a1 : Bool) (mr ks : List Bool),
      CfMask.adjMask m cp = ⟨a0 :: a1 :: mr, ks⟩ → result) :
    result := by
  have hproperAdj := CfMask.cpadj_proper cp m hm
  cases hinner : CfMask.adjMask m cp with
  | mk r' k' =>
      have hproperAdj' : CfMask.Proper cp ⟨r', k'⟩ := by
        simpa [hinner] using hproperAdj
      cases r' with
      | nil =>
          have hlen : 0 = CProg.ringSize cp := by
            simpa [CfMask.Proper] using hproperAdj'.1
          omega
      | cons a0 rt =>
          cases rt with
          | nil =>
              have hlen : 1 = CProg.ringSize cp := by
                simpa [CfMask.Proper] using hproperAdj'.1
              omega
          | cons a1 mr => exact hresult a0 a1 mr k' (by simpa using hinner)

private theorem adjMask_three_ring_bits_elim
    {cp : CProg} {m : CfMask}
    (hm : CfMask.Proper cp m)
    (hsize : 2 < CProg.ringSize cp)
    (result : Prop)
    (hresult : ∀ (a0 a1 a2 : Bool) (mr ks : List Bool),
      CfMask.adjMask m cp = ⟨a0 :: a1 :: a2 :: mr, ks⟩ → result) :
    result := by
  apply adjMask_two_ring_bits_elim hm (by omega) result
  intro a0 a1 mr ks hinner
  cases mr with
  | nil =>
      have hproperAdj := CfMask.cpadj_proper cp m hm
      rw [hinner] at hproperAdj
      have hlen : 2 = CProg.ringSize cp := by
        simpa [CfMask.Proper] using hproperAdj.1
      omega
  | cons a2 mr => exact hresult a0 a1 a2 mr ks hinner

private theorem proper_y_elim
    {cp : CProg}
    (hsize : 1 < CProg.ringSize cp)
    (result : CfMask → Prop)
    (hresult : ∀ (b0 b1 b2 : Bool) (mr ks : List Bool)
      (a0 a2 : Bool) (mr' ks' : List Bool),
      CfMask.Proper cp (⟨b0 :: b2 :: mr, ks⟩ : CfMask) →
      CfMask.adjMask (⟨b0 :: b2 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a2 :: mr', ks'⟩ →
      result (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask)) :
    ∀ m, CfMask.Proper (CpStep.y :: cp) m → result m
  | ⟨mr₀, ks⟩, ⟨hr, hk⟩ => by
      cases mr₀ with
      | nil => simp [CProg.ringSize] at hr
      | cons b0 mr₁ =>
          cases mr₁ with
          | nil => simp [CProg.ringSize] at hr; omega
          | cons b1 mr₂ =>
              cases mr₂ with
              | nil => simp [CProg.ringSize] at hr; omega
              | cons b2 mr =>
                  let m₀ : CfMask := ⟨b0 :: b2 :: mr, ks⟩
                  have hm₀ : CfMask.Proper cp m₀ := by
                    constructor
                    · simp [m₀, CProg.ringSize] at hr ⊢
                      omega
                    · simpa [m₀, CfMask.Proper, CProg.kernelSize] using hk
                  apply adjMask_two_ring_bits_elim hm₀ hsize
                  intro a0 a2 mr' ks' hinner
                  exact hresult b0 b1 b2 mr ks a0 a2 mr' ks' hm₀
                    (by simpa [m₀] using hinner)

private theorem proper_h_elim
    {cp : CProg}
    (hsize : 2 < CProg.ringSize cp)
    (result : CfMask → Prop)
    (hresult : ∀ (b0 b1 : Bool) (mr : List Bool) (b1' : Bool)
      (ks : List Bool) (a0 a1 a2 : Bool) (mr' ks' : List Bool),
      CfMask.Proper cp (⟨b0 :: b1' :: mr, ks⟩ : CfMask) →
      CfMask.adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩ →
      result (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask)) :
    ∀ m, CfMask.Proper (CpStep.h :: cp) m → result m
  | ⟨mr₀, ks₀⟩, ⟨hr, hk⟩ => by
      cases mr₀ with
      | nil => simp [CProg.ringSize] at hr; omega
      | cons b0 mr₁ =>
          cases mr₁ with
          | nil => simp [CProg.ringSize] at hr; omega
          | cons b1 mr =>
              cases ks₀ with
              | nil => simp [CProg.kernelSize] at hk
              | cons b1' ks =>
                  let m₀ : CfMask := ⟨b0 :: b1' :: mr, ks⟩
                  have hm₀ : CfMask.Proper cp m₀ := by
                    constructor
                    · simpa [m₀, CProg.ringSize] using hr
                    · simp [m₀, CProg.kernelSize] at hk ⊢
                      omega
                  apply adjMask_three_ring_bits_elim hm₀ hsize
                  intro a0 a1 a2 mr' ks' hinner
                  exact hresult b0 b1 mr b1' ks a0 a1 a2 mr' ks' hm₀
                    (by simpa [m₀] using hinner)

theorem cpMaskAdjSound_yOld_of_cpMaskAdjInvariant_proper
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hsize : 1 < CProg.ringSize cp)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.y :: cp) m)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).y).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.y :: cp)) (CpStep.y :: cp))
        ((cpmap cp).yOld x) ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask m (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x) y := by
  refine proper_y_elim hsize (fun m =>
    ((cpmap cp).y).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.y :: cp)) (CpStep.y :: cp))
        ((cpmap cp).yOld x) ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask m (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).yOld x) y) ?_ m hm
  intro b0 b1 b2 mr ks a0 a2 mr' ks' hm₀ hinner
  exact cpMaskAdjSound_yOld_of_cpMaskAdjInvariant
    (cp := cp) h hproper hplainY hsize (hm := hm₀) (hinner := hinner)

theorem cpMaskAdjSound_hOld_of_cpMaskAdjInvariant_proper
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hsize : 2 < CProg.ringSize cp)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.h :: cp) m)
    {x : (cpmap cp).map.Dart} :
    ((cpmap cp).h).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.h :: cp)) (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask m (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x) y := by
  refine proper_h_elim hsize (fun m =>
    ((cpmap cp).h).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.h :: cp)) (CpStep.h :: cp))
        ((cpmap cp).hOld x) ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask m (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).hOld x) y) ?_ m hm
  intro b0 b1 mr b1' ks a0 a1 a2 mr' ks' hm₀ hinner
  exact cpMaskAdjSound_hOld_of_cpMaskAdjInvariant_cons
    (cp := cp) h hproper hlong hplainH hsize (hm := hm₀) (hinner := hinner)

private theorem faceBand_iff_exists_ringAdj_congr_faceReachable
    {G : Hypermap} {adjacent selected : List G.Dart} {u v : G.Dart}
    (huv : PermReachable G.face u v)
    (hv : G.FaceBand adjacent v ↔
      ∃ y : G.Dart, y ∈ selected ∧ G.RingAdj v y) :
    G.FaceBand adjacent u ↔
      ∃ y : G.Dart, y ∈ selected ∧ G.RingAdj u y :=
  (Hypermap.FaceBand.congr_faceReachable (G := G) (r := adjacent) huv).trans
    (hv.trans
      (Hypermap.RingAdj.exists_mem_congr_faceReachable_left
        (G := G) (r := selected) huv).symm)

theorem cpMaskAdjSound_y_oldFace_of_cpMaskAdjInvariant_proper
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hsize : 1 < CProg.ringSize cp)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.y :: cp) m)
    {u : ((cpmap cp).y).map.Dart}
    {x : (cpmap cp).map.Dart}
    (hu : PermReachable ((cpmap cp).y).map.face
      u ((cpmap cp).yOld x)) :
    ((cpmap cp).y).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.y :: cp)) (CpStep.y :: cp))
        u ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask m (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj u y :=
  faceBand_iff_exists_ringAdj_congr_faceReachable hu
    (cpMaskAdjSound_yOld_of_cpMaskAdjInvariant_proper
      h hproper hplainY hsize m hm)

theorem cpMaskAdjSound_h_oldFace_of_cpMaskAdjInvariant_proper
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hsize : 2 < CProg.ringSize cp)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.h :: cp) m)
    {u : ((cpmap cp).h).map.Dart}
    {x : (cpmap cp).map.Dart}
    (hu : PermReachable ((cpmap cp).h).map.face
      u ((cpmap cp).hOld x)) :
    ((cpmap cp).h).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.h :: cp)) (CpStep.h :: cp))
        u ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask m (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj u y :=
  faceBand_iff_exists_ringAdj_congr_faceReachable hu
    (cpMaskAdjSound_hOld_of_cpMaskAdjInvariant_proper
      h hproper hlong hplainH hsize m hm)

theorem cpMaskAdjSound_y_point_of_cpMaskAdjInvariant_proper_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.y :: cp) m) :
    ((cpmap cp).y).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.y :: cp)) (CpStep.y :: cp))
        ((cpmap cp).y).point ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask m (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).y).point y := by
  refine proper_y_elim hsize (fun m =>
    ((cpmap cp).y).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.y :: cp)) (CpStep.y :: cp))
        ((cpmap cp).y).point ↔
      ∃ y : ((cpmap cp).y).map.Dart,
        y ∈ cpMask m (CpStep.y :: cp) ∧
          ((cpmap cp).y).map.RingAdj ((cpmap cp).y).point y) ?_ m hm
  intro b0 b1 b2 mr ks a0 a2 mr' ks' hm₀ hinner
  rw [cpMaskAdjSound_y_point_faceBand_rewrite_of_ringCycle
    h.ringCycle hproper (hinner := hinner)]
  rw [cpMaskAdjSound_y_point_exists_split_of_ringCycle_bridgeless
    h.ringCycle hproper hbridgeY hsize b0 b1 b2 mr ks]
  simp [Bool.or_eq_true, htail mr ks]

theorem cpMaskAdjSound_h_point_of_cpMaskAdjInvariant_proper_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x)
    (m : CfMask)
    (hm : CfMask.Proper (CpStep.h :: cp) m) :
    ((cpmap cp).h).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.h :: cp)) (CpStep.h :: cp))
        ((cpmap cp).h).point ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask m (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).h).point y := by
  refine proper_h_elim hsize (fun m =>
    ((cpmap cp).h).map.FaceBand
        (cpMask (CfMask.adjMask m (CpStep.h :: cp)) (CpStep.h :: cp))
        ((cpmap cp).h).point ↔
      ∃ y : ((cpmap cp).h).map.Dart,
        y ∈ cpMask m (CpStep.h :: cp) ∧
          ((cpmap cp).h).map.RingAdj ((cpmap cp).h).point y) ?_ m hm
  intro b0 b1 mr b1' ks a0 a1 a2 mr' ks' hm₀ hinner
  cases mr with
  | nil =>
      have hlen : 2 = CProg.ringSize cp := by
        simpa [CfMask.Proper] using hm₀.1
      omega
  | cons b2 mr =>
      rw [cpMaskAdjSound_h_point_faceBand_rewrite_of_ringCycle_cons
        h.ringCycle hproper hlong hsize (hinner := hinner)]
      rw [cpMaskAdjSound_h_point_exists_split_of_ringCycle_bridgeless
        h.ringCycle hproper hlong hbridgeH hsize b0 b1 b2 b1' mr ks]
      simp only [List.headD_cons, Bool.or_eq_true, htail mr ks]
      tauto

theorem cpMaskAdjSoundAllProper_y_of_cpMaskAdjInvariant_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjSoundAllProper (CpStep.y :: cp) := by
  intro m hm u
  rcases Hypermap.extensionY_exists_old_faceReachable_or_new
      (G := (cpmap cp).map) (cpmap cp).point u with hOld | hNew
  · rcases hOld with ⟨x, hu⟩
    exact faceBand_iff_exists_ringAdj_congr_faceReachable hu
      (cpMaskAdjSound_yOld_of_cpMaskAdjInvariant_proper
        h hproper hplainY hsize m hm)
  · exact faceBand_iff_exists_ringAdj_congr_faceReachable
      (PermReachable.symm ((cpmap cp).y).map.face hNew)
      (cpMaskAdjSound_y_point_of_cpMaskAdjInvariant_proper_of_tail_avoids
        h hproper hbridgeY hsize htail m hm)

theorem cpMaskAdjSoundAllProper_h_of_cpMaskAdjInvariant_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjSoundAllProper (CpStep.h :: cp) := by
  intro m hm u
  rcases Hypermap.extensionH_exists_old_faceReachable_or_new
      (G := (cpmap cp).map) (cpmap cp).point u with hOld | hNew
  · rcases hOld with ⟨x, hu⟩
    exact faceBand_iff_exists_ringAdj_congr_faceReachable hu
      (cpMaskAdjSound_hOld_of_cpMaskAdjInvariant_proper
        h hproper hlong hplainH hsize m hm)
  · exact faceBand_iff_exists_ringAdj_congr_faceReachable
      (PermReachable.symm ((cpmap cp).h).map.face hNew)
      (cpMaskAdjSound_h_point_of_cpMaskAdjInvariant_proper_of_tail_avoids
        h hproper hlong hbridgeH hsize htail m hm)

theorem cpMaskAdjInvariant_y_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 2) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjInvariant (CpStep.y :: cp) where
  ringCycle := cpRingCycle_y h.ringCycle hproper hsize
  maskAdj :=
    cpMaskAdjSoundAllProper_y_of_cpMaskAdjInvariant_of_tail_avoids
      h hproper hplainY hbridgeY hsize htail

theorem cpMaskAdjInvariant_h_of_tail_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (htail :
      ∀ (mr ks : List Bool),
        ¬ ∃ x : (cpmap cp).map.Dart,
          x ∈ CfMask.selectMask (⟨mr, ks⟩ : CfMask)
            ((cpRing cp).drop 3) (cpKernel cp) ∧
          (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjInvariant (CpStep.h :: cp) where
  ringCycle := cpRingCycle_h h.ringCycle hproper hlong hsize
  maskAdj :=
    cpMaskAdjSoundAllProper_h_of_cpMaskAdjInvariant_of_tail_avoids
      h hproper hlong hplainH hbridgeH hsize htail

theorem no_selectMask_faceBand_of_forall_not_mem
    {G : Hypermap} {sources ring kernel : List G.Dart} (m : CfMask)
    (hring : ∀ x : G.Dart, x ∈ ring → ¬ G.FaceBand sources x)
    (hkernel : ∀ x : G.Dart, x ∈ kernel → ¬ G.FaceBand sources x) :
    ¬ ∃ x : G.Dart,
      x ∈ CfMask.selectMask m ring kernel ∧ G.FaceBand sources x := by
  rintro ⟨x, hx, hband⟩
  rcases CfMask.mem_of_mem_selectMask hx with hxRing | hxKernel
  · exact hring x hxRing hband
  · exact hkernel x hxKernel hband

theorem cpMaskAdjSoundAllProper_y_of_cpMaskAdjInvariant_of_tail_lists_avoid
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (hring :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 2 →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x)
    (hkernel :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjSoundAllProper (CpStep.y :: cp) :=
  cpMaskAdjSoundAllProper_y_of_cpMaskAdjInvariant_of_tail_avoids
    h hproper hplainY hbridgeY hsize
    (by
      intro mr ks
      exact no_selectMask_faceBand_of_forall_not_mem
        (G := (cpmap cp).map)
        (sources :=
          [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point])
        (ring := (cpRing cp).drop 2)
        (kernel := cpKernel cp)
        (⟨mr, ks⟩ : CfMask) hring hkernel)

theorem cpMaskAdjSoundAllProper_h_of_cpMaskAdjInvariant_of_tail_lists_avoid
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (hring :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 3 →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x)
    (hkernel :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjSoundAllProper (CpStep.h :: cp) :=
  cpMaskAdjSoundAllProper_h_of_cpMaskAdjInvariant_of_tail_avoids
    h hproper hlong hplainH hbridgeH hsize
    (by
      intro mr ks
      exact no_selectMask_faceBand_of_forall_not_mem
        (G := (cpmap cp).map)
        (sources :=
          [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
            (cpmap cp).point,
            (cpmap cp).map.node (cpmap cp).point])
        (ring := (cpRing cp).drop 3)
        (kernel := cpKernel cp)
        (⟨mr, ks⟩ : CfMask) hring hkernel)

theorem cpMaskAdjInvariant_y_of_tail_lists_avoid
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (hring :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 2 →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x)
    (hkernel :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).point, (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjInvariant (CpStep.y :: cp) where
  ringCycle := cpRingCycle_y h.ringCycle hproper hsize
  maskAdj :=
    cpMaskAdjSoundAllProper_y_of_cpMaskAdjInvariant_of_tail_lists_avoid
      h hproper hplainY hbridgeY hsize hring hkernel

theorem cpMaskAdjInvariant_h_of_tail_lists_avoid
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (hring :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 3 →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x)
    (hkernel :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ (cpmap cp).map.FaceBand
            [(cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point),
              (cpmap cp).point,
              (cpmap cp).map.node (cpmap cp).point] x) :
    cpMaskAdjInvariant (CpStep.h :: cp) where
  ringCycle := cpRingCycle_h h.ringCycle hproper hlong hsize
  maskAdj :=
    cpMaskAdjSoundAllProper_h_of_cpMaskAdjInvariant_of_tail_lists_avoid
      h hproper hlong hplainH hbridgeH hsize hring hkernel

theorem cpMaskAdjInvariant_y_of_tail_reach_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hplainY : ((cpmap cp).y).map.Plain)
    (hbridgeY : ((cpmap cp).y).map.Bridgeless)
    (hsize : 1 < CProg.ringSize cp)
    (hringPoint :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 2 →
          ¬ PermReachable (cpmap cp).map.face (cpmap cp).point x)
    (hringNode :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 2 →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.node (cpmap cp).point) x)
    (hkernelPoint :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ PermReachable (cpmap cp).map.face (cpmap cp).point x)
    (hkernelNode :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.node (cpmap cp).point) x) :
    cpMaskAdjInvariant (CpStep.y :: cp) :=
  cpMaskAdjInvariant_y_of_tail_lists_avoid
    h hproper hplainY hbridgeY hsize
    (by
      intro x hx
      rw [Hypermap.not_FaceBand_pair]
      exact ⟨hringPoint x hx, hringNode x hx⟩)
    (by
      intro x hx
      rw [Hypermap.not_FaceBand_pair]
      exact ⟨hkernelPoint x hx, hkernelNode x hx⟩)

theorem cpMaskAdjInvariant_h_of_tail_reach_avoids
    {cp : CProg}
    (h : cpMaskAdjInvariant cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hplainH : ((cpmap cp).h).map.Plain)
    (hbridgeH : ((cpmap cp).h).map.Bridgeless)
    (hsize : 2 < CProg.ringSize cp)
    (hringFaceEdge :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 3 →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) x)
    (hringPoint :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 3 →
          ¬ PermReachable (cpmap cp).map.face (cpmap cp).point x)
    (hringNode :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ (cpRing cp).drop 3 →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.node (cpmap cp).point) x)
    (hkernelFaceEdge :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) x)
    (hkernelPoint :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ PermReachable (cpmap cp).map.face (cpmap cp).point x)
    (hkernelNode :
      ∀ x : (cpmap cp).map.Dart,
        x ∈ cpKernel cp →
          ¬ PermReachable (cpmap cp).map.face
            ((cpmap cp).map.node (cpmap cp).point) x) :
    cpMaskAdjInvariant (CpStep.h :: cp) :=
  cpMaskAdjInvariant_h_of_tail_lists_avoid
    h hproper hlong hplainH hbridgeH hsize
    (by
      intro x hx
      rw [Hypermap.not_FaceBand_triple]
      exact ⟨hringFaceEdge x hx, hringPoint x hx, hringNode x hx⟩)
    (by
      intro x hx
      rw [Hypermap.not_FaceBand_triple]
      exact ⟨hkernelFaceEdge x hx, hkernelPoint x hx, hkernelNode x hx⟩)

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
