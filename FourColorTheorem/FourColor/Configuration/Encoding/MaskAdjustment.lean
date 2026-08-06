import FourColorTheorem.FourColor.Configuration.Encoding.MaskSelection

/-! Adjacency propagation and contract-band masks. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask

/-- Adjacency propagation on ring/kernel masks, porting Coq's `cpadj`
executable syntax.  The geometric correctness theorem belongs to the later
configuration-map layer. -/
def adjMask (m : CfMask) : CProg → CfMask
  | [] =>
      match m.ring, m.kernel with
      | [b0, b1], [] => ⟨[b1, b0], []⟩
      | _, _ => m
  | CpStep.rotate n :: cp =>
      let m' := adjMask ⟨CProg.rotateRight n m.ring, m.kernel⟩ cp
      ⟨CProg.rotateLeft n m'.ring, m'.kernel⟩
  | CpStep.y :: cp =>
      match m.ring, m.kernel with
      | b0 :: b1 :: b2 :: mr, ks =>
          let m' := adjMask ⟨b0 :: b2 :: mr, ks⟩ cp
          match m'.ring, m'.kernel with
          | a0 :: a2 :: mr', ks' =>
              ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', ks'⟩
          | _, _ => ⟨b0 :: b1 :: b2 :: mr, ks⟩
      | _, _ => m
  | CpStep.h :: cp =>
      match m.ring, m.kernel with
      | b0 :: b1 :: mr, b1' :: ks =>
          let m' := adjMask ⟨b0 :: b1' :: mr, ks⟩ cp
          match m'.ring, m'.kernel with
          | a0 :: a1 :: mr', ks' =>
              let ringTail :=
                match mr' with
                | a2 :: mr'' => (a2 || b1) :: mr''
                | [] => []
              ⟨(a0 || b1) :: (b0 || b1' || mr.headD b0) :: ringTail,
                (a1 || b1) :: ks'⟩
          | _, _ => ⟨b0 :: b1 :: mr, b1' :: ks⟩
      | _, _ => m
  | _ => m

theorem adjMask_y_eq_of_inner
    {cp : CProg} {b0 b1 b2 : Bool} {mr ks : List Bool}
    {a0 a2 : Bool} {mr' ks' : List Bool}
    (hinner :
      adjMask (⟨b0 :: b2 :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a2 :: mr', ks'⟩) :
    adjMask (⟨b0 :: b1 :: b2 :: mr, ks⟩ : CfMask) (CpStep.y :: cp) =
      ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', ks'⟩ := by
  simp [adjMask, hinner]

theorem adjMask_h_eq_of_inner_cons
    {cp : CProg} {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 a2 : Bool} {mr' ks' : List Bool}
    (hinner :
      adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨a0 :: a1 :: a2 :: mr', ks'⟩) :
    adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask) (CpStep.h :: cp) =
      ⟨(a0 || b1) :: (b0 || b1' || mr.headD b0) ::
          (a2 || b1) :: mr',
        (a1 || b1) :: ks'⟩ := by
  simp [adjMask, hinner]

theorem adjMask_h_eq_of_inner_nil
    {cp : CProg} {b0 b1 b1' : Bool} {mr ks : List Bool}
    {a0 a1 : Bool} {ks' : List Bool}
    (hinner :
      adjMask (⟨b0 :: b1' :: mr, ks⟩ : CfMask) cp =
        ⟨[a0, a1], ks'⟩) :
    adjMask (⟨b0 :: b1 :: mr, b1' :: ks⟩ : CfMask) (CpStep.h :: cp) =
      ⟨[(a0 || b1), (b0 || b1' || mr.headD b0)],
        (a1 || b1) :: ks'⟩ := by
  simp [adjMask, hinner]

/-- Coq `cpadj_proper`: adjacency propagation preserves the ring/kernel mask
lengths required by a construction program. -/
theorem cpadj_proper :
    ∀ (cp : CProg) (m : CfMask), Proper cp m → Proper cp (adjMask m cp)
  | [], ⟨mr, ks₀⟩, hm => by
      rcases hm with ⟨hr, hk⟩
      cases mr with
      | nil =>
          simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
            using And.intro hr hk
      | cons b0 mr₁ =>
          cases mr₁ with
          | nil =>
              simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
                using And.intro hr hk
          | cons b1 mr₂ =>
              cases mr₂ with
              | nil =>
                  cases ks₀ with
                  | nil =>
                      simp [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
                  | cons k ks =>
                      simpa [Proper, adjMask, CProg.ringSize,
                        CProg.kernelSize] using And.intro hr hk
              | cons b2 mr₃ =>
                  simpa [Proper, adjMask, CProg.ringSize,
                    CProg.kernelSize] using And.intro hr hk
  | CpStep.rotate n :: cp, ⟨mr, ks₀⟩, hm => by
      rcases hm with ⟨hr, hk⟩
      let m₀ : CfMask := ⟨CProg.rotateRight n mr, ks₀⟩
      have hm₀ : Proper cp m₀ := by
        constructor
        · simpa [m₀, CProg.length_rotateRight, CProg.ringSize] using hr
        · simpa [m₀, CProg.kernelSize] using hk
      rcases cpadj_proper cp m₀ hm₀ with ⟨hr', hk'⟩
      simp [Proper, adjMask, m₀, CProg.ringSize, CProg.kernelSize,
        CProg.length_rotateLeft, hr', hk']
  | CpStep.reverseRotate :: cp, m, hm => by
      simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize] using hm
  | CpStep.y :: cp, ⟨mr, ks₀⟩, hm => by
      rcases hm with ⟨hr, hk⟩
      cases mr with
      | nil =>
          simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
            using And.intro hr hk
      | cons b0 mr₁ =>
          cases mr₁ with
          | nil =>
              simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
                using And.intro hr hk
          | cons b1 mr₂ =>
              cases mr₂ with
              | nil =>
                  simpa [Proper, adjMask, CProg.ringSize,
                    CProg.kernelSize] using And.intro hr hk
              | cons b2 mr =>
                  let m₀ : CfMask := ⟨b0 :: b2 :: mr, ks₀⟩
                  have hm₀ : Proper cp m₀ := by
                    constructor
                    · simp [m₀, CProg.ringSize] at hr ⊢
                      omega
                    · simpa [m₀, CProg.kernelSize] using hk
                  cases hadj : adjMask m₀ cp with
                  | mk r' k' =>
                      have hproper' : Proper cp ⟨r', k'⟩ := by
                        simpa [hadj] using cpadj_proper cp m₀ hm₀
                      rcases hproper' with ⟨hr', hk'⟩
                      cases r' with
                      | nil =>
                          simpa [Proper, adjMask, m₀, hadj, CProg.ringSize,
                            CProg.kernelSize] using And.intro hr hk
                      | cons a0 rt =>
                          cases rt with
                          | nil =>
                              simpa [Proper, adjMask, m₀, hadj,
                                CProg.ringSize, CProg.kernelSize] using
                                And.intro hr hk
                          | cons a2 mr' =>
                              constructor
                              · simp [adjMask, m₀, hadj, CProg.ringSize]
                                  at hr' ⊢
                                omega
                              · simpa [Proper, adjMask, m₀, hadj,
                                  CProg.kernelSize] using hk'
  | CpStep.h :: cp, ⟨mr, ks₀⟩, hm => by
      rcases hm with ⟨hr, hk⟩
      cases mr with
      | nil =>
          simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
            using And.intro hr hk
      | cons b0 mr₁ =>
          cases mr₁ with
          | nil =>
              simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize]
                using And.intro hr hk
          | cons b1 mr =>
              cases ks₀ with
              | nil =>
                  simpa [Proper, adjMask, CProg.ringSize,
                    CProg.kernelSize] using And.intro hr hk
              | cons b1' ks =>
                  let m₀ : CfMask := ⟨b0 :: b1' :: mr, ks⟩
                  have hm₀ : Proper cp m₀ := by
                    constructor
                    · simpa [m₀, CProg.ringSize] using hr
                    · simp [m₀, CProg.kernelSize] at hk ⊢
                      omega
                  cases hadj : adjMask m₀ cp with
                  | mk r' k' =>
                      have hproper' : Proper cp ⟨r', k'⟩ := by
                        simpa [hadj] using cpadj_proper cp m₀ hm₀
                      rcases hproper' with ⟨hr', hk'⟩
                      cases r' with
                      | nil =>
                          simpa [Proper, adjMask, m₀, hadj, CProg.ringSize,
                            CProg.kernelSize] using And.intro hr hk
                      | cons a0 rt =>
                          cases rt with
                          | nil =>
                              simpa [Proper, adjMask, m₀, hadj,
                                CProg.ringSize, CProg.kernelSize] using
                                And.intro hr hk
                          | cons a1 mr' =>
                              constructor
                              · cases mr' with
                                | nil =>
                                    simpa [Proper, adjMask, m₀, hadj,
                                      CProg.ringSize] using hr'
                                | cons a2 mr'' =>
                                    simpa [Proper, adjMask, m₀, hadj,
                                      CProg.ringSize] using hr'
                              · simp [adjMask, m₀, hadj, CProg.kernelSize]
                                  at hk' ⊢
                                omega
  | CpStep.u :: cp, m, hm => by
      simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize] using hm
  | CpStep.k :: cp, m, hm => by
      simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize] using hm
  | CpStep.a :: cp, m, hm => by
      simpa [Proper, adjMask, CProg.ringSize, CProg.kernelSize] using hm

/-- Contract-edge band propagation on masks, porting Coq's `ctrband`
executable syntax. -/
def contractBand : List Bool → CProg → CfMask
  | cm, CpStep.rotate n :: cp =>
      rotateRing n (contractBand cm cp)
  | _, [CpStep.y] =>
      ⟨List.replicate 3 false, []⟩
  | b1 :: cm, CpStep.y :: cp =>
      let m := contractBand cm cp
      match m.ring, m.kernel with
      | a0 :: a1 :: mr, ks =>
          ⟨(b1 || a0) :: false :: (b1 || a1) :: mr, ks⟩
      | _, _ => empty
  | b1 :: b0 :: b2 :: cm, CpStep.h :: cp =>
      let m := contractBand cm cp
      match m.ring, m.kernel with
      | a0 :: a1 :: a2 :: mr, ks =>
          ⟨(b0 || a0) :: b1 :: (b2 || a2) :: mr,
            (b0 || b1 || b2 || a1) :: ks⟩
      | _, _ => empty
  | _, _ => empty

/-- First, syntax-only component of Coq `ctrband_correct`: when the contract
mask has the expected `ctrmsize`/`contractEdgeSize`, `contractBand` produces a
proper ring/kernel face mask for a well-formed configuration program. -/
theorem proper_contractBand_of_length :
    ∀ {cm : List Bool} {cp : CProg},
      cm.length = CProg.contractEdgeSize cp →
      CProg.config cp = true →
      Proper cp (contractBand cm cp)
  | cm, CpStep.rotate n :: cp, hcm, hcp => by
      have hcp' : CProg.config cp = true := by
        simpa [CProg.config] using hcp
      have hproper := proper_contractBand_of_length
        (cm := cm) (cp := cp)
        (by simpa [CProg.contractEdgeSize] using hcm) hcp'
      exact proper_rotateRing n hproper
  | cm, CpStep.reverseRotate :: cp, _hcm, hcp => by
      simp [CProg.config] at hcp
  | cm, CpStep.y :: [], _hcm, _hcp => by
      simp [Proper, contractBand, CProg.ringSize, CProg.kernelSize]
  | [], CpStep.y :: s :: cp, hcm, _hcp => by
      simp [CProg.contractEdgeSize] at hcm
  | b :: cm, CpStep.y :: s :: cp, hcm, hcp => by
      have hcp' : CProg.config (s :: cp) = true := by
        simpa [CProg.config] using hcp
      have hcm' : cm.length = CProg.contractEdgeSize (s :: cp) := by
        simp [CProg.contractEdgeSize] at hcm
        omega
      have hproper := proper_contractBand_of_length
        (cm := cm) (cp := s :: cp) hcm' hcp'
      rcases hproper with ⟨hr, hk⟩
      cases hband : contractBand cm (s :: cp) with
      | mk r k =>
          have hrk : r.length = CProg.ringSize (s :: cp) := by
            simpa [hband] using hr
          have hkk : k.length = CProg.kernelSize (s :: cp) := by
            simpa [hband] using hk
          cases r with
          | nil =>
              have hlong := CProg.ringSize_gt_two_of_config hcp'
              simp at hrk
              omega
          | cons a0 rtail =>
              cases rtail with
              | nil =>
                  have hlong := CProg.ringSize_gt_two_of_config hcp'
                  simp at hrk
                  omega
              | cons a1 mr =>
                  constructor
                  · simp [contractBand, hband, CProg.ringSize] at hrk ⊢
                    omega
                  · simpa [Proper, contractBand, hband, CProg.kernelSize]
                      using hkk
  | cm, CpStep.h :: cp, hcm, hcp => by
      have hcp' : CProg.config cp = true := by
        simpa [CProg.config] using hcp
      cases cm with
      | nil =>
          simp [CProg.contractEdgeSize] at hcm
      | cons b1 cm₁ =>
          cases cm₁ with
          | nil =>
              simp [CProg.contractEdgeSize] at hcm
          | cons b0 cm₂ =>
              cases cm₂ with
              | nil =>
                  simp [CProg.contractEdgeSize] at hcm
              | cons b2 cm' =>
                  have hcm' :
                      cm'.length = CProg.contractEdgeSize cp := by
                    simp [CProg.contractEdgeSize] at hcm
                    omega
                  have hproper := proper_contractBand_of_length
                    (cm := cm') (cp := cp) hcm' hcp'
                  rcases hproper with ⟨hr, hk⟩
                  cases hband : contractBand cm' cp with
                  | mk r k =>
                      have hrk : r.length = CProg.ringSize cp := by
                        simpa [hband] using hr
                      have hkk : k.length = CProg.kernelSize cp := by
                        simpa [hband] using hk
                      cases r with
                      | nil =>
                          have hlong := CProg.ringSize_gt_two_of_config hcp'
                          simp at hrk
                          omega
                      | cons a0 r₁ =>
                          cases r₁ with
                          | nil =>
                              have hlong := CProg.ringSize_gt_two_of_config hcp'
                              simp at hrk
                              omega
                          | cons a1 r₂ =>
                              cases r₂ with
                              | nil =>
                                  have hlong :=
                                    CProg.ringSize_gt_two_of_config hcp'
                                  simp at hrk
                                  omega
                              | cons a2 mr =>
                                  constructor
                                  · simpa [contractBand, hband,
                                      CProg.ringSize] using hrk
                                  · simp [contractBand, hband,
                                      CProg.kernelSize] at hkk ⊢
                                    omega
  | cm, CpStep.u :: cp, _hcm, hcp => by
      simp [CProg.config] at hcp
  | cm, CpStep.k :: cp, _hcm, hcp => by
      simp [CProg.config] at hcp
  | cm, CpStep.a :: cp, _hcm, hcp => by
      simp [CProg.config] at hcp
  | cm, [], _hcm, hcp => by
      simp [CProg.config] at hcp

end CfMask

end FourColor

end Schematic.Math.GraphTheory
