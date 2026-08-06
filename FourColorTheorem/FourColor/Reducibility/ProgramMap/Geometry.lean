import FourColorTheorem.FourColor.Reducibility.ProgramMap.Interpretation

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

theorem step?_plain
    {s : CpStep} {P Q : PointedHypermap}
    (hstep : step? s P = some Q)
    (hP : P.Plain) :
    Q.Plain := by
  cases s with
  | rotate n =>
      simp [step?] at hstep
      cases hstep
      exact rotate_plain n P hP
  | reverseRotate =>
      simp [step?] at hstep
      cases hstep
      exact reverseRotate_plain P hP
  | y =>
      simp [step?] at hstep
      cases hstep
      exact y_plain P hP
  | h =>
      simp [step?] at hstep
      cases hstep
      exact h_plain P hP
  | u =>
      simp [step?] at hstep
      cases hstep
      exact u_plain P hP
  | k =>
      simp [step?] at hstep
  | a =>
      simp [step?] at hstep

theorem step?_connected
    {s : CpStep} {P Q : PointedHypermap}
    (hstep : step? s P = some Q)
    (hP : P.Connected) :
    Q.Connected := by
  cases s with
  | rotate n =>
      simp [step?] at hstep
      cases hstep
      exact rotate_connected n P hP
  | reverseRotate =>
      simp [step?] at hstep
      cases hstep
      exact reverseRotate_connected P hP
  | y =>
      simp [step?] at hstep
      cases hstep
      exact y_connected P hP
  | h =>
      simp [step?] at hstep
      cases hstep
      exact h_connected P hP
  | u =>
      simp [step?] at hstep
      cases hstep
      exact u_connected P hP
  | k =>
      simp [step?] at hstep
  | a =>
      simp [step?] at hstep

theorem stepPlainConnected?_plain
    {s : CpStep} {P Q : PointedHypermap}
    (hstep : stepPlainConnected? s P = some Q)
    (hP : P.Plain) :
    Q.Plain := by
  cases s with
  | rotate n =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact rotate_plain n P hP
  | reverseRotate =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact reverseRotate_plain P hP
  | y =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact y_plain P hP
  | h =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact h_plain P hP
  | u =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact u_plain P hP
  | k =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact k_plain P hP
  | a =>
      simp [stepPlainConnected?] at hstep

theorem stepPlainConnected?_connected
    {s : CpStep} {P Q : PointedHypermap}
    (hstep : stepPlainConnected? s P = some Q)
    (hP : P.Connected) :
    Q.Connected := by
  cases s with
  | rotate n =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact rotate_connected n P hP
  | reverseRotate =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact reverseRotate_connected P hP
  | y =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact y_connected P hP
  | h =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact h_connected P hP
  | u =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact u_connected P hP
  | k =>
      simp [stepPlainConnected?] at hstep
      cases hstep
      exact k_connected P hP
  | a =>
      simp [stepPlainConnected?] at hstep

theorem step?_bridgeless
    {s : CpStep} {P Q : PointedHypermap}
    (hstep : step? s P = some Q)
    (hP : P.Bridgeless)
    (hyProper : s = CpStep.y → P.ProperRingHead)
    (hhProper : s = CpStep.h → P.ProperRingHead) :
    Q.Bridgeless := by
  cases s with
  | rotate n =>
      simp [step?] at hstep
      cases hstep
      exact rotate_bridgeless n P hP
  | reverseRotate =>
      simp [step?] at hstep
      cases hstep
      exact reverseRotate_bridgeless P hP
  | y =>
      simp [step?] at hstep
      cases hstep
      exact y_bridgeless_of_proper P (hyProper rfl) hP
  | h =>
      simp [step?] at hstep
      cases hstep
      exact h_bridgeless_of_proper P (hhProper rfl) hP
  | u =>
      simp [step?] at hstep
      cases hstep
      exact u_bridgeless P hP
  | k =>
      simp [step?] at hstep
  | a =>
      simp [step?] at hstep

private theorem program_property_of_supported
    (runStep : CpStep → PointedHypermap → Option PointedHypermap)
    (run : CProg → Option PointedHypermap)
    (supported : CProg → Bool)
    (property : PointedHypermap → Prop)
    (runNil : run [] = some base)
    (runCons : ∀ s cp, run (s :: cp) = (run cp).bind (runStep s))
    (supportedTail : ∀ {s cp}, supported (s :: cp) = true → supported cp = true)
    (runSome : ∀ {cp}, supported cp = true → ∃ P, run cp = some P)
    (baseProperty : property base)
    (stepProperty : ∀ {s P Q}, runStep s P = some Q → property P → property Q) :
    ∀ {cp P}, supported cp = true → run cp = some P → property P
  | [], P, _hcp, hmap => by
      rw [runNil] at hmap
      cases hmap
      exact baseProperty
  | s :: cp, P, hcp, hmap => by
      have htail := supportedTail hcp
      rcases runSome htail with ⟨Q, hQ⟩
      have hstep : runStep s Q = some P := by
        rw [runCons, hQ] at hmap
        exact hmap
      exact stepProperty hstep
        (program_property_of_supported runStep run supported property runNil
          runCons supportedTail runSome baseProperty stepProperty htail hQ)

theorem cpmap?_plain_of_mapSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.mapSupported cp = true)
    (hmap : cpmap? cp = some P) :
    P.Plain :=
  program_property_of_supported step? cpmap? CProg.mapSupported
    PointedHypermap.Plain rfl cpmap?_cons
    (fun {s cp} h => by cases s <;> simp_all [CProg.mapSupported])
    cpmap?_isSome_of_mapSupported base_plain step?_plain hcp hmap

theorem cpmap?_connected_of_mapSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.mapSupported cp = true)
    (hmap : cpmap? cp = some P) :
    P.Connected :=
  program_property_of_supported step? cpmap? CProg.mapSupported
    PointedHypermap.Connected rfl cpmap?_cons
    (fun {s cp} h => by cases s <;> simp_all [CProg.mapSupported])
    cpmap?_isSome_of_mapSupported base_connected step?_connected hcp hmap

theorem cpmapPlainConnected?_plain_of_plainConnectedSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.plainConnectedSupported cp = true)
    (hmap : cpmapPlainConnected? cp = some P) :
    P.Plain :=
  program_property_of_supported stepPlainConnected? cpmapPlainConnected?
    CProg.plainConnectedSupported PointedHypermap.Plain rfl
    cpmapPlainConnected?_cons
    (fun {s cp} h => by cases s <;> simp_all [CProg.plainConnectedSupported])
    cpmapPlainConnected?_isSome_of_plainConnectedSupported base_plain
    stepPlainConnected?_plain hcp hmap

theorem cpmapPlainConnected?_connected_of_plainConnectedSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.plainConnectedSupported cp = true)
    (hmap : cpmapPlainConnected? cp = some P) :
    P.Connected :=
  program_property_of_supported stepPlainConnected? cpmapPlainConnected?
    CProg.plainConnectedSupported PointedHypermap.Connected rfl
    cpmapPlainConnected?_cons
    (fun {s cp} h => by cases s <;> simp_all [CProg.plainConnectedSupported])
    cpmapPlainConnected?_isSome_of_plainConnectedSupported base_connected
    stepPlainConnected?_connected hcp hmap

theorem cpmap?_plain_of_cubic
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.cubic cp = true)
    (hmap : cpmap? cp = some P) :
    P.Plain :=
  cpmap?_plain_of_mapSupported (CProg.cubic_implies_mapSupported hcp) hmap

theorem cpmap?_connected_of_cubic
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.cubic cp = true)
    (hmap : cpmap? cp = some P) :
    P.Connected :=
  cpmap?_connected_of_mapSupported (CProg.cubic_implies_mapSupported hcp) hmap

theorem cpmap?_plain_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.Plain :=
  cpmap?_plain_of_cubic (CProg.config_implies_cubic hcp) hmap

theorem cpmap?_connected_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.Connected :=
  cpmap?_connected_of_cubic (CProg.config_implies_cubic hcp) hmap

theorem cpmap?_bridgeless_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.Bridgeless :=
  ConfigProgram.property_of_config
    (fun cp => ∀ {P}, cpmap? cp = some P → P.Bridgeless)
    (fun {n cp} hcfg hbridge {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hstep : step? (CpStep.rotate n) Q = some P := by
        simpa [cpmap?, hQ] using hmap
      exact step?_bridgeless hstep (hbridge hQ)
        (by intro h; cases h) (by intro h; cases h))
    (by
      intro P hmap
      have hstep : step? CpStep.y base = some P := by
        simpa [cpmap?] using hmap
      exact step?_bridgeless hstep base_bridgeless
        (by intro _; exact base_properRingHead)
        (by intro h; cases h))
    (fun {s cp} hcfg hbridge {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hQproper := cpmap?_properRingHead_of_config hcfg hQ
      have hstep : step? CpStep.y Q = some P := by
        change (cpmap? (s :: cp)).bind (step? CpStep.y) = some P at hmap
        rw [hQ] at hmap
        exact hmap
      exact step?_bridgeless hstep (hbridge hQ)
        (by intro _; exact hQproper)
        (by intro h; cases h))
    (fun {cp} hcfg hbridge {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hQproper := cpmap?_properRingHead_of_config hcfg hQ
      have hstep : step? CpStep.h Q = some P := by
        simpa [cpmap?, hQ] using hmap
      exact step?_bridgeless hstep (hbridge hQ)
        (by intro h; cases h)
        (by intro _; exact hQproper))
    hcp hmap

theorem cpmap?_cubicGeometry_of_cubic
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.cubic cp = true)
    (hmap : cpmap? cp = some P) :
    P.CubicGeometry where
  proper := cpmap?_properRingHead_of_cubic hcp hmap
  plain := cpmap?_plain_of_cubic hcp hmap
  connected := cpmap?_connected_of_cubic hcp hmap

private theorem cpmap_property_of_cubic
    (property : PointedHypermap → Prop)
    (baseProperty : property base)
    (stepProperty : ∀ {s cp}, CProg.cubic (s :: cp) = true →
      property (cpmap cp) → property (step s (cpmap cp))) :
    ∀ {cp}, CProg.cubic cp = true → property (cpmap cp)
  | [], _hcp => baseProperty
  | s :: cp, hcp =>
      stepProperty (s := s) (cp := cp) hcp
        (cpmap_property_of_cubic property baseProperty stepProperty
          (CProg.cubic_cons_tail hcp))

/-- Coq `cpmap_cubic`: a cubic construction program is cubic away from its
current perimeter node orbit. -/
theorem cpmap_quasicubic_of_cubic :
    ∀ {cp : CProg}, CProg.cubic cp = true → (cpmap cp).Quasicubic :=
  cpmap_property_of_cubic PointedHypermap.Quasicubic base_quasicubic
    (fun {s cp} hcp htail => by
      cases s with
      | rotate n => exact rotate_quasicubic n (cpmap cp) htail
      | reverseRotate => simp [CProg.cubic] at hcp
      | y => exact y_quasicubic (cpmap cp) htail
      | h => exact h_quasicubic (cpmap cp) htail
      | u => exact u_quasicubic (cpmap cp) htail
      | k => simp [CProg.cubic] at hcp
      | a => simp [CProg.cubic] at hcp)

/-- Coq `cpmap_planar`: every cubic construction program preserves genus
zero.  Rotations leave the map unchanged, while `U`, `Y`, and `H` are the
three genus-preserving dart extensions. -/
theorem cpmap_eulerPlanar_of_cubic :
    ∀ {cp : CProg}, CProg.cubic cp = true → (cpmap cp).map.EulerPlanar :=
  cpmap_property_of_cubic (fun P => P.map.EulerPlanar) cpmap0_eulerPlanar
    (fun {s cp} hcp htail => by
      cases s with
      | rotate n => simpa [step] using htail
      | reverseRotate => simp [CProg.cubic] at hcp
      | y => exact (Hypermap.extensionY_eulerPlanar_iff
          (G := (cpmap cp).map) (cpmap cp).point).2 htail
      | h => exact (Hypermap.extensionH_eulerPlanar_iff
          (G := (cpmap cp).map) (cpmap cp).point).2 htail
      | u => exact (Hypermap.extensionU_eulerPlanar_iff
          (G := (cpmap cp).map) (cpmap cp).point).2 htail
      | k => simp [CProg.cubic] at hcp
      | a => simp [CProg.cubic] at hcp)

theorem cpmap?_supportedGeometry_of_mapSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.mapSupported cp = true)
    (hmap : cpmap? cp = some P) :
    P.SupportedGeometry where
  plain := cpmap?_plain_of_mapSupported hcp hmap
  connected := cpmap?_connected_of_mapSupported hcp hmap

theorem cpmapPlainConnected?_supportedGeometry_of_plainConnectedSupported
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.plainConnectedSupported cp = true)
    (hmap : cpmapPlainConnected? cp = some P) :
    P.SupportedGeometry where
  plain := cpmapPlainConnected?_plain_of_plainConnectedSupported hcp hmap
  connected := cpmapPlainConnected?_connected_of_plainConnectedSupported hcp hmap

theorem cpmap?_configGeometry_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.ConfigGeometry where
  proper := cpmap?_properRingHead_of_config hcp hmap
  plain := cpmap?_plain_of_config hcp hmap
  connected := cpmap?_connected_of_config hcp hmap
  long := cpmap?_longRingHead_of_config hcp hmap
  bridgeless := cpmap?_bridgeless_of_config hcp hmap

theorem cpmap_cubicGeometry_of_cubic
    {cp : CProg}
    (hcp : CProg.cubic cp = true) :
    (cpmap cp).CubicGeometry :=
  cpmap?_cubicGeometry_of_cubic hcp
    (cpmap?_eq_some_cpmap_of_cubic hcp)

/-- Coq `cpmap_bridgeless`: every cubic construction program is bridgeless. -/
theorem cpmap_bridgeless_of_cubic :
    ∀ {cp : CProg}, CProg.cubic cp = true → (cpmap cp).map.Bridgeless :=
  cpmap_property_of_cubic (fun P => P.map.Bridgeless) cpmap0_bridgeless
    (fun {s cp} hcp htail => by
      have hcubic := CProg.cubic_cons_tail hcp
      cases s with
      | rotate n => exact rotate_bridgeless n (cpmap cp) htail
      | reverseRotate => simp [CProg.cubic] at hcp
      | y =>
          apply y_bridgeless_of_proper (cpmap cp)
          · exact (cpmap_cubicGeometry_of_cubic hcubic).proper
          · exact htail
      | h =>
          apply h_bridgeless_of_proper (cpmap cp)
          · exact (cpmap_cubicGeometry_of_cubic hcubic).proper
          · exact htail
      | u => exact u_bridgeless (cpmap cp) htail
      | k => simp [CProg.cubic] at hcp
      | a => simp [CProg.cubic] at hcp)

theorem cpmap_configGeometry_of_config
    {cp : CProg}
    (hcp : CProg.config cp = true) :
    (cpmap cp).ConfigGeometry :=
  cpmap?_configGeometry_of_config hcp
    (cpmap?_eq_some_cpmap_of_config hcp)

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
