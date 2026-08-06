import FourColorTheorem.FourColor.Reducibility.ProgramMap.Configuration.ProgramInduction

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

/-- Interpret one supported construction step.  The remaining Coq steps are
left undefined until their ring-order/contraction semantics are ported. -/
noncomputable def step? : CpStep → PointedHypermap → Option PointedHypermap
  | CpStep.rotate n, P => some (P.rotate n)
  | CpStep.reverseRotate, P => some P.reverseRotate
  | CpStep.y, P => some P.y
  | CpStep.h, P => some P.h
  | CpStep.u, P => some P.u
  | CpStep.k, _ => none
  | CpStep.a, _ => none

/-- Right-to-left program interpretation, matching Coq `cpmap` on the
supported cubic/configuration fragment. -/
noncomputable def cpmap? : CProg → Option PointedHypermap
  | [] => some base
  | s :: cp => (cpmap? cp).bind (step? s)

/-- Interpret one construction step in the plain/connected fragment.  This
interpreter includes `K`, whose plainness and connectedness preservation have
already been ported, but still excludes `A`. -/
noncomputable def stepPlainConnected? : CpStep → PointedHypermap → Option PointedHypermap
  | CpStep.rotate n, P => some (P.rotate n)
  | CpStep.reverseRotate, P => some P.reverseRotate
  | CpStep.y, P => some P.y
  | CpStep.h, P => some P.h
  | CpStep.u, P => some P.u
  | CpStep.k, P => some P.k
  | CpStep.a, _ => none

/-- Right-to-left program interpretation for the plain/connected fragment. -/
noncomputable def cpmapPlainConnected? : CProg → Option PointedHypermap
  | [] => some base
  | s :: cp => (cpmapPlainConnected? cp).bind (stepPlainConnected? s)

@[simp]
theorem step?_rotate (n : Nat) (P : PointedHypermap) :
    step? (CpStep.rotate n) P = some (P.rotate n) :=
  rfl

@[simp]
theorem step?_y (P : PointedHypermap) :
    step? CpStep.y P = some P.y :=
  rfl

@[simp]
theorem step?_h (P : PointedHypermap) :
    step? CpStep.h P = some P.h :=
  rfl

@[simp]
theorem step?_u (P : PointedHypermap) :
    step? CpStep.u P = some P.u :=
  rfl

@[simp]
theorem step?_reverseRotate (P : PointedHypermap) :
    step? CpStep.reverseRotate P = some P.reverseRotate :=
  rfl

@[simp]
theorem step?_k (P : PointedHypermap) :
    step? CpStep.k P = none :=
  rfl

@[simp]
theorem step?_a (P : PointedHypermap) :
    step? CpStep.a P = none :=
  rfl

@[simp]
theorem stepPlainConnected?_rotate (n : Nat) (P : PointedHypermap) :
    stepPlainConnected? (CpStep.rotate n) P = some (P.rotate n) :=
  rfl

@[simp]
theorem stepPlainConnected?_reverseRotate (P : PointedHypermap) :
    stepPlainConnected? CpStep.reverseRotate P = some P.reverseRotate :=
  rfl

@[simp]
theorem stepPlainConnected?_y (P : PointedHypermap) :
    stepPlainConnected? CpStep.y P = some P.y :=
  rfl

@[simp]
theorem stepPlainConnected?_h (P : PointedHypermap) :
    stepPlainConnected? CpStep.h P = some P.h :=
  rfl

@[simp]
theorem stepPlainConnected?_u (P : PointedHypermap) :
    stepPlainConnected? CpStep.u P = some P.u :=
  rfl

@[simp]
theorem stepPlainConnected?_k (P : PointedHypermap) :
    stepPlainConnected? CpStep.k P = some P.k :=
  rfl

@[simp]
theorem stepPlainConnected?_a (P : PointedHypermap) :
    stepPlainConnected? CpStep.a P = none :=
  rfl

@[simp]
theorem cpmap?_nil :
    cpmap? [] = some base :=
  rfl

@[simp]
theorem cpmap?_cons (s : CpStep) (cp : CProg) :
    cpmap? (s :: cp) = (cpmap? cp).bind (step? s) :=
  rfl

@[simp]
theorem cpmapPlainConnected?_nil :
    cpmapPlainConnected? [] = some base :=
  rfl

@[simp]
theorem cpmapPlainConnected?_cons (s : CpStep) (cp : CProg) :
    cpmapPlainConnected? (s :: cp) =
      (cpmapPlainConnected? cp).bind (stepPlainConnected? s) :=
  rfl

private theorem program_eq_some_cpmap_of_supported
    (runStep : CpStep → PointedHypermap → Option PointedHypermap)
    (run : CProg → Option PointedHypermap)
    (supported : CProg → Bool)
    (runNil : run [] = some base)
    (runCons : ∀ s cp, run (s :: cp) = (run cp).bind (runStep s))
    (supportedTail : ∀ {s cp}, supported (s :: cp) = true → supported cp = true)
    (runStep_eq : ∀ {s cp}, supported (s :: cp) = true → ∀ P,
      runStep s P = some (step s P)) :
    ∀ {cp}, supported cp = true → run cp = some (cpmap cp)
  | [], _ => runNil
  | s :: cp, hcp => by
      rw [runCons, program_eq_some_cpmap_of_supported runStep run supported
        runNil runCons supportedTail runStep_eq (supportedTail hcp)]
      simpa [cpmap_cons] using runStep_eq hcp (cpmap cp)

private theorem program_isSome_eq_supported
    (runStep : CpStep → PointedHypermap → Option PointedHypermap)
    (run : CProg → Option PointedHypermap)
    (supported : CProg → Bool)
    (stepSupported : CpStep → Bool)
    (runNil : run [] = some base)
    (runCons : ∀ s cp, run (s :: cp) = (run cp).bind (runStep s))
    (supportedNil : supported [] = true)
    (supportedCons : ∀ s cp,
      supported (s :: cp) = (stepSupported s && supported cp))
    (runStepIsSome : ∀ s P, (runStep s P).isSome = stepSupported s) :
    ∀ cp, (run cp).isSome = supported cp
  | [] => by simp [runNil, supportedNil]
  | s :: cp => by
      rw [runCons, supportedCons, ← program_isSome_eq_supported runStep run
        supported stepSupported runNil runCons supportedNil supportedCons
        runStepIsSome cp]
      cases hrun : run cp with
      | none => simp
      | some P => simpa [hrun] using runStepIsSome s P

theorem cpmap?_eq_some_cpmap_of_mapSupported :
    ∀ {cp : CProg}, CProg.mapSupported cp = true → cpmap? cp = some (cpmap cp) :=
  program_eq_some_cpmap_of_supported step? cpmap? CProg.mapSupported rfl
    cpmap?_cons
    (fun {s cp} hcp => by
      cases s <;> simp_all [CProg.mapSupported])
    (fun {s cp} hcp P => by
      cases s <;> simp [CProg.mapSupported] at hcp ⊢)

theorem cpmap?_isSome_of_mapSupported
    {cp : CProg}
    (hcp : CProg.mapSupported cp = true) :
    ∃ P, cpmap? cp = some P :=
  ⟨cpmap cp, cpmap?_eq_some_cpmap_of_mapSupported hcp⟩

theorem cpmap?_isSome_eq_mapSupported :
    ∀ cp : CProg, (cpmap? cp).isSome = CProg.mapSupported cp :=
  program_isSome_eq_supported step? cpmap? CProg.mapSupported
    (fun s => match s with
      | CpStep.k | CpStep.a => false
      | _ => true)
    rfl cpmap?_cons rfl
    (fun s cp => by cases s <;> rfl)
    (fun s P => by cases s <;> rfl)

theorem cpmap?_isSome_iff_mapSupported {cp : CProg} :
    (∃ P, cpmap? cp = some P) ↔ CProg.mapSupported cp = true := by
  constructor
  · intro h
    have hs : (cpmap? cp).isSome = true := by
      rcases h with ⟨P, hP⟩
      simp [hP]
    simpa [cpmap?_isSome_eq_mapSupported cp] using hs
  · intro h
    exact cpmap?_isSome_of_mapSupported h

theorem cpmapPlainConnected?_eq_some_cpmap_of_plainConnectedSupported :
    ∀ {cp : CProg}, CProg.plainConnectedSupported cp = true →
      cpmapPlainConnected? cp = some (cpmap cp) :=
  program_eq_some_cpmap_of_supported stepPlainConnected? cpmapPlainConnected?
    CProg.plainConnectedSupported rfl cpmapPlainConnected?_cons
    (fun {s cp} hcp => by
      cases s <;> simp_all [CProg.plainConnectedSupported])
    (fun {s cp} hcp P => by
      cases s <;> simp [CProg.plainConnectedSupported] at hcp ⊢)

theorem cpmapPlainConnected?_isSome_of_plainConnectedSupported
    {cp : CProg}
    (hcp : CProg.plainConnectedSupported cp = true) :
    ∃ P, cpmapPlainConnected? cp = some P :=
  ⟨cpmap cp,
    cpmapPlainConnected?_eq_some_cpmap_of_plainConnectedSupported hcp⟩

theorem cpmapPlainConnected?_isSome_eq_plainConnectedSupported :
    ∀ cp : CProg,
      (cpmapPlainConnected? cp).isSome = CProg.plainConnectedSupported cp :=
  program_isSome_eq_supported stepPlainConnected? cpmapPlainConnected?
    CProg.plainConnectedSupported
    (fun s => match s with | CpStep.a => false | _ => true)
    rfl cpmapPlainConnected?_cons rfl
    (fun s cp => by cases s <;> rfl)
    (fun s P => by cases s <;> rfl)

theorem cpmapPlainConnected?_isSome_iff_plainConnectedSupported
    {cp : CProg} :
    (∃ P, cpmapPlainConnected? cp = some P) ↔
      CProg.plainConnectedSupported cp = true := by
  constructor
  · intro h
    have hs : (cpmapPlainConnected? cp).isSome = true := by
      rcases h with ⟨P, hP⟩
      simp [hP]
    simpa [cpmapPlainConnected?_isSome_eq_plainConnectedSupported cp] using hs
  · intro h
    exact cpmapPlainConnected?_isSome_of_plainConnectedSupported h

theorem cpmapPlainConnected?_isSome_iff_not_mem_a
    {cp : CProg} :
    (∃ P, cpmapPlainConnected? cp = some P) ↔ CpStep.a ∉ cp := by
  rw [cpmapPlainConnected?_isSome_iff_plainConnectedSupported,
    CProg.plainConnectedSupported_eq_true_iff_not_mem_a]

theorem cpmapPlainConnected?_eq_some_cpmap_of_not_mem_a
    {cp : CProg}
    (hcp : CpStep.a ∉ cp) :
    cpmapPlainConnected? cp = some (cpmap cp) :=
  cpmapPlainConnected?_eq_some_cpmap_of_plainConnectedSupported
    (CProg.plainConnectedSupported_of_not_mem_a hcp)

theorem cpmap?_isSome_of_cubic
    {cp : CProg}
    (hcp : CProg.cubic cp = true) :
    ∃ P, cpmap? cp = some P :=
  cpmap?_isSome_of_mapSupported (CProg.cubic_implies_mapSupported hcp)

theorem cpmap?_isSome_of_config
    {cp : CProg}
    (hcp : CProg.config cp = true) :
    ∃ P, cpmap? cp = some P :=
  cpmap?_isSome_of_cubic (CProg.config_implies_cubic hcp)

theorem cpmap?_eq_some_cpmap_of_cubic
    {cp : CProg}
    (hcp : CProg.cubic cp = true) :
    cpmap? cp = some (cpmap cp) :=
  cpmap?_eq_some_cpmap_of_mapSupported (CProg.cubic_implies_mapSupported hcp)

theorem cpmap?_eq_some_cpmap_of_config
    {cp : CProg}
    (hcp : CProg.config cp = true) :
    cpmap? cp = some (cpmap cp) :=
  cpmap?_eq_some_cpmap_of_mapSupported (CProg.config_implies_mapSupported hcp)

theorem cpmap?_properRingHead_of_cubic
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.cubic cp = true)
    (hmap : cpmap? cp = some P) :
    P.ProperRingHead := by
  induction cp generalizing P with
  | nil =>
      cases hmap
      exact base_properRingHead
  | cons s cp ih =>
      cases s with
      | rotate n =>
          have htail : CProg.cubic cp = true := by
            simpa [CProg.cubic] using hcp
          rcases cpmap?_isSome_of_cubic htail with ⟨Q, hQ⟩
          have hQproper : Q.ProperRingHead := ih htail hQ
          have hstep : step? (CpStep.rotate n) Q = some P := by
            simpa [cpmap?, hQ] using hmap
          simp [step?] at hstep
          cases hstep
          exact rotate_properRingHead n Q hQproper
      | reverseRotate =>
          simp [CProg.cubic] at hcp
      | y =>
          have htail : CProg.cubic cp = true := by
            simpa [CProg.cubic] using hcp
          rcases cpmap?_isSome_of_cubic htail with ⟨Q, hQ⟩
          have hstep : step? CpStep.y Q = some P := by
            simpa [cpmap?, hQ] using hmap
          simp [step?] at hstep
          cases hstep
          exact y_properRingHead Q
      | h =>
          have htail : CProg.cubic cp = true := by
            simpa [CProg.cubic] using hcp
          rcases cpmap?_isSome_of_cubic htail with ⟨Q, hQ⟩
          have hQproper : Q.ProperRingHead := ih htail hQ
          have hstep : step? CpStep.h Q = some P := by
            simpa [cpmap?, hQ] using hmap
          simp [step?] at hstep
          cases hstep
          exact h_properRingHead_of_proper Q hQproper
      | u =>
          have htail : CProg.cubic cp = true := by
            simpa [CProg.cubic] using hcp
          rcases cpmap?_isSome_of_cubic htail with ⟨Q, hQ⟩
          have hstep : step? CpStep.u Q = some P := by
            simpa [cpmap?, hQ] using hmap
          simp [step?] at hstep
          cases hstep
          exact u_properRingHead Q
      | k =>
          simp [CProg.cubic] at hcp
      | a =>
          simp [CProg.cubic] at hcp

theorem cpmap?_properRingHead_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.ProperRingHead :=
  cpmap?_properRingHead_of_cubic (CProg.config_implies_cubic hcp) hmap

theorem cpmap?_longRingHead_of_config
    {cp : CProg} {P : PointedHypermap}
    (hcp : CProg.config cp = true)
    (hmap : cpmap? cp = some P) :
    P.LongRingHead :=
  ConfigProgram.property_of_config
    (fun cp => ∀ {P}, cpmap? cp = some P → P.LongRingHead)
    (fun {n cp} hcfg hlong {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hstep : step? (CpStep.rotate n) Q = some P := by
        simpa [cpmap?, hQ] using hmap
      simp [step?] at hstep
      cases hstep
      exact rotate_longRingHead n Q (hlong hQ))
    (by
      intro P hmap
      have hstep : step? CpStep.y base = some P := by
        simpa [cpmap?] using hmap
      simp [step?] at hstep
      cases hstep
      exact y_longRingHead_of_proper base base_properRingHead)
    (fun {s cp} hcfg _hlong {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hQproper := cpmap?_properRingHead_of_config hcfg hQ
      have hstep : step? CpStep.y Q = some P := by
        change (cpmap? (s :: cp)).bind (step? CpStep.y) = some P at hmap
        rw [hQ] at hmap
        exact hmap
      simp [step?] at hstep
      cases hstep
      exact y_longRingHead_of_proper Q hQproper)
    (fun {cp} hcfg hlong {P} hmap => by
      rcases cpmap?_isSome_of_config hcfg with ⟨Q, hQ⟩
      have hQproper := cpmap?_properRingHead_of_config hcfg hQ
      have hstep : step? CpStep.h Q = some P := by
        simpa [cpmap?, hQ] using hmap
      simp [step?] at hstep
      cases hstep
      exact h_longRingHead_of_proper_long Q hQproper (hlong hQ))
    hcp hmap

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
