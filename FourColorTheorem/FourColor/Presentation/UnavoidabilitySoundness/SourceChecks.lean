import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.MinimalGeometry

/-! Soundness of the executable source-bound checks. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

/-- Semantic soundness target for the executable source-bound checker.  The
remaining proof here is the Lean port of Coq `check_dbound1P`, specialized to
the four small source arities. -/
def SourceCheckSoundForArity (n : Nat) : Prop :=
  Presentation.RedpartSound.{u} →
      Discharge.Hubcap.checkDbound1 Presentation.theRedpart
        (Discharge.theDruleFork n) (Part.pconsN n) 5 = true →
        SourceBoundForArity.{u} n

theorem checkDbound1Rec_sound
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample) (x : G.Dart) :
    ∀ {m p rs ns},
      Discharge.Hubcap.checkDbound1Rec Presentation.theRedpart p rs ns m =
          true →
        Part.exactFitp G x p = true →
          G.dbound1 rs x ≤ ns := by
  intro m
  induction m with
  | zero =>
      intro p rs ns hcheck _hfit
      simp [Discharge.Hubcap.checkDbound1Rec] at hcheck
  | succ m ih =>
      intro p rs ns hcheck hfit
      cases rs with
      | nil =>
          simp [Hypermap.dbound1, Discharge.countBy]
      | cons r rs' =>
          by_cases hshort : rs'.length < ns
          · have hlen : (r :: rs').length ≤ ns := by
              simp
              omega
            exact le_trans (G.dbound1_le_length (r :: rs') x) hlen
          · simp [Discharge.Hubcap.checkDbound1Rec, hshort] at hcheck
            rcases hcheck with ⟨hfirst, hrest⟩
            by_cases hrtrue : Part.fitp G x r = true
            · let p' := Part.meet p r
              let sorted := Discharge.sortDrules p' rs'
              have hp' : Part.exactFitp G x p' = true :=
                Part.exactFitp_meet_of_fitp (G := G) hfit hrtrue
              have hpfit : Part.fitp G x p' = true := by
                have hs := hp'
                simp [Part.exactFitp] at hs
                exact hs.2
              have hsort := G.sortDrules_dbound1_eq hpfit rs'
              have hsort' :
                  sorted.nbForcedDrules +
                      G.dbound1 sorted.straddlingDrules x =
                    G.dbound1 rs' x := by
                simpa [sorted] using hsort
              cases hsub : ns - sorted.nbForcedDrules with
              | zero =>
                  simp [p', sorted, hsub] at hfirst
                  have hpfalse := hredpart hG x p' hfirst
                  rw [hp'] at hpfalse
                  cases hpfalse
              | succ ns' =>
                  simp [p', sorted, hsub] at hfirst
                  have hstrad :=
                    ih (p := p') (rs := sorted.straddlingDrules)
                      (ns := ns') hfirst hp'
                  change
                    (if Part.fitp G x r then 1 else 0) +
                        G.dbound1 rs' x ≤ ns
                  rw [hrtrue]
                  simp
                  omega
            · have hrfalse : Part.fitp G x r = false := by
                cases h : Part.fitp G x r with
                | false => rfl
                | true => exact False.elim (hrtrue h)
              have htail := ih (p := p) (rs := rs') (ns := ns) hrest hfit
              change
                (if Part.fitp G x r then 1 else 0) + G.dbound1 rs' x ≤ ns
              rw [hrfalse]
              simp
              exact htail

theorem checkDbound2Rec_sound
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample) (x : G.Dart) :
    ∀ {m p rt rs ru nt},
      Discharge.Hubcap.checkDbound2Rec Presentation.theRedpart
          p rt rs ru nt m = true →
        (∀ r ∈ ru, Part.fitp G x r = false) →
          Part.exactFitp G x p = true →
            G.dbound2 rt rs x ≤ (nt : Int) := by
  intro m
  induction m with
  | zero =>
      intro p rt rs ru nt hcheck _hru _hfit
      simp [Discharge.Hubcap.checkDbound2Rec] at hcheck
  | succ m ih =>
      intro p rt rs ru nt hcheck hru hfit
      cases rt with
      | nil =>
          simp [Hypermap.dbound2, Hypermap.dbound1, Discharge.countBy]
      | cons r rt' =>
          by_cases hshort : rt'.length < nt
          · have hlen : (r :: rt').length ≤ nt := by
              simp
              omega
            have htarget : G.dbound1 (r :: rt') x ≤ nt :=
              le_trans (G.dbound1_le_length (r :: rt') x) hlen
            calc
              G.dbound2 (r :: rt') rs x ≤ (G.dbound1 (r :: rt') x : Int) := by
                simp [Hypermap.dbound2]
              _ ≤ (nt : Int) := by
                exact_mod_cast htarget
          · simp [Discharge.Hubcap.checkDbound2Rec, hshort] at hcheck
            rcases hcheck with ⟨hfirst, hrest⟩
            by_cases hrtrue : Part.fitp G x r = true
            · let p' := Part.meet p r
              have hp' : Part.exactFitp G x p' = true :=
                Part.exactFitp_meet_of_fitp (G := G) hfit hrtrue
              have hpfit : Part.fitp G x p' = true := by
                have hs := hp'
                simp [Part.exactFitp] at hs
                exact hs.2
              rcases hfirst with hunfit | hfirst
              · rcases Discharge.Hubcap.checkUnfit_eq_true_exists_subset
                    (p := p') hunfit with
                  ⟨u, hu, hcmp⟩
                have hufit : Part.fitp G x u = true :=
                  Part.fitp_of_cmp_eq_subset (G := G) p' u x hcmp hpfit
                have hufalse := hru u hu
                rw [hufit] at hufalse
                cases hufalse
              ·
                let srt := Discharge.sortDrules p' rt'
                let srs := Discharge.sortDrules p' rs
                have hsort := G.sortDrules_dbound2_eq hpfit rt' rs
                have hsort' :
                    G.dbound2 rt' rs x =
                      ((srt.nbForcedDrules : Int) -
                          (srs.nbForcedDrules : Int)) +
                        G.dbound2 srt.straddlingDrules
                          srs.straddlingDrules x := by
                  simpa [srt, srs] using hsort
                cases hsub :
                    (Discharge.sortDrules (Part.meet p r) rs).nbForcedDrules +
                        nt -
                      (Discharge.sortDrules (Part.meet p r) rt').nbForcedDrules with
                | zero =>
                    simp [hsub] at hfirst
                    have hpfalse := hredpart hG x p' hfirst
                    rw [hp'] at hpfalse
                    cases hpfalse
                | succ nt' =>
                    simp [hsub] at hfirst
                    have hsub' :
                        srs.nbForcedDrules + nt - srt.nbForcedDrules =
                          nt' + 1 := by
                      simpa [p', srt, srs] using hsub
                    have hstrad :=
                      ih (p := p') (rt := srt.straddlingDrules)
                        (rs := srs.straddlingDrules) (ru := ru)
                        (nt := nt') hfirst hru hp'
                    have htailBound :
                        G.dbound2 rt' rs x ≤
                          ((srt.nbForcedDrules : Int) -
                              (srs.nbForcedDrules : Int)) +
                            (nt' : Int) := by
                      rw [hsort']
                      omega
                    have hbudget :
                        (1 : Int) +
                            (((srt.nbForcedDrules : Int) -
                                (srs.nbForcedDrules : Int)) +
                              (nt' : Int)) ≤
                          (nt : Int) := by
                      omega
                    have hhead :
                        G.dbound2 (r :: rt') rs x =
                          1 + G.dbound2 rt' rs x := by
                      simp [Hypermap.dbound2, Hypermap.dbound1,
                        Discharge.countBy, hrtrue]
                      omega
                    calc
                      G.dbound2 (r :: rt') rs x =
                          1 + G.dbound2 rt' rs x := hhead
                      _ ≤
                          1 + (((srt.nbForcedDrules : Int) -
                              (srs.nbForcedDrules : Int)) +
                            (nt' : Int)) := by omega
                      _ ≤ (nt : Int) := hbudget
            · have hrfalse : Part.fitp G x r = false := by
                cases h : Part.fitp G x r with
                | false => rfl
                | true => exact False.elim (hrtrue h)
              have hru' : ∀ r' ∈ r :: ru, Part.fitp G x r' = false := by
                intro r' hr'
                rcases List.mem_cons.mp hr' with hEq | hmem
                · simpa [hEq] using hrfalse
                · exact hru r' hmem
              have htail :=
                ih (p := p) (rt := rt') (rs := rs) (ru := r :: ru)
                  (nt := nt) hrest hru' hfit
              simpa [Hypermap.dbound2, Hypermap.dbound1,
                Discharge.countBy, hrfalse] using htail

theorem checkDbound2_sound
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample) (x : G.Dart)
    {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p : Part} {b : Int}
    (hcheck :
      Discharge.Hubcap.checkDbound2 Presentation.theRedpart rf p b = true)
    (hfit : Part.exactFitp G x p = true) :
    G.dbound2 rf.targetDrules rf.sourceDrules x ≤ b := by
  let srt := Discharge.sortDrules p rf.targetDrules
  let srs := Discharge.sortDrules p rf.sourceDrules
  have hpfit : Part.fitp G x p = true := by
    have hs := hfit
    simp [Part.exactFitp] at hs
    exact hs.2
  have hsort := G.sortDrules_dbound2_eq hpfit
    rf.targetDrules rf.sourceDrules
  have hsort' :
      G.dbound2 rf.targetDrules rf.sourceDrules x =
        ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
          G.dbound2 srt.straddlingDrules srs.straddlingDrules x := by
    simpa [srt, srs] using hsort
  have hcheckRaw :
      (match
          Discharge.Hubcap.intAsNat?
            (Int.ofNat (Discharge.sortDrules p rf.sourceDrules).nbForcedDrules -
              Int.ofNat (Discharge.sortDrules p rf.targetDrules).nbForcedDrules +
                b) with
        | none => false
        | some nt =>
            Discharge.Hubcap.checkDbound2Rec Presentation.theRedpart p
              (Discharge.sortDrules p rf.targetDrules).straddlingDrules
              (Discharge.sortDrules p rf.sourceDrules).straddlingDrules []
              nt
              ((Discharge.sortDrules p rf.targetDrules).straddlingDrules.length +
                2)) = true := by
    simpa [Discharge.Hubcap.checkDbound2] using hcheck
  cases hopt :
      Discharge.Hubcap.intAsNat?
        (Int.ofNat (Discharge.sortDrules p rf.sourceDrules).nbForcedDrules -
          Int.ofNat (Discharge.sortDrules p rf.targetDrules).nbForcedDrules +
            b) with
  | none =>
      have hfalse : False := by
        rw [hopt] at hcheckRaw
        simp at hcheckRaw
      exact False.elim hfalse
  | some nt =>
      have hoptLocal :
          Discharge.Hubcap.intAsNat?
            (Int.ofNat srs.nbForcedDrules -
              Int.ofNat srt.nbForcedDrules + b) = some nt := by
        simpa [srt, srs] using hopt
      have hcheckRec :
          Discharge.Hubcap.checkDbound2Rec Presentation.theRedpart p
              srt.straddlingDrules srs.straddlingDrules [] nt
              (srt.straddlingDrules.length + 2) = true := by
        rw [hopt] at hcheckRaw
        simpa [srt, srs] using hcheckRaw
      have hnt := Discharge.Hubcap.intAsNat?_eq_some hoptLocal
      have hrec :=
        checkDbound2Rec_sound hredpart hG x
          (m := srt.straddlingDrules.length + 2)
          (p := p) (rt := srt.straddlingDrules)
          (rs := srs.straddlingDrules) (ru := []) (nt := nt)
          hcheckRec (by simp) hfit
      have hrecLocal :
          G.dbound2 srt.straddlingDrules srs.straddlingDrules x ≤
            (nt : Int) := by
        simpa using hrec
      have hbudget :
          (Int.ofNat srs.nbForcedDrules -
              Int.ofNat srt.nbForcedDrules + b) = (nt : Int) := hnt.2
      have htarget :
          ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
              (nt : Int) = b := by
        calc
          ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
              (nt : Int)
              = ((srt.nbForcedDrules : Int) -
                  (srs.nbForcedDrules : Int)) +
                (Int.ofNat srs.nbForcedDrules -
                  Int.ofNat srt.nbForcedDrules + b) :=
                congrArg
                  (fun z : Int =>
                    ((srt.nbForcedDrules : Int) -
                      (srs.nbForcedDrules : Int)) + z)
                  hbudget.symm
          _ = b := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hsort']
      calc
        ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
            G.dbound2 srt.straddlingDrules srs.straddlingDrules x
            ≤ ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
              (nt : Int) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hrecLocal
                  ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int))
        _ = b := htarget

theorem check2Dbound2Rec_sound
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample) :
    ∀ {m} (x1 x2 : G.Dart)
      {nhub : Nat} {p1 p2 : Part}
      {rt1 rs1 ru1 rt2 rs2 ru2 : Drules}
      {i nt : Nat},
        i ≤ nhub →
          Discharge.Hubcap.check2Dbound2Rec nhub Presentation.theRedpart
              p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m = true →
            (∀ r ∈ ru1, Part.fitp G x1 r = false) →
              (∀ r ∈ ru2, Part.fitp G x2 r = false) →
                (∀ q : Part,
                  Part.exactFitp G x1 q = true →
                    Part.exactFitp G x2 (Part.rotate i q) = true) →
                  (∀ q : Part,
                    Part.exactFitp G x2 q = true →
                      Part.exactFitp G x1
                        (Part.rotate (nhub - i) q) = true) →
                    Part.exactFitp G x1 p1 = true →
                      Part.exactFitp G x2 p2 = true →
                        G.dbound2 rt1 rs1 x1 +
                          G.dbound2 rt2 rs2 x2 ≤ (nt : Int) := by
  intro m
  induction m with
  | zero =>
      intro x1 x2 nhub p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt
        _hi hcheck _hru1 _hru2 _hrot12 _hrot21 _hfit1 _hfit2
      simp [Discharge.Hubcap.check2Dbound2Rec] at hcheck
  | succ m ih =>
      intro x1 x2 nhub p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt
        hi hcheck hru1 hru2 hrot12 hrot21 hfit1 hfit2
      cases rt1 with
      | nil =>
          cases rt2 with
          | nil =>
              simp [Hypermap.dbound2, Hypermap.dbound1,
                Discharge.countBy]
              omega
          | cons r rt2' =>
              simp [Discharge.Hubcap.check2Dbound2Rec] at hcheck
              have hiSwap : nhub - i ≤ nhub := by omega
              have hrotBack :
                  ∀ q : Part,
                    Part.exactFitp G x1 q = true →
                      Part.exactFitp G x2
                        (Part.rotate (nhub - (nhub - i)) q) = true := by
                intro q hq
                have hdiff : nhub - (nhub - i) = i := by omega
                simpa [hdiff] using hrot12 q hq
              have hswap :=
                ih x2 x1 (nhub := nhub) (p1 := p2) (p2 := p1)
                  (rt1 := r :: rt2') (rs1 := rs2) (ru1 := ru2)
                  (rt2 := []) (rs2 := rs1) (ru2 := ru1)
                  (i := nhub - i) (nt := nt)
                  hiSwap hcheck hru2 hru1 hrot21 hrotBack hfit2 hfit1
              simpa [Hypermap.dbound2, Hypermap.dbound1,
                Discharge.countBy, add_comm] using hswap
      | cons r rt1' =>
          by_cases hshort : rt1'.length + rt2.length < nt
          · have hlen : (r :: rt1').length + rt2.length ≤ nt := by
              simp
              omega
            have htarget1 :
                G.dbound1 (r :: rt1') x1 ≤ (r :: rt1').length :=
              G.dbound1_le_length (r :: rt1') x1
            have htarget2 : G.dbound1 rt2 x2 ≤ rt2.length :=
              G.dbound1_le_length rt2 x2
            have hnat :
                G.dbound1 (r :: rt1') x1 + G.dbound1 rt2 x2 ≤ nt := by
              omega
            have hint :
                (G.dbound1 (r :: rt1') x1 : Int) +
                    (G.dbound1 rt2 x2 : Int) ≤ (nt : Int) := by
              exact_mod_cast hnat
            calc
              G.dbound2 (r :: rt1') rs1 x1 +
                  G.dbound2 rt2 rs2 x2
                  ≤ (G.dbound1 (r :: rt1') x1 : Int) +
                    (G.dbound1 rt2 x2 : Int) := by
                    simp [Hypermap.dbound2]
                    omega
              _ ≤ (nt : Int) := hint
          · simp [Discharge.Hubcap.check2Dbound2Rec, hshort] at hcheck
            rcases hcheck with ⟨hfirst, hrest⟩
            by_cases hrtrue : Part.fitp G x1 r = true
            · let p1' := Part.meet p1 r
              let p2' := Part.rotate i p1'
              have hp1' : Part.exactFitp G x1 p1' = true :=
                Part.exactFitp_meet_of_fitp (G := G) hfit1 hrtrue
              have hp2' : Part.exactFitp G x2 p2' = true := by
                simpa [p1', p2'] using hrot12 p1' hp1'
              have hp1fit : Part.fitp G x1 p1' = true := by
                have hs := hp1'
                simp [Part.exactFitp] at hs
                exact hs.2
              have hp2fit : Part.fitp G x2 p2' = true := by
                have hs := hp2'
                simp [Part.exactFitp] at hs
                exact hs.2
              rcases hfirst with hunfit | hfirst
              · rcases hunfit with hunfit1 | hunfit2
                · rcases Discharge.Hubcap.checkUnfit_eq_true_exists_subset
                      (p := p1') hunfit1 with
                    ⟨u, hu, hcmp⟩
                  have hufit : Part.fitp G x1 u = true :=
                    Part.fitp_of_cmp_eq_subset (G := G) p1' u x1
                      hcmp hp1fit
                  have hufalse := hru1 u hu
                  rw [hufit] at hufalse
                  cases hufalse
                · rcases Discharge.Hubcap.checkUnfit_eq_true_exists_subset
                      (p := p2') hunfit2 with
                    ⟨u, hu, hcmp⟩
                  have hufit : Part.fitp G x2 u = true :=
                    Part.fitp_of_cmp_eq_subset (G := G) p2' u x2
                      hcmp hp2fit
                  have hufalse := hru2 u hu
                  rw [hufit] at hufalse
                  cases hufalse
              ·
                let srt1 := Discharge.sortDrules p1' rt1'
                let srs1 := Discharge.sortDrules p1' rs1
                let srt2 := Discharge.sortDrules p2' rt2
                let srs2 := Discharge.sortDrules p2' rs2
                have hsort1 := G.sortDrules_dbound2_eq hp1fit rt1' rs1
                have hsort1' :
                    G.dbound2 rt1' rs1 x1 =
                      ((srt1.nbForcedDrules : Int) -
                          (srs1.nbForcedDrules : Int)) +
                        G.dbound2 srt1.straddlingDrules
                          srs1.straddlingDrules x1 := by
                  simpa [srt1, srs1] using hsort1
                have hsort2 := G.sortDrules_dbound2_eq hp2fit rt2 rs2
                have hsort2' :
                    G.dbound2 rt2 rs2 x2 =
                      ((srt2.nbForcedDrules : Int) -
                          (srs2.nbForcedDrules : Int)) +
                        G.dbound2 srt2.straddlingDrules
                          srs2.straddlingDrules x2 := by
                  simpa [srt2, srs2] using hsort2
                cases hsub :
                    (Discharge.sortDrules (Part.meet p1 r) rs1).nbForcedDrules +
                        ((Discharge.sortDrules
                              (Part.rotate i (Part.meet p1 r)) rs2).nbForcedDrules +
                          nt) -
                      ((Discharge.sortDrules
                            (Part.meet p1 r) rt1').nbForcedDrules +
                        (Discharge.sortDrules
                          (Part.rotate i (Part.meet p1 r)) rt2).nbForcedDrules) with
                | zero =>
                    simp [hsub] at hfirst
                    have hpfalse := hredpart hG x1 p1' hfirst
                    rw [hp1'] at hpfalse
                    cases hpfalse
                | succ nt' =>
                    simp [hsub] at hfirst
                    have hsub' :
                        srs1.nbForcedDrules +
                            (srs2.nbForcedDrules + nt) -
                          (srt1.nbForcedDrules +
                            srt2.nbForcedDrules) = nt' + 1 := by
                      simpa [p1', p2', srt1, srs1, srt2, srs2] using hsub
                    have hstrad :=
                      ih x1 x2 (nhub := nhub) (p1 := p1') (p2 := p2')
                        (rt1 := srt1.straddlingDrules)
                        (rs1 := srs1.straddlingDrules) (ru1 := ru1)
                        (rt2 := srt2.straddlingDrules)
                        (rs2 := srs2.straddlingDrules) (ru2 := ru2)
                        (i := i) (nt := nt') hi hfirst hru1 hru2
                        hrot12 hrot21 hp1' hp2'
                    have htailBound :
                        G.dbound2 rt1' rs1 x1 +
                            G.dbound2 rt2 rs2 x2 ≤
                          (((srt1.nbForcedDrules : Int) -
                              (srs1.nbForcedDrules : Int)) +
                            ((srt2.nbForcedDrules : Int) -
                              (srs2.nbForcedDrules : Int))) +
                            (nt' : Int) := by
                      rw [hsort1', hsort2']
                      omega
                    have hbudget :
                        (1 : Int) +
                            ((((srt1.nbForcedDrules : Int) -
                                (srs1.nbForcedDrules : Int)) +
                              ((srt2.nbForcedDrules : Int) -
                                (srs2.nbForcedDrules : Int))) +
                              (nt' : Int)) ≤
                          (nt : Int) := by
                      omega
                    have hhead :
                        G.dbound2 (r :: rt1') rs1 x1 =
                          1 + G.dbound2 rt1' rs1 x1 := by
                      simp [Hypermap.dbound2, Hypermap.dbound1,
                        Discharge.countBy, hrtrue]
                      omega
                    calc
                      G.dbound2 (r :: rt1') rs1 x1 +
                          G.dbound2 rt2 rs2 x2 =
                            1 + (G.dbound2 rt1' rs1 x1 +
                              G.dbound2 rt2 rs2 x2) := by
                            rw [hhead]
                            omega
                      _ ≤ 1 +
                          ((((srt1.nbForcedDrules : Int) -
                              (srs1.nbForcedDrules : Int)) +
                            ((srt2.nbForcedDrules : Int) -
                              (srs2.nbForcedDrules : Int))) +
                            (nt' : Int)) := by omega
                      _ ≤ (nt : Int) := hbudget
            · have hrfalse : Part.fitp G x1 r = false := by
                cases h : Part.fitp G x1 r with
                | false => rfl
                | true => exact False.elim (hrtrue h)
              have hru1' : ∀ r' ∈ r :: ru1, Part.fitp G x1 r' = false := by
                intro r' hr'
                rcases List.mem_cons.mp hr' with hEq | hmem
                · simpa [hEq] using hrfalse
                · exact hru1 r' hmem
              have htail :=
                ih x1 x2 (nhub := nhub) (p1 := p1) (p2 := p2)
                  (rt1 := rt1') (rs1 := rs1) (ru1 := r :: ru1)
                  (rt2 := rt2) (rs2 := rs2) (ru2 := ru2)
                  (i := i) (nt := nt) hi hrest hru1' hru2
                  hrot12 hrot21 hfit1 hfit2
              simpa [Hypermap.dbound2, Hypermap.dbound1,
                Discharge.countBy, hrfalse, add_assoc] using htail

theorem check2Dbound2_sound
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample)
    (x1 x2 : G.Dart) {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p1 : Part} {i : Nat} {b : Int}
    (hi : i ≤ nhub)
    (hcheck :
      Discharge.Hubcap.check2Dbound2 Presentation.theRedpart
        rf p1 i b = true)
    (hrot12 : ∀ q : Part,
      Part.exactFitp G x1 q = true →
        Part.exactFitp G x2 (Part.rotate i q) = true)
    (hrot21 : ∀ q : Part,
      Part.exactFitp G x2 q = true →
        Part.exactFitp G x1 (Part.rotate (nhub - i) q) = true)
    (hfit1 : Part.exactFitp G x1 p1 = true) :
    G.dbound2 rf.targetDrules rf.sourceDrules x1 +
      G.dbound2 rf.targetDrules rf.sourceDrules x2 ≤ b := by
  let p2 := Part.rotate i p1
  let srt1 := Discharge.sortDrules p1 rf.targetDrules
  let srs1 := Discharge.sortDrules p1 rf.sourceDrules
  let srt2 := Discharge.sortDrules p2 rf.targetDrules
  let srs2 := Discharge.sortDrules p2 rf.sourceDrules
  have hfit2 : Part.exactFitp G x2 p2 = true := by
    simpa [p2] using hrot12 p1 hfit1
  have hp1fit : Part.fitp G x1 p1 = true := by
    have hs := hfit1
    simp [Part.exactFitp] at hs
    exact hs.2
  have hp2fit : Part.fitp G x2 p2 = true := by
    have hs := hfit2
    simp [Part.exactFitp] at hs
    exact hs.2
  have hsort1 := G.sortDrules_dbound2_eq hp1fit
    rf.targetDrules rf.sourceDrules
  have hsort1' :
      G.dbound2 rf.targetDrules rf.sourceDrules x1 =
        ((srt1.nbForcedDrules : Int) - (srs1.nbForcedDrules : Int)) +
          G.dbound2 srt1.straddlingDrules srs1.straddlingDrules x1 := by
    simpa [srt1, srs1] using hsort1
  have hsort2 := G.sortDrules_dbound2_eq hp2fit
    rf.targetDrules rf.sourceDrules
  have hsort2' :
      G.dbound2 rf.targetDrules rf.sourceDrules x2 =
        ((srt2.nbForcedDrules : Int) - (srs2.nbForcedDrules : Int)) +
          G.dbound2 srt2.straddlingDrules srs2.straddlingDrules x2 := by
    simpa [srt2, srs2] using hsort2
  have hcheckRaw :
      (match
          Discharge.Hubcap.intAsNat?
            (Int.ofNat
                ((Discharge.sortDrules p1 rf.sourceDrules).nbForcedDrules +
                  (Discharge.sortDrules
                    (Part.rotate i p1) rf.sourceDrules).nbForcedDrules) -
              Int.ofNat
                ((Discharge.sortDrules p1 rf.targetDrules).nbForcedDrules +
                  (Discharge.sortDrules
                    (Part.rotate i p1) rf.targetDrules).nbForcedDrules) +
                b) with
        | none => false
        | some nt =>
            Discharge.Hubcap.check2Dbound2Rec nhub Presentation.theRedpart
              p1 (Part.rotate i p1)
              (Discharge.sortDrules p1 rf.targetDrules).straddlingDrules
              (Discharge.sortDrules p1 rf.sourceDrules).straddlingDrules []
              (Discharge.sortDrules
                (Part.rotate i p1) rf.targetDrules).straddlingDrules
              (Discharge.sortDrules
                (Part.rotate i p1) rf.sourceDrules).straddlingDrules []
              i nt
              ((Discharge.sortDrules p1 rf.targetDrules).straddlingDrules.length +
                ((Discharge.sortDrules
                  (Part.rotate i p1) rf.targetDrules).straddlingDrules.length +
                  3))) = true := by
    simpa [Discharge.Hubcap.check2Dbound2] using hcheck
  cases hopt :
      Discharge.Hubcap.intAsNat?
        (Int.ofNat
            ((Discharge.sortDrules p1 rf.sourceDrules).nbForcedDrules +
              (Discharge.sortDrules
                (Part.rotate i p1) rf.sourceDrules).nbForcedDrules) -
          Int.ofNat
            ((Discharge.sortDrules p1 rf.targetDrules).nbForcedDrules +
              (Discharge.sortDrules
                (Part.rotate i p1) rf.targetDrules).nbForcedDrules) +
            b) with
  | none =>
      have hfalse : False := by
        rw [hopt] at hcheckRaw
        simp at hcheckRaw
      exact False.elim hfalse
  | some nt =>
      have hoptLocal :
          Discharge.Hubcap.intAsNat?
            (Int.ofNat (srs1.nbForcedDrules + srs2.nbForcedDrules) -
              Int.ofNat (srt1.nbForcedDrules + srt2.nbForcedDrules) + b) =
              some nt := by
        simpa [p2, srt1, srs1, srt2, srs2] using hopt
      have hcheckRec :
          Discharge.Hubcap.check2Dbound2Rec nhub Presentation.theRedpart
              p1 p2 srt1.straddlingDrules srs1.straddlingDrules []
              srt2.straddlingDrules srs2.straddlingDrules []
              i nt
              (srt1.straddlingDrules.length +
                (srt2.straddlingDrules.length + 3)) = true := by
        rw [hopt] at hcheckRaw
        simpa [p2, srt1, srs1, srt2, srs2] using hcheckRaw
      have hnt := Discharge.Hubcap.intAsNat?_eq_some hoptLocal
      have hrec :=
        check2Dbound2Rec_sound hredpart hG x1 x2
          (nhub := nhub) (p1 := p1) (p2 := p2)
          (rt1 := srt1.straddlingDrules)
          (rs1 := srs1.straddlingDrules) (ru1 := [])
          (rt2 := srt2.straddlingDrules)
          (rs2 := srs2.straddlingDrules) (ru2 := [])
          (i := i) (nt := nt)
          hi hcheckRec (by simp) (by simp) hrot12 hrot21 hfit1 hfit2
      have hrecLocal :
          G.dbound2 srt1.straddlingDrules srs1.straddlingDrules x1 +
            G.dbound2 srt2.straddlingDrules srs2.straddlingDrules x2 ≤
              (nt : Int) := by
        simpa using hrec
      have hbudget :
          (Int.ofNat (srs1.nbForcedDrules + srs2.nbForcedDrules) -
              Int.ofNat (srt1.nbForcedDrules + srt2.nbForcedDrules) + b) =
            (nt : Int) := hnt.2
      have htarget :
          (((srt1.nbForcedDrules : Int) - (srs1.nbForcedDrules : Int)) +
            ((srt2.nbForcedDrules : Int) - (srs2.nbForcedDrules : Int))) +
              (nt : Int) = b := by
        calc
          (((srt1.nbForcedDrules : Int) - (srs1.nbForcedDrules : Int)) +
            ((srt2.nbForcedDrules : Int) - (srs2.nbForcedDrules : Int))) +
              (nt : Int)
              =
            (((srt1.nbForcedDrules : Int) - (srs1.nbForcedDrules : Int)) +
              ((srt2.nbForcedDrules : Int) - (srs2.nbForcedDrules : Int))) +
                (Int.ofNat (srs1.nbForcedDrules + srs2.nbForcedDrules) -
                  Int.ofNat (srt1.nbForcedDrules + srt2.nbForcedDrules) +
                    b) :=
                congrArg
                  (fun z : Int =>
                    (((srt1.nbForcedDrules : Int) -
                        (srs1.nbForcedDrules : Int)) +
                      ((srt2.nbForcedDrules : Int) -
                        (srs2.nbForcedDrules : Int))) + z)
                  hbudget.symm
          _ = b := by
            simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm]
      rw [hsort1', hsort2']
      calc
        ((srt1.nbForcedDrules : Int) - (srs1.nbForcedDrules : Int)) +
              G.dbound2 srt1.straddlingDrules srs1.straddlingDrules x1 +
            (((srt2.nbForcedDrules : Int) - (srs2.nbForcedDrules : Int)) +
              G.dbound2 srt2.straddlingDrules srs2.straddlingDrules x2)
            ≤ (((srt1.nbForcedDrules : Int) -
                (srs1.nbForcedDrules : Int)) +
              ((srt2.nbForcedDrules : Int) -
                (srs2.nbForcedDrules : Int))) +
              (nt : Int) := by
              omega
        _ = b := htarget

theorem check2Dbound2_sound_face_iter
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample)
    {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p : Part} {i : Nat} {b : Int} {x : G.Dart}
    (hi : i ≤ nhub) (hx : G.arity x = nhub)
    (hcheck :
      Discharge.Hubcap.check2Dbound2 Presentation.theRedpart
        rf p i b = true)
    (hfit : Part.exactFitp G x p = true) :
    G.dbound2 rf.targetDrules rf.sourceDrules x +
      G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[i] x) ≤ b :=
  check2Dbound2_sound hredpart hG x
    ((G.face : G.Dart → G.Dart)^[i] x) rf hi hcheck
    (fun _ hq =>
      Part.exactFitp_face_iter_rotate_of_arity_eq
        (G := G) hi hx hq)
    (fun _ hq =>
      Part.exactFitp_face_iter_reverse_rotate_of_arity_eq
        (G := G) hi hx hq)
    hfit

theorem checkDbound2_sound_hubcap_rot
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample)
    {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p : Part} {j : Nat} {b : Int} {x : G.Dart}
    (hj : j < nhub) (h2 : 2 ≤ nhub) (hsize : p.size = nhub)
    (hcheck :
      Discharge.Hubcap.checkDbound2 Presentation.theRedpart
        rf (Discharge.Hubcap.rot nhub j p) b = true)
    (hfit : Part.exactFitp G x p = true) :
    G.dbound2 rf.targetDrules rf.sourceDrules
      ((G.face : G.Dart → G.Dart)^[j] (G.invFace2 x)) ≤ b := by
  have hrotFit :
      Part.exactFitp G
        ((G.face : G.Dart → G.Dart)^[j] (G.invFace2 x))
        (Discharge.Hubcap.rot nhub j p) = true :=
    Discharge.Hubcap.exactFitp_rot_of_exactFitp
      (G := G) hj h2 hsize hfit
  exact checkDbound2_sound hredpart hG
    ((G.face : G.Dart → G.Dart)^[j] (G.invFace2 x))
    rf hcheck hrotFit

theorem check2Dbound2_sound_hubcap_rot
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample)
    {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p : Part} {j1 j2 : Nat} {b : Int} {x : G.Dart}
    (hj1 : j1 < nhub) (hj2 : j2 < nhub)
    (h2 : 2 ≤ nhub) (hsize : p.size = nhub)
    (hcheck :
      Discharge.Hubcap.check2Dbound2 Presentation.theRedpart
        rf (Discharge.Hubcap.rot nhub j1 p)
        (Discharge.Hubcap.hubSubn nhub j2 j1) b = true)
    (hfit : Part.exactFitp G x p = true) :
    G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[j1] (G.invFace2 x)) +
      G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[j2] (G.invFace2 x)) ≤ b := by
  have hs := hfit
  simp [Part.exactFitp] at hs
  have hx : G.arity x = nhub := hs.1.trans hsize
  have hxInv : G.arity (G.invFace2 x) = nhub := by
    simpa [hx] using G.arity_invFace2 x
  have hx1 :
      G.arity ((G.face : G.Dart → G.Dart)^[j1] (G.invFace2 x)) =
        nhub := by
    simpa [hxInv] using
      Hypermap.arity_face_iter (G := G) j1 (G.invFace2 x)
  have hrotFit :
      Part.exactFitp G
        ((G.face : G.Dart → G.Dart)^[j1] (G.invFace2 x))
        (Discharge.Hubcap.rot nhub j1 p) = true :=
    Discharge.Hubcap.exactFitp_rot_of_exactFitp
      (G := G) hj1 h2 hsize hfit
  have hi :
      Discharge.Hubcap.hubSubn nhub j2 j1 ≤ nhub :=
    Discharge.Hubcap.hubSubn_le (nhub := nhub) (i := j2)
      (j := j1) hj2
  have hbound :=
    check2Dbound2_sound_face_iter hredpart hG rf
      (p := Discharge.Hubcap.rot nhub j1 p)
      (i := Discharge.Hubcap.hubSubn nhub j2 j1)
      (b := b)
      (x := (G.face : G.Dart → G.Dart)^[j1] (G.invFace2 x))
      hi hx1 hcheck hrotFit
  have hpoint :
      (G.face : G.Dart → G.Dart)^[Discharge.Hubcap.hubSubn nhub j2 j1]
          ((G.face : G.Dart → G.Dart)^[j1] (G.invFace2 x)) =
        (G.face : G.Dart → G.Dart)^[j2] (G.invFace2 x) :=
    Discharge.Hubcap.face_iter_hubSubn
      (G := G) (nhub := nhub) (i := j2) (j := j1)
      hj1 (G.invFace2 x) hxInv
  simpa [hpoint] using hbound

theorem hubcap_bounds_of_fit
    (hredpart : Presentation.RedpartSound.{u})
    {G : Hypermap.{u}} (hG : G.MinimalCounterexample)
    {nhub : Nat} (rf : Discharge.DruleFork nhub)
    {p : Part} {x : G.Dart}
    (hsize : p.size = nhub) (h2 : 2 ≤ nhub)
    (hfit : Part.exactFitp G x p = true) :
    ∀ {hc : Discharge.Hubcap} {v : List Nat},
      v.length = nhub →
        (∀ k : Nat, (Discharge.Hubcap.tally hc).getD k 0 ≤
          v.getD k 0) →
          Discharge.Hubcap.fit nhub Presentation.theRedpart rf p hc = true →
            Discharge.Hubcap.Bounds G rf (G.invFace2 x) hc := by
  intro hc
  induction hc with
  | Hubcap0 =>
      intro v _hlen _hle _hcheck
      trivial
  | Hubcap1 j b hc ih =>
      intro v hlen hle hcheck
      rcases (by simpa [Discharge.Hubcap.fit] using hcheck) with
        ⟨hhead, htail⟩
      have hpos : 0 < v.getD j 0 := by
        have hfull :
            0 < (Discharge.Hubcap.incrNth
              (Discharge.Hubcap.tally hc) j).getD j 0 := by
          rw [Discharge.Hubcap.getD_incrNth_self]
          omega
        exact lt_of_lt_of_le hfull (hle j)
      have hj : j < nhub := by
        simpa [hlen] using
          Discharge.Hubcap.lt_length_of_getD_pos (v := v) hpos
      have hleTail :
          ∀ k : Nat, (Discharge.Hubcap.tally hc).getD k 0 ≤
            v.getD k 0 :=
        Discharge.Hubcap.forall_getD_le_of_forall_getD_incrNth_le
          (w := Discharge.Hubcap.tally hc) (v := v) (i := j) hle
      exact ⟨
        checkDbound2_sound_hubcap_rot hredpart hG rf
          (p := p) (j := j) (b := b) (x := x)
          hj h2 hsize hhead hfit,
        ih hlen hleTail htail⟩
  | Hubcap2 j1 j2 b hc ih =>
      intro v hlen hle hcheck
      rcases (by simpa [Discharge.Hubcap.fit] using hcheck) with
        ⟨hhead, htail⟩
      have hleMid :
          ∀ k : Nat,
            (Discharge.Hubcap.incrNth
              (Discharge.Hubcap.tally hc) j1).getD k 0 ≤
              v.getD k 0 :=
        Discharge.Hubcap.forall_getD_le_of_forall_getD_incrNth_le
          (w := Discharge.Hubcap.incrNth
            (Discharge.Hubcap.tally hc) j1)
          (v := v) (i := j2) hle
      have hleTail :
          ∀ k : Nat, (Discharge.Hubcap.tally hc).getD k 0 ≤
            v.getD k 0 :=
        Discharge.Hubcap.forall_getD_le_of_forall_getD_incrNth_le
          (w := Discharge.Hubcap.tally hc) (v := v) (i := j1) hleMid
      have hpos1 : 0 < v.getD j1 0 := by
        have hmidPos :
            0 < (Discharge.Hubcap.incrNth
              (Discharge.Hubcap.tally hc) j1).getD j1 0 := by
          rw [Discharge.Hubcap.getD_incrNth_self]
          omega
        have hfullPos :
            0 <
              (Discharge.Hubcap.incrNth
                (Discharge.Hubcap.incrNth
                  (Discharge.Hubcap.tally hc) j1) j2).getD j1 0 :=
          lt_of_lt_of_le hmidPos
            (Discharge.Hubcap.getD_le_getD_incrNth
              (Discharge.Hubcap.incrNth
                (Discharge.Hubcap.tally hc) j1) j2 j1)
        exact lt_of_lt_of_le hfullPos (hle j1)
      have hpos2 : 0 < v.getD j2 0 := by
        have hfullPos :
            0 <
              (Discharge.Hubcap.incrNth
                (Discharge.Hubcap.incrNth
                  (Discharge.Hubcap.tally hc) j1) j2).getD j2 0 := by
          rw [Discharge.Hubcap.getD_incrNth_self]
          omega
        exact lt_of_lt_of_le hfullPos (hle j2)
      have hj1 : j1 < nhub := by
        simpa [hlen] using
          Discharge.Hubcap.lt_length_of_getD_pos (v := v) hpos1
      have hj2 : j2 < nhub := by
        simpa [hlen] using
          Discharge.Hubcap.lt_length_of_getD_pos (v := v) hpos2
      exact ⟨
        check2Dbound2_sound_hubcap_rot hredpart hG rf
          (p := p) (j1 := j1) (j2 := j2) (b := b) (x := x)
          hj1 hj2 h2 hsize hhead hfit,
        ih hlen hleTail htail⟩

end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
