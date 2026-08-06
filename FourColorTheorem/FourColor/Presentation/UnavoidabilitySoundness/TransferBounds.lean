import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.ConversePart12

/-! Pointwise discharge-transfer bounds and hubcap soundness. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

def Dbound2ForkDscoreSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (x : G.Dart) (nhub : Nat),
        G.arity x = nhub →
          ∀ i : Fin nhub,
            G.dbound2
                (Discharge.theDruleFork nhub).targetDrules
                (Discharge.theDruleFork nhub).sourceDrules
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) =
              G.dscore2
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x))

/-- Pointwise transfer bound corresponding to Coq `dbound2_leq`, specialized
to the canonical fork and the face orbit of a hub. -/
def Dbound2ForkPointwiseSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (x : G.Dart) (nhub : Nat),
        G.arity x = nhub →
          ∀ i : Fin nhub,
            G.dscore2
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) ≤
              G.dbound2
                (Discharge.theDruleFork nhub).targetDrules
                (Discharge.theDruleFork nhub).sourceDrules
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x))

/-- Shifted pointwise transfer bound matching Coq `dbound2_leq`: the checker
at a dart bounds the actual score transfer two face steps later.  The face
sum cap then follows by rotating the finite face orbit. -/
def finTwo (n : Nat) (hpos : 0 < n) : Fin n :=
  ⟨2 % n, Nat.mod_lt 2 hpos⟩

def Dbound2ForkShiftedPointwiseSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (x : G.Dart) (nhub : Nat),
        G.arity x = nhub →
          ∀ hpos : 0 < nhub, ∀ i : Fin nhub,
            G.dscore2
                ((G.face : G.Dart → G.Dart)^[
                  (i + finTwo nhub hpos).1] (G.invFace2 x)) ≤
              G.dbound2
                (Discharge.theDruleFork nhub).targetDrules
                (Discharge.theDruleFork nhub).sourceDrules
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x))

theorem dbound2ForkShiftedPointwiseSound_of_conversePartSound
    (hcubic : CubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hconv : ConversePartSound.{u}) :
    Dbound2ForkShiftedPointwiseSound.{u} := by
  intro G hG x nhub hx hpos i
  have hpenta : G.Pentagonal := hpentagonal G hG
  have hge : 5 ≤ nhub := by
    simpa [hx] using Hypermap.arity_ge_five_of_pentagonal hpenta x
  let z : G.Dart := (G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)
  have hz : G.arity z = nhub := by
    simp [z, Hypermap.arity_face_iter, G.arity_invFace2 x, hx]
  have hplain : G.Plain := hG.plain
  have hconvAt : ∀ p ∈ Discharge.theDrules,
      Part.exactFitp G
          (G.invFace2 (G.edge (G.face (G.face z)))) p = true →
        Part.tightFitp G z p.converse = true := by
    intro p _hp hfit
    have htight := hconv hG (hcubic G hG) hpenta hfit
    simpa [z,
      Hypermap.invFace2_edge_edge_face_face_of_plain
        (G := G) hplain z] using htight
  have hle :=
    G.dscore2_face_face_le_dbound2_of_tightConverse
      (x := z) hz hconvAt
  have htwo : (finTwo nhub hpos).1 = 2 := by
    change 2 % nhub = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hshiftVal :
      (i + finTwo nhub hpos).1 = (i.1 + 2) % nhub := by
    rw [Fin.val_add, htwo]
  have hcycle :
      (G.face : G.Dart → G.Dart)^[nhub] (G.invFace2 x) =
        G.invFace2 x := by
    have hxInv : G.arity (G.invFace2 x) = nhub := by
      simpa [hx] using G.arity_invFace2 x
    simpa [hxInv] using G.face_iterate_arity (G.invFace2 x)
  have hpoint :
      G.face (G.face z) =
        (G.face : G.Dart → G.Dart)^[(i + finTwo nhub hpos).1]
          (G.invFace2 x) := by
    have hff :
        G.face (G.face z) =
          (G.face : G.Dart → G.Dart)^[i.1 + 2] (G.invFace2 x) := by
      calc
        G.face (G.face z) =
            (G.face : G.Dart → G.Dart)^[2]
              ((G.face : G.Dart → G.Dart)^[i.1]
                (G.invFace2 x)) := by
              rfl
        _ = (G.face : G.Dart → G.Dart)^[2 + i.1]
              (G.invFace2 x) := by
              rw [Function.iterate_add_apply]
        _ = (G.face : G.Dart → G.Dart)^[i.1 + 2]
              (G.invFace2 x) := by
              rw [Nat.add_comm]
    calc
      G.face (G.face z) =
          (G.face : G.Dart → G.Dart)^[i.1 + 2]
            (G.invFace2 x) := hff
      _ = (G.face : G.Dart → G.Dart)^[(i.1 + 2) % nhub]
            (G.invFace2 x) := by
            exact (Hypermap.face_iter_mod_eq_of_period (G := G)
              (m := i.1 + 2) (n := nhub) (x := G.invFace2 x)
              hcycle).symm
      _ = (G.face : G.Dart → G.Dart)^[
              (i + finTwo nhub hpos).1] (G.invFace2 x) := by
            rw [hshiftVal]
  simpa [Discharge.theDruleFork, z, hpoint] using hle

theorem dbound2ForkShiftedPointwiseSound_of_convPart4_convPart12
    (hcubic : CubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (h4 : ConvPart4Sound.{u}) (h12 : ConvPart12Sound.{u}) :
    Dbound2ForkShiftedPointwiseSound.{u} :=
  dbound2ForkShiftedPointwiseSound_of_conversePartSound
    hcubic hpentagonal (conversePartSound_of_convPart4_convPart12 h4 h12)

theorem dbound2ForkShiftedPointwiseSound_of_minimalGeometry
    (hcubic : CubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u}) :
    Dbound2ForkShiftedPointwiseSound.{u} :=
  dbound2ForkShiftedPointwiseSound_of_conversePartSound
    hcubic hpentagonal conversePartSound

theorem dbound2ForkPointwiseSound_of_dscoreSound
    (hfork : Dbound2ForkDscoreSound.{u}) :
    Dbound2ForkPointwiseSound.{u} := by
  intro G hG x nhub hx i
  rw [hfork hG x nhub hx i]

/-- Semantic cap target matching Coq `dscore_cap2` for the canonical
source/target discharge-rule fork.  This is the exact inequality needed by
the hubcap cover argument. -/
def Dbound2ForkDscoreCapSound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.MinimalCounterexample →
      ∀ (x : G.Dart) (nhub : Nat),
        G.arity x = nhub →
          0 < G.dscore x →
            0 < Discharge.dboundK nhub +
              ∑ i : Fin nhub,
                G.dbound2
                  (Discharge.theDruleFork nhub).targetDrules
                  (Discharge.theDruleFork nhub).sourceDrules
                  ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x))

theorem dbound2ForkDscoreCapSound_of_pointwise
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hpoint : Dbound2ForkPointwiseSound.{u}) :
    Dbound2ForkDscoreCapSound.{u} := by
  intro G hG x nhub hx hscore
  subst nhub
  have hpenta : G.Pentagonal := hpentagonal G hG
  have hge : 5 ≤ G.arity x :=
    Hypermap.arity_ge_five_of_pentagonal hpenta x
  have hdscore :=
    Discharge.dscore_eq_dboundK_add_faceScoreSum_of_arity_ge_five
      G x hge
  rw [hdscore] at hscore
  have hreach : PermReachable G.face (G.invFace2 x) x :=
    permReachable_of_iterate_eq (G.face)
      (n := 2) (by simp [G.face_face_invFace2 x])
  have hface :
      G.faceScoreSum (G.invFace2 x) = G.faceScoreSum x :=
    G.faceScoreSum_eq_of_faceReachable hreach
  have hscoreInv :
      0 < Discharge.dboundK (G.arity x) +
        G.faceScoreSum (G.invFace2 x) := by
    simpa [hface] using hscore
  have hsumLe :
      G.faceScoreSum (G.invFace2 x) ≤
        ∑ i : Fin (G.arity x),
          G.dbound2
            (Discharge.theDruleFork (G.arity x)).targetDrules
            (Discharge.theDruleFork (G.arity x)).sourceDrules
            ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) := by
    rw [G.faceScoreSum_eq_sum_fin_arity (G.invFace2 x)]
    rw [G.arity_invFace2 x]
    exact Finset.sum_le_sum (fun i _hi => hpoint hG x (G.arity x) rfl i)
  have hsumLe' :
      Discharge.dboundK (G.arity x) + G.faceScoreSum (G.invFace2 x) ≤
        Discharge.dboundK (G.arity x) +
          ∑ i : Fin (G.arity x),
            G.dbound2
              (Discharge.theDruleFork (G.arity x)).targetDrules
              (Discharge.theDruleFork (G.arity x)).sourceDrules
              ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsumLe (Discharge.dboundK (G.arity x))
  exact lt_of_lt_of_le hscoreInv hsumLe'

theorem dbound2ForkDscoreCapSound_of_shiftedPointwise
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hpoint : Dbound2ForkShiftedPointwiseSound.{u}) :
    Dbound2ForkDscoreCapSound.{u} := by
  intro G hG x nhub hx hscore
  subst nhub
  have hpenta : G.Pentagonal := hpentagonal G hG
  have hge : 5 ≤ G.arity x :=
    Hypermap.arity_ge_five_of_pentagonal hpenta x
  haveI : NeZero (G.arity x) := ⟨by omega⟩
  let two : Fin (G.arity x) := finTwo (G.arity x) (by omega)
  have hdscore :=
    Discharge.dscore_eq_dboundK_add_faceScoreSum_of_arity_ge_five
      G x hge
  rw [hdscore] at hscore
  have hreach : PermReachable G.face (G.invFace2 x) x :=
    permReachable_of_iterate_eq (G.face)
      (n := 2) (by simp [G.face_face_invFace2 x])
  have hface :
      G.faceScoreSum (G.invFace2 x) = G.faceScoreSum x :=
    G.faceScoreSum_eq_of_faceReachable hreach
  have hscoreInv :
      0 < Discharge.dboundK (G.arity x) +
        G.faceScoreSum (G.invFace2 x) := by
    simpa [hface] using hscore
  have hsumShift :
      G.faceScoreSum (G.invFace2 x) =
        ∑ i : Fin (G.arity x),
          G.dscore2
            ((G.face : G.Dart → G.Dart)^[
              (i + two).1] (G.invFace2 x)) := by
    rw [G.faceScoreSum_eq_sum_fin_arity (G.invFace2 x)]
    rw [G.arity_invFace2 x]
    exact (Fintype.sum_equiv
      (Equiv.addRight two)
      (fun i : Fin (G.arity x) =>
        G.dscore2
          ((G.face : G.Dart → G.Dart)^[
            ((Equiv.addRight two) i).1] (G.invFace2 x)))
      (fun i : Fin (G.arity x) =>
        G.dscore2
          ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)))
      (fun _ => rfl)).symm
  have hsumLe :
      G.faceScoreSum (G.invFace2 x) ≤
        ∑ i : Fin (G.arity x),
          G.dbound2
            (Discharge.theDruleFork (G.arity x)).targetDrules
            (Discharge.theDruleFork (G.arity x)).sourceDrules
            ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) := by
    rw [hsumShift]
    exact Finset.sum_le_sum (fun i _hi =>
      hpoint hG x (G.arity x) rfl (by omega) i)
  have hsumLe' :
      Discharge.dboundK (G.arity x) + G.faceScoreSum (G.invFace2 x) ≤
        Discharge.dboundK (G.arity x) +
          ∑ i : Fin (G.arity x),
            G.dbound2
              (Discharge.theDruleFork (G.arity x)).targetDrules
              (Discharge.theDruleFork (G.arity x)).sourceDrules
              ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsumLe (Discharge.dboundK (G.arity x))
  exact lt_of_lt_of_le hscoreInv hsumLe'

theorem hubcapSound_of_pentagonal_and_dbound2ForkDscore
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hfork : Dbound2ForkDscoreSound.{u})
    (hredpart : Presentation.RedpartSound.{u}) :
    Presentation.HubcapSound.{u} := by
  intro G hG p hc hcover hcheck x hscore
  cases hexact : Part.exactFitp G x p with
  | false =>
      rfl
  | true =>
      exfalso
      rcases Discharge.Hubcap.cover_eq_true hcover with
        ⟨hlen, hzero, hcoverRec⟩
      have hs := hexact
      simp [Part.exactFitp] at hs
      have harity : G.arity x = p.size := hs.1
      have hpenta : G.Pentagonal := hpentagonal G hG
      have hgeArity : 5 ≤ G.arity x :=
        Hypermap.arity_ge_five_of_pentagonal hpenta x
      have hgeSize : 5 ≤ p.size := by
        simpa [harity] using hgeArity
      have h2 : 2 ≤ p.size := by omega
      have hleSelf :
          ∀ k : Nat,
            (Discharge.Hubcap.tally hc).getD k 0 ≤
              (Discharge.Hubcap.tally hc).getD k 0 :=
        fun _ => le_rfl
      have hbounds :
          Discharge.Hubcap.Bounds G (Discharge.theDruleFork p.size)
            (G.invFace2 x) hc :=
        hubcap_bounds_of_fit hredpart hG
          (Discharge.theDruleFork p.size)
          (p := p) (x := x) rfl h2 hexact
          (v := Discharge.Hubcap.tally hc)
          hlen hleSelf hcheck
      have hweighted :
          Discharge.dboundK p.size * 2 - 1 +
              Discharge.Hubcap.weightedDbound2Sum G
                (Discharge.theDruleFork p.size) (G.invFace2 x)
                (Discharge.Hubcap.tally hc) (Discharge.Hubcap.tally hc) ≤
            0 :=
        Discharge.Hubcap.coverRec_weightedDbound2Sum_le
          G (Discharge.theDruleFork p.size) (G.invFace2 x)
          hlen hcoverRec hbounds hleSelf
      have hxInv : G.arity (G.invFace2 x) = p.size := by
        simpa [harity] using G.arity_invFace2 x
      have hweightedEq :
          Discharge.Hubcap.weightedDbound2Sum G
              (Discharge.theDruleFork p.size) (G.invFace2 x)
              (Discharge.Hubcap.tally hc) (Discharge.Hubcap.tally hc) =
            2 * G.faceScoreSum (G.invFace2 x) :=
        Discharge.Hubcap.weightedDbound2Sum_self_eq_two_faceScoreSum
          (G := G) (rf := Discharge.theDruleFork p.size)
          (x := G.invFace2 x) hxInv hlen hzero
          (fun i => hfork hG x p.size harity i)
      rw [hweightedEq] at hweighted
      have hreach : PermReachable G.face (G.invFace2 x) x :=
        permReachable_of_iterate_eq (G.face)
          (n := 2) (by simp [G.face_face_invFace2 x])
      have hface :
          G.faceScoreSum (G.invFace2 x) = G.faceScoreSum x :=
        G.faceScoreSum_eq_of_faceReachable hreach
      rw [hface] at hweighted
      rw [← harity] at hweighted
      have hdscore :=
        Discharge.dscore_eq_dboundK_add_faceScoreSum_of_arity_ge_five
          G x hgeArity
      rw [hdscore] at hscore
      omega

theorem hubcapSound_of_pentagonal_and_dbound2ForkDscoreCap
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hcap : Dbound2ForkDscoreCapSound.{u})
    (hredpart : Presentation.RedpartSound.{u}) :
    Presentation.HubcapSound.{u} := by
  intro G hG p hc hcover hcheck x hscore
  cases hexact : Part.exactFitp G x p with
  | false =>
      rfl
  | true =>
      exfalso
      rcases Discharge.Hubcap.cover_eq_true hcover with
        ⟨hlen, hzero, hcoverRec⟩
      have hs := hexact
      simp [Part.exactFitp] at hs
      have harity : G.arity x = p.size := hs.1
      have hpenta : G.Pentagonal := hpentagonal G hG
      have hgeArity : 5 ≤ G.arity x :=
        Hypermap.arity_ge_five_of_pentagonal hpenta x
      have hgeSize : 5 ≤ p.size := by
        simpa [harity] using hgeArity
      have h2 : 2 ≤ p.size := by omega
      have hleSelf :
          ∀ k : Nat,
            (Discharge.Hubcap.tally hc).getD k 0 ≤
              (Discharge.Hubcap.tally hc).getD k 0 :=
        fun _ => le_rfl
      have hbounds :
          Discharge.Hubcap.Bounds G (Discharge.theDruleFork p.size)
            (G.invFace2 x) hc :=
        hubcap_bounds_of_fit hredpart hG
          (Discharge.theDruleFork p.size)
          (p := p) (x := x) rfl h2 hexact
          (v := Discharge.Hubcap.tally hc)
          hlen hleSelf hcheck
      have hweighted :
          Discharge.dboundK p.size * 2 - 1 +
              Discharge.Hubcap.weightedDbound2Sum G
                (Discharge.theDruleFork p.size) (G.invFace2 x)
                (Discharge.Hubcap.tally hc) (Discharge.Hubcap.tally hc) ≤
            0 :=
        Discharge.Hubcap.coverRec_weightedDbound2Sum_le
          G (Discharge.theDruleFork p.size) (G.invFace2 x)
          hlen hcoverRec hbounds hleSelf
      have hweightedEq :
          Discharge.Hubcap.weightedDbound2Sum G
              (Discharge.theDruleFork p.size) (G.invFace2 x)
              (Discharge.Hubcap.tally hc) (Discharge.Hubcap.tally hc) =
            2 * ∑ i : Fin p.size,
              G.dbound2
                (Discharge.theDruleFork p.size).targetDrules
                (Discharge.theDruleFork p.size).sourceDrules
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) :=
        Discharge.Hubcap.weightedDbound2Sum_self_eq_two_sum
          (G := G) (rf := Discharge.theDruleFork p.size)
          (x := G.invFace2 x) (hlen := hlen) (hzero := hzero)
      rw [hweightedEq] at hweighted
      have hcapPos :
          0 < Discharge.dboundK p.size +
            ∑ i : Fin p.size,
              G.dbound2
                (Discharge.theDruleFork p.size).targetDrules
                (Discharge.theDruleFork p.size).sourceDrules
                ((G.face : G.Dart → G.Dart)^[i.1] (G.invFace2 x)) :=
        hcap hG x p.size harity hscore
      omega

theorem hubcapSound_of_pentagonal_and_dbound2ForkPointwise
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hpoint : Dbound2ForkPointwiseSound.{u})
    (hredpart : Presentation.RedpartSound.{u}) :
    Presentation.HubcapSound.{u} :=
  hubcapSound_of_pentagonal_and_dbound2ForkDscoreCap
    hpentagonal
    (dbound2ForkDscoreCapSound_of_pointwise hpentagonal hpoint)
    hredpart

theorem hubcapSound_of_pentagonal_and_dbound2ForkShiftedPointwise
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hpoint : Dbound2ForkShiftedPointwiseSound.{u})
    (hredpart : Presentation.RedpartSound.{u}) :
    Presentation.HubcapSound.{u} :=
  hubcapSound_of_pentagonal_and_dbound2ForkDscoreCap
    hpentagonal
    (dbound2ForkDscoreCapSound_of_shiftedPointwise hpentagonal hpoint)
    hredpart

theorem hubcapSound_of_minimalGeometry
    (hcubic : CubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hredpart : Presentation.RedpartSound.{u}) :
    Presentation.HubcapSound.{u} :=
  hubcapSound_of_pentagonal_and_dbound2ForkShiftedPointwise
    hpentagonal
    (dbound2ForkShiftedPointwiseSound_of_minimalGeometry
      hcubic hpentagonal)
    hredpart

theorem succeedsIn_of_hubcapCheck_minimalGeometry
    (hcubic : CubicMinimalCounterexamples.{u})
    (hpentagonal : PentagonalMinimalCounterexamples.{u})
    (hredpart : Presentation.RedpartSound.{u})
    {g : Presentation.CheckGoal} {hc : Discharge.Hubcap}
    (hcheck : Presentation.hubcapCheck g hc = true) :
    Presentation.SucceedsIn.{u} g.p0 g.p :=
  Presentation.succeedsIn_of_hubcapCheck_sound
    (hubcapSound_of_minimalGeometry hcubic hpentagonal hredpart)
    hcheck


end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
