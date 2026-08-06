import FourColorTheorem.FourColor.Discharging.Rules.MirrorScore

/-! Source and target bounds for local discharging rules. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Number of discharge rules from a list fitting at a dart.  Coq `dbound1`. -/
noncomputable def dbound1 (rs : Drules) (x : G.Dart) : Nat :=
  Discharge.countBy (fun p => Part.fitp G x p) rs

theorem dscore1_face_face_eq_dbound1_source
    {nhub : Nat} {x : G.Dart}
    (hx : G.arity x = nhub) :
    G.dscore1 (G.face (G.face x)) =
      G.dbound1
        (Discharge.pickSourceDrules nhub Discharge.theDrules) x := by
  unfold dscore1 dbound1 Discharge.pickSourceDrules
  simp [Discharge.countBy_filter,
    exactFitp_eq_size_filter_fitp_of_arity_eq (G := G) hx]

theorem dscore1_eq_dbound1_source_invFace2 (x : G.Dart) :
    G.dscore1 x =
      G.dbound1
        (Discharge.pickSourceDrules
          (G.arity (G.invFace2 x)) Discharge.theDrules)
        (G.invFace2 x) := by
  conv_lhs => rw [← G.face_face_invFace2 x]
  exact G.dscore1_face_face_eq_dbound1_source rfl

theorem dscore1_eq_zero_of_invFace2_not_Pr58 {x : G.Dart}
    (hx : PRange.Pr58 (G.arity (G.invFace2 x)) = false) :
    G.dscore1 x = 0 := by
  rw [G.dscore1_eq_dbound1_source_invFace2 x]
  rw [Discharge.pickSourceDrules_eq_nil_of_not_Pr58 hx]
  rfl

/-- Difference between target and source fit counts.  Coq `dbound2`. -/
noncomputable def dbound2 (rt rs : Drules) (x : G.Dart) : Int :=
  (G.dbound1 rt x : Int) - (G.dbound1 rs x : Int)

@[simp]
theorem dbound1_nil (x : G.Dart) :
    G.dbound1 [] x = 0 :=
  rfl

@[simp]
theorem dbound1_cons (r : Part) (rs : Drules) (x : G.Dart) :
    G.dbound1 (r :: rs) x =
      (if Part.fitp G x r then 1 else 0) + G.dbound1 rs x :=
  rfl

theorem countBy_exactFitp_le_dbound1_pickTargetDrules
    {nhub : Nat} {x y : G.Dart} {rs : Drules}
    (hx : G.arity x = nhub)
    (hconv : ∀ p ∈ rs,
      Part.exactFitp G y p = true →
        Part.tightFitp G x p.converse = true) :
    Discharge.countBy (fun p => Part.exactFitp G y p) rs ≤
      G.dbound1 (Discharge.pickTargetDrules nhub rs) x := by
  induction rs with
  | nil =>
      simp [Discharge.countBy, Hypermap.dbound1,
        Discharge.pickTargetDrules]
  | cons p ps ih =>
      have hconvTail : ∀ q ∈ ps,
          Part.exactFitp G y q = true →
            Part.tightFitp G x q.converse = true := by
        intro q hq hfit
        exact hconv q (by simp [hq]) hfit
      have htail := ih hconvTail
      simp only [Discharge.countBy, Discharge.pickTargetDrules]
      cases hcp : p.converse with
      | mk u p' =>
          by_cases hexact : Part.exactFitp G y p = true
          · have htight := hconv p (by simp) hexact
            simp [Part.tightFitp, hcp, hx] at htight
            rcases htight with ⟨hu, hpfit⟩
            simpa [hexact, hcp, hu, hpfit] using
              Nat.succ_le_succ htail
          · have hexactFalse : Part.exactFitp G y p = false := by
              cases h : Part.exactFitp G y p with
              | false => rfl
              | true => exact False.elim (hexact h)
            by_cases hu : u nhub = true
            · by_cases hpfit : Part.fitp G x p' = true
              · have hle :
                    Discharge.countBy
                        (fun p => Part.exactFitp G y p) ps ≤
                      1 + G.dbound1
                        (Discharge.pickTargetDrules nhub ps) x := by
                  omega
                simpa [hexactFalse, hcp, hu, hpfit] using hle
              · have hpfitFalse : Part.fitp G x p' = false := by
                  cases h : Part.fitp G x p' with
                  | false => rfl
                  | true => exact False.elim (hpfit h)
                simpa [hexactFalse, hcp, hu, hpfitFalse] using htail
            · have huFalse : u nhub = false := by
                cases h : u nhub with
                | false => rfl
                | true => exact False.elim (hu h)
              simpa [hexactFalse, hcp, huFalse] using htail

theorem dscore2_face_face_le_dbound2_of_tightConverse
    {nhub : Nat} {x : G.Dart}
    (hx : G.arity x = nhub)
    (hconv : ∀ p ∈ Discharge.theDrules,
      Part.exactFitp G
          (G.invFace2 (G.edge (G.face (G.face x)))) p = true →
        Part.tightFitp G x p.converse = true) :
    G.dscore2 (G.face (G.face x)) ≤
      G.dbound2
        (Discharge.pickTargetDrules nhub Discharge.theDrules)
        (Discharge.pickSourceDrules nhub Discharge.theDrules) x := by
  have htargetNat :=
    G.countBy_exactFitp_le_dbound1_pickTargetDrules
      (rs := Discharge.theDrules)
      (x := x) (y := G.invFace2 (G.edge (G.face (G.face x))))
      hx hconv
  have htargetInt :
      G.dscore1 (G.edge (G.face (G.face x))) ≤
        (G.dbound1
          (Discharge.pickTargetDrules nhub Discharge.theDrules) x :
            Int) := by
    unfold dscore1
    exact Int.ofNat_le.mpr htargetNat
  have hsource := G.dscore1_face_face_eq_dbound1_source (x := x) hx
  rw [dscore2, dbound2]
  rw [hsource]
  omega

theorem dbound1_eq_zero_of_forall_fitp_false
    {rs : Drules} {x : G.Dart}
    (h : ∀ r ∈ rs, Part.fitp G x r = false) :
    G.dbound1 rs x = 0 := by
  induction rs with
  | nil =>
      rfl
  | cons r rs ih =>
      have hr : Part.fitp G x r = false := h r (by simp)
      have hrs : ∀ r' ∈ rs, Part.fitp G x r' = false := by
        intro r' hr'
        exact h r' (by simp [hr'])
      change (if Part.fitp G x r then 1 else 0) + G.dbound1 rs x = 0
      rw [hr, ih hrs]
      simp

theorem sortDrulesRec_dbound1_eq
    {p : Part} {x : G.Dart}
    (hp : Part.fitp G x p = true) :
    ∀ (todo acc : Drules) (n : Nat),
      let s := Discharge.sortDrulesRec p n acc todo
      s.nbForcedDrules + G.dbound1 s.straddlingDrules x =
        n + G.dbound1 acc x + G.dbound1 todo x := by
  intro todo
  induction todo with
  | nil =>
      intro acc n
      simp [Discharge.sortDrulesRec, dbound1, Discharge.countBy]
  | cons r todo ih =>
      intro acc n
      simp only [Discharge.sortDrulesRec]
      cases hcmp : Part.cmp p r
      · have hr : Part.fitp G x r = false :=
          Part.fitp_false_of_cmp_eq_disjoint (G := G) hcmp hp
        have h := ih acc n
        simp [hr, dbound1, Discharge.countBy, Nat.add_comm,
          Nat.add_left_comm] at h ⊢
        omega
      · have h := ih (r :: acc) n
        simp [dbound1, Discharge.countBy, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] at h ⊢
        omega
      · have hr : Part.fitp G x r = true :=
          Part.fitp_of_cmp_eq_subset (G := G) p r x hcmp hp
        have h := ih acc (n + 1)
        simp [hr, dbound1, Discharge.countBy, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] at h ⊢
        omega

theorem sortDrules_dbound1_eq
    {p : Part} {x : G.Dart}
    (hp : Part.fitp G x p = true) (rs : Drules) :
    let s := Discharge.sortDrules p rs
    s.nbForcedDrules + G.dbound1 s.straddlingDrules x =
      G.dbound1 rs x := by
  have h := G.sortDrulesRec_dbound1_eq hp rs [] 0
  simpa [Discharge.sortDrules, dbound1, Discharge.countBy] using h

theorem sortDrules_dbound2_eq
    {p : Part} {x : G.Dart}
    (hp : Part.fitp G x p = true) (rt rs : Drules) :
    let srt := Discharge.sortDrules p rt
    let srs := Discharge.sortDrules p rs
    G.dbound2 rt rs x =
      ((srt.nbForcedDrules : Int) - (srs.nbForcedDrules : Int)) +
        G.dbound2 srt.straddlingDrules srs.straddlingDrules x := by
  have ht := G.sortDrules_dbound1_eq hp rt
  have hs := G.sortDrules_dbound1_eq hp rs
  simp [dbound2]
  rw [← ht, ← hs]
  omega

theorem dbound1_le_length (rs : Drules) (x : G.Dart) :
    G.dbound1 rs x ≤ rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      change
        (if Part.fitp G x r then 1 else 0) +
            Discharge.countBy (fun p => Part.fitp G x p) rs ≤
          (r :: rs).length
      change Discharge.countBy (fun p => Part.fitp G x p) rs ≤ rs.length at ih
      cases Part.fitp G x r <;> simp <;> omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
