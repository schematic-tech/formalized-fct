import FourColorTheorem.FourColor.Discharging.Rules.BaseRules

/-! Mirror transport for local discharging scores. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Coq `inv_face2`: the dart two face-steps before `x`, expressed via the
plain-cubic hypermap permutations. -/
def invFace2 (x : G.Dart) : G.Dart :=
  G.edge (G.node (G.edge (G.node x)))

theorem invFace2_eq_face_symm_face_symm (x : G.Dart) :
    G.invFace2 x = G.face.symm (G.face.symm x) := by
  exact Hypermap.edge_node_edge_node_eq_face_symm_face_symm (G := G) x

/-- Coq's `x2' := inv_face2 x; x3 := face (face (face x))` satisfies
`x3 = iter 5 face x2'`. -/
theorem face_iterate_five_invFace2 (x : G.Dart) :
    ((G.face : G.Dart → G.Dart)^[5] (G.invFace2 x)) =
      G.face (G.face (G.face x)) := by
  rw [G.invFace2_eq_face_symm_face_symm]
  simp [Function.iterate_succ_apply]

/-- The mirrored predecessor of `face x` is the third face successor of `x`.
This is the dart identity used before pairing a rule with its symmetric
counterpart in Coq `dscore_mirror`. -/
theorem mirror_invFace2_face (x : G.Dart) :
    G.mirror.invFace2 (G.face x) =
      G.face (G.face (G.face x)) := by
  rw [Hypermap.invFace2_eq_face_symm_face_symm (G := G.mirror)]
  simp [Hypermap.mirror]
  rfl

/-- The inverse face walk in the mirror returns the third successor of `x` to
the original `invFace2 x`. -/
theorem mirror_face_iterate_five_face_three (x : G.Dart) :
    ((G.mirror.face : G.Dart → G.Dart)^[5]
        (G.face (G.face (G.face x)))) =
      G.invFace2 x := by
  rw [G.invFace2_eq_face_symm_face_symm]
  change
    ((G.face.symm : G.Dart → G.Dart)^[5]
        (G.face (G.face (G.face x)))) =
      G.face.symm (G.face.symm x)
  simp [Function.iterate_succ_apply]

/-- Local rule-pair identity used in Coq `dscore_mirror`: fitting a rule at
the mirrored predecessor of `face x` is the same as fitting its symmetric
discharge-rule partner at the original predecessor of `x`. -/
theorem exactFitp_mirror_invFace2_face_eq_symmetricRule
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) (p : Part) (hpos : 1 ≤ p.size) :
    Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x)) p =
      Part.exactFitp G (G.invFace2 x) (Discharge.symmetricRule p) := by
  calc
    Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x)) p =
        Part.exactFitp G.mirror (G.face (G.face (G.face x))) p := by
          rw [G.mirror_invFace2_face]
    _ = Part.exactFitp G (G.face (G.face (G.face x))) p.mirror := by
          rw [← Part.exactFitp_mirror (G := G) hPlain hCubic
            (p := p) (x := G.face (G.face (G.face x)))]
    _ = Part.exactFitp G
        ((G.face : G.Dart → G.Dart)^[5] (G.invFace2 x)) p.mirror := by
          rw [G.face_iterate_five_invFace2]
    _ = Part.exactFitp G (G.invFace2 x) (Discharge.symmetricRule p) := by
          rw [← Discharge.exactFitp_symmetricRule_eq_face_iter_mirror
            (G := G) (x := G.invFace2 x) (p := p) hpos]

/-- The converse local pairing: fitting the symmetric partner at the mirrored
predecessor is the same as fitting the original rule at the original
predecessor. -/
theorem exactFitp_mirror_invFace2_face_symmetricRule_eq
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) (p : Part) (hpos : 1 ≤ p.size) :
    Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x))
        (Discharge.symmetricRule p) =
      Part.exactFitp G (G.invFace2 x) p := by
  calc
    Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x))
        (Discharge.symmetricRule p) =
        Part.exactFitp G.mirror (G.face (G.face (G.face x)))
          (Discharge.symmetricRule p) := by
          rw [G.mirror_invFace2_face]
    _ = Part.exactFitp G.mirror
          ((G.mirror.face : G.Dart → G.Dart)^[5]
            (G.face (G.face (G.face x)))) p.mirror := by
          rw [Discharge.exactFitp_symmetricRule_eq_face_iter_mirror
            (G := G.mirror) (x := G.face (G.face (G.face x)))
            (p := p) hpos]
    _ = Part.exactFitp G
          ((G.mirror.face : G.Dart → G.Dart)^[5]
            (G.face (G.face (G.face x)))) p := by
          have h := Part.exactFitp_mirror (G := G) hPlain hCubic
            (p := p.mirror)
            (x := ((G.mirror.face : G.Dart → G.Dart)^[5]
              (G.face (G.face (G.face x)))))
          simpa [Part.mirror_mirror] using h.symm
    _ = Part.exactFitp G (G.invFace2 x) p := by
          rw [G.mirror_face_iterate_five_face_three]

/-- The symmetrized discharge-rule list has the same fitting count after
mirroring the pointed predecessor.  This is the list-recursive core of Coq's
`score1F` proof inside `dscore_mirror`. -/
theorem countBy_symmetrizeDrules_mirror_invFace2_face_eq
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    ∀ rs : Drules,
      (∀ p ∈ rs, 1 ≤ p.size) →
        Discharge.countBy
            (fun p => Part.exactFitp G.mirror
              (G.mirror.invFace2 (G.face x)) p)
            (Discharge.symmetrizeDrules rs) =
          Discharge.countBy
            (fun p => Part.exactFitp G (G.invFace2 x) p)
            (Discharge.symmetrizeDrules rs) := by
  intro rs
  induction rs with
  | nil =>
      intro _hpos
      simp [Discharge.symmetrizeDrules, Discharge.countBy]
  | cons p ps ih =>
      intro hpos
      let p' : Part := Discharge.symmetricRule p
      have hp_pos : 1 ≤ p.size := hpos p (by simp)
      have hps_pos : ∀ q ∈ ps, 1 ≤ q.size := by
        intro q hq
        exact hpos q (by simp [hq])
      have htail := ih hps_pos
      have hpair :
          Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x)) p =
            Part.exactFitp G (G.invFace2 x) p' := by
        simpa [p'] using
          G.exactFitp_mirror_invFace2_face_eq_symmetricRule
            hPlain hCubic x p hp_pos
      have hpair' :
          Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x)) p' =
            Part.exactFitp G (G.invFace2 x) p := by
        simpa [p'] using
          G.exactFitp_mirror_invFace2_face_symmetricRule_eq
            hPlain hCubic x p hp_pos
      cases hcmp : Part.cmp p p' with
      | Pdisjoint =>
          simp [Discharge.symmetrizeDrules, p', hcmp, Discharge.countBy,
            htail, hpair, hpair', Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc]
      | Pstraddle =>
          simp [Discharge.symmetrizeDrules, p', hcmp, Discharge.countBy,
            htail, hpair, hpair', Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc]
      | Psubset =>
          have hsize : p.size = p'.size := by
            simp [p']
          have hsame :
              Part.exactFitp G.mirror (G.mirror.invFace2 (G.face x)) p =
                Part.exactFitp G (G.invFace2 x) p := by
            apply Bool.eq_iff_iff.mpr
            constructor
            · intro hpMirror
              have hpMirror' :
                  Part.exactFitp G.mirror
                      (G.mirror.invFace2 (G.face x)) p' = true :=
                Part.exactFitp_of_cmp_eq_subset_of_size_eq
                  (G := G.mirror) hcmp hsize hpMirror
              rw [hpair'] at hpMirror'
              exact hpMirror'
            · intro hpOrig
              have hpOrig' :
                  Part.exactFitp G (G.invFace2 x) p' = true :=
                Part.exactFitp_of_cmp_eq_subset_of_size_eq
                  (G := G) hcmp hsize hpOrig
              rw [← hpair] at hpOrig'
              exact hpOrig'
          simp [Discharge.symmetrizeDrules, p', hcmp, Discharge.countBy,
            htail, hsame]

/-- Source score transferred from the face of `x` to its edge-neighbour:
the number of exact discharge rules fitting at `invFace2 x`. -/
noncomputable def dscore1 (x : G.Dart) : Int :=
  Int.ofNat <|
    Discharge.countBy
      (fun p => Part.exactFitp G (G.invFace2 x) p)
      Discharge.theDrules

theorem dscore1_mirror_face_of_plain_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    G.mirror.dscore1 (G.face x) = G.dscore1 x := by
  change
    Int.ofNat
        (Discharge.countBy
          (fun p => Part.exactFitp G.mirror
            (G.mirror.invFace2 (G.face x)) p)
          Discharge.theDrules) =
      Int.ofNat
        (Discharge.countBy
          (fun p => Part.exactFitp G (G.invFace2 x) p)
          Discharge.theDrules)
  apply congrArg Int.ofNat
  unfold Discharge.theDrules
  exact G.countBy_symmetrizeDrules_mirror_invFace2_face_eq
    hPlain hCubic x Discharge.baseDrules
    (fun p hp => Discharge.one_le_size_of_mem_baseDrules hp)

@[simp]
theorem invFace2_face_face (x : G.Dart) :
    G.invFace2 (G.face (G.face x)) = x := by
  simp [invFace2]

@[simp]
theorem face_face_invFace2 (x : G.Dart) :
    G.face (G.face (G.invFace2 x)) = x := by
  simp [invFace2]

theorem arity_invFace2 (x : G.Dart) :
    G.arity (G.invFace2 x) = G.arity x := by
  have h := Hypermap.arity_face_iter (G := G) 2 (G.invFace2 x)
  have h' : G.arity x = G.arity (G.invFace2 x) := by
    simpa [G.face_face_invFace2 x] using h
  exact h'.symm

theorem invFace2_edge_face_face_invFace2_edge_face_face_of_plain
    (hG : G.Plain) (x : G.Dart) :
    G.invFace2
        (G.edge
          (G.face
            (G.face
              (G.invFace2 (G.edge (G.face (G.face x))))))) = x := by
  simp [invFace2]
  rw [Plain.edge_edge (G := G) hG]
  rw [Hypermap.edge_node_edge_node_eq_face_symm_face_symm]
  rw [G.face.symm_apply_apply]
  simp

theorem invFace2_edge_edge_face_face_of_plain
    (hG : G.Plain) (x : G.Dart) :
    G.invFace2 (G.edge (G.edge (G.face (G.face x)))) = x := by
  rw [Plain.edge_edge (G := G) hG]
  simp

theorem exactFitp_eq_size_filter_fitp_of_arity_eq
    {nhub : Nat} {x : G.Dart}
    (hx : G.arity x = nhub) (p : Part) :
    Part.exactFitp G x p =
      ((p.size == nhub) && Part.fitp G x p) := by
  by_cases hsize : p.size = nhub
  · simp [Part.exactFitp, hx, hsize]
  · have hleft : (nhub == p.size) = false := by
      rw [Bool.beq_eq_decide_eq]
      exact decide_eq_false (fun h : nhub = p.size => hsize h.symm)
    have hright : (p.size == nhub) = false := by
      rw [Bool.beq_eq_decide_eq]
      exact decide_eq_false hsize
    simp [Part.exactFitp, hx, hleft, hright]

theorem dscore1_le_theDrules_length (x : G.Dart) :
    G.dscore1 x ≤ (Discharge.theDrules.length : Int) := by
  have h := Discharge.countBy_le_length
    (fun p => Part.exactFitp G (G.invFace2 x) p) Discharge.theDrules
  unfold dscore1
  change
    Int.ofNat
        (Discharge.countBy
          (fun p => Part.exactFitp G (G.invFace2 x) p)
          Discharge.theDrules) ≤
      Int.ofNat Discharge.theDrules.length
  exact Int.ofNat_le.mpr h

theorem dscore1_le_seventy_one (x : G.Dart) :
    G.dscore1 x ≤ (71 : Int) := by
  simpa [Discharge.length_theDrules] using G.dscore1_le_theDrules_length x

/-- Net score transfer across an edge. -/
noncomputable def dscore2 (x : G.Dart) : Int :=
  G.dscore1 (G.edge x) - G.dscore1 x

theorem dscore2_mirror_eq_face_symm_of_plain_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    G.mirror.dscore2 x = G.dscore2 (G.face.symm x) := by
  unfold dscore2
  have hedge :
      G.mirror.edge x = G.face (G.edge (G.face.symm x)) :=
    Hypermap.Plain.mirror_edge_eq_face_edge_face_symm
      (G := G) hPlain x
  rw [hedge]
  rw [G.dscore1_mirror_face_of_plain_cubic hPlain hCubic
    (G.edge (G.face.symm x))]
  rw [show x = G.face (G.face.symm x) by simp]
  rw [G.dscore1_mirror_face_of_plain_cubic hPlain hCubic
    (G.face.symm x)]
  simp

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
