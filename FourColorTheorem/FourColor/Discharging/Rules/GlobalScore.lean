import FourColorTheorem.FourColor.Discharging.Rules.Bounds

/-! Face-orbit and global sums of discharged scores. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Total net score received by the face orbit of `x`. -/
noncomputable def faceScoreSum (x : G.Dart) : Int :=
  ∑ y : G.FaceClass x, G.dscore2 y.1

noncomputable def faceClassFaceSymmEquiv (x : G.Dart) :
    G.FaceClass x ≃ G.FaceClass x where
  toFun z :=
    ⟨G.face.symm z.1,
      PermReachable.trans G.face z.2
        (PermReachable.backward G.face z.1)⟩
  invFun z :=
    ⟨G.face z.1,
      PermReachable.trans G.face z.2
        (PermReachable.forward G.face z.1)⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

theorem sum_dscore2_face_symm_faceClass (x : G.Dart) :
    (∑ y : G.FaceClass x, G.dscore2 (G.face.symm y.1)) =
      ∑ y : G.FaceClass x, G.dscore2 y.1 :=
  Fintype.sum_equiv (G.faceClassFaceSymmEquiv x)
    (fun y : G.FaceClass x => G.dscore2 (G.face.symm y.1))
    (fun y : G.FaceClass x => G.dscore2 y.1)
    (fun _ => rfl)

theorem faceScoreSum_mirror_of_plain_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    G.mirror.faceScoreSum x = G.faceScoreSum x := by
  unfold faceScoreSum
  calc
    (∑ y : G.mirror.FaceClass x, G.mirror.dscore2 y.1) =
        ∑ y : G.FaceClass x, G.mirror.dscore2 y.1 :=
      Fintype.sum_equiv (G.mirrorFaceClassEquiv x)
        (fun y : G.mirror.FaceClass x => G.mirror.dscore2 y.1)
        (fun y : G.FaceClass x => G.mirror.dscore2 y.1)
        (fun _ => rfl)
    _ = ∑ y : G.FaceClass x, G.dscore2 (G.face.symm y.1) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact G.dscore2_mirror_eq_face_symm_of_plain_cubic
        hPlain hCubic y.1
    _ = ∑ y : G.FaceClass x, G.dscore2 y.1 :=
      G.sum_dscore2_face_symm_faceClass x

theorem faceScoreSum_eq_sum_fin_arity (x : G.Dart) :
    G.faceScoreSum x =
      ∑ i : Fin (G.arity x),
        G.dscore2 ((G.face : G.Dart → G.Dart)^[i.1] x) := by
  rw [G.arity_eq_minimalPeriod x]
  unfold faceScoreSum
  exact (Fintype.sum_equiv (G.faceClassEquivMinimalPeriod x).symm
    (fun i : Fin (Function.minimalPeriod
        (G.face : G.Dart → G.Dart) x) =>
      G.dscore2 ((G.face : G.Dart → G.Dart)^[i.1] x))
    (fun y : G.FaceClass x => G.dscore2 y.1)
    (fun _ => rfl)).symm

/-- Coq `dscore`: initial face charge plus all edge-transfer contributions
around the face orbit. -/
noncomputable def dscore (x : G.Dart) : Int :=
  (60 : Int) - 10 * (G.arity x : Int) + G.faceScoreSum x

theorem dscore_mirror_of_plain_cubic
    (hPlain : G.Plain) (hCubic : G.Cubic) (x : G.Dart) :
    G.mirror.dscore x = G.dscore x := by
  simp [dscore, G.arity_mirror x,
    G.faceScoreSum_mirror_of_plain_cubic hPlain hCubic x]

theorem sum_dscore2_eq_zero :
    (∑ x : G.Dart, G.dscore2 x) = 0 := by
  simp [dscore2, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Fintype.sum_equiv G.edge
    (fun x : G.Dart => G.dscore1 (G.edge x))
    (fun x : G.Dart => G.dscore1 x)
    (fun _ => rfl)

theorem dscore2_edge_of_plain
    (hG : G.Plain) (x : G.Dart) :
    G.dscore2 (G.edge x) = -G.dscore2 x := by
  simp [dscore2, (hG x).1]

theorem dscore2_edge_add_self_of_plain
    (hG : G.Plain) (x : G.Dart) :
    G.dscore2 (G.edge x) + G.dscore2 x = 0 := by
  rw [G.dscore2_edge_of_plain hG x]
  simp

theorem dscore1_nonneg (x : G.Dart) :
    0 ≤ G.dscore1 x := by
  simp [dscore1]

theorem dscore2_le_of_dscore1_le {M : Int}
    (hM : ∀ y : G.Dart, G.dscore1 y ≤ M)
    (x : G.Dart) :
    G.dscore2 x ≤ M := by
  calc
    G.dscore2 x = G.dscore1 (G.edge x) - G.dscore1 x := rfl
    _ ≤ G.dscore1 (G.edge x) := by
      exact sub_le_self _ (G.dscore1_nonneg x)
    _ ≤ M := hM (G.edge x)

theorem faceScoreSum_le_of_dscore2_le {M : Int}
    (hM : ∀ y : G.Dart, G.dscore2 y ≤ M)
    (x : G.Dart) :
    G.faceScoreSum x ≤ (G.arity x : Int) * M := by
  unfold faceScoreSum arity
  rw [Nat.card_eq_fintype_card]
  simpa [nsmul_eq_mul, mul_comm] using
    (Finset.sum_le_card_nsmul (Finset.univ : Finset (G.FaceClass x))
      (fun y : G.FaceClass x => G.dscore2 y.1) M
      (by intro y _; exact hM y.1))

theorem dscore_le_of_dscore1_le {M : Int}
    (hM : ∀ y : G.Dart, G.dscore1 y ≤ M)
    (x : G.Dart) :
    G.dscore x ≤
      (60 : Int) - 10 * (G.arity x : Int) + (G.arity x : Int) * M := by
  have hface : G.faceScoreSum x ≤ (G.arity x : Int) * M :=
    G.faceScoreSum_le_of_dscore2_le
      (fun y => G.dscore2_le_of_dscore1_le hM y) x
  simpa [dscore, add_comm, add_left_comm, add_assoc] using
    add_le_add_left hface ((60 : Int) - 10 * (G.arity x : Int))

theorem initial_bound_pos_of_dscore_pos_of_dscore1_le {M : Int}
    (hM : ∀ y : G.Dart, G.dscore1 y ≤ M)
    {x : G.Dart}
    (hpos : 0 < G.dscore x) :
    0 < (60 : Int) - 10 * (G.arity x : Int) +
      (G.arity x : Int) * M :=
  lt_of_lt_of_le hpos (G.dscore_le_of_dscore1_le hM x)

theorem arity_le_eleven_of_dscore_pos_of_dscore1_le_five
    (hM : ∀ y : G.Dart, G.dscore1 y ≤ (5 : Int))
    {x : G.Dart}
    (hpos : 0 < G.dscore x) :
    G.arity x ≤ 11 := by
  have hbound :
      0 < (60 : Int) - 10 * (G.arity x : Int) +
        (G.arity x : Int) * (5 : Int) :=
    G.initial_bound_pos_of_dscore_pos_of_dscore1_le hM hpos
  omega

theorem faceScoreSum_eq_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.faceScoreSum x = G.faceScoreSum y := by
  unfold faceScoreSum
  exact Fintype.sum_equiv (G.faceClassEquivOfReachable hxy)
    (fun z : G.FaceClass x => G.dscore2 z.1)
    (fun z : G.FaceClass y => G.dscore2 z.1)
    (fun _ => rfl)

theorem dscore_eq_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.dscore x = G.dscore y := by
  simp [dscore, G.arity_eq_of_faceReachable hxy,
    G.faceScoreSum_eq_of_faceReachable hxy]

theorem dscore_face (x : G.Dart) :
    G.dscore (G.face x) = G.dscore x := by
  exact G.dscore_eq_of_faceReachable
    (PermReachable.symm G.face (PermReachable.forward G.face x))

theorem dscore_cface
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.dscore x = G.dscore y :=
  G.dscore_eq_of_faceReachable hxy

theorem sum_faceScoreSum_faceOrbit_eq_sum_dscore2 :
    (∑ o : G.FaceOrbit, G.faceScoreSum (Quotient.out o)) =
      ∑ x : G.Dart, G.dscore2 x := by
  unfold faceScoreSum
  rw [← Fintype.sum_sigma
    (fun p : Sigma fun o : G.FaceOrbit => G.FaceClass (Quotient.out o) =>
      G.dscore2 p.2.1)]
  exact Fintype.sum_equiv G.faceClassSigmaEquivDart
    (fun p : Sigma fun o : G.FaceOrbit => G.FaceClass (Quotient.out o) =>
      G.dscore2 p.2.1)
    (fun x : G.Dart => G.dscore2 x)
    (fun _ => rfl)

theorem sum_faceScoreSum_faceOrbit_eq_zero :
    (∑ o : G.FaceOrbit, G.faceScoreSum (Quotient.out o)) = 0 := by
  rw [G.sum_faceScoreSum_faceOrbit_eq_sum_dscore2, G.sum_dscore2_eq_zero]

/-- Sum of discharged scores over one representative from each face orbit. -/
noncomputable def faceDscoreSum : Int :=
  ∑ o : G.FaceOrbit, G.dscore (Quotient.out o)

theorem faceDscoreSum_eq_initial :
    G.faceDscoreSum =
      ∑ o : G.FaceOrbit,
        ((60 : Int) - 10 * (G.arity (Quotient.out o) : Int)) := by
  rw [faceDscoreSum]
  simp [dscore, Finset.sum_add_distrib,
    G.sum_faceScoreSum_faceOrbit_eq_sum_dscore2, G.sum_dscore2_eq_zero]

theorem sum_initialDscore_faceOrbit_eq :
    (∑ o : G.FaceOrbit,
        ((60 : Int) - 10 * (G.arity (Quotient.out o) : Int))) =
      60 * (Fintype.card G.FaceOrbit : Int) -
        10 * (Fintype.card G.Dart : Int) := by
  have hmul :
      (∑ x : G.FaceOrbit,
          (10 : Int) * (G.arity (Quotient.out x) : Int)) =
        10 * (Fintype.card G.Dart : Int) := by
    calc
      (∑ x : G.FaceOrbit,
          (10 : Int) * (G.arity (Quotient.out x) : Int)) =
          10 * (∑ x : G.FaceOrbit,
            (G.arity (Quotient.out x) : Int)) := by
        rw [Finset.mul_sum]
      _ = 10 * (Fintype.card G.Dart : Int) := by
        rw [show
          (∑ x : G.FaceOrbit, (G.arity (Quotient.out x) : Int)) =
            (Fintype.card G.Dart : Int) by
          exact_mod_cast G.sum_arity_faceOrbit_eq_card_dart]
  rw [Finset.sum_sub_distrib]
  simp [hmul, mul_comm]

theorem faceDscoreSum_eq_euler_expression :
    G.faceDscoreSum =
      60 * (Fintype.card G.FaceOrbit : Int) -
        10 * (Fintype.card G.Dart : Int) := by
  rw [G.faceDscoreSum_eq_initial, G.sum_initialDscore_faceOrbit_eq]

theorem faceDscoreSum_eq_of_euler_expression
    (h :
      60 * (Fintype.card G.FaceOrbit : Int) -
          10 * (Fintype.card G.Dart : Int) =
        120) :
    G.faceDscoreSum = 120 := by
  rw [G.faceDscoreSum_eq_euler_expression, h]

theorem eulerCharge_int
    {D E N F : Int}
    (hE : D = 2 * E)
    (hN : D = 3 * N)
    (hEuler : 2 + D = E + N + F) :
    60 * F - 10 * D = 120 := by
  omega

theorem eulerChargeFormula_of_counts
    (hcomp : G.componentCount = 1)
    (hedge : Fintype.card G.Dart = 2 * G.edgeOrbitCount)
    (hnode : Fintype.card G.Dart = 3 * G.nodeOrbitCount)
    (heuler : G.eulerLeft = G.eulerRight) :
    60 * (Fintype.card G.FaceOrbit : Int) -
        10 * (Fintype.card G.Dart : Int) =
      120 := by
  have hFaceCard : Fintype.card G.FaceOrbit = G.faceOrbitCount := by
    rw [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card]
  have hEint :
      (Fintype.card G.Dart : Int) =
        2 * (G.edgeOrbitCount : Int) := by
    exact_mod_cast hedge
  have hNint :
      (Fintype.card G.Dart : Int) =
        3 * (G.nodeOrbitCount : Int) := by
    exact_mod_cast hnode
  have hEulerNat :
      2 + Fintype.card G.Dart =
        G.edgeOrbitCount + G.nodeOrbitCount + G.faceOrbitCount := by
    unfold Hypermap.eulerLeft Hypermap.eulerRight at heuler
    rw [hcomp] at heuler
    simpa [Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      heuler
  have hEulerInt :
      2 + (Fintype.card G.Dart : Int) =
        (G.edgeOrbitCount : Int) + (G.nodeOrbitCount : Int) +
          (G.faceOrbitCount : Int) := by
    exact_mod_cast hEulerNat
  rw [hFaceCard]
  exact eulerCharge_int hEint hNint hEulerInt

theorem dscore_quotient_out_eq_of_faceOrbit_eq
    {x : G.Dart} {o : G.FaceOrbit}
    (hxo : PermOrbit.of G.face x = o) :
    G.dscore (Quotient.out o) = G.dscore x := by
  have hout : PermOrbit.of G.face (Quotient.out o) = o :=
    Quotient.out_eq o
  exact G.dscore_eq_of_faceReachable (Quotient.exact (hout.trans hxo.symm))

theorem exists_positive_dscore_of_faceDscoreSum_eq
    (htotal : G.faceDscoreSum = 120) :
    ∃ x : G.Dart, 0 < G.dscore x := by
  by_contra hnone
  push Not at hnone
  have hle : G.faceDscoreSum ≤ 0 := by
    unfold faceDscoreSum
    exact Finset.sum_nonpos (fun o _ => hnone (Quotient.out o))
  omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
