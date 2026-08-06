import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.StepRelations

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

theorem permReachable_to_iff_of_faceReachable
    {G : Hypermap} {x y : G.Dart}
    (hxy : PermReachable G.face x y) (u : G.Dart) :
    PermReachable G.face x u ↔ PermReachable G.face y u := by
  constructor
  · intro hxu
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hxy) hxu
  · intro hyu
    exact PermReachable.trans G.face hxy hyu

theorem faceBand_optional_singleton_iff_of_faceReachable
    {G : Hypermap} {x y u : G.Dart}
    (hxy : PermReachable G.face x y) (b : Bool) :
    G.FaceBand (if b then [x] else []) u ↔
      G.FaceBand (if b then [y] else []) u := by
  cases b
  · simp [Hypermap.FaceBand.nil]
  · simp [Hypermap.FaceBand.singleton,
      permReachable_to_iff_of_faceReachable hxy u]

/-- Coq's `EqsF` calculation for `CpH`: every successful H compiler branch
meets the same face orbits as the old first two question walks together with
the removed middle perimeter face. -/
theorem hQuestionCase_walk_faceBand_iff
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    (hface : ∀ x y : P.h.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y)
    (hproperP : P.map.ProperRingHead P.point)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hrel1 :
      G0.edge (G0.node (h (P.hOld (P.map.node P.point)))) =
        h (P.h.map.node P.h.point))
    (hrel2 :
      PermReachable G0.face
        (G0.node (h (P.hOld (P.map.node P.point)))) (h P.h.point))
    (hrel3 :
      G0.edge (G0.node (G0.node (h (P.hOld P.point)))) =
        h P.h.point)
    {q1' q2' : Question}
    (hcase : HQuestionCase rq1 rq2 q1' q2')
    (u : G0.Dart) :
    G0.FaceBand
        (rqSeqWalk G0 (rqsH rq1 rq3 qs q1' q2')
          (r.map (fun x ↦ h (P.hOld x))) ++ r0) u ↔
      G0.FaceBand
        (h (P.hOld P.point) ::
          (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
            ((P.h.map.node P.h.point :: P.h.point ::
              (r.drop 2).map P.hOld).map h) ++ r0)) u := by
  let a := P.map.face (P.map.edge P.point)
  let nu0 := P.h.map.node P.h.point
  let u0 := P.h.point
  let v1 := P.hOld (P.map.node P.point)
  let v2 := P.hOld P.point
  let root1 := G0.node (h v1)
  let root2 := G0.node (h v2)
  have hdrop2 : r.drop 2 = a :: r.drop 3 := by
    calc
      r.drop 2 =
          (P.map.node P.point :: P.point :: a :: r.drop 3).drop 2 :=
        congrArg (List.drop 2) (by simpa [a] using hr)
      _ = a :: r.drop 3 := rfl
  have hnuV1 : PermReachable P.h.map.face nu0 v1 := by
    exact (PointedHypermap.h_faceReachable_node_point_old_iff
      P hproperP).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have htargetV1Nu : PermReachable G0.face (h v1) (h nu0) :=
    (hface _ _).2 (PermReachable.symm P.h.map.face hnuV1)
  have hoptional :=
    faceBand_optional_singleton_iff_of_faceReachable
      htargetV1Nu rq1.isKernel (u := u)
  have hroot1PointIff (z : G0.Dart) :
      PermReachable G0.face root1 z ↔
        PermReachable G0.face (h u0) z :=
    permReachable_to_iff_of_faceReachable hrel2 z
  have hfacePoint2 : G0.face (h u0) = root2 := by
    calc
      G0.face (h u0) =
          G0.face (G0.edge (G0.node root2)) := by
        simpa [u0, root2, v2] using congrArg G0.face hrel3.symm
      _ = root2 := G0.face_edge_node root2
  have hroot2Point : PermReachable G0.face root2 (h u0) := by
    have hforward := PermReachable.forward G0.face (h u0)
    rw [hfacePoint2] at hforward
    exact PermReachable.symm G0.face hforward
  have hroot2PointIff (z : G0.Dart) :
      PermReachable G0.face root2 z ↔
        PermReachable G0.face (h u0) z :=
    permReachable_to_iff_of_faceReachable hroot2Point z
  have hstepR : qstepR G0 root1 = G0.node (h nu0) := by
    simp [root1, v1, nu0, qstepR, hrel1]
  have hstepL : qstepL G0 root2 = G0.node (h u0) := by
    simp [root2, v2, u0, qstepL, hrel3]
  have hnewRoots :
      r.map (fun x ↦ h (P.hOld x)) =
        h v1 :: h v2 :: h (P.hOld a) ::
          (r.drop 3).map (fun x ↦ h (P.hOld x)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h =
        h nu0 :: h u0 :: h (P.hOld a) ::
          (r.drop 3).map (fun x ↦ h (P.hOld x)) := by
    rw [hdrop2]
    simp [nu0, u0, List.map_map, Function.comp_def]
  rw [hnewRoots, holdRoots]
  dsimp only [a, nu0, u0, v1, v2, root1, root2]
  dsimp only [a, nu0, u0, v1, v2, root1, root2] at hoptional hroot1PointIff
  dsimp only [a, nu0, u0, v1, v2, root1, root2] at hroot2PointIff hstepR hstepL
  have hu0 : P.h.point = (ExtDart.new : P.h.map.Dart) := rfl
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨hk, _hbad, hshape⟩
    rcases hshape with hfirst | hsecond | hleft | hright
    · rcases hfirst with ⟨hq1, hq2, hk1, rfl, rfl⟩
      simp only [rqSeqWalk_rqsH, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ,
        Hypermap.FaceBand.append, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil,
        hk, hq1, hq2, hk1]
      rw [hroot1PointIff u]
      rw [hu0]
      apply iff_of_eq
      ac_rfl
    · rcases hsecond with ⟨hq1, hq2, hk1, rfl, rfl⟩
      simp only [rqSeqWalk_rqsH, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ,
        Hypermap.FaceBand.append, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil,
        hk, hq1, hq2, hk1]
      rw [hroot2PointIff u]
      rw [hu0]
      apply iff_of_eq
      ac_rfl
    · rcases hleft with ⟨hq1, hq2, rfl, rfl⟩
      simp only [rqSeqWalk_rqsH, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ,
        Hypermap.FaceBand.append, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil, hk, hq1, hstepL]
      rw [hroot2PointIff u]
      rw [hu0]
      apply iff_of_eq
      ac_rfl
    · rcases hright with ⟨hq1, hq2, rfl, rfl⟩
      simp only [rqSeqWalk_rqsH, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ,
        Hypermap.FaceBand.append, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil, hk, hq2, hstepR]
      rw [hroot1PointIff u]
      rw [hu0]
      apply iff_of_eq
      ac_rfl
  · rcases hnonkernel with ⟨hk, _hbad, hq1, hq2, rfl, rfl⟩
    simp only [rqSeqWalk_rqsH, rqSeqWalk_cons_cons,
      Hypermap.FaceBand.append]
    rw [hoptional]
    simp [Hypermap.walkQ,
      Hypermap.FaceBand.append, Hypermap.FaceBand.cons,
      Hypermap.FaceBand.nil,
      hk, hq1, hq2]
    apply iff_of_eq
    ac_rfl

/-- The length half of Coq's `eq_simple` calculation for `CpH`.  Each
successful replacement walk has the old length plus the explicitly retained
middle perimeter dart. -/
theorem hQuestionCase_walk_length_eq
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    {q1' q2' : Question}
    (hcase : HQuestionCase rq1 rq2 q1' q2') :
    (rqSeqWalk G0 (rqsH rq1 rq3 qs q1' q2')
          (r.map (fun x ↦ h (P.hOld x))) ++ r0).length =
      (h (P.hOld P.point) ::
        (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
          ((P.h.map.node P.h.point :: P.h.point ::
            (r.drop 2).map P.hOld).map h) ++ r0)).length := by
  let a := P.map.face (P.map.edge P.point)
  have hdrop2 : r.drop 2 = a :: r.drop 3 := by
    calc
      r.drop 2 =
          (P.map.node P.point :: P.point :: a :: r.drop 3).drop 2 :=
        congrArg (List.drop 2) (by simpa [a] using hr)
      _ = a :: r.drop 3 := rfl
  have hnewRoots :
      r.map (fun x ↦ h (P.hOld x)) =
        h (P.hOld (P.map.node P.point)) :: h (P.hOld P.point) ::
          h (P.hOld a) ::
            (r.drop 3).map (fun x ↦ h (P.hOld x)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h =
        h (P.h.map.node P.h.point) :: h P.h.point ::
          h (P.hOld a) ::
            (r.drop 3).map (fun x ↦ h (P.hOld x)) := by
    rw [hdrop2]
    simp [List.map_map, Function.comp_def]
  rw [hnewRoots, holdRoots]
  have hkernelLength :
      (if rq1.isKernel then
          [h (P.hOld (P.map.node P.point))] else []).length =
        (if rq1.isKernel then
          [h ((P.map.extensionH P.point).node ExtDart.new)] else []).length := by
    cases rq1.isKernel <;> rfl
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨hk, _hbad, hshape⟩
    rcases hshape with hfirst | hsecond | hleft | hright
    · rcases hfirst with ⟨hq1, hq2, hk1, rfl, rfl⟩
      simp [rqSeqWalk_rqsH, rqSeqWalk, hk, hq1, hq2, hk1,
        Hypermap.length_walkQ, Question.flat]
      omega
    · rcases hsecond with ⟨hq1, hq2, hk1, rfl, rfl⟩
      simp [rqSeqWalk_rqsH, rqSeqWalk, hk, hq1, hq2, hk1,
        Hypermap.length_walkQ, Question.flat]
      omega
    · rcases hleft with ⟨hq1, hq2, rfl, rfl⟩
      simp [rqSeqWalk_rqsH, rqSeqWalk, hk, hq1,
        Hypermap.length_walkQ, Question.flat]
      rw [hkernelLength]
      omega
    · rcases hright with ⟨hq1, hq2, rfl, rfl⟩
      simp [rqSeqWalk_rqsH, rqSeqWalk, hk, hq2,
        Hypermap.length_walkQ, Question.flat]
      rw [hkernelLength]
      omega
  · rcases hnonkernel with ⟨hk, _hbad, hq1, hq2, rfl, rfl⟩
    simp [rqSeqWalk_rqsH, rqSeqWalk, hk, hq1, hq2,
      Hypermap.length_walkQ, Question.flat]
    rw [hkernelLength]
    omega

/-- Coq's `Eq12F`/`EqsF` calculation for `CpY`: every successful compiler
branch replaces the first two old question walks by a walk meeting exactly
the same target face orbits. -/
theorem yQuestionCase_walk_faceBand_iff
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    (hface : ∀ x y : P.y.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hrel1 :
      G0.edge (G0.node (h (P.yOld (P.map.node P.point)))) =
        h (P.y.map.node P.y.point))
    (hrel2 :
      G0.edge (G0.node (G0.node
        (h (P.yOld (P.map.node P.point))))) = h P.y.point)
    {q' : Question}
    (hcase : YQuestionCase rq1 rq2 q')
    (u : G0.Dart) :
    G0.FaceBand
        (rqSeqWalk G0 (rqsY rq1 rq3 qs q')
          (r.map (fun x => h (P.yOld x))) ++ r0) u ↔
      G0.FaceBand
        (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
          ((P.y.map.node P.y.point :: P.y.point ::
            (r.drop 1).map P.yOld).map h) ++ r0) u := by
  have hdrop1 : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  let v1 := P.yOld (P.map.node P.point)
  let nu0 := P.y.map.node P.y.point
  let u0 := P.y.point
  let root := G0.node (h v1)
  have hsourceV1Nu : PermReachable P.y.map.face v1 nu0 :=
    PermReachable.symm P.y.map.face
      ((PointedHypermap.y_faceReachable_node_point_old_iff P).2
        (PermReachable.refl P.map.face (P.map.node P.point)))
  have htargetV1Nu : PermReachable G0.face (h v1) (h nu0) :=
    (hface _ _).2 hsourceV1Nu
  have hv1Nu (z : G0.Dart) :
      PermReachable G0.face (h v1) z ↔
        PermReachable G0.face (h nu0) z :=
    permReachable_to_iff_of_faceReachable htargetV1Nu z
  have hfacePoint : G0.face (h u0) = root := by
    calc
      G0.face (h u0) =
          G0.face (G0.edge (G0.node (G0.node (h v1)))) := by
        simpa [v1, u0] using congrArg G0.face hrel2.symm
      _ = root := by
        simp [root]
  have hrootPoint : PermReachable G0.face root (h u0) := by
    have hforward := PermReachable.forward G0.face (h u0)
    rw [hfacePoint] at hforward
    exact PermReachable.symm G0.face hforward
  have hrootPointIff (z : G0.Dart) :
      PermReachable G0.face root z ↔
        PermReachable G0.face (h u0) z :=
    permReachable_to_iff_of_faceReachable hrootPoint z
  have hstepR : qstepR G0 root = G0.node (h nu0) := by
    simp [root, v1, nu0, qstepR, hrel1]
  have hstepL : qstepL G0 root = G0.node (h u0) := by
    simp [root, v1, u0, qstepL, hrel2]
  have hllReach :
      PermReachable G0.face
        (G0.edge (G0.node (G0.node (h u0)))) (G0.node (h u0)) := by
    have hforward :=
      PermReachable.forward G0.face
        (G0.edge (G0.node (G0.node (h u0))))
    simpa [G0.face_edge_node] using hforward
  have hllIff (z : G0.Dart) :
      PermReachable G0.face
          (G0.edge (G0.node (G0.node (h u0)))) z ↔
        PermReachable G0.face (G0.node (h u0)) z :=
    permReachable_to_iff_of_faceReachable hllReach z
  have hnewRoots :
      r.map (fun x => h (P.yOld x)) =
        h v1 :: h (P.yOld P.point) ::
          (r.drop 2).map (fun x => h (P.yOld x)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld).map h =
        h nu0 :: h u0 :: h (P.yOld P.point) ::
          (r.drop 2).map (fun x => h (P.yOld x)) := by
    rw [hdrop1]
    simp [nu0, u0, List.map_map, Function.comp_def]
  rw [hnewRoots, holdRoots]
  dsimp only [v1, nu0, u0, root]
  dsimp only [v1, nu0, u0, root] at htargetV1Nu hv1Nu hrootPointIff hstepR hstepL hllIff
  have hoptional :=
    faceBand_optional_singleton_iff_of_faceReachable
      htargetV1Nu rq1.isKernel (u := u)
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨hk, _hbad, rfl⟩
    simp only [rqSeqWalk_rqsY, rqSeqWalk_cons_cons,
      Hypermap.FaceBand.append]
    rw [hoptional]
    simp [yKernelQuestion_walk,
      Hypermap.walkQ, Hypermap.FaceBand.append,
      Hypermap.FaceBand.cons,
      Hypermap.FaceBand.nil, hk, hstepL, hstepR]
    rw [hrootPointIff u]
    have hu0 : P.y.point = (ExtDart.new : P.y.map.Dart) := rfl
    rw [hu0]
    tauto
  · rcases hnonkernel with ⟨hk, _hbad, hshape⟩
    rcases hshape with hzero | hright | hleft
    · rcases hzero with ⟨hq1, hq2, hq'⟩
      simp only [rqSeqWalk_rqsY, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ, Hypermap.FaceBand.nil,
        hk, hq1, hq2, hq']
      simp only [or_assoc]
    · rcases hright with ⟨qa, q, hq1, hq2, hq'⟩
      simp only [rqSeqWalk_rqsY, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil,
        hk, hq1, hq2, hq', hstepR]
      simp only [or_assoc]
    · rcases hleft with ⟨qa, q, hq1, hq2, hq'⟩
      simp only [rqSeqWalk_rqsY, rqSeqWalk_cons_cons,
        Hypermap.FaceBand.append]
      rw [hoptional]
      simp [Hypermap.walkQ, Hypermap.FaceBand.cons,
        Hypermap.FaceBand.nil,
        hk, hq1, hq2, hq', hstepL]
      have hllIffU :
          PermReachable G0.face
              (G0.edge (G0.node (G0.node (h ExtDart.new)))) u ↔
            PermReachable G0.face (G0.node (h ExtDart.new)) u := by
        simpa [PointedHypermap.y] using hllIff u
      rw [hllIffU]
      simp only [or_assoc]

/-- The length half of Coq's `eq_simple` calculation for `CpY`.  The four
successful compiler branches preserve the number of accumulated walk darts. -/
theorem yQuestionCase_walk_length_eq
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    {q' : Question}
    (hcase : YQuestionCase rq1 rq2 q') :
    (rqSeqWalk G0 (rqsY rq1 rq3 qs q')
          (r.map (fun x => h (P.yOld x))) ++ r0).length =
      (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
          ((P.y.map.node P.y.point :: P.y.point ::
            (r.drop 1).map P.yOld).map h) ++ r0).length := by
  have hdrop1 : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  have hnewRoots :
      r.map (fun x => h (P.yOld x)) =
        h (P.yOld (P.map.node P.point)) :: h (P.yOld P.point) ::
          (r.drop 2).map (fun x => h (P.yOld x)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld).map h =
        h (P.y.map.node P.y.point) :: h P.y.point ::
          h (P.yOld P.point) ::
            (r.drop 2).map (fun x => h (P.yOld x)) := by
    rw [hdrop1]
    simp [List.map_map, Function.comp_def]
  rw [hnewRoots, holdRoots]
  have hkernelLength :
      (if rq1.isKernel then
          [h (P.yOld (P.map.node P.point))] else []).length =
        (if rq1.isKernel then
          [h ((P.map.extensionY P.point).node ExtDart.new)] else []).length := by
    cases rq1.isKernel <;> rfl
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨hk, _hbad, rfl⟩
    simp [rqSeqWalk_rqsY, rqSeqWalk, hk, yKernelQuestion_flat,
      Hypermap.length_walkQ, Question.flat]
    rw [hkernelLength]
    omega
  · rcases hnonkernel with ⟨hk, _hbad, hshape⟩
    rcases hshape with hzero | hright | hleft
    · rcases hzero with ⟨hq1, hq2, rfl⟩
      simp [rqSeqWalk_rqsY, rqSeqWalk, hk, hq1, hq2,
        Hypermap.length_walkQ, Question.flat]
      exact hkernelLength
    · rcases hright with ⟨qa, q, hq1, hq2, rfl⟩
      simp [rqSeqWalk_rqsY, rqSeqWalk, hk, hq1, hq2,
        Hypermap.length_walkQ, Question.flat]
      exact hkernelLength
    · rcases hleft with ⟨qa, q, hq1, hq2, rfl⟩
      simp [rqSeqWalk_rqsY, rqSeqWalk, hk, hq1, hq2,
        Hypermap.length_walkQ, Question.flat]
      exact hkernelLength

/-- Coq `nFr0_H1`: the `CpH` compiler guard preserves good target-ring
arities outside the new source image and perimeter face band. -/
theorem hQuestionCase_goodRingArity
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    (hface : ∀ x y : P.h.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y)
    (hproperP : P.map.ProperRingHead P.point)
    (hlongP : P.map.LongRingHead P.point)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld))
    {q1' q2' : Question}
    (hcase : HQuestionCase rq1 rq2 q1' q2') :
    ∀ ⦃x : G0.Dart⦄,
      x ∈ r0 →
        ¬ RqSeqCodom (fun y ↦ h (P.hOld y)) x →
          ¬ G0.FaceBand (r.map (fun y ↦ h (P.hOld y))) x →
            G0.GoodRingArity x := by
  let a := P.map.face (P.map.edge P.point)
  let v1 := P.hOld (P.map.node P.point)
  let v2 := P.hOld P.point
  let nu0 := P.h.map.node P.h.point
  let u0 := P.h.point
  have hdrop2 : r.drop 2 = a :: r.drop 3 := by
    calc
      r.drop 2 =
          (P.map.node P.point :: P.point :: a :: r.drop 3).drop 2 :=
        congrArg (List.drop 2) (by simpa [a] using hr)
      _ = a :: r.drop 3 := rfl
  have hsourceV1Nu : PermReachable P.h.map.face v1 nu0 :=
    PermReachable.symm P.h.map.face
      ((PointedHypermap.h_faceReachable_node_point_old_iff
        P hproperP).2
        (PermReachable.refl P.map.face (P.map.node P.point)))
  have htargetV1Nu : PermReachable G0.face (h v1) (h nu0) :=
    (hface _ _).2 hsourceV1Nu
  have hv1Nu (z : G0.Dart) :
      PermReachable G0.face (h v1) z ↔
        PermReachable G0.face (h nu0) z :=
    permReachable_to_iff_of_faceReachable htargetV1Nu z
  have hnewRoots :
      r.map (fun y ↦ h (P.hOld y)) =
        h v1 :: h v2 :: h (P.hOld a) ::
          (r.drop 3).map (fun y ↦ h (P.hOld y)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h =
        h nu0 :: h u0 :: h (P.hOld a) ::
          (r.drop 3).map (fun y ↦ h (P.hOld y)) := by
    rw [hdrop2]
    simp [nu0, u0, List.map_map, Function.comp_def]
  have hbandOld (x : G0.Dart) :
      G0.FaceBand
          ((P.h.map.node P.h.point :: P.h.point ::
            (r.drop 2).map P.hOld).map h) x →
        PermReachable G0.face (h u0) x ∨
          G0.FaceBand (r.map (fun y ↦ h (P.hOld y))) x := by
    rw [hnewRoots, holdRoots]
    simp only [Hypermap.FaceBand.cons]
    rw [← hv1Nu x]
    tauto
  have hv2Mem : h v2 ∈ r.map (fun y ↦ h (P.hOld y)) := by
    rw [hr]
    simp [v2]
  have hfitOld := hproper.fits
  rw [hdrop2] at hfitOld
  have hfit2 := rqSeqFits_tail hfitOld
  have hA2 := rqSeqFits_head_arity hfit2
  have hpointArity : P.h.map.arity P.h.point = 3 :=
    h_point_arity_of_proper P hproperP
  intro x hx hnotCodom hnotBand
  by_cases hmiddle : PermReachable G0.face (h u0) x
  · rcases hcase with hkernel | hnonkernel
    · rcases hkernel with ⟨hk, _hbad, _hshape⟩
      have huWalk :
          h u0 ∈ rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
            ((P.h.map.node P.h.point :: P.h.point ::
              (r.drop 2).map P.hOld).map h) := by
        rw [holdRoots]
        simp [rqSeqWalk, hk, u0]
      have hcross :=
        (List.pairwise_append.mp hproper.simple).2.2
          (h u0) huWalk x hx
      exact False.elim (hcross hmiddle)
    · rcases hnonkernel with ⟨_hk, hbad, _hq1, _hq2, _hq1', _hq2'⟩
      have harityMiddle : G0.arity (h u0) = G0.arity x :=
        G0.arity_eq_of_faceReachable hmiddle
      apply goodRingArity_of_badRingArity_sub_two_eq_false
      have hsub : G0.arity x - 2 = rq2.outerArity + 1 := by
        dsimp only [u0] at hA2 harityMiddle
        omega
      rw [hsub]
      exact hbad
  · apply hproper.goodRingArity hx
    · have hnewTarget :
          RqSeqTarget (fun y ↦ h (P.hOld y)) r x :=
        Or.inl hnotCodom
      have holdTarget :=
        (rqSeqTarget_comp_hOld_iff P h hface hproperP hlongP r hr x).1
          hnewTarget
      rcases holdTarget with hmiddleBand | holdTarget
      · exact False.elim (hnotBand
          (Hypermap.FaceBand.of_mem (G := G0) hv2Mem
            ((Hypermap.FaceBand.singleton (G := G0)).1 hmiddleBand)))
      rcases holdTarget with holdNotCodom | holdBand
      · exact holdNotCodom
      · rcases hbandOld x holdBand with holdMiddle | hnewBand
        · exact False.elim (hmiddle holdMiddle)
        · exact False.elim (hnotBand hnewBand)
    · intro holdBand
      rcases hbandOld x holdBand with holdMiddle | hnewBand
      · exact hmiddle holdMiddle
      · exact hnotBand hnewBand

/-- Coq `nFr0_Y1`: the `CpY` compiler guard preserves good target-ring
arities outside the new source image and perimeter face band. -/
theorem yQuestionCase_goodRingArity
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    (hface : ∀ x y : P.y.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y)
    (hproperP : P.map.ProperRingHead P.point)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld))
    {q' : Question}
    (hcase : YQuestionCase rq1 rq2 q') :
    ∀ ⦃x : G0.Dart⦄,
      x ∈ r0 →
        ¬ RqSeqCodom (fun y => h (P.yOld y)) x →
          ¬ G0.FaceBand (r.map (fun y => h (P.yOld y))) x →
            G0.GoodRingArity x := by
  have hdrop1 : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  let v1 := P.yOld (P.map.node P.point)
  let nu0 := P.y.map.node P.y.point
  let u0 := P.y.point
  have hsourceV1Nu : PermReachable P.y.map.face v1 nu0 :=
    PermReachable.symm P.y.map.face
      ((PointedHypermap.y_faceReachable_node_point_old_iff P).2
        (PermReachable.refl P.map.face (P.map.node P.point)))
  have htargetV1Nu : PermReachable G0.face (h v1) (h nu0) :=
    (hface _ _).2 hsourceV1Nu
  have hv1Nu (z : G0.Dart) :
      PermReachable G0.face (h v1) z ↔
        PermReachable G0.face (h nu0) z :=
    permReachable_to_iff_of_faceReachable htargetV1Nu z
  have hnewRoots :
      r.map (fun y => h (P.yOld y)) =
        h v1 :: h (P.yOld P.point) ::
          (r.drop 2).map (fun y => h (P.yOld y)) := by
    rw [hr]
    rfl
  have holdRoots :
      (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld).map h =
        h nu0 :: h u0 :: h (P.yOld P.point) ::
          (r.drop 2).map (fun y => h (P.yOld y)) := by
    rw [hdrop1]
    simp [nu0, u0, List.map_map, Function.comp_def]
  have hbandOldIff (x : G0.Dart) :
      G0.FaceBand
          ((P.y.map.node P.y.point :: P.y.point ::
            (r.drop 1).map P.yOld).map h) x ↔
        PermReachable G0.face (h u0) x ∨
          G0.FaceBand (r.map (fun y => h (P.yOld y))) x := by
    rw [hnewRoots, holdRoots]
    simp only [Hypermap.FaceBand.cons]
    rw [← hv1Nu x]
    tauto
  have hfitOld := hproper.fits
  rw [hdrop1] at hfitOld
  have hfit2 := rqSeqFits_tail hfitOld
  have hA2 := rqSeqFits_head_arity hfit2
  have hyPointArity : P.y.map.arity P.y.point = 2 :=
    y_point_arity_of_proper P hproperP
  intro x hx hnotCodom hnotBand
  by_cases hmiddle : PermReachable G0.face (h u0) x
  · rcases hcase with hkernel | hnonkernel
    · rcases hkernel with ⟨hk, _hbad, _hq'⟩
      have huWalk :
          h u0 ∈ rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
            ((P.y.map.node P.y.point :: P.y.point ::
              (r.drop 1).map P.yOld).map h) := by
        rw [holdRoots]
        simp [rqSeqWalk, hk, u0]
      have hcross :=
        (List.pairwise_append.mp hproper.simple).2.2
          (h u0) huWalk x hx
      exact False.elim (hcross hmiddle)
    · rcases hnonkernel with ⟨_hk, hbad, _hshape⟩
      have harityMiddle : G0.arity (h u0) = G0.arity x :=
        G0.arity_eq_of_faceReachable hmiddle
      apply goodRingArity_of_badRingArity_sub_two_eq_false
      have hsub : G0.arity x - 2 = rq2.outerArity := by
        dsimp only [u0] at hA2 harityMiddle
        omega
      rw [hsub]
      exact hbad
  · apply hproper.goodRingArity hx
    · have hnewTarget :
          RqSeqTarget (fun y => h (P.yOld y)) r x :=
        Or.inl hnotCodom
      have holdTarget :=
        (rqSeqTarget_comp_yOld_iff P h hface r hr x).1 hnewTarget
      rcases holdTarget with holdNotCodom | holdBand
      · exact holdNotCodom
      · exact False.elim (hnotBand
          (Or.resolve_left ((hbandOldIff x).1 holdBand) hmiddle))
    · intro holdBand
      exact hnotBand
        (Or.resolve_left ((hbandOldIff x).1 holdBand) hmiddle)

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
