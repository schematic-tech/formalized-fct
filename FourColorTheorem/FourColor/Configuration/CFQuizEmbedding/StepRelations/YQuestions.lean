import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.StepRelations.HStep

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- The source-fit part of Coq `cfquizP`'s `CpY` branch, after the compiler
has supplied the replacement question at the surviving first ring dart. -/
theorem rqSeqFits_rqsY_of_yOld
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    (hface : ∀ x y : P.y.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    (hsimple : P.map.FaceSimple r)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld))
    (q' : Question)
    (hqfit :
      G0.fitQ
        (G0.node (h (P.yOld (P.map.node P.point)))) q' = true) :
    rqSeqFits G0 P.map (fun x => h (P.yOld x))
      (rqsY rq1 rq3 qs q') r = true := by
  have hdrop1 : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  have hfitOld := hproper.fits
  rw [hdrop1] at hfitOld
  have hfit2 := rqSeqFits_tail hfitOld
  have hfit3 := rqSeqFits_tail hfit2
  have hfitTail := rqSeqFits_tail hfit3
  have hA1 := rqSeqFits_head_arity hfitOld
  have hq1 := rqSeqFits_head_fitQ hfitOld
  have hA2 := rqSeqFits_head_arity hfit2
  have hq2 := rqSeqFits_head_fitQ hfit2
  have hA3 := rqSeqFits_head_arity hfit3
  have hq3 := rqSeqFits_head_fitQ hfit3
  have hsimple' :
      P.map.FaceSimple
        (P.map.node P.point :: P.point :: r.drop 2) := by
    rw [← hr]
    exact hsimple
  have hsep :
      ¬ PermReachable P.map.face P.point (P.map.node P.point) := by
    intro hreach
    exact (Hypermap.FaceSimple.not_faceReachable_head
      (G := P.map) hsimple' (List.Mem.head (r.drop 2)))
      (PermReachable.symm P.map.face hreach)
  have hnodeBand :
      P.map.FaceBand [P.map.node P.point, P.point]
        (P.map.node P.point) :=
    (Hypermap.FaceBand.pair (G := P.map)).2
      (Or.inl (PermReachable.refl P.map.face (P.map.node P.point)))
  have hpointBand :
      P.map.FaceBand [P.map.node P.point, P.point] P.point :=
    (Hypermap.FaceBand.pair (G := P.map)).2
      (Or.inr (PermReachable.refl P.map.face P.point))
  have hnodeOldReach :
      PermReachable P.y.map.face (P.y.map.node P.y.point)
        (P.yOld (P.map.node P.point)) :=
    (PointedHypermap.y_faceReachable_node_point_old_iff P).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have htargetNodeArity :
      G0.arity (h (P.yOld (P.map.node P.point))) =
        G0.arity (h (P.y.map.node P.y.point)) :=
    G0.arity_eq_of_faceReachable
      ((hface _ _).2 (PermReachable.symm P.y.map.face hnodeOldReach))
  have hsourceNodeArity :
      P.y.map.arity (P.y.map.node P.y.point) =
        P.y.map.arity (P.yOld (P.map.node P.point)) :=
    P.y.map.arity_eq_of_faceReachable hnodeOldReach
  have hnodeOldArity := yOld_arity_of_faceBand P hsep hnodeBand
  have hpointOldArity := yOld_arity_of_faceBand P hsep hpointBand
  have hnewA1 :
      G0.arity (h (P.yOld (P.map.node P.point))) =
        (rq1.outerArity + 1) + P.map.arity (P.map.node P.point) := by
    omega
  have hnewA3 :
      G0.arity (h (P.yOld P.point)) =
        (rq3.outerArity + 1) + P.map.arity P.point := by
    omega
  have htailArity :
      ∀ x : P.map.Dart, x ∈ r.drop 2 →
        P.y.map.arity (P.yOld x) = P.map.arity x := by
    intro x hx
    apply yOld_arity_of_not_faceBand P
    intro hband
    rcases (Hypermap.FaceBand.pair (G := P.map)).1 hband with
      hnode | hpoint
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple'
        (List.Mem.tail P.point hx)) hnode
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple'.tail hx) hpoint
  have hfitTail' :
      rqSeqFits G0 P.map (fun x => h (P.yOld x)) qs (r.drop 2) = true := by
    rw [rqSeqFits_comp_of_arity_eq G0 P.map P.y.map h P.yOld
      qs (r.drop 2) htailArity]
    exact hfitTail
  rw [hr, rqSeqFits_rqsY]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨hnewA1, hqfit⟩, hnewA3⟩, hq3⟩, hfitTail'⟩

/-- The replacement question selected by a successful `cfquizY` branch fits
at the surviving first ring dart.  This is Coq's `Eq1`/`Eq1v1` argument and
the three explicit nonkernel subcases. -/
theorem yQuestionCase_fitQ
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    (hproperP : P.map.ProperRingHead P.point)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld))
    (hrel1 :
      G0.edge (G0.node (h (P.yOld (P.map.node P.point)))) =
        h (P.y.map.node P.y.point))
    (hrel2 :
      G0.edge (G0.node (G0.node
        (h (P.yOld (P.map.node P.point))))) = h P.y.point)
    {q' : Question}
    (hcase : YQuestionCase rq1 rq2 q') :
    G0.fitQ (G0.node (h (P.yOld (P.map.node P.point)))) q' = true := by
  have hdrop1 : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  have hfitOld := hproper.fits
  rw [hdrop1] at hfitOld
  have hfit2 := rqSeqFits_tail hfitOld
  have hA2 := rqSeqFits_head_arity hfit2
  have hq1 := rqSeqFits_head_fitQ hfitOld
  have hq2 := rqSeqFits_head_fitQ hfit2
  have hyPointArity : P.y.map.arity P.y.point = 2 :=
    y_point_arity_of_proper P hproperP
  let root := G0.node (h (P.yOld (P.map.node P.point)))
  have hfacePoint : G0.face (h P.y.point) = root := by
    calc
      G0.face (h P.y.point) =
          G0.face (G0.edge (G0.node (G0.node
            (h (P.yOld (P.map.node P.point)))))) := by rw [hrel2]
      _ = root := by
        simp [root]
  have hrootArity : G0.arity root = rq2.outerArity + 2 := by
    calc
      G0.arity root = G0.arity (G0.face (h P.y.point)) := by
        rw [hfacePoint]
      _ = G0.arity (h P.y.point) := G0.arity_face (h P.y.point)
      _ = rq2.outerArity + 2 := by omega
  have hstepR :
      qstepR G0 root = G0.node (h (P.y.map.node P.y.point)) := by
    simp [root, qstepR, hrel1]
  have hstepL : qstepL G0 root = G0.node (h P.y.point) := by
    simp [root, qstepL, hrel2]
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨_hk, hbad, rfl⟩
    apply (fitQ_yKernelQuestion_iff G0 root _ _ _).2
    apply Hypermap.fitQ_qaskLR_of_arity
    · rw [smallQArity_toNat_eq_add_two_of_not_bad hbad]
      exact hrootArity
    · rw [hstepL]
      exact hq2
    · rw [hstepR]
      exact hq1
  · rcases hnonkernel with ⟨_hk, _hbad, hshape⟩
    rcases hshape with hzero | hright | hleft
    · rcases hzero with ⟨_hq1, _hq2, rfl⟩
      exact Hypermap.fitQ_qask0 G0 root
    · rcases hright with ⟨qa, q, hq1eq, _hq2, rfl⟩
      rw [hq1eq] at hq1
      have hdecomp := Hypermap.fitQ_qaskR_decomp (G := G0) hq1
      apply Hypermap.fitQ_qaskRR_of_arity
      · rw [hstepR]
        exact hdecomp.1
      · rw [hstepR]
        exact hdecomp.2
    · rcases hleft with ⟨qa, q, _hq1, hq2eq, rfl⟩
      rw [hq2eq] at hq2
      have hdecomp := Hypermap.fitQ_qaskL_decomp (G := G0) hq2
      apply Hypermap.fitQ_qaskLL_of_arity
      · calc
          G0.arity (G0.edge (G0.node (qstepL G0 root))) =
              G0.arity (qstepL G0 root) :=
            Hypermap.arity_edge_node_eq_arity (G := G0) (qstepL G0 root)
          _ = G0.arity (G0.node (h P.y.point)) := by rw [hstepL]
          _ = qa.toNat := hdecomp.1
      · rw [hstepL]
        exact hdecomp.2

/-- The two replacement questions selected by a successful `cfquizH` branch
fit at the two old ring darts retained by `rqsH`.  This is Coq's `q11ok` and
`q21ok` argument. -/
theorem hQuestionCase_fitQ
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    (hproperP : P.map.ProperRingHead P.point)
    {tail : List P.h.map.Dart}
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.h.map.node P.h.point :: P.h.point :: tail))
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
    (hcase : HQuestionCase rq1 rq2 q1' q2') :
    G0.fitQ (G0.node (h (P.hOld (P.map.node P.point)))) q1' = true ∧
      G0.fitQ (G0.node (h (P.hOld P.point))) q2' = true := by
  have hfitOld := hproper.fits
  have hfit2 := rqSeqFits_tail hfitOld
  have hA2 := rqSeqFits_head_arity hfit2
  have hq1 := rqSeqFits_head_fitQ hfitOld
  have hq2 := rqSeqFits_head_fitQ hfit2
  have hpointArity : P.h.map.arity P.h.point = 3 :=
    h_point_arity_of_proper P hproperP
  let root1 := G0.node (h (P.hOld (P.map.node P.point)))
  let root2 := G0.node (h (P.hOld P.point))
  have hroot1Arity : G0.arity root1 = rq2.outerArity + 3 := by
    calc
      G0.arity root1 = G0.arity (h P.h.point) :=
        G0.arity_eq_of_faceReachable hrel2
      _ = rq2.outerArity + 3 := by omega
  have hfacePoint2 : G0.face (h P.h.point) = root2 := by
    calc
      G0.face (h P.h.point) =
          G0.face (G0.edge (G0.node root2)) := by rw [hrel3]
      _ = root2 := G0.face_edge_node root2
  have hroot2Arity : G0.arity root2 = rq2.outerArity + 3 := by
    calc
      G0.arity root2 = G0.arity (G0.face (h P.h.point)) := by
        rw [hfacePoint2]
      _ = G0.arity (h P.h.point) := G0.arity_face (h P.h.point)
      _ = rq2.outerArity + 3 := by omega
  have hstepR :
      qstepR G0 root1 = G0.node (h (P.h.map.node P.h.point)) := by
    simp [root1, qstepR, hrel1]
  have hstepL : qstepL G0 root2 = G0.node (h P.h.point) := by
    simp [root2, qstepL, hrel3]
  rcases hcase with hkernel | hnonkernel
  · rcases hkernel with ⟨_hk, hbad, hshape⟩
    have hqa1 :
        (smallQArity (rq2.outerArity + 1)).toNat =
          rq2.outerArity + 3 := by
      rw [smallQArity_toNat_eq_add_two_of_not_bad hbad]
    rcases hshape with hfirst | hsecond | hleft | hright
    · rcases hfirst with ⟨_hq1, _hq2, _hk1, rfl, rfl⟩
      exact ⟨
        Hypermap.fitQ_qask1_of_arity (G := G0)
          (by simpa [root1, hqa1] using hroot1Arity),
        Hypermap.fitQ_qask0 G0 root2⟩
    · rcases hsecond with ⟨_hq1, _hq2, _hk1, rfl, rfl⟩
      exact ⟨
        Hypermap.fitQ_qask0 G0 root1,
        Hypermap.fitQ_qask1_of_arity (G := G0)
          (by simpa [root2, hqa1] using hroot2Arity)⟩
    · rcases hleft with ⟨_hq1, _hq2, rfl, rfl⟩
      exact ⟨
        Hypermap.fitQ_qask0 G0 root1,
        Hypermap.fitQ_qaskL_of_arity (G := G0)
          (by simpa [root2, hqa1] using hroot2Arity)
          (by rw [hstepL]; exact hq2)⟩
    · rcases hright with ⟨_hq1, _hq2, rfl, rfl⟩
      exact ⟨
        Hypermap.fitQ_qaskR_of_arity (G := G0)
          (by simpa [root1, hqa1] using hroot1Arity)
          (by rw [hstepR]; exact hq1),
        Hypermap.fitQ_qask0 G0 root2⟩
  · rcases hnonkernel with ⟨_hk, _hbad, _hq1, _hq2, rfl, rfl⟩
    exact ⟨Hypermap.fitQ_qask0 G0 root1,
      Hypermap.fitQ_qask0 G0 root2⟩

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
