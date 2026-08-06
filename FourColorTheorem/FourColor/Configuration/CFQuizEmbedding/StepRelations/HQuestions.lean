import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.StepRelations.YQuestions

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- The old middle perimeter dart removed by `rqsH` is outside the target of
the recursive H-state invariant.  This is the separation fact used twice in
Coq's `CpH` branch: for `nFv2` and for the extra singleton in `eq_simple`. -/
theorem hMiddle_not_target
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    (hface : ∀ x y : P.h.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y)
    (hproperP : P.map.ProperRingHead P.point)
    {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    (hsimple : P.map.FaceSimple r) :
    ¬ RqSeqTarget h
      (P.h.map.node P.h.point :: P.h.point ::
        (r.drop 2).map P.hOld)
      (h (P.hOld P.point)) := by
  have hr2 :
      r = P.map.node P.point :: P.point :: r.drop 2 := by
    rw [hr]
    rfl
  have hsimple2 :
      P.map.FaceSimple
        (P.map.node P.point :: P.point :: r.drop 2) := by
    rw [← hr2]
    exact hsimple
  have hnotSource :
      ¬ P.h.map.FaceBand
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld)
        (P.hOld P.point) := by
    rintro ⟨z, hz, hzMiddle⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple2 (List.Mem.head _))
        ((PointedHypermap.h_faceReachable_node_point_old_iff
          P hproperP).1 hzMiddle)
    rcases List.mem_cons.mp hz with rfl | hz
    · exact PointedHypermap.h_not_faceReachable_point_old
        P P.point hzMiddle
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    have hxMiddle : PermReachable P.map.face x P.point :=
      (PointedHypermap.hOld_faceReachable_iff P).1 hzMiddle
    exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimple2.tail hx)
      (PermReachable.symm P.map.face hxMiddle)
  have hnotMapped :
      ¬ G0.FaceBand
        ((P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h)
        (h (P.hOld P.point)) := by
    rintro ⟨z, hz, hzMiddle⟩
    rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact hnotSource ⟨y, hy, (hface _ _).1 hzMiddle⟩
  rintro (houtside | hband)
  · exact houtside ⟨P.hOld P.point, rfl⟩
  · exact hnotMapped hband

/-- The source-fit half of Coq `cfquizP`'s `CpH` branch.  The outer
embedding preserves the removed middle face arity by `nFv2`; the three
detached source faces gain one dart and all remaining faces are unchanged. -/
theorem rqSeqFits_rqsH_of_hOld
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
    (hsimple : P.map.FaceSimple r)
    {r0 : List G0.Dart}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hproper :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld))
    (hmiddleArity :
      G0.arity (h (P.hOld P.point)) =
        P.h.map.arity (P.hOld P.point))
    (q1' q2' : Question)
    (hqfit :
      G0.fitQ (G0.node (h (P.hOld (P.map.node P.point)))) q1' = true ∧
        G0.fitQ (G0.node (h (P.hOld P.point))) q2' = true) :
    rqSeqFits G0 P.map (fun x ↦ h (P.hOld x))
      (rqsH rq1 rq3 qs q1' q2') r = true := by
  let a := P.map.face (P.map.edge P.point)
  let nu0 := P.h.map.node P.h.point
  let v1 := P.hOld (P.map.node P.point)
  let v2 := P.hOld P.point
  have hdrop2 : r.drop 2 = a :: r.drop 3 := by
    calc
      r.drop 2 =
          (P.map.node P.point :: P.point :: a :: r.drop 3).drop 2 :=
        congrArg (List.drop 2) (by simpa [a] using hr)
      _ = a :: r.drop 3 := rfl
  have hsimpleFull :
      P.map.FaceSimple
        (P.map.node P.point :: P.point :: a :: r.drop 3) := by
    rw [← hr]
    exact hsimple
  have hsimpleTriple :
      P.map.FaceSimple [P.map.node P.point, P.point, a] := by
    simpa [Hypermap.FaceSimple] using hsimpleFull.take (i := 3)
  have hfitOld := hproper.fits
  rw [hdrop2] at hfitOld
  have hfit2 := rqSeqFits_tail hfitOld
  have hfit3 := rqSeqFits_tail hfit2
  have hfitTail := rqSeqFits_tail hfit3
  have hA1 := rqSeqFits_head_arity hfitOld
  have hA3 := rqSeqFits_head_arity hfit3
  have hq3 := rqSeqFits_head_fitQ hfit3
  have hnuV1 : PermReachable P.h.map.face nu0 v1 := by
    exact (PointedHypermap.h_faceReachable_node_point_old_iff
      P hproperP).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have htargetV1Nu : G0.arity (h v1) = G0.arity (h nu0) :=
    G0.arity_eq_of_faceReachable
      ((hface _ _).2 (PermReachable.symm P.h.map.face hnuV1))
  have hsourceNuV1 : P.h.map.arity nu0 = P.h.map.arity v1 :=
    P.h.map.arity_eq_of_faceReachable hnuV1
  have hv1SourceArity :
      P.h.map.arity v1 = P.map.arity (P.map.node P.point) + 1 := by
    simpa [v1, a] using
      hOld_arity_of_faceBand P hproperP hlongP hsimpleTriple
        ((Hypermap.FaceBand.triple (G := P.map)).2
          (Or.inl (PermReachable.refl P.map.face
            (P.map.node P.point))))
  have hv2SourceArity :
      P.h.map.arity v2 = P.map.arity P.point + 1 := by
    simpa [v2, a] using
      hOld_arity_of_faceBand P hproperP hlongP hsimpleTriple
        ((Hypermap.FaceBand.triple (G := P.map)).2
          (Or.inr (Or.inl
            (PermReachable.refl P.map.face P.point))))
  have haSourceArity :
      P.h.map.arity (P.hOld a) = P.map.arity a + 1 := by
    simpa [a] using
      hOld_arity_of_faceBand P hproperP hlongP hsimpleTriple
        ((Hypermap.FaceBand.triple (G := P.map)).2
          (Or.inr (Or.inr (PermReachable.refl P.map.face a))))
  have hnewA1 :
      G0.arity (h v1) =
        (rq1.outerArity + 1) + P.map.arity (P.map.node P.point) := by
    calc
      G0.arity (h v1) = G0.arity (h nu0) := htargetV1Nu
      _ = rq1.outerArity + P.h.map.arity nu0 := by
        simpa [nu0] using hA1
      _ = rq1.outerArity + P.h.map.arity v1 := by
        rw [hsourceNuV1]
      _ = rq1.outerArity +
          (P.map.arity (P.map.node P.point) + 1) := by
        rw [hv1SourceArity]
      _ = (rq1.outerArity + 1) +
          P.map.arity (P.map.node P.point) := by omega
  have hnewA2 :
      G0.arity (h v2) = 1 + P.map.arity P.point := by
    calc
      G0.arity (h v2) = P.h.map.arity v2 := by
        simpa [v2] using hmiddleArity
      _ = P.map.arity P.point + 1 := hv2SourceArity
      _ = 1 + P.map.arity P.point := Nat.add_comm _ _
  have hnewA3 :
      G0.arity (h (P.hOld a)) =
        (rq3.outerArity + 1) + P.map.arity a := by
    calc
      G0.arity (h (P.hOld a)) =
          rq3.outerArity + P.h.map.arity (P.hOld a) := by
        simpa [a] using hA3
      _ = rq3.outerArity + (P.map.arity a + 1) := by
        rw [haSourceArity]
      _ = (rq3.outerArity + 1) + P.map.arity a := by omega
  have htailArity :
      ∀ x : P.map.Dart, x ∈ r.drop 3 →
        P.h.map.arity (P.hOld x) = P.map.arity x := by
    intro x hx
    apply hOld_arity_of_not_faceBand P hproperP hlongP
    intro hband
    rcases (Hypermap.FaceBand.triple (G := P.map)).1 hband with
        hnode | hpoint | ha
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimpleFull
        (List.Mem.tail P.point (List.Mem.tail a hx))) hnode
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimpleFull.tail
        (List.Mem.tail a hx)) hpoint
    · exact (Hypermap.FaceSimple.not_faceReachable_head
        (G := P.map) hsimpleFull.tail.tail hx) ha
  have hfitTail' :
      rqSeqFits G0 P.map (fun x ↦ h (P.hOld x)) qs (r.drop 3) = true := by
    rw [rqSeqFits_comp_of_arity_eq G0 P.map P.h.map h P.hOld
      qs (r.drop 3) htailArity]
    exact hfitTail
  rw [hr, rqSeqFits_rqsH]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨hnewA1, hqfit.1⟩, hnewA2⟩, hqfit.2⟩,
    by simpa [a] using hnewA3⟩, hq3⟩, hfitTail'⟩

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
