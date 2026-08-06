import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.WalkProperties

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- Coq `cfquizP`, `CpY` branch, packaged against the actual construction
program injections and semantic rings. -/
theorem rqSeqProper_yStep
    {cp1 cp2 : CProg}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hcp1 : CProg.cubic cp1 = true)
    (hcp2 : cp2 = [] ∨ CProg.config cp2 = true)
    (hproper :
      RqSeqProper
        (PointedHypermap.injcp cp1 (CpStep.y :: cp2))
        (rq1 :: rq2 :: rq3 :: qs)
        (PointedHypermap.cpRing
          (CProg.appendRev cp1 (CpStep.y :: cp2)))
        (PointedHypermap.cpRing (CpStep.y :: cp2)))
    (hR :
      (cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs)) cp2).isQuizR = true) :
    RqSeqProper
      (PointedHypermap.injcp (CpStep.y :: cp1) cp2)
      (cfquizY rq1 rq2 (rqsY rq1 rq3 qs))
      (PointedHypermap.cpRing
        (CProg.appendRev (CpStep.y :: cp1) cp2))
      (PointedHypermap.cpRing cp2) := by
  let P := PointedHypermap.cpmap cp2
  let h := PointedHypermap.injcp cp1 (CpStep.y :: cp2)
  let G0 := (PointedHypermap.cpmap
    (CProg.appendRev cp1 (CpStep.y :: cp2))).map
  let r := PointedHypermap.cpRing cp2
  let r0 := PointedHypermap.cpRing
    (CProg.appendRev cp1 (CpStep.y :: cp2))
  have htail :
      P.ProperRingHead ∧ PointedHypermap.cpRingCycle cp2 ∧
        1 < CProg.ringSize cp2 ∧ P.map.FaceSimple r := by
    rcases hcp2 with rfl | hcfg
    · refine ⟨?_, PointedHypermap.cpRingCycle_nil, by decide, ?_⟩
      · simpa [P] using PointedHypermap.base_properRingHead
      · change cpmap0.FaceSimple [false, true]
        simp [Hypermap.FaceSimple, cpmap0_faceReachable_iff]
    · have hgeom := PointedHypermap.cpmap_configGeometry_of_config hcfg
      have hsimpleFull := PointedHypermap.cpMapSimple_of_config hcfg
      have hsimpleFull' :
          P.map.FaceSimple
            (PointedHypermap.cpRing cp2 ++
              PointedHypermap.cpKernel cp2) := by
        simpa [P, PointedHypermap.cpMapSimple] using hsimpleFull
      exact ⟨hgeom.proper,
        PointedHypermap.cpRingCycle_of_config hcfg,
        by
          have hgt := CProg.ringSize_gt_two_of_config hcfg
          omega,
        by simpa [r] using (List.pairwise_append.mp hsimpleFull').1⟩
  have hproperHead := htail.1
  have hcycle := htail.2.1
  have hsize := htail.2.2.1
  have hsimple := htail.2.2.2
  have hr :
      r = P.map.node P.point :: P.point :: r.drop 2 := by
    simpa [P, r] using
      PointedHypermap.cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
        (cp := cp2) hsize
  have hringY :
      PointedHypermap.cpRing (CpStep.y :: cp2) =
        P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld := by
    simpa [P, r] using
      PointedHypermap.cpRing_y_eq_of_ringCycle
        hcycle hproperHead
  have hproper' :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld) := by
    simpa [h, r0, hringY] using hproper
  have hinj : Function.Injective h := by
    simpa [h] using
      PointedHypermap.injcp_injective cp1 (CpStep.y :: cp2)
  have hface (x y : P.y.map.Dart) :
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y := by
    simpa [P, h, G0] using
      (PointedHypermap.injcp_faceReachable_iff_of_cubic
        cp1 (CpStep.y :: cp2) hcp1 (x := x) (y := y))
  have hrels :
      G0.edge (G0.node (h (P.yOld (P.map.node P.point)))) =
          h (P.y.map.node P.y.point) ∧
        G0.edge (G0.node (G0.node
          (h (P.yOld (P.map.node P.point))))) = h P.y.point := by
    simpa [P, h, G0] using yStep_outer_relations hcp1 hcp2
  obtain ⟨q', hcompile, hcase⟩ :=
    cfquizY_case_of_isQuizR rq1 rq2 rq3 qs cp2 hR
  have hqfit :=
    yQuestionCase_fitQ P h hproperHead hr hproper'
      hrels.1 hrels.2 hcase
  have hfits :=
    rqSeqFits_rqsY_of_yOld P h hface hr hsimple hproper' q' hqfit
  have hgood :=
    yQuestionCase_goodRingArity P h hface hproperHead hr
      hproper' hcase
  have hband (x : G0.Dart) :
      G0.FaceBand
          (rqSeqWalk G0 (rqsY rq1 rq3 qs q')
            (r.map (fun y => h (P.yOld y))) ++ r0) x ↔
        G0.FaceBand
          (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
            ((P.y.map.node P.y.point :: P.y.point ::
              (r.drop 1).map P.yOld).map h) ++ r0) x :=
    yQuestionCase_walk_faceBand_iff P h hface hr
      (r0 := r0) (rq3 := rq3) (qs := qs) hrels.1 hrels.2 hcase x
  have hlen :
      (rqSeqWalk G0 (rqsY rq1 rq3 qs q')
          (r.map (fun y => h (P.yOld y))) ++ r0).length =
        (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
          ((P.y.map.node P.y.point :: P.y.point ::
            (r.drop 1).map P.yOld).map h) ++ r0).length :=
    yQuestionCase_walk_length_eq P h hr
      (r0 := r0) (rq3 := rq3) (qs := qs) hcase
  have hresult :
      RqSeqProper (fun x => h (P.yOld x))
        (rqsY rq1 rq3 qs q') r0 r :=
    RqSeqProper.yOld P hface hr hproper'
      hfits hgood hband hlen
  rw [hcompile]
  simpa [P, h, r, r0, PointedHypermap.injcp,
    PointedHypermap.oldStep, PointedHypermap.cpmap,
    PointedHypermap.step] using hresult

/-- Coq `cfquizP`, `CpH` branch, packaged against the actual construction
program injections and semantic rings. -/
theorem rqSeqProper_hStep
    {cp1 cp2 : CProg}
    {rq1 rq2 rq3 : RingQuestion} {qs : RqSeq}
    (hcp1 : CProg.cubic cp1 = true)
    (hcp2 : CProg.config cp2 = true)
    (hproper :
      RqSeqProper
        (PointedHypermap.injcp cp1 (CpStep.h :: cp2))
        (rq1 :: rq2 :: rq3 :: qs)
        (PointedHypermap.cpRing
          (CProg.appendRev cp1 (CpStep.h :: cp2)))
        (PointedHypermap.cpRing (CpStep.h :: cp2)))
    (hR :
      (cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs)) cp2).isQuizR = true) :
    RqSeqProper
      (PointedHypermap.injcp (CpStep.h :: cp1) cp2)
      (cfquizH rq1 rq2 (rqsH rq1 rq3 qs))
      (PointedHypermap.cpRing
        (CProg.appendRev (CpStep.h :: cp1) cp2))
      (PointedHypermap.cpRing cp2) := by
  let P := PointedHypermap.cpmap cp2
  let h := PointedHypermap.injcp cp1 (CpStep.h :: cp2)
  let G0 := (PointedHypermap.cpmap
    (CProg.appendRev cp1 (CpStep.h :: cp2))).map
  let r := PointedHypermap.cpRing cp2
  let r0 := PointedHypermap.cpRing
    (CProg.appendRev cp1 (CpStep.h :: cp2))
  have hgeom := PointedHypermap.cpmap_configGeometry_of_config hcp2
  have hcycle := PointedHypermap.cpRingCycle_of_config hcp2
  have hsize : 2 < CProg.ringSize cp2 :=
    CProg.ringSize_gt_two_of_config hcp2
  have hr :
      r = P.map.node P.point :: P.point ::
        P.map.face (P.map.edge P.point) :: r.drop 3 := by
    simpa [P, r] using
      PointedHypermap.cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
        (cp := cp2) hsize
  have hringH :
      PointedHypermap.cpRing (CpStep.h :: cp2) =
        P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld := by
    simpa [P, r] using
      PointedHypermap.cpRing_h_eq_of_ringCycle
        hcycle hgeom.proper hgeom.long hsize
  have hproper' :
      RqSeqProper h (rq1 :: rq2 :: rq3 :: qs) r0
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld) := by
    simpa [h, r0, hringH] using hproper
  have hinj : Function.Injective h := by
    simpa [h] using
      PointedHypermap.injcp_injective cp1 (CpStep.h :: cp2)
  have hface (x y : P.h.map.Dart) :
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y := by
    simpa [P, h, G0] using
      (PointedHypermap.injcp_faceReachable_iff_of_cubic
        cp1 (CpStep.h :: cp2) hcp1 (x := x) (y := y))
  have hsimpleFull := PointedHypermap.cpMapSimple_of_config hcp2
  have hsimpleFull' :
      P.map.FaceSimple
        (PointedHypermap.cpRing cp2 ++ PointedHypermap.cpKernel cp2) := by
    simpa [P, PointedHypermap.cpMapSimple] using hsimpleFull
  have hsimple : P.map.FaceSimple r := by
    simpa [r] using (List.pairwise_append.mp hsimpleFull').1
  have hrels :
      G0.edge (G0.node (h (P.hOld (P.map.node P.point)))) =
          h (P.h.map.node P.h.point) ∧
        PermReachable G0.face
            (G0.node (h (P.hOld (P.map.node P.point)))) (h P.h.point) ∧
          G0.edge (G0.node (G0.node (h (P.hOld P.point)))) =
            h P.h.point := by
    simpa [P, h, G0] using hStep_outer_relations hcp1 hcp2
  obtain ⟨q1', q2', hcompile, hcase⟩ :=
    cfquizH_case_of_isQuizR rq1 rq2 rq3 qs cp2 hR
  have hnotTarget :=
    hMiddle_not_target P h hface hgeom.proper hr hsimple
  have hmiddleArity :
      G0.arity (h (P.hOld P.point)) =
        P.h.map.arity (P.hOld P.point) :=
    RqSeqProper.arity_image_eq_of_not_target
      hinj hface hproper' hnotTarget
  have hqfit :=
    hQuestionCase_fitQ P h hgeom.proper hproper'
      hrels.1 hrels.2.1 hrels.2.2 hcase
  have hfits :=
    rqSeqFits_rqsH_of_hOld P h hface hgeom.proper hgeom.long
      hr hsimple hproper' hmiddleArity q1' q2' hqfit
  have hgood :=
    hQuestionCase_goodRingArity P h hface hgeom.proper hgeom.long
      hr hproper' hcase
  have hmiddleNot :
      ¬ G0.FaceBand
        (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
          ((P.h.map.node P.h.point :: P.h.point ::
            (r.drop 2).map P.hOld).map h) ++ r0)
        (h (P.hOld P.point)) := by
    intro hband
    exact hnotTarget ((hproper'.covers _).1 hband)
  have hband (x : G0.Dart) :
      G0.FaceBand
          (rqSeqWalk G0 (rqsH rq1 rq3 qs q1' q2')
            (r.map (fun y ↦ h (P.hOld y))) ++ r0) x ↔
        G0.FaceBand
          (h (P.hOld P.point) ::
            (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
              ((P.h.map.node P.h.point :: P.h.point ::
                (r.drop 2).map P.hOld).map h) ++ r0)) x :=
    hQuestionCase_walk_faceBand_iff P h hface hgeom.proper hr
      (r0 := r0) (rq3 := rq3) (qs := qs)
      hrels.1 hrels.2.1 hrels.2.2 hcase x
  have hlen :
      (rqSeqWalk G0 (rqsH rq1 rq3 qs q1' q2')
          (r.map (fun y ↦ h (P.hOld y))) ++ r0).length =
        (h (P.hOld P.point) ::
          (rqSeqWalk G0 (rq1 :: rq2 :: rq3 :: qs)
            ((P.h.map.node P.h.point :: P.h.point ::
              (r.drop 2).map P.hOld).map h) ++ r0)).length :=
    hQuestionCase_walk_length_eq P h hr
      (r0 := r0) (rq3 := rq3) (qs := qs) hcase
  have hresult :
      RqSeqProper (fun x ↦ h (P.hOld x))
        (rqsH rq1 rq3 qs q1' q2') r0 r :=
    RqSeqProper.hOld P hface hgeom.proper hgeom.long hr hproper'
      hfits hgood hmiddleNot hband hlen
  rw [hcompile]
  simpa [P, h, r, r0, PointedHypermap.injcp,
    PointedHypermap.oldStep, PointedHypermap.cpmap,
    PointedHypermap.step] using hresult

theorem rqSeqProper_initial_identity
    (G : Hypermap) (r : List G.Dart)
    (hsimple : G.FaceSimple r) :
    RqSeqProper (G0 := G) (G := G) (fun x => x)
      (initialRingQuestions r.length) r r where
  fits := rqSeqFits_initialRingQuestions_id G r
  goodRingArity := by
    intro x _hx hnot _hband
    exact False.elim (hnot ⟨x, rfl⟩)
  simple := by
    have hwalk :
        rqSeqWalk G (initialRingQuestions r.length)
          (List.map (fun x => x) r) = [] := by
      simpa using rqSeqWalk_initialRingQuestions G r
    rw [hwalk]
    simpa using hsimple
  covers := by
    intro x
    have hwalk :
        rqSeqWalk G (initialRingQuestions r.length)
          (List.map (fun x => x) r) = [] := by
      simpa using rqSeqWalk_initialRingQuestions G r
    rw [hwalk]
    constructor
    · intro hx
      exact Or.inr (by simpa using hx)
    · intro hx
      rcases hx with hnot | hband
      · exact False.elim (hnot ⟨x, rfl⟩)
      · simpa using hband

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
