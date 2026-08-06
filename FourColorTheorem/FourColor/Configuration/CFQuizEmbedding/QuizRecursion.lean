import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.StepProperness

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

theorem fitQuiz_qaskR_pair_of_decomp
    {G : Hypermap} {x : G.Dart}
    {qaL qaR : QArity} {qL qR : Question}
    (hroot : G.arity x = qaL.toNat)
    (hfitL : G.fitQ (qstepR G x) qL = true)
    (hedge : G.arity (G.edge x) = qaR.toNat)
    (hfitR : G.fitQ (qstepR G (G.edge x)) qR = true) :
    G.fitQuiz x ⟨Question.QaskR qaL qL,
      Question.QaskR qaR qR⟩ = true := by
  have hflatL := Hypermap.fitQ_flat_eq_map_arity (G := G) hfitL
  have hflatR := Hypermap.fitQ_flat_eq_map_arity (G := G) hfitR
  simp [Hypermap.fitQuiz, Hypermap.walkQuiz, Hypermap.walkQ,
    Quiz.flat, Question.flat, List.map_append,
    hroot, hedge, hflatL, hflatR]

theorem cfquizRec_pair_nil_isQuizR_iff
    (rq1 rq2 : RingQuestion) :
    (cfquizRec [rq1, rq2] []).isQuizR = true ↔
      rq1.isKernel = true ∧ rq2.isKernel = true ∧
        (largeQArity (rq1.outerArity - 1)).toNat =
          rq1.outerArity + 1 ∧
        badSmallArity (smallQArity (rq2.outerArity - 1)) = false := by
  cases rq1 with
  | mk k1 a1 q1 =>
      cases rq2 with
      | mk k2 a2 q2 =>
          cases k1 <;> cases k2
          all_goals
            simp [cfquizRec, noQuiz, Quiz.isQuizR,
              Question.isQaskR]
          case true.true =>
            by_cases hEq :
                (largeQArity (a1 - 1)).toNat = a1 + 1
            · by_cases hbad :
                  badSmallArity (smallQArity (a2 - 1)) = false
              · simp [hEq, hbad]
              · have hbad' :
                    badSmallArity (smallQArity (a2 - 1)) = true := by
                  cases h : badSmallArity (smallQArity (a2 - 1)) <;>
                    simp [h] at hbad ⊢
                simp [hEq, hbad']
            · simp [hEq]

theorem rqSeqFits_pair_cpmap0_iff
    {G0 : Hypermap} (h : cpmap0.Dart → G0.Dart)
    (rq1 rq2 : RingQuestion) :
    rqSeqFits G0 cpmap0 h [rq1, rq2] [false, true] = true ↔
      G0.arity (h false) = rq1.outerArity + 1 ∧
        G0.fitQ (G0.node (h false)) rq1.nodeQuestion = true ∧
        G0.arity (h true) = rq2.outerArity + 1 ∧
          G0.fitQ (G0.node (h true)) rq2.nodeQuestion = true := by
  have harity (x : cpmap0.Dart) : cpmap0.arity x = 1 := by
    rw [Hypermap.arity_eq_minimalPeriod]
    exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr rfl
  simp [rqSeqFits, harity]
  tauto

theorem cfquizRec_nil_ringComplement_valid_of_rqSeqProper
    {cp1 : CProg} {qs : RqSeq}
    (hcp1 : CProg.cubic cp1 = true)
    (hproper :
      RqSeqProper (PointedHypermap.injcp cp1 []) qs
        (PointedHypermap.cpRing (CProg.appendRev cp1 []))
        (PointedHypermap.cpRing []))
    (hR : (cfquizRec qs []).isQuizR = true) :
    (∀ x : (PointedHypermap.cpmap
        (CProg.appendRev cp1 [])).map.Dart,
      x ∈ PointedHypermap.cpRing (CProg.appendRev cp1 []) →
        (PointedHypermap.cpmap
          (CProg.appendRev cp1 [])).map.GoodRingArity x) ∧
      ∃ x0 : (PointedHypermap.cpmap (CProg.appendRev cp1 [])).map.Dart,
        (PointedHypermap.cpmap (CProg.appendRev cp1 [])).map.ValidQuizFor
          (fun x =>
            ¬ (PointedHypermap.cpmap
                (CProg.appendRev cp1 [])).map.FaceBand
                (PointedHypermap.cpRing (CProg.appendRev cp1 [])) x)
          x0 (cfquizRec qs []) := by
  have hlen := hproper.length_eq
  rw [PointedHypermap.cpRing_nil] at hlen
  cases qs with
  | nil => simp at hlen
  | cons rq1 qs =>
      cases qs with
      | nil =>
          have hbad : (1 : Nat) = 2 := hlen
          omega
      | cons rq2 qs =>
          cases qs with
          | cons rq3 qs =>
              have hbad :
                  (rq1 :: rq2 :: rq3 :: qs).length = 2 := hlen
              have hleft :
                  3 ≤ (rq1 :: rq2 :: rq3 :: qs).length := by simp
              omega
          | nil =>
              let G0 :=
                (PointedHypermap.cpmap
                  (CProg.appendRev cp1 [])).map
              let h : cpmap0.Dart → G0.Dart :=
                PointedHypermap.injcp cp1 []
              have hguard :=
                (cfquizRec_pair_nil_isQuizR_iff rq1 rq2).mp hR
              rcases hguard with ⟨hk1, hk2, hqa1, hgood2⟩
              let qa1 := largeQArity (rq1.outerArity - 1)
              let qa2 := smallQArity (rq2.outerArity - 1)
              let qz : Quiz :=
                ⟨Question.QaskR qa1 rq2.nodeQuestion,
                  Question.QaskR qa2 rq1.nodeQuestion⟩
              have hqz : cfquizRec [rq1, rq2] [] = qz := by
                simp [cfquizRec, qz, qa1, qa2, hk1, hk2, hqa1,
                  hgood2]
              have hfits :=
                (rqSeqFits_pair_cpmap0_iff h rq1 rq2).mp
                  hproper.fits
              have hE (b : cpmap0.Dart) :
                  h (cpmap0.edge b) = G0.edge (h b) := by
                exact PointedHypermap.injcp_edge_of_cubic
                  cp1 [] hcp1 b
              have hedgeFalse : G0.edge (h false) = h true := by
                simpa [cpmap0] using (hE false).symm
              have hedgeTrue : G0.edge (h true) = h false := by
                simpa [cpmap0] using (hE true).symm
              have hstepFalse :
                  qstepR G0 (h false) = G0.node (h true) := by
                simp [qstepR, hedgeFalse]
              have hstepTrue :
                  qstepR G0 (G0.edge (h false)) =
                    G0.node (h false) := by
                rw [hedgeFalse]
                simp [qstepR, hedgeTrue]
              have hstepFromTrue :
                  qstepR G0 (h true) = G0.node (h false) := by
                simp [qstepR, hedgeTrue]
              have hqa2raw :=
                smallQArity_toNat_eq_add_two_of_not_bad hgood2
              have hqa2bounds := smallQArity_not_bad_iff.mp hgood2
              have hqa2 : qa2.toNat = rq2.outerArity + 1 := by
                dsimp [qa2]
                omega
              have hfitQuiz : G0.fitQuiz (h false) qz = true := by
                apply fitQuiz_qaskR_pair_of_decomp
                · simpa [qa1] using hfits.1.trans hqa1.symm
                · rw [hstepFalse]
                  exact hfits.2.2.2
                · rw [hedgeFalse]
                  exact hfits.2.2.1.trans hqa2.symm
                · rw [hstepTrue]
                  exact hfits.2.1
              let sQuiz := G0.walkQuiz (h false) qz
              let sRq :=
                rqSeqWalk G0 [rq1, rq2]
                  ((PointedHypermap.cpRing []).map h)
              let r0 :=
                PointedHypermap.cpRing (CProg.appendRev cp1 [])
              have hmapRing :
                  (PointedHypermap.cpRing []).map h =
                    [h false, h true] := by
                rw [PointedHypermap.cpRing_nil]
                rfl
              have hmappedRing_mem_sRq
                  {z : G0.Dart}
                  (hz : z ∈ (PointedHypermap.cpRing []).map h) :
                  z ∈ sRq := by
                rw [hmapRing] at hz
                simp at hz
                rcases hz with rfl | rfl
                · dsimp [sRq]
                  rw [hmapRing]
                  simp [rqSeqWalk, hk1]
                · dsimp [sRq]
                  rw [hmapRing]
                  simp [rqSeqWalk, hk1, hk2]
              have hgoodRing :
                  ∀ u : G0.Dart, u ∈ r0 → G0.GoodRingArity u := by
                intro u hu
                have hnotBand :
                    ¬ G0.FaceBand
                        ((PointedHypermap.cpRing []).map h) u := by
                  rintro ⟨z, hz, hzu⟩
                  have hzWalk : z ∈ sRq := hmappedRing_mem_sRq hz
                  have hzuEq : z = u :=
                    Hypermap.FaceSimple.eq_of_faceReachable_of_mem
                      (G := G0) hproper.simple
                      (List.mem_append.mpr (Or.inl hzWalk))
                      (List.mem_append.mpr (Or.inr hu)) hzu
                  have hdisjoint : sRq.Disjoint r0 :=
                    List.disjoint_of_nodup_append hproper.simple.nodup
                  exact hdisjoint hzWalk (hzuEq ▸ hu)
                have hnotCodom : ¬ RqSeqCodom h u := by
                  rintro ⟨b, hb⟩
                  apply hnotBand
                  exact Hypermap.FaceBand.of_mem
                    (G := G0)
                    (List.mem_map.mpr
                      ⟨b, by
                        cases b
                        · exact List.Mem.head _
                        · exact List.Mem.tail _ (List.Mem.head _), hb⟩)
                    (PermReachable.refl G0.face u)
                exact hproper.goodRingArity hu hnotCodom hnotBand
              have hbandWalk (u : G0.Dart) :
                  G0.FaceBand sQuiz u ↔ G0.FaceBand sRq u := by
                have hquiz :
                    G0.FaceBand sQuiz u ↔
                      PermReachable G0.face (h false) u ∨
                        G0.FaceBand
                          (G0.walkQ (G0.node (h true))
                            rq2.nodeQuestion) u ∨
                          PermReachable G0.face (h true) u ∨
                            G0.FaceBand
                              (G0.walkQ (G0.node (h false))
                                rq1.nodeQuestion) u := by
                  dsimp [sQuiz]
                  simp [qz, Hypermap.walkQuiz, Hypermap.walkQ,
                    hstepFalse, hstepFromTrue, hedgeFalse,
                    Hypermap.FaceBand.append, Hypermap.FaceBand.cons]
                have hrq :
                    G0.FaceBand sRq u ↔
                      PermReachable G0.face (h false) u ∨
                        G0.FaceBand
                          (G0.walkQ (G0.node (h false))
                            rq1.nodeQuestion) u ∨
                          PermReachable G0.face (h true) u ∨
                            G0.FaceBand
                              (G0.walkQ (G0.node (h true))
                                rq2.nodeQuestion) u := by
                  dsimp [sRq]
                  rw [hmapRing]
                  simp [rqSeqWalk, hk1, hk2,
                    Hypermap.FaceBand.append,
                    Hypermap.FaceBand.cons]
                constructor
                · intro hu
                  rcases hquiz.mp hu with h0 | h2 | h1 | h3
                  · exact hrq.mpr (Or.inl h0)
                  · exact hrq.mpr (Or.inr (Or.inr (Or.inr h2)))
                  · exact hrq.mpr (Or.inr (Or.inr (Or.inl h1)))
                  · exact hrq.mpr (Or.inr (Or.inl h3))
                · intro hu
                  rcases hrq.mp hu with h0 | h3 | h1 | h2
                  · exact hquiz.mpr (Or.inl h0)
                  · exact hquiz.mpr (Or.inr (Or.inr (Or.inr h3)))
                  · exact hquiz.mpr (Or.inr (Or.inr (Or.inl h1)))
                  · exact hquiz.mpr (Or.inr (Or.inl h2))
              have hlenWalk : sQuiz.length = sRq.length := by
                have hquiz :
                    sQuiz.length =
                      2 + rq1.nodeQuestion.flat.length +
                        rq2.nodeQuestion.flat.length := by
                  dsimp [sQuiz]
                  simp [qz, Hypermap.walkQuiz, Hypermap.walkQ,
                    Hypermap.length_walkQ]
                  omega
                have hrq :
                    sRq.length =
                      2 + rq1.nodeQuestion.flat.length +
                        rq2.nodeQuestion.flat.length := by
                  dsimp [sRq]
                  rw [hmapRing]
                  simp [rqSeqWalk, hk1, hk2,
                    Hypermap.length_walkQ]
                  omega
                exact hquiz.trans hrq.symm
              have hbandCombined (u : G0.Dart) :
                  G0.FaceBand (sQuiz ++ r0) u ↔
                    G0.FaceBand (sRq ++ r0) u := by
                simp only [Hypermap.FaceBand.append]
                rw [hbandWalk]
              have hlenCombined :
                  (sQuiz ++ r0).length = (sRq ++ r0).length := by
                simp [hlenWalk]
              have hsimpleCombined : G0.FaceSimple (sQuiz ++ r0) :=
                (Hypermap.FaceSimple.congr_of_faceBand_iff_of_length_eq
                  (G := G0) hbandCombined hlenCombined).2 hproper.simple
              have hcoverRq (u : G0.Dart) :
                  G0.FaceBand (sRq ++ r0) u := by
                apply (hproper.covers u).2
                by_cases hcodom : RqSeqCodom h u
                · rcases hcodom with ⟨b, rfl⟩
                  have hb : b ∈ PointedHypermap.cpRing [] := by
                    rw [PointedHypermap.cpRing_nil]
                    cases b
                    · exact List.Mem.head _
                    · exact List.Mem.tail _ (List.Mem.head _)
                  exact Or.inr
                    (Hypermap.FaceBand.of_mem
                      (G := G0)
                      (List.mem_map.mpr ⟨b, hb, rfl⟩)
                      (PermReachable.refl G0.face (h b)))
                · exact Or.inl hcodom
              have hcoverCombined (u : G0.Dart) :
                  G0.FaceBand (sQuiz ++ r0) u :=
                (hbandCombined u).2 (hcoverRq u)
              have hpartition (u : G0.Dart) :
                  G0.FaceBand sQuiz u ↔ ¬ G0.FaceBand r0 u :=
                Hypermap.FaceSimple.faceBand_left_iff_not_right_of_append_cover
                  (G := G0) hsimpleCombined hcoverCombined u
              have hsimpleQuiz : G0.FaceSimple sQuiz := by
                rw [Hypermap.FaceSimple] at hsimpleCombined ⊢
                exact (List.pairwise_append.mp hsimpleCombined).1
              refine ⟨hgoodRing, h false, ?_⟩
              rw [hqz]
              exact
                { rightRooted := by simpa [hqz] using hR
                  fits := hfitQuiz
                  simple := hsimpleQuiz
                  covers := hpartition }

/-- Coq `cfquizP`: traverse a configuration program backwards while carrying
the complete ring-question invariant.  The disjunction on `cp2` is the exact
recursive tail condition: a configuration ends at the distinguished initial
`Y`, whose recursive tail is the empty base program. -/
theorem cfquizP :
    ∀ {cp1 cp2 : CProg} {qs : RqSeq},
      CProg.cubic cp1 = true →
      (cp2 = [] ∨ CProg.config cp2 = true) →
      RqSeqProper (PointedHypermap.injcp cp1 cp2) qs
        (PointedHypermap.cpRing (CProg.appendRev cp1 cp2))
        (PointedHypermap.cpRing cp2) →
      (cfquizRec qs cp2).isQuizR = true →
      (∀ x : (PointedHypermap.cpmap
          (CProg.appendRev cp1 cp2)).map.Dart,
        x ∈ PointedHypermap.cpRing (CProg.appendRev cp1 cp2) →
          (PointedHypermap.cpmap
            (CProg.appendRev cp1 cp2)).map.GoodRingArity x) ∧
        ∃ x0 : (PointedHypermap.cpmap
            (CProg.appendRev cp1 cp2)).map.Dart,
          (PointedHypermap.cpmap
              (CProg.appendRev cp1 cp2)).map.ValidQuizFor
            (fun x =>
              ¬ (PointedHypermap.cpmap
                  (CProg.appendRev cp1 cp2)).map.FaceBand
                  (PointedHypermap.cpRing
                    (CProg.appendRev cp1 cp2)) x)
            x0 (cfquizRec qs cp2)
  | cp1, [], qs, hcp1, _hcp2, hproper, hR =>
      cfquizRec_nil_ringComplement_valid_of_rqSeqProper
        hcp1 hproper hR
  | cp1, s :: cp2, qs, hcp1, hcp2, hproper, hR => by
      have hcfg : CProg.config (s :: cp2) = true := by
        rcases hcp2 with hnil | hcfg
        · cases hnil
        · exact hcfg
      cases qs with
      | nil =>
          change noQuiz.isQuizR = true at hR
          simp [noQuiz, Quiz.isQuizR, Question.isQaskR] at hR
      | cons rq1 qs =>
          cases qs with
          | nil =>
              change noQuiz.isQuizR = true at hR
              simp [noQuiz, Quiz.isQuizR, Question.isQaskR] at hR
          | cons rq2 qs =>
              cases qs with
              | nil =>
                  change noQuiz.isQuizR = true at hR
                  simp [noQuiz, Quiz.isQuizR, Question.isQaskR] at hR
              | cons rq3 qs =>
                  cases s with
                  | rotate n =>
                      have htail : CProg.config cp2 = true := by
                        simpa [CProg.config] using hcfg
                      have hring :
                          PointedHypermap.cpRing
                              (CpStep.rotate n :: cp2) =
                            CProg.rotateLeft n
                              (PointedHypermap.cpRing cp2) :=
                        PointedHypermap.cpRing_rotate_of_ringCycle
                          (PointedHypermap.cpRingCycle_of_config htail)
                      have hproper' :=
                        rqSeqProper_rotateStep
                          (cp1 := cp1) (cp2 := cp2) hring hproper
                      have hR' :
                          (cfquizRec
                            (CProg.rotateRight n
                              (rq1 :: rq2 :: rq3 :: qs)) cp2).isQuizR =
                            true := by
                        simpa [cfquizRec] using hR
                      simpa [cfquizRec] using
                        (cfquizP
                          (cp1 := CpStep.rotate n :: cp1)
                          (cp2 := cp2)
                          (qs := CProg.rotateRight n
                            (rq1 :: rq2 :: rq3 :: qs))
                          (by simpa [CProg.cubic] using hcp1)
                          (Or.inr htail) hproper' hR')
                  | reverseRotate =>
                      simp [CProg.config] at hcfg
                  | y =>
                      have htail :
                          cp2 = [] ∨ CProg.config cp2 = true := by
                        cases cp2 with
                        | nil => exact Or.inl rfl
                        | cons t cp =>
                            exact Or.inr (by
                              simpa [CProg.config] using hcfg)
                      have hR' :
                          (cfquizRec
                            (cfquizY rq1 rq2 (rqsY rq1 rq3 qs))
                            cp2).isQuizR = true := by
                        simpa [cfquizRec] using hR
                      have hproper' :=
                        rqSeqProper_yStep
                          (cp1 := cp1) (cp2 := cp2)
                          hcp1 htail hproper hR'
                      simpa [cfquizRec] using
                        (cfquizP
                          (cp1 := CpStep.y :: cp1)
                          (cp2 := cp2)
                          (qs := cfquizY rq1 rq2 (rqsY rq1 rq3 qs))
                          (by simpa [CProg.cubic] using hcp1)
                          htail hproper' hR')
                  | h =>
                      have htail : CProg.config cp2 = true := by
                        simpa [CProg.config] using hcfg
                      have hR' :
                          (cfquizRec
                            (cfquizH rq1 rq2 (rqsH rq1 rq3 qs))
                            cp2).isQuizR = true := by
                        simpa [cfquizRec] using hR
                      have hproper' :=
                        rqSeqProper_hStep
                          (cp1 := cp1) (cp2 := cp2)
                          hcp1 htail hproper hR'
                      simpa [cfquizRec] using
                        (cfquizP
                          (cp1 := CpStep.h :: cp1)
                          (cp2 := cp2)
                          (qs := cfquizH rq1 rq2 (rqsH rq1 rq3 qs))
                          (by simpa [CProg.cubic] using hcp1)
                          (Or.inr htail) hproper' hR')
                  | u =>
                      simp [CProg.config] at hcfg
                  | k =>
                      simp [CProg.config] at hcfg
                  | a =>
                      simp [CProg.config] at hcfg

/-- Coq `cfquizP` specialized to a complete configuration: all perimeter
faces have accepted arity, and the raw quiz is valid for the perimeter
complement. -/
theorem rawConfigQuiz_ringGood_and_ringComplement_valid_of_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (rawConfigQuiz cf).isQuizR = true) :
    (∀ x : cf.map.map.Dart, x ∈ cf.ringDarts →
      cf.map.map.GoodRingArity x) ∧
      ∃ x0 : cf.map.map.Dart,
        cf.map.map.ValidQuizFor
          (fun x => ¬ cf.map.map.FaceBand cf.ringDarts x)
          x0 (rawConfigQuiz cf) := by
  have hsimpleFull :=
    PointedHypermap.cpMapSimple_of_config (cp := cf.program) hcf
  have hsimple :
      (PointedHypermap.cpmap cf.program).map.FaceSimple
        (PointedHypermap.cpRing cf.program) := by
    have hsimple' :
        (PointedHypermap.cpmap cf.program).map.FaceSimple
          (PointedHypermap.cpRing cf.program ++
            PointedHypermap.cpKernel cf.program) := by
      simpa [PointedHypermap.cpMapSimple] using hsimpleFull
    exact (List.pairwise_append.mp hsimple').1
  have hinitial :=
    rqSeqProper_initial_identity
      (PointedHypermap.cpmap cf.program).map
      (PointedHypermap.cpRing cf.program) hsimple
  have hproper :
      RqSeqProper
        (PointedHypermap.injcp [] cf.program)
        (initialRingQuestions (CProg.ringSize cf.program))
        (PointedHypermap.cpRing
          (CProg.appendRev [] cf.program))
        (PointedHypermap.cpRing cf.program) := by
    simpa using hinitial
  have hvalid :=
    cfquizP (cp1 := []) (cp2 := cf.program)
      (qs := initialRingQuestions (CProg.ringSize cf.program))
      (by simp [CProg.cubic]) (Or.inr hcf) hproper hR
  simpa [Config.map, Config.ringDarts, rawConfigQuiz] using hvalid

/-- Source fit, face simplicity, and exact perimeter-complement coverage for
the raw configuration quiz. -/
theorem rawConfigQuiz_ringComplement_valid_of_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (rawConfigQuiz cf).isQuizR = true) :
    ∃ x0 : cf.map.map.Dart,
      cf.map.map.ValidQuizFor
        (fun x => ¬ cf.map.map.FaceBand cf.ringDarts x)
        x0 (rawConfigQuiz cf) :=
  (rawConfigQuiz_ringGood_and_ringComplement_valid_of_isQuizR
    hcf hR).2

/-- Coq `cfquizP`'s perimeter-arity half for the source configuration. -/
theorem goodRingArity_of_mem_ringDarts_of_rawConfigQuiz_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (rawConfigQuiz cf).isQuizR = true)
    {x : cf.map.map.Dart}
    (hx : x ∈ cf.ringDarts) :
    cf.map.map.GoodRingArity x :=
  (rawConfigQuiz_ringGood_and_ringComplement_valid_of_isQuizR
    hcf hR).1 x hx

theorem allTrue_eq_true_iff {bs : List Bool} :
    allTrue bs = true ↔ ∀ b ∈ bs, b = true := by
  induction bs with
  | nil =>
      simp [allTrue]
  | cons b bs ih =>
      cases b
      · simp [allTrue]
      · simp [allTrue]

theorem eq_true_of_mem_allTrue {bs : List Bool} {b : Bool}
    (hall : allTrue bs = true)
    (hb : b ∈ bs) :
    b = true :=
  (allTrue_eq_true_iff.mp hall) b hb

theorem false_not_mem_of_allTrue {bs : List Bool}
    (hall : allTrue bs = true) :
    false ∉ bs := by
  intro hfalse
  have h := eq_true_of_mem_allTrue hall hfalse
  cases h

theorem countTrue_eq_length_of_allTrue {bs : List Bool}
    (hall : allTrue bs = true) :
    CfMask.countTrue bs = bs.length := by
  have hfalse :
      CProg.countFalse bs = 0 :=
    (CfMask.countFalse_eq_zero_iff bs).2
      (allTrue_eq_true_iff.mp hall)
  have hsum := CfMask.countFalse_add_countTrue bs
  omega

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
