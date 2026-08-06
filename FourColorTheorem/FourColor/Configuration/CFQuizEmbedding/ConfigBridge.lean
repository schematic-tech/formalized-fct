import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.RadiusTwo

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

@[simp]
theorem noQuiz_isQuizR :
    noQuiz.isQuizR = false := by
  simp [noQuiz, Quiz.isQuizR, Question.isQaskR]

@[simp]
theorem cfquizRec_nil_eq_noQuiz (cp : CProg) :
    cfquizRec [] cp = noQuiz := by
  cases cp <;> rfl

@[simp]
theorem cfquizRec_singleton_eq_noQuiz
    (rq : RingQuestion) (cp : CProg) :
    cfquizRec [rq] cp = noQuiz := by
  cases cp <;> rfl

@[simp]
theorem cfquizRec_pair_cons_eq_noQuiz
    (rq1 rq2 : RingQuestion) (s : CpStep) (cp : CProg) :
    cfquizRec [rq1, rq2] (s :: cp) = noQuiz := by
  rfl

theorem cfquizRec_nil_isQuizR_false (cp : CProg) :
    (cfquizRec [] cp).isQuizR = false := by
  simp

theorem cfquizRec_singleton_isQuizR_false
    (rq : RingQuestion) (cp : CProg) :
    (cfquizRec [rq] cp).isQuizR = false := by
  simp

theorem cfquizRec_pair_cons_isQuizR_false
    (rq1 rq2 : RingQuestion) (s : CpStep) (cp : CProg) :
    (cfquizRec [rq1, rq2] (s :: cp)).isQuizR = false := by
  simp

theorem cfquizRec_isQuizR_length_ge_two
    {qs : RqSeq} {cp : CProg}
    (hR : (cfquizRec qs cp).isQuizR = true) :
    2 ≤ qs.length := by
  cases qs with
  | nil =>
      simp at hR
  | cons rq qs =>
      cases qs with
      | nil =>
          simp at hR
      | cons rq' qs =>
          simp

theorem cfquizRec_cons_program_isQuizR_length_ge_three
    {qs : RqSeq} {s : CpStep} {cp : CProg}
    (hR : (cfquizRec qs (s :: cp)).isQuizR = true) :
    3 ≤ qs.length := by
  cases qs with
  | nil =>
      simp at hR
  | cons rq1 qs =>
      cases qs with
      | nil =>
          simp at hR
      | cons rq2 qs =>
          cases qs with
          | nil =>
              simp at hR
          | cons rq3 qs =>
              simp

theorem configQuiz_eq_noQuiz_of_cpradius2_eq_false
    {cf : Config}
    (h : cpradius2 cf.program (CProg.kernelSize cf.program) = false) :
    configQuiz cf = noQuiz := by
  simp [configQuiz, h]

theorem configQuiz_eq_rawConfigQuiz_of_cpradius2_eq_true
    {cf : Config}
    (h : cpradius2 cf.program (CProg.kernelSize cf.program) = true) :
    configQuiz cf = rawConfigQuiz cf := by
  simp [configQuiz, h]

theorem configQuiz_isQuizR_eq_true_iff
    {cf : Config} :
    (configQuiz cf).isQuizR = true ↔
      cpradius2 cf.program (CProg.kernelSize cf.program) = true ∧
        (rawConfigQuiz cf).isQuizR = true := by
  unfold configQuiz
  by_cases h : cpradius2 cf.program (CProg.kernelSize cf.program) = true
  · simp [h]
  · have hfalse :
        cpradius2 cf.program (CProg.kernelSize cf.program) = false := by
      cases hc : cpradius2 cf.program (CProg.kernelSize cf.program) <;>
        simp [hc] at h ⊢
    simp [hfalse]

theorem cpradius2_of_configQuiz_isQuizR
    {cf : Config}
    (hR : (configQuiz cf).isQuizR = true) :
    cpradius2 cf.program (CProg.kernelSize cf.program) = true := by
  exact ((configQuiz_isQuizR_eq_true_iff (cf := cf)).1 hR).1

theorem config_radiusTwo_kernelSet_of_configQuiz_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (configQuiz cf).isQuizR = true)
    (hsound :
      ∀ m : CfMask, CfMask.Proper cf.program m →
        PointedHypermap.cpMaskAdjSound cf.program m) :
    cf.map.map.RadiusTwo cf.kernelSet :=
  config_radiusTwo_kernelSet_of_cpradius2_eq_true
    hcf (cpradius2_of_configQuiz_isQuizR hR) hsound

theorem rawConfigQuiz_isQuizR_of_configQuiz_isQuizR
    {cf : Config}
    (hR : (configQuiz cf).isQuizR = true) :
    (rawConfigQuiz cf).isQuizR = true :=
  ((configQuiz_isQuizR_eq_true_iff (cf := cf)).1 hR).2

theorem configQuiz_isQuizR_of_cpradius2_of_rawConfigQuiz_isQuizR
    {cf : Config}
    (hradius : cpradius2 cf.program (CProg.kernelSize cf.program) = true)
    (hraw : (rawConfigQuiz cf).isQuizR = true) :
    (configQuiz cf).isQuizR = true :=
  (configQuiz_isQuizR_eq_true_iff (cf := cf)).2 ⟨hradius, hraw⟩

theorem exists_radiusTwoMaskWitness_of_configQuiz_isQuizR
    {cf : Config}
    (hR : (configQuiz cf).isQuizR = true) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      RadiusTwoMaskWitness cf.program i :=
  exists_witness_of_cpradius2_eq_true
    (cpradius2_of_configQuiz_isQuizR hR)

theorem exists_radiusTwoKernelCenter_all_true_of_configQuiz_isQuizR
    {cf : Config}
    (hR : (configQuiz cf).isQuizR = true) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      ∀ (k : Nat) (hk : k < CProg.kernelSize cf.program),
        (radiusTwoKernelMask cf.program i).get
          ⟨k, by simpa [radiusTwoKernelMask_length] using hk⟩ =
            true := by
  rcases exists_radiusTwoMaskWitness_of_configQuiz_isQuizR hR with
    ⟨i, hi, hw⟩
  exact
    ⟨i, hi, fun k hk =>
      hw.get_eq_true_of_kernel_lt hk⟩

theorem exists_radiusTwoKernelCenter_dart_of_configQuiz_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (configQuiz cf).isQuizR = true) :
    ∃ (i : Nat) (_hi : i < CProg.kernelSize cf.program)
      (x : cf.map.map.Dart),
        x ∈ cf.kernelDarts ∧
          cf.maskDarts (CfMask.cfmask1 cf.program i) = [x] ∧
            CfMask.select (radiusTwoKernelMask cf.program i)
              cf.kernelDarts = cf.kernelDarts := by
  rcases exists_radiusTwoMaskWitness_of_configQuiz_isQuizR hR with
    ⟨i, hi, hw⟩
  let x : cf.map.map.Dart :=
    cf.kernelDarts.get
      ⟨i, by
        rw [Config.length_kernelDarts_of_wellFormed hcf]
        exact hi⟩
  refine ⟨i, hi, x, ?_, ?_, ?_⟩
  · exact List.get_mem cf.kernelDarts
      ⟨i, by
        rw [Config.length_kernelDarts_of_wellFormed hcf]
        exact hi⟩
  · simpa [x] using
      Config.maskDarts_cfmask1_eq_singleton_of_wellFormed
        (cf := cf) (i := i) hcf hi
  · exact hw.select_eq_self_of_length
      (Config.length_kernelDarts_of_wellFormed hcf)

/-- Source-side validity target for Coq `valid_cfquiz`: the compiled
configuration quiz is valid for the semantic kernel face band of the
configuration map. -/
def ConfigQuizSourceValid (cf : Config) : Prop :=
  ∃ x0 : cf.map.map.Dart,
    cf.map.map.ValidQuizFor cf.kernelSet x0 (configQuiz cf)

/-- Final `valid_cfquiz` extraction: Coq first obtains validity for the
complement of the perimeter face band, then rewrites that predicate to the
semantic kernel face band using `cpmap_simple` and `cpmap_cover`. -/
theorem configQuizSourceValid_of_ringComplement
    {cf : Config}
    (hcf : cf.WellFormed)
    {x0 : cf.map.map.Dart}
    (hvalid :
      cf.map.map.ValidQuizFor
        (fun x => ¬ cf.map.map.FaceBand cf.ringDarts x)
        x0 (configQuiz cf)) :
    ConfigQuizSourceValid cf := by
  refine ⟨x0,
    { rightRooted := hvalid.rightRooted
      fits := hvalid.fits
      simple := hvalid.simple
      covers := ?_ }⟩
  intro x
  rw [hvalid.covers]
  simpa [Config.map, Config.ringDarts, Config.kernelDarts,
    Config.kernelSet] using
    (PointedHypermap.cpKernel_faceBand_iff_not_cpRing_faceBand
      (PointedHypermap.cpMapSimple_of_config hcf)
      (PointedHypermap.cpMapCover_of_config hcf) x).symm

/-- Coq `valid_cfquiz`: every right-rooted compiled quiz of a well-formed
configuration is valid for its source kernel. -/
theorem configQuizSourceValid_of_isQuizR
    {cf : Config}
    (hcf : cf.WellFormed)
    (hR : (configQuiz cf).isQuizR = true) :
    ConfigQuizSourceValid cf := by
  have hrawR : (rawConfigQuiz cf).isQuizR = true :=
    rawConfigQuiz_isQuizR_of_configQuiz_isQuizR hR
  obtain ⟨x0, hraw⟩ :=
    rawConfigQuiz_ringComplement_valid_of_isQuizR hcf hrawR
  have heq : configQuiz cf = rawConfigQuiz cf :=
    configQuiz_eq_rawConfigQuiz_of_cpradius2_eq_true
      (cpradius2_of_configQuiz_isQuizR hR)
  apply configQuizSourceValid_of_ringComplement hcf
  simpa [heq] using hraw

namespace ConfigQuizSourceValid

theorem rightRooted
    {cf : Config}
    (hsource : ConfigQuizSourceValid cf) :
    (configQuiz cf).isQuizR = true := by
  rcases hsource with ⟨_x0, hvalid⟩
  exact hvalid.rightRooted

theorem exists_radiusTwoKernelCenter_dart
    {cf : Config}
    (hsource : ConfigQuizSourceValid cf)
    (hcf : cf.WellFormed) :
    ∃ (i : Nat) (_hi : i < CProg.kernelSize cf.program)
      (x : cf.map.map.Dart),
        x ∈ cf.kernelDarts ∧
          cf.maskDarts (CfMask.cfmask1 cf.program i) = [x] ∧
            CfMask.select (radiusTwoKernelMask cf.program i)
              cf.kernelDarts = cf.kernelDarts :=
  exists_radiusTwoKernelCenter_dart_of_configQuiz_isQuizR
    hcf hsource.rightRooted

end ConfigQuizSourceValid

theorem configQuiz_eq_rawConfigQuiz_of_isQuizR
    {cf : Config}
    (hR : (configQuiz cf).isQuizR = true) :
    configQuiz cf = rawConfigQuiz cf := by
  exact configQuiz_eq_rawConfigQuiz_of_cpradius2_eq_true
    (cpradius2_of_configQuiz_isQuizR hR)

theorem configQuiz_preembedding_of_valid
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.Dart} {cf : Config}
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hfitH : H.fitQuiz x0H (configQuiz cf) = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    Preembedding G H A (hvalid.embedMap H x0H) :=
  hvalid.embedMap_preembedding
    (H := H) (x0H := x0H)
    hfitH hPlainG hPlainH hCubicG hCubicH

theorem configQuiz_preembedding_of_valid_mirrorTarget
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {x0H : H.mirror.Dart} {cf : Config}
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hfitH : H.mirror.fitQuiz x0H (configQuiz cf) = true)
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    Preembedding G H.mirror A (hvalid.embedMap H.mirror x0H) :=
  hvalid.embedMap_preembedding
    (H := H.mirror) (x0H := x0H)
    hfitH hPlainG hPlainH.mirror hCubicG hCubicH.mirror

theorem configQuizMirrorFitWitness_preembedding_of_valid
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf)
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    (∃ x0H : H.Dart,
      Preembedding G H A (hvalid.embedMap H x0H)) ∨
      (∃ x0H : H.mirror.Dart,
        Preembedding G H.mirror A
          (hvalid.embedMap H.mirror x0H)) := by
  rcases hwit with ⟨_hR, hfit | hfitMirror⟩
  · rcases hfit with ⟨x0H, hx0H⟩
    exact Or.inl
      ⟨x0H,
        configQuiz_preembedding_of_valid
          (cf := cf) hvalid hx0H
          hPlainG hPlainH hCubicG hCubicH⟩
  · rcases hfitMirror with ⟨x0H, hx0H⟩
    exact Or.inr
      ⟨x0H,
        configQuiz_preembedding_of_valid_mirrorTarget
          (cf := cf) hvalid hx0H
          hPlainG hPlainH hCubicG hCubicH⟩

theorem configQuizFitWitness_preembedding_of_valid
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf)
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic) :
    (∃ x0H : H.Dart,
      Preembedding G H A (hvalid.embedMap H x0H)) ∨
      (∃ x0H : H.mirror.Dart,
        Preembedding G H.mirror A
          (hvalid.embedMap H.mirror x0H)) := by
  exact
    configQuizMirrorFitWitness_preembedding_of_valid
      (cf := cf)
      (QuizTree.Hypermap.ConfigQuizMirrorFitWitness_of_raw
        (G := H) hPlainH hCubicH hwit)
      hvalid hPlainG hPlainH hCubicG hCubicH

theorem cpradius2_of_configQuizMirrorFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf) :
    cpradius2 cf.program (CProg.kernelSize cf.program) = true :=
  cpradius2_of_configQuiz_isQuizR hwit.1

theorem rawConfigQuiz_isQuizR_of_configQuizMirrorFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf) :
    (rawConfigQuiz cf).isQuizR = true :=
  rawConfigQuiz_isQuizR_of_configQuiz_isQuizR hwit.1

theorem configQuiz_eq_rawConfigQuiz_of_configQuizMirrorFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf) :
    configQuiz cf = rawConfigQuiz cf :=
  configQuiz_eq_rawConfigQuiz_of_isQuizR hwit.1

theorem exists_radiusTwoMaskWitness_of_configQuizMirrorFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      RadiusTwoMaskWitness cf.program i :=
  exists_radiusTwoMaskWitness_of_configQuiz_isQuizR hwit.1

theorem exists_radiusTwoKernelCenter_all_true_of_configQuizMirrorFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      ∀ (k : Nat) (hk : k < CProg.kernelSize cf.program),
        (radiusTwoKernelMask cf.program i).get
          ⟨k, by simpa [radiusTwoKernelMask_length] using hk⟩ =
            true :=
  exists_radiusTwoKernelCenter_all_true_of_configQuiz_isQuizR hwit.1

theorem cpradius2_of_configQuizFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf) :
    cpradius2 cf.program (CProg.kernelSize cf.program) = true :=
  cpradius2_of_configQuiz_isQuizR hwit.1

theorem rawConfigQuiz_isQuizR_of_configQuizFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf) :
    (rawConfigQuiz cf).isQuizR = true :=
  rawConfigQuiz_isQuizR_of_configQuiz_isQuizR hwit.1

theorem configQuiz_eq_rawConfigQuiz_of_configQuizFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf) :
    configQuiz cf = rawConfigQuiz cf :=
  configQuiz_eq_rawConfigQuiz_of_isQuizR hwit.1

theorem exists_radiusTwoMaskWitness_of_configQuizFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      RadiusTwoMaskWitness cf.program i :=
  exists_radiusTwoMaskWitness_of_configQuiz_isQuizR hwit.1

theorem exists_radiusTwoKernelCenter_all_true_of_configQuizFitWitness
    {H : Hypermap} {cf : Config}
    (hwit : QuizTree.Hypermap.ConfigQuizFitWitness H cf) :
    ∃ i : Nat, i < CProg.kernelSize cf.program ∧
      ∀ (k : Nat) (hk : k < CProg.kernelSize cf.program),
        (radiusTwoKernelMask cf.program i).get
          ⟨k, by simpa [radiusTwoKernelMask_length] using hk⟩ =
            true :=
  exists_radiusTwoKernelCenter_all_true_of_configQuiz_isQuizR hwit.1

theorem not_configQuizMirrorFitWitness_of_valid_no_preembedding
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {cf : Config}
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hno :
      (∀ x0H : H.Dart,
        ¬ Preembedding G H A (hvalid.embedMap H x0H)) ∧
        ∀ x0H : H.mirror.Dart,
          ¬ Preembedding G H.mirror A
            (hvalid.embedMap H.mirror x0H)) :
    ¬ QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf := by
  intro hwit
  rcases configQuizMirrorFitWitness_preembedding_of_valid
      (cf := cf) hwit hvalid
      hPlainG hPlainH hCubicG hCubicH with
    hpre | hpreMirror
  · rcases hpre with ⟨x0H, hpre⟩
    exact hno.1 x0H hpre
  · rcases hpreMirror with ⟨x0H, hpre⟩
    exact hno.2 x0H hpre

theorem not_configQuizFitWitness_of_valid_no_preembedding
    {G H : Hypermap} {A : G.Dart → Prop}
    {x0G : G.Dart} {cf : Config}
    (hvalid : G.ValidQuizFor A x0G (configQuiz cf))
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hno :
      (∀ x0H : H.Dart,
        ¬ Preembedding G H A (hvalid.embedMap H x0H)) ∧
        ∀ x0H : H.mirror.Dart,
          ¬ Preembedding G H.mirror A
            (hvalid.embedMap H.mirror x0H)) :
    ¬ QuizTree.Hypermap.ConfigQuizFitWitness H cf := by
  intro hwit
  exact not_configQuizMirrorFitWitness_of_valid_no_preembedding
    (cf := cf) hvalid hPlainG hPlainH hCubicG hCubicH hno
    (QuizTree.Hypermap.ConfigQuizMirrorFitWitness_of_raw
      (G := H) hPlainH hCubicH hwit)

namespace ConfigQuizSourceValid

theorem not_configQuizMirrorFitWitness_of_no_preembedding
    {cf : Config} {H : Hypermap}
    (hsource : ConfigQuizSourceValid cf)
    (hcf : cf.WellFormed)
    (hPlainSource : cf.map.map.Plain) (hPlainH : H.Plain)
    (hCubicH : H.Cubic)
    (hno :
      ∀ (x0G : cf.map.map.Dart)
        (hvalid :
          cf.map.map.ValidQuizFor cf.kernelSet x0G (configQuiz cf)),
        (∀ x0H : H.Dart,
          ¬ Preembedding cf.map.map H cf.kernelSet
            (hvalid.embedMap H x0H)) ∧
          ∀ x0H : H.mirror.Dart,
            ¬ Preembedding cf.map.map H.mirror cf.kernelSet
              (hvalid.embedMap H.mirror x0H)) :
    ¬ QuizTree.Hypermap.ConfigQuizMirrorFitWitness H cf := by
  rcases hsource with ⟨x0G, hvalid⟩
  exact not_configQuizMirrorFitWitness_of_valid_no_preembedding
    (cf := cf) hvalid
    hPlainSource hPlainH
    (Config.map_cubicOn_kernelSet_of_wellFormed hcf) hCubicH
    (hno x0G hvalid)

end ConfigQuizSourceValid

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
