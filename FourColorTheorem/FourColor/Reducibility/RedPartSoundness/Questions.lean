import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Steps

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal

/-- The validity and geometric origin facts shared by every right-fan branch.
Bundling them here keeps the branch proofs focused on their differing fan data. -/
theorem valid_hubRightShift_and_zorg_left_eq_face
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hvalidStep : ZippedStepValid ctx)
    (hstep : ZippedStepSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr)) :
    let zpR := zshiftR ctx Zhub (mkZ Zhub pl pr)
    zpvalid ctx (mkZ Zhubr zpR.left zpR.right) ∧
      zorg G x0 zpR.left = G.face (zorg G x0 pl) := by
  let zp := mkZ Zhub pl pr
  let zpR := zshiftR ctx Zhub zp
  have hstepREq : zstepR ctx zp = mkZ Zhubr zpR.left zpR.right := by
    simpa [zp, zpR, zstepR] using
      (mkZ_zshiftR_left_right_eq ctx Zhubr Zhub zp).symm
  have hproperRhub : (mkZ Zhubr zpR.left zpR.right).proper = true := by
    simp [mkZ, ZPart.proper]
  have hvalidRhub : zpvalid ctx (mkZ Zhubr zpR.left zpR.right) := by
    have h := hvalidStep.stepR (zp := zp) (by simpa [zp] using hvalid)
    simpa [hstepREq] using h
  have hshiftDart :
      zdart G x0 (mkZ Zhubr zpR.left zpR.right) =
        qstepR G (zdart G x0 zp) := by
    have hfit := hstep.stepR (zp := zp) (by simpa [zp] using hvalid)
    have hproperStep : (zstepR ctx zp).proper = true := by
      simpa [hstepREq] using hproperRhub
    simpa [hstepREq] using hfit hproperStep
  have hzorgR : zorg G x0 zpR.left = G.face (zorg G x0 pl) := by
    have hnn :
        G.node (G.node (zorg G x0 zpR.left)) =
          G.node (G.node (G.face (zorg G x0 pl))) := by
      calc
        G.node (G.node (zorg G x0 zpR.left))
            = zdart G x0 (mkZ Zhubr zpR.left zpR.right) := by rfl
        _ = qstepR G (zdart G x0 zp) := hshiftDart
        _ = G.node (G.node (G.face (zorg G x0 pl))) := by
              simpa [zp, mkZ, zdart, zporg, zmove] using
                Hypermap.qstepR_eq_node_node_face_of_plain
                  (G := G) hPlain (zorg G x0 pl)
    exact G.node.injective (G.node.injective hnn)
  simpa [zpR, zp] using And.intro hvalidRhub hzorgR

/-- Every local view of a valid right-shifted hub has the same valid zipper
sectors.  This is the form used by fan branches, which inspect several local
darts without changing those sectors. -/
theorem valid_hubRightShift_locations_and_zorg_left_eq_face
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart} {pl pr : Part}
    (hPlain : G.Plain)
    (hvalidStep : ZippedStepValid ctx)
    (hstep : ZippedStepSound G ctx x0)
    (hvalid : zpvalid ctx (mkZ Zhub pl pr)) :
    let zpR := zshiftR ctx Zhub (mkZ Zhub pl pr)
    (∀ loc, zpvalid ctx (mkZ loc zpR.left zpR.right)) ∧
      zorg G x0 zpR.left = G.face (zorg G x0 pl) := by
  have hshift := valid_hubRightShift_and_zorg_left_eq_face
    (G := G) (ctx := ctx) (x0 := x0) (pl := pl) (pr := pr)
    hPlain hvalidStep hstep hvalid
  exact ⟨fun _ => zpvalid_mkZ_loc hshift.1, hshift.2⟩

/-- A root-arity fact at the right hub is the spoke arity at the zipper's
left origin. -/
theorem arity_edge_zorg_eq_of_hubr
    {G : Hypermap.{u}} (hCubic : G.Cubic)
    {x0 : G.Dart} {pl pr : Part} {n : Nat}
    (hroot : G.arity (zdart G x0 (mkZ Zhubr pl pr)) = n) :
    G.arity (G.edge (zorg G x0 pl)) = n := by
  simpa [mkZ, zdart, zporg, zmove,
    Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic,
    Hypermap.arity_face] using hroot

theorem arity_face_iter_edge_zorg_eq_of_hubr
    {G : Hypermap.{u}} (hCubic : G.Cubic) (i : Nat)
    {x0 : G.Dart} {pl pr : Part} {n : Nat}
    (hroot : G.arity (zdart G x0 (mkZ Zhubr pl pr)) = n) :
    G.arity ((G.face : G.Dart → G.Dart)^[i]
      (G.edge (zorg G x0 pl))) = n :=
  (Hypermap.arity_face_iter (G := G) i (G.edge (zorg G x0 pl))).trans
    (arity_edge_zorg_eq_of_hubr hCubic hroot)

theorem zpfit_mkZ_nil
    {G : Hypermap.{u}} {x0 x : G.Dart} {pl pr : Part} :
    zpfit G x0 x (mkZ Znil pl pr) :=
  zpfit_of_proper_false (by simp [mkZ, ZPart.proper])

theorem fitQa_getr_three_of_redQztLeaf
    {ctx : Context} {zp1 zp2 zp3 : ZPart}
    {r1 r2 r3 : PRange} {qt : QuizTree}
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (qztGetr r1 qt))) = true) :
    fitQa r1 (topQa r1) = true ∧
      fitQa r2 (topQa r2) = true ∧
      fitQa r3 (topQa r3) = true := by
  have h3 := qztGetr_fit_of_redQztLeaf hred
  have h2 := qztGetr_fit h3.2.2
  have h1 := qztGetr_fit h2.2.2
  exact ⟨h1.1, h2.1, h3.1⟩

theorem zippedLeftDoubleRootSound_of_components
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hroot : ZippedRootSound G ctx x0)
    (hvalidStep : ZippedStepValid ctx)
    (hstep : ZippedStepSound G ctx x0) :
    ZippedLeftDoubleRootSound G ctx x0 := by
  intro zp qa hvalid hfit hred
  let zpl := zstepL ctx zp
  have hvalidL : zpvalid ctx zpl := hvalidStep.stepL hvalid
  have hproperL : zpl.proper = true :=
    proper_of_fitQa_zrange (ctx := ctx) (zp := zpl) hfit
  have hrootL :
      G.arity (zdart G x0 zpl) = qa.toNat :=
    hroot hvalidL hfit hred
  have hstepEq :
      zdart G x0 zpl = qstepL G (zdart G x0 zp) :=
    hstep.stepL hvalid hproperL
  rw [arity_edge_node_eq (G := G) (qstepL G (zdart G x0 zp))]
  simpa [zpl, hstepEq] using hrootL

theorem zippedQuestionSound_of_noRedRec_and_steps
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hvalidStep : ZippedStepValid ctx)
    (hstep : ZippedStepSound G ctx x0) :
    ZippedQuestionSound G ctx x0 := by
  let hroot : ZippedRootSound G ctx x0 :=
    zippedRootSound_of_noRedRec
      (G := G) (ctx := ctx) (x0 := x0)
      hPlain hCubic hNoRedRec hx0 hfit0
  exact zippedQuestionSound_of_components
    (G := G) (ctx := ctx) (x0 := x0)
    hroot
    (zippedLeftDoubleRootSound_of_components
      (G := G) (ctx := ctx) (x0 := x0)
      hroot hvalidStep hstep)
    hvalidStep hstep

theorem zippedQuestionSound_of_noRedRec_and_reverse_steps
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hstep : ZippedStepSound G ctx x0) :
    ZippedQuestionSound G ctx x0 :=
  zippedQuestionSound_of_noRedRec_and_steps
    (G := G) (ctx := ctx) (x0 := x0)
    hPlain hCubic hNoRedRec hx0 hfit0
    (zippedStepValid_of_reverse (ctx := ctx) hleft)
    hstep

theorem zippedQuestionSound_of_noRedRec_and_reverse_exact
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hNoRedRec : NoRedRec G ctx)
    (hx0 : G.arity x0 = ctx.nhub)
    (hfit0 : Part.exactFitp G x0 ctx.p0r = true)
    (hleft : ctx.p0l = Part.reverse ctx.p0r) :
    ZippedQuestionSound G ctx x0 :=
  zippedQuestionSound_of_noRedRec_and_reverse_steps
    (G := G) (ctx := ctx) (x0 := x0)
    hPlain hCubic hNoRedRec hx0 hfit0 hleft
    (zippedStepSound_of_reverse_exact
      (G := G) (ctx := ctx) (x0 := x0) hPlain hCubic hleft hfit0)

/-- Semantic induction hypothesis for a bounded redpart loop: any successful
recursive redpart call excludes an exact fit at a dart with the hub arity. -/
def RedpartLoopSound
    (G : Hypermap.{u}) (qt : QuizTree) (ahub : QArity) (d : Nat) : Prop :=
  ∀ (x : G.Dart) (p : Part),
    G.arity x = ahub.toNat →
      redpartLoop qt ahub d p = true →
        Part.exactFitp G x p = false

theorem redpartLoopSound_zero
    (G : Hypermap.{u}) (qt : QuizTree) (ahub : QArity) :
    RedpartLoopSound G qt ahub 0 := by
  intro x p _ hred
  simp [redpartLoop] at hred

theorem noRedRec_of_redpartLoopSound
    {G : Hypermap.{u}} {qt : QuizTree} {ahub : QArity} {d : Nat}
    {p0l p0r : Part}
    (hsound : RedpartLoopSound G qt ahub d) :
    NoRedRec G
      { qt := qt
        ahub := ahub
        redRec := fun q => redpartLoop qt ahub d q
        p0l := p0l
        p0r := p0r } := by
  intro x p hx hfit
  by_cases hred : redpartLoop qt ahub d p = true
  · have hfalse := hsound x p hx hred
    rw [hfit] at hfalse
    contradiction
  · cases h : redpartLoop qt ahub d p
    · simp [h]
    · exact False.elim (hred h)

theorem zippedQuestionSound_of_redpartLoopSound
    {G : Hypermap.{u}} {qt : QuizTree} {ahub : QArity} {d : Nat}
    {p : Part} {x0 : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hloopSound : RedpartLoopSound G qt ahub d)
    (hx0 : G.arity x0 = ahub.toNat)
    (hfit0 : Part.exactFitp G x0 p = true) :
    ZippedQuestionSound G
      { qt := qt
        ahub := ahub
        redRec := fun q => redpartLoop qt ahub d q
        p0l := Part.reverse p
        p0r := p } x0 := by
  exact zippedQuestionSound_of_noRedRec_and_reverse_exact
    (G := G)
    (ctx :=
      { qt := qt
        ahub := ahub
        redRec := fun q => redpartLoop qt ahub d q
        p0l := Part.reverse p
        p0r := p })
    (x0 := x0) hPlain hCubic
    (noRedRec_of_redpartLoopSound
      (G := G) (qt := qt) (ahub := ahub) (d := d)
      (p0l := Part.reverse p) (p0r := p) hloopSound)
    hx0 hfit0 rfl

theorem get1_truncate_topQa_eq_of_fitQa
    {r : PRange} {qt : QuizTree}
    (hfit : fitQa r (topQa r) = true) :
    QuizTree.get1 (topQa r) (QuizTree.truncate qt) =
      QuizTree.get1 (topQa r) qt := by
  cases r <;> cases qt <;>
    simp [fitQa, topQa, QuizTree.truncate, QuizTree.get1] at hfit ⊢

theorem get3_eq_qztGetr_qztGetr_truncate_of_redQztLeaf
    {ctx : Context} {zp1 zp2 zp3 : ZPart}
    {r1 r2 r3 : PRange} {qt : QuizTree}
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt)))) =
        true) :
    QuizTree.get3 (topQa r1) (topQa r2) (topQa r3) qt =
      qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt))) := by
  have h3 := qztGetr_fit_of_redQztLeaf hred
  have h2 := qztGetr_fit h3.2.2
  have h1 := qztGetr_fit h2.2.2
  have htrunc :=
    get1_truncate_topQa_eq_of_fitQa
      (r := r1) (qt := qt) h1.1
  have h1qt :
      QuizTree.get1 (topQa r1) qt =
        qztGetr r1 (QuizTree.truncate qt) := by
    rw [← htrunc]
    exact h1.2.1
  exact QuizTree.get3_eq_of_get1_eq
    (qa1 := topQa r1) (qa2 := topQa r2) (qa3 := topQa r3)
    (t := qt) (t1 := qztGetr r1 (QuizTree.truncate qt))
    (t2 := qztGetr r2 (qztGetr r1 (QuizTree.truncate qt)))
    (t3 := qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt))))
    h1qt h2.2.1 h3.2.1

theorem false_of_redQztLeaf_get3_of_zippedQuestionSound_of_arity_eq
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {zp1 zp2 zp3 : ZPart} {qa1 : QArity} {r2 r3 : PRange}
    {qt : QuizTree} {x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid1 : zpvalid ctx zp1)
    (hvalid2 : zpvalid ctx zp2)
    (hvalid3 : zpvalid ctx zp3)
    (hzp1 : zpfit G x0 (qstepR G x) zp1)
    (hzp2 : zpfit G x0 (qstepR G (G.node x)) zp2)
    (hzp3 : zpfit G x0 (qstepR G (G.node (G.node x))) zp3)
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (QuizTree.get1 qa1 qt))) = true)
    (hnofit : QuizTree.Hypermap.quizTreeFit G x qt = false)
    (harity1 : G.arity x = qa1.toNat)
    (harity2 : G.arity (G.node x) = (topQa r2).toNat)
    (harity3 : G.arity (G.node (G.node x)) = (topQa r3).toNat) :
    False := by
  have hbounds1 := QArity.toNat_bounds qa1
  have hbounds2 := QArity.toNat_bounds (topQa r2)
  have hbounds3 := QArity.toNat_bounds (topQa r3)
  have harities :
      QuizTree.Hypermap.quizTreeFitsArities G x = true :=
    QuizTree.Hypermap.quizTreeFitsArities_eq_true_of_bounds
      (G := G) (x1 := x)
      (by simpa [harity1] using hbounds1.1)
      (by simpa [harity1] using hbounds1.2)
      (by simpa [harity2] using hbounds2.1)
      (by simpa [harity2] using hbounds2.2)
      (by simpa [harity3] using hbounds3.1)
      (by simpa [harity3] using hbounds3.2)
  have hqa1 : QArity.ofNatCode (G.arity x) = qa1 := by
    rw [harity1]
    exact QArity.ofNat_toNat qa1
  have hqa2 :
      QArity.ofNatCode (G.arity (G.node x)) = topQa r2 := by
    rw [harity2]
    exact QArity.ofNat_toNat (topQa r2)
  have hqa3 :
      QArity.ofNatCode (G.arity (G.node (G.node x))) = topQa r3 := by
    rw [harity3]
    exact QArity.ofNat_toNat (topQa r3)
  exact false_of_redQztLeaf_get3_of_quizTreeFit_eq_false_of_zippedQuestionSound
    (G := G) (ctx := ctx) (x0 := x0)
    (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
    (qa1 := qa1) (r2 := r2) (r3 := r3) (qt := qt) (x := x)
    hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3 hred
    hnofit harities hqa1 hqa2 hqa3

theorem false_of_redQztLeaf_get3_truncate_of_zippedQuestionSound_of_arity_eq
    {G : Hypermap.{u}} {ctx : Context} {x0 : G.Dart}
    {zp1 zp2 zp3 : ZPart} {r1 r2 r3 : PRange}
    {qt : QuizTree} {x : G.Dart}
    (hsound : ZippedQuestionSound G ctx x0)
    (hvalid1 : zpvalid ctx zp1)
    (hvalid2 : zpvalid ctx zp2)
    (hvalid3 : zpvalid ctx zp3)
    (hzp1 : zpfit G x0 (qstepR G x) zp1)
    (hzp2 : zpfit G x0 (qstepR G (G.node x)) zp2)
    (hzp3 : zpfit G x0 (qstepR G (G.node (G.node x))) zp3)
    (hred : redQztLeaf ctx zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt)))) =
        true)
    (hnofit : QuizTree.Hypermap.quizTreeFit G x qt = false)
    (harity1 : G.arity x = (topQa r1).toNat)
    (harity2 : G.arity (G.node x) = (topQa r2).toNat)
    (harity3 : G.arity (G.node (G.node x)) = (topQa r3).toNat) :
    False := by
  have hbounds1 := QArity.toNat_bounds (topQa r1)
  have hbounds2 := QArity.toNat_bounds (topQa r2)
  have hbounds3 := QArity.toNat_bounds (topQa r3)
  have harities :
      QuizTree.Hypermap.quizTreeFitsArities G x = true :=
    QuizTree.Hypermap.quizTreeFitsArities_eq_true_of_bounds
      (G := G) (x1 := x)
      (by simpa [harity1] using hbounds1.1)
      (by simpa [harity1] using hbounds1.2)
      (by simpa [harity2] using hbounds2.1)
      (by simpa [harity2] using hbounds2.2)
      (by simpa [harity3] using hbounds3.1)
      (by simpa [harity3] using hbounds3.2)
  have hqa1 : QArity.ofNatCode (G.arity x) = topQa r1 := by
    rw [harity1]
    exact QArity.ofNat_toNat (topQa r1)
  have hqa2 :
      QArity.ofNatCode (G.arity (G.node x)) = topQa r2 := by
    rw [harity2]
    exact QArity.ofNat_toNat (topQa r2)
  have hqa3 :
      QArity.ofNatCode (G.arity (G.node (G.node x))) = topQa r3 := by
    rw [harity3]
    exact QArity.ofNat_toNat (topQa r3)
  have hbranch :=
    get3_eq_qztGetr_qztGetr_truncate_of_redQztLeaf
      (ctx := ctx) (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
      (r1 := r1) (r2 := r2) (r3 := r3) (qt := qt) hred
  have hlist :=
    QuizTree.Hypermap.quizTreeFitList_get3_eq_false_of_quizTreeFit_eq_false
      (G := G) (x1 := x) (t := qt) hnofit harities
  have hlist' :
      QuizTree.Hypermap.quizTreeFitList G x
        (qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt)))) =
          false := by
    simpa [hqa1, hqa2, hqa3, hbranch] using hlist
  exact
    false_of_redQztLeaf_of_quizTreeFitList_eq_false_of_zippedQuestionSound
      (G := G) (ctx := ctx) (x0 := x0)
      (zp1 := zp1) (zp2 := zp2) (zp3 := zp3)
      (qt := qztGetr r3 (qztGetr r2 (qztGetr r1 (QuizTree.truncate qt))))
      (x := x)
      hsound hvalid1 hvalid2 hvalid3 hzp1 hzp2 hzp3 hred hlist'

def NoQuizTreeFit (G : Hypermap.{u}) (qt : QuizTree) : Prop :=
  ∀ y : G.Dart, QuizTree.Hypermap.quizTreeFit G y qt = false


end Schematic.Math.GraphTheory.FourColor.RedPart
