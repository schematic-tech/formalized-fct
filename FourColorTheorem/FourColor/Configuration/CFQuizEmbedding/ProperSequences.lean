import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.Sequences

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

/-- Lean form of Coq `rqs_proper`.

The source ring `r` is mapped into the target ring map through `h`; `r0` is
the target ring list.  The invariant records the executable fit check, the
good-arity condition on target ring darts outside the injected source band,
face-simplicity of the accumulated quiz walk plus target ring, and the exact
face-band coverage equation. -/
structure RqSeqProper {G0 G : Hypermap} (h : G.Dart → G0.Dart)
    (qs : RqSeq) (r0 : List G0.Dart) (r : List G.Dart) : Prop where
  fits : rqSeqFits G0 G h qs r = true
  goodRingArity :
    ∀ ⦃x : G0.Dart⦄,
      x ∈ r0 →
        ¬ RqSeqCodom h x →
          ¬ G0.FaceBand (r.map h) x →
            G0.GoodRingArity x
  simple :
    G0.FaceSimple (rqSeqWalk G0 qs (r.map h) ++ r0)
  covers :
    ∀ x : G0.Dart,
      G0.FaceBand (rqSeqWalk G0 qs (r.map h) ++ r0) x ↔
        RqSeqTarget h r x

namespace RqSeqProper

theorem length_eq
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {qs : RqSeq} {r0 : List G0.Dart} {r : List G.Dart}
    (hproper : RqSeqProper h qs r0 r) :
    qs.length = r.length :=
  rqSeqFits_length_eq hproper.fits

theorem faceBand_iff_target
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {qs : RqSeq} {r0 : List G0.Dart} {r : List G.Dart}
    (hproper : RqSeqProper h qs r0 r) (x : G0.Dart) :
    G0.FaceBand (rqSeqWalk G0 qs (r.map h) ++ r0) x ↔
      RqSeqTarget h r x :=
  hproper.covers x

theorem target_closed
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {qs : RqSeq} {r0 : List G0.Dart} {r : List G.Dart}
    (hproper : RqSeqProper h qs r0 r)
    {x y : G0.Dart}
    (hx : RqSeqTarget h r x)
    (hxy : PermReachable G0.face x y) :
    RqSeqTarget h r y :=
  (hproper.covers y).1
  (Hypermap.FaceBand.of_faceReachable (G := G0)
      ((hproper.covers x).2 hx) hxy)

/-- Coq's cardinal-image argument used for `nFv2`: an injective embedding
that reflects face reachability preserves the arity of every source face
whose image is outside the `rqs_proper` target. -/
theorem arity_image_eq_of_not_target
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {qs : RqSeq} {r0 : List G0.Dart} {r : List G.Dart}
    (hinj : Function.Injective h)
    (hface : ∀ x y : G.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable G.face x y)
    (hproper : RqSeqProper h qs r0 r)
    {x : G.Dart}
    (hnot : ¬ RqSeqTarget h r (h x)) :
    G0.arity (h x) = G.arity x := by
  let lift : G.FaceClass x → G0.FaceClass (h x) := fun z ↦
    ⟨h z.1, (hface x z.1).2 z.2⟩
  have hliftInj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hab
  have hliftSurj : Function.Surjective lift := by
    intro z
    have hcodom : RqSeqCodom h z.1 := by
      by_contra houtside
      have htargetZ : RqSeqTarget h r z.1 := Or.inl houtside
      have htargetX := hproper.target_closed htargetZ
        (PermReachable.symm G0.face z.2)
      exact hnot htargetX
    rcases hcodom with ⟨y, hy⟩
    have hyReach : PermReachable G.face x y :=
      (hface x y).1 (by simpa [hy] using z.2)
    refine ⟨⟨y, hyReach⟩, ?_⟩
    exact Subtype.ext hy
  exact (Nat.card_congr
    (Equiv.ofBijective lift ⟨hliftInj, hliftSurj⟩)).symm

/-- Package a local `cfquizP` step once fit and the two extensional
face-band comparisons have been established.  This is the common final
argument in Coq's `CpY` and `CpH` branches. -/
theorem transport
    {G0 G G' : Hypermap}
    {h : G.Dart → G0.Dart} {h' : G'.Dart → G0.Dart}
    {qs qs' : RqSeq} {r0 : List G0.Dart}
    {r : List G.Dart} {r' : List G'.Dart}
    (hproper : RqSeqProper h qs r0 r)
    (hfits : rqSeqFits G0 G' h' qs' r' = true)
    (hgood :
      ∀ ⦃x : G0.Dart⦄,
        x ∈ r0 →
          ¬ RqSeqCodom h' x →
            ¬ G0.FaceBand (r'.map h') x →
              G0.GoodRingArity x)
    (hband : ∀ x : G0.Dart,
      G0.FaceBand (rqSeqWalk G0 qs' (r'.map h') ++ r0) x ↔
        G0.FaceBand (rqSeqWalk G0 qs (r.map h) ++ r0) x)
    (hlen :
      (rqSeqWalk G0 qs' (r'.map h') ++ r0).length =
        (rqSeqWalk G0 qs (r.map h) ++ r0).length)
    (htarget : ∀ x : G0.Dart,
      RqSeqTarget h' r' x ↔ RqSeqTarget h r x) :
    RqSeqProper h' qs' r0 r' where
  fits := hfits
  goodRingArity := hgood
  simple :=
    (Hypermap.FaceSimple.congr_of_faceBand_iff_of_length_eq
      (G := G0) hband hlen).2 hproper.simple
  covers := by
    intro x
    rw [hband x, hproper.covers x, htarget x]

/-- Common invariant packaging for Coq `cfquizP`'s `CpY` branch.  The
compiler-specific case split only has to provide fit, good arity, and the
walk comparison. -/
theorem yOld
    (P : PointedHypermap) {G0 : Hypermap}
    {h : P.y.map.Dart → G0.Dart}
    (hface : ∀ x y : P.y.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y)
    {qs qs' : RqSeq} {r0 : List G0.Dart} {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    (hproper :
      RqSeqProper h qs r0
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld))
    (hfits : rqSeqFits G0 P.map (fun x => h (P.yOld x)) qs' r = true)
    (hgood :
      ∀ ⦃x : G0.Dart⦄,
        x ∈ r0 →
          ¬ RqSeqCodom (fun y => h (P.yOld y)) x →
            ¬ G0.FaceBand (r.map (fun y => h (P.yOld y))) x →
              G0.GoodRingArity x)
    (hband : ∀ x : G0.Dart,
      G0.FaceBand
          (rqSeqWalk G0 qs' (r.map (fun y => h (P.yOld y))) ++ r0) x ↔
        G0.FaceBand
          (rqSeqWalk G0 qs
            ((P.y.map.node P.y.point :: P.y.point ::
              (r.drop 1).map P.yOld).map h) ++ r0) x)
    (hlen :
      (rqSeqWalk G0 qs' (r.map (fun y => h (P.yOld y))) ++ r0).length =
        (rqSeqWalk G0 qs
          ((P.y.map.node P.y.point :: P.y.point ::
            (r.drop 1).map P.yOld).map h) ++ r0).length) :
    RqSeqProper (fun x => h (P.yOld x)) qs' r0 r :=
  transport hproper hfits hgood hband hlen
    (rqSeqTarget_comp_yOld_iff P h hface r hr)

/-- Common invariant packaging for Coq `cfquizP`'s `CpH` branch.  Unlike
`CpY`, the compiled H walk always contributes the removed middle ring dart;
`rqSeqTarget_comp_hOld_iff` proves that this is exactly the missing target
face. -/
theorem hOld
    (P : PointedHypermap) {G0 : Hypermap}
    {h : P.h.map.Dart → G0.Dart}
    (hface : ∀ x y : P.h.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y)
    (hproperP : P.map.ProperRingHead P.point)
    (hlongP : P.map.LongRingHead P.point)
    {qs qs' : RqSeq} {r0 : List G0.Dart} {r : List P.map.Dart}
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    (hproper :
      RqSeqProper h qs r0
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld))
    (hfits : rqSeqFits G0 P.map (fun x => h (P.hOld x)) qs' r = true)
    (hgood :
      ∀ ⦃x : G0.Dart⦄,
        x ∈ r0 →
          ¬ RqSeqCodom (fun y => h (P.hOld y)) x →
            ¬ G0.FaceBand (r.map (fun y => h (P.hOld y))) x →
              G0.GoodRingArity x)
    (hmiddleNot :
      ¬ G0.FaceBand
        (rqSeqWalk G0 qs
          ((P.h.map.node P.h.point :: P.h.point ::
            (r.drop 2).map P.hOld).map h) ++ r0)
        (h (P.hOld P.point)))
    (hband : ∀ x : G0.Dart,
      G0.FaceBand
          (rqSeqWalk G0 qs' (r.map (fun y => h (P.hOld y))) ++ r0) x ↔
        G0.FaceBand
          (h (P.hOld P.point) ::
            (rqSeqWalk G0 qs
              ((P.h.map.node P.h.point :: P.h.point ::
                (r.drop 2).map P.hOld).map h) ++ r0)) x)
    (hlen :
      (rqSeqWalk G0 qs' (r.map (fun y => h (P.hOld y))) ++ r0).length =
        (h (P.hOld P.point) ::
          (rqSeqWalk G0 qs
            ((P.h.map.node P.h.point :: P.h.point ::
              (r.drop 2).map P.hOld).map h) ++ r0)).length) :
    RqSeqProper (fun x => h (P.hOld x)) qs' r0 r := by
  let oldFull :=
    rqSeqWalk G0 qs
      ((P.h.map.node P.h.point :: P.h.point ::
        (r.drop 2).map P.hOld).map h) ++ r0
  have hsimpleCons :
      G0.FaceSimple (h (P.hOld P.point) :: oldFull) := by
    rw [Hypermap.FaceSimple, List.pairwise_cons]
    constructor
    · intro y hy hreach
      exact hmiddleNot
        (Hypermap.FaceBand.of_mem (G := G0) hy
          (PermReachable.symm G0.face hreach))
    · exact hproper.simple
  refine
    { fits := hfits
      goodRingArity := hgood
      simple :=
        (Hypermap.FaceSimple.congr_of_faceBand_iff_of_length_eq
          (G := G0) hband hlen).2 hsimpleCons
      covers := ?_ }
  intro x
  rw [hband x]
  have hcons :
      G0.FaceBand (h (P.hOld P.point) :: oldFull) x ↔
        G0.FaceBand [h (P.hOld P.point)] x ∨
          G0.FaceBand oldFull x := by
    rw [Hypermap.FaceBand.cons, Hypermap.FaceBand.singleton]
  rw [hcons, hproper.covers x]
  exact (rqSeqTarget_comp_hOld_iff P h hface hproperP hlongP r hr x).symm

/-- Coq `cfquizP`, `CpR` branch.  Rotating the source ring left and then
rotating its aligned question sequence right preserves the complete
`rqs_proper` invariant. -/
theorem rotateRight_of_rotateLeft
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {qs : RqSeq} {r0 : List G0.Dart} {r : List G.Dart}
    (n : Nat)
    (hproper : RqSeqProper h qs r0 (CProg.rotateLeft n r)) :
    RqSeqProper h (CProg.rotateRight n qs) r0 r := by
  have hlenMap :
      qs.length = ((CProg.rotateLeft n r).map h).length := by
    simpa using hproper.length_eq
  have hmapInv :
      CProg.rotateRight n ((CProg.rotateLeft n r).map h) = r.map h := by
    rw [CProg.map_rotateLeft, CProg.rotateRight_rotateLeft]
  have hringPerm :
      ((CProg.rotateLeft n r).map h).Perm (r.map h) := by
    rw [CProg.map_rotateLeft]
    exact CProg.perm_rotateLeft n (r.map h)
  have hwalkPerm0 :=
    rqSeqWalk_rotateRight_perm G0 n qs
      ((CProg.rotateLeft n r).map h) hlenMap
  rw [hmapInv] at hwalkPerm0
  have hcombinedPerm :
      (rqSeqWalk G0 (CProg.rotateRight n qs) (r.map h) ++ r0).Perm
        (rqSeqWalk G0 qs ((CProg.rotateLeft n r).map h) ++ r0) :=
    hwalkPerm0.append_right r0
  constructor
  · have hfitRot :=
      rqSeqFits_rotateRight G0 G h n qs (CProg.rotateLeft n r)
        hproper.length_eq
    rw [CProg.rotateRight_rotateLeft] at hfitRot
    exact hfitRot.trans hproper.fits
  · intro x hx hcodom hband
    apply hproper.goodRingArity hx hcodom
    intro hold
    exact hband ((Hypermap.FaceBand.perm (G := G0) hringPerm).1 hold)
  · exact Hypermap.FaceSimple.perm (G := G0) hcombinedPerm.symm
      hproper.simple
  · intro x
    constructor
    · intro hnew
      have hold :=
        (Hypermap.FaceBand.perm (G := G0) hcombinedPerm).1 hnew
      rcases (hproper.covers x).1 hold with hcodom | hband
      · exact Or.inl hcodom
      · exact Or.inr
          ((Hypermap.FaceBand.perm (G := G0) hringPerm).1 hband)
    · intro htarget
      have holdTarget :
          RqSeqTarget h (CProg.rotateLeft n r) x := by
        rcases htarget with hcodom | hband
        · exact Or.inl hcodom
        · exact Or.inr
            ((Hypermap.FaceBand.perm (G := G0) hringPerm).2 hband)
      have hold := (hproper.covers x).2 holdTarget
      exact (Hypermap.FaceBand.perm (G := G0) hcombinedPerm).2 hold

end RqSeqProper

theorem rqSeqProper_rotateStep
    {cp1 cp2 : CProg} {qs : RqSeq} {n : Nat}
    (hring :
      PointedHypermap.cpRing (CpStep.rotate n :: cp2) =
        CProg.rotateLeft n (PointedHypermap.cpRing cp2))
    (hproper :
      RqSeqProper (PointedHypermap.injcp cp1 (CpStep.rotate n :: cp2)) qs
        (PointedHypermap.cpRing
          (CProg.appendRev cp1 (CpStep.rotate n :: cp2)))
        (PointedHypermap.cpRing (CpStep.rotate n :: cp2))) :
    RqSeqProper
      (PointedHypermap.injcp (CpStep.rotate n :: cp1) cp2)
      (CProg.rotateRight n qs)
      (PointedHypermap.cpRing
        (CProg.appendRev (CpStep.rotate n :: cp1) cp2))
      (PointedHypermap.cpRing cp2) := by
  have hproper' :
      RqSeqProper (PointedHypermap.injcp cp1 (CpStep.rotate n :: cp2)) qs
        (PointedHypermap.cpRing
          (CProg.appendRev cp1 (CpStep.rotate n :: cp2)))
        (CProg.rotateLeft n (PointedHypermap.cpRing cp2)) := by
    simpa [hring] using hproper
  simpa [PointedHypermap.injcp, PointedHypermap.oldStep,
    PointedHypermap.cpmap, PointedHypermap.step] using
    (RqSeqProper.rotateRight_of_rotateLeft n hproper')

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
