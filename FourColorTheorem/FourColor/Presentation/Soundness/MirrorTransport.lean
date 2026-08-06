import FourColorTheorem.FourColor.Presentation.Soundness.HubBounds

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

/-- Valid hubs transport to mirror hypermaps.  Coq proves this from
`minimal_counter_example_mirror` and `dscore_mirror`; it is kept as a precise
dependency until the mirror discharge facts are ported. -/
def MirrorValidHubTransport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    ValidHub G x → ValidHub G.mirror x

/-- The score-invariance theorem needed to prove `MirrorValidHubTransport`.
Coq proves this as `dscore_mirror`. -/
def MirrorDscoreTransport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    G.MinimalCounterexample →
      G.mirror.dscore x = G.dscore x

/-- Plain/cubic form of Coq `dscore_mirror`, now proved in `Discharge.lean`.
The minimal-counterexample-facing transport additionally needs the separate
cubicity theorem for minimal counterexamples. -/
def PlainCubicDscoreMirror : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    G.Plain → G.Cubic →
      G.mirror.dscore x = G.dscore x

theorem plainCubicDscoreMirror :
    PlainCubicDscoreMirror.{u} := by
  intro G x hPlain hCubic
  exact G.dscore_mirror_of_plain_cubic hPlain hCubic x

/-- Once minimal counterexamples are known to be cubic, the proved
plain/cubic `dscore_mirror` theorem supplies the presentation-facing score
transport. -/
theorem mirrorDscoreTransport_of_minimalCounterexample_cubic
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic) :
    MirrorDscoreTransport.{u} := by
  intro G x hG
  exact G.dscore_mirror_of_plain_cubic
    (Hypermap.MinimalCounterexample.plain hG) (hcubic G hG) x

/-- Pointwise invariance of edge-transfer scores under mirror.  This is the
local discharge target below `MirrorDscoreTransport`. -/
def MirrorDscore2Transport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    G.MinimalCounterexample →
      G.mirror.dscore2 x = G.dscore2 x

/-- Invariance of the discharged face-score sum under mirror. -/
def MirrorFaceScoreTransport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart),
    G.MinimalCounterexample →
      G.mirror.faceScoreSum x = G.faceScoreSum x

theorem mirrorFaceScoreTransport_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u}) :
    MirrorFaceScoreTransport.{u} := by
  intro G x hG
  unfold Hypermap.faceScoreSum
  exact Fintype.sum_equiv (G.mirrorFaceClassEquiv x)
    (fun z : G.mirror.FaceClass x => G.mirror.dscore2 z.1)
    (fun z : G.FaceClass x => G.dscore2 z.1)
    (fun z => h2 G z.1 hG)

theorem mirrorDscoreTransport_of_faceScore_mirror
    (hface : MirrorFaceScoreTransport.{u}) :
    MirrorDscoreTransport.{u} := by
  intro G x hG
  have harity := G.arity_mirror x
  have hsum := hface G x hG
  simp [Hypermap.dscore, harity, hsum]

theorem mirrorDscoreTransport_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u}) :
    MirrorDscoreTransport.{u} :=
  mirrorDscoreTransport_of_faceScore_mirror
    (mirrorFaceScoreTransport_of_dscore2_mirror h2)

/-- Exact fitting transports across mirror hypermaps.  This is the
presentation-facing form of Coq `fitp_mirror` plus `mirror_mirror_part`. -/
def MirrorExactFitTransport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart) (p : Part),
    G.MinimalCounterexample →
      Part.exactFitp G x p =
        Part.exactFitp G.mirror x (Part.mirror p)

/-- Bounded exact-fit mirror transport for partial `fitp_mirror` ports. -/
def MirrorExactFitTransportUpTo (n : Nat) : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart) (p : Part),
    p.size ≤ n →
      G.MinimalCounterexample →
        Part.exactFitp G x p =
          Part.exactFitp G.mirror x (Part.mirror p)

/-- Fit transports across mirror hypermaps.  This is the lower-level geometric
target below exact-fit transport; exact fitting then follows from arity and
part-size invariance. -/
def MirrorFitTransport : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart) (p : Part),
    G.MinimalCounterexample →
      Part.fitp G x p = Part.fitp G.mirror x (Part.mirror p)

/-- The Coq `fitp_mirror` target, isolated at its real geometric strength:
plain cubic hypermaps.  In Coq this lemma is named `fitp_mirror`, but its
statement is for `exact_fitp`. -/
def PlainCubicFitpMirror : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart) (p : Part),
    G.Plain → G.Cubic →
      Part.exactFitp G x (Part.mirror p) =
        Part.exactFitp G.mirror x p

/-- Bounded version of `PlainCubicFitpMirror`, useful while porting the
accumulator induction in Coq's `fitp_mirror`. -/
def PlainCubicFitpMirrorUpTo (n : Nat) : Prop :=
  ∀ (G : Hypermap.{u}) (x : G.Dart) (p : Part),
    p.size ≤ n →
      G.Plain → G.Cubic →
        Part.exactFitp G x (Part.mirror p) =
          Part.exactFitp G.mirror x p

theorem plainCubicFitpMirrorUpTo_mono
    {m n : Nat} (hmn : m ≤ n)
    (hfit : PlainCubicFitpMirrorUpTo.{u} n) :
    PlainCubicFitpMirrorUpTo.{u} m := by
  intro G x p hsize hPlain hCubic
  exact hfit G x p (le_trans hsize hmn) hPlain hCubic

theorem plainCubicFitpMirrorUpTo_of_plainCubicFitpMirror
    {n : Nat}
    (hfit : PlainCubicFitpMirror.{u}) :
    PlainCubicFitpMirrorUpTo.{u} n := by
  intro G x p _ hPlain hCubic
  exact hfit G x p hPlain hCubic

theorem plainCubicFitpMirror :
    PlainCubicFitpMirror.{u} := by
  intro G x p hPlain hCubic
  exact Part.exactFitp_mirror (G := G) hPlain hCubic p x

theorem plainCubicFitpMirrorUpTo_two :
    PlainCubicFitpMirrorUpTo.{u} 2 := by
  intro G x p _ hPlain hCubic
  exact Part.exactFitp_mirror (G := G) hPlain hCubic p x

theorem plainCubicFitpMirrorUpTo_three :
    PlainCubicFitpMirrorUpTo.{u} 3 := by
  intro G x p _ hPlain hCubic
  exact Part.exactFitp_mirror (G := G) hPlain hCubic p x

theorem mirrorExactFitTransportUpTo_mono
    {m n : Nat} (hmn : m ≤ n)
    (hfit : MirrorExactFitTransportUpTo.{u} n) :
    MirrorExactFitTransportUpTo.{u} m := by
  intro G x p hsize hG
  exact hfit G x p (le_trans hsize hmn) hG

theorem mirrorExactFitTransportUpTo_of_mirrorExactFitTransport
    {n : Nat}
    (hfit : MirrorExactFitTransport.{u}) :
    MirrorExactFitTransportUpTo.{u} n := by
  intro G x p _ hG
  exact hfit G x p hG

theorem mirrorExactFitTransportUpTo_of_plainCubic_fitp_mirror_upTo
    {n : Nat}
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hfit : PlainCubicFitpMirrorUpTo.{u} n) :
    MirrorExactFitTransportUpTo.{u} n := by
  intro G x p hsize hG
  have hplain : G.Plain := Hypermap.MinimalCounterexample.plain hG
  have hcubicG : G.Cubic := hcubic G hG
  have hmirrorSize : (Part.mirror p).size ≤ n := by
    simpa [Part.size_mirror] using hsize
  have h := hfit G x (Part.mirror p) hmirrorSize hplain hcubicG
  simpa [Part.mirror_mirror] using h

theorem mirrorExactFitTransportUpTo_two
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic) :
    MirrorExactFitTransportUpTo.{u} 2 :=
  mirrorExactFitTransportUpTo_of_plainCubic_fitp_mirror_upTo
    hcubic plainCubicFitpMirrorUpTo_two

theorem mirrorExactFitTransportUpTo_three
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic) :
    MirrorExactFitTransportUpTo.{u} 3 :=
  mirrorExactFitTransportUpTo_of_plainCubic_fitp_mirror_upTo
    hcubic plainCubicFitpMirrorUpTo_three

theorem mirrorExactFitTransport_of_fit_mirror
    (hfit : MirrorFitTransport.{u}) :
    MirrorExactFitTransport.{u} := by
  intro G x p hG
  have harity := G.arity_mirror x
  have hsize := Part.size_mirror p
  have hfitp := hfit G x p hG
  simp [Part.exactFitp, harity, hsize, hfitp]

theorem mirrorExactFitTransport_of_plainCubic_fitp_mirror
    (hcubic : ∀ G : Hypermap.{u}, G.MinimalCounterexample → G.Cubic)
    (hfit : PlainCubicFitpMirror.{u}) :
    MirrorExactFitTransport.{u} := by
  intro G x p hG
  have hplain : G.Plain := Hypermap.MinimalCounterexample.plain hG
  have hcubicG : G.Cubic := hcubic G hG
  have h := hfit G x (Part.mirror p) hplain hcubicG
  simpa [Part.mirror_mirror] using h

theorem mirrorValidHubTransport_symm
    (hvalid : MirrorValidHubTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) :
    ValidHub G.mirror x → ValidHub G x := by
  intro hx
  have h := hvalid G.mirror x hx
  convert h using 1
  exact (Hypermap.mirror_mirror G).symm

theorem mirrorValidHubTransport_iff
    (hvalid : MirrorValidHubTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) :
    ValidHub G.mirror x ↔ ValidHub G x := by
  constructor
  · exact mirrorValidHubTransport_symm hvalid G x
  · exact hvalid G x

theorem mirrorExactFitTransport_symm
    (hfitMirror : MirrorExactFitTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x p =
      Part.exactFitp G x (Part.mirror p) := by
  have heq := hfitMirror G x (Part.mirror p) hG
  simpa [Part.mirror_mirror] using heq.symm

theorem mirrorExactFitTransport_true_iff
    (hfitMirror : MirrorExactFitTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x (Part.mirror p) = true ↔
      Part.exactFitp G x p = true := by
  have heq := hfitMirror G x p hG
  constructor
  · intro h
    rw [heq]
    exact h
  · intro h
    rw [← heq]
    exact h

theorem mirrorExactFitTransport_symm_true_iff
    (hfitMirror : MirrorExactFitTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x p = true ↔
      Part.exactFitp G x (Part.mirror p) = true := by
  have heq := mirrorExactFitTransport_symm hfitMirror G x p hG
  constructor
  · intro h
    rw [← heq]
    exact h
  · intro h
    rw [heq]
    exact h

theorem mirrorExactFitTransportUpTo_symm
    {n : Nat}
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hsize : p.size ≤ n)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x p =
      Part.exactFitp G x (Part.mirror p) := by
  have hmirrorSize : (Part.mirror p).size ≤ n := by
    simpa [Part.size_mirror] using hsize
  have heq := hfitMirror G x (Part.mirror p) hmirrorSize hG
  simpa [Part.mirror_mirror] using heq.symm

theorem mirrorExactFitTransportUpTo_true_iff
    {n : Nat}
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hsize : p.size ≤ n)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x (Part.mirror p) = true ↔
      Part.exactFitp G x p = true := by
  have heq := hfitMirror G x p hsize hG
  constructor
  · intro h
    rw [heq]
    exact h
  · intro h
    rw [← heq]
    exact h

theorem mirrorExactFitTransportUpTo_symm_true_iff
    {n : Nat}
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hsize : p.size ≤ n)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G.mirror x p = true ↔
      Part.exactFitp G x (Part.mirror p) = true := by
  have heq := mirrorExactFitTransportUpTo_symm
    hfitMirror G x p hsize hG
  constructor
  · intro h
    rw [← heq]
    exact h
  · intro h
    rw [heq]
    exact h

theorem mirrorExactFit_pconsN_of_minimalCounterexample_pentagonal
    (hpentagonal : ∀ G : Hypermap.{u},
      G.MinimalCounterexample → G.Pentagonal)
    (G : Hypermap.{u}) (x : G.Dart) (n : Nat)
    (hG : G.MinimalCounterexample) :
    Part.exactFitp G x (Part.pconsN n) =
      Part.exactFitp G.mirror x (Part.mirror (Part.pconsN n)) :=
  (Part.exactFitp_mirror_pconsN_of_pentagonal
    (G := G) (hpentagonal G hG) x n).symm

theorem mirrorExactFit_of_minimalCounterexample_pentagonal_size_lt_five
    (hpentagonal : ∀ G : Hypermap.{u},
      G.MinimalCounterexample → G.Pentagonal)
    (G : Hypermap.{u}) (x : G.Dart) (p : Part)
    (hG : G.MinimalCounterexample)
    (hsize : p.size < 5) :
    Part.exactFitp G x p =
      Part.exactFitp G.mirror x (Part.mirror p) :=
  Part.exactFitp_mirror_of_pentagonal_size_lt_five
    (G := G) (hpentagonal G hG) p x hsize

theorem mirrorExactFitTransportUpTo_of_minimalCounterexample_pentagonal_lt_five
    {n : Nat}
    (hpentagonal : ∀ G : Hypermap.{u},
      G.MinimalCounterexample → G.Pentagonal)
    (hn : n < 5) :
    MirrorExactFitTransportUpTo.{u} n := by
  intro G x p hsize hG
  exact mirrorExactFit_of_minimalCounterexample_pentagonal_size_lt_five
    hpentagonal G x p hG (by omega)

theorem mirrorExactFitTransportUpTo_four_of_minimalCounterexample_pentagonal
    (hpentagonal : ∀ G : Hypermap.{u},
      G.MinimalCounterexample → G.Pentagonal) :
    MirrorExactFitTransportUpTo.{u} 4 :=
  mirrorExactFitTransportUpTo_of_minimalCounterexample_pentagonal_lt_five
    hpentagonal (by omega)

theorem mirrorValidHubTransport_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u}) :
    MirrorValidHubTransport.{u} := by
  intro G x hx
  exact ⟨hx.1.mirror, by
    have h := hscore G x hx.1
    simpa [h] using hx.2⟩

theorem mirrorValidHubTransport_iff_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u})
    (G : Hypermap.{u}) (x : G.Dart) :
    ValidHub G.mirror x ↔ ValidHub G x :=
  mirrorValidHubTransport_iff
    (mirrorValidHubTransport_of_dscore_mirror hscore) G x

theorem mirrorValidHubTransport_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u}) :
    MirrorValidHubTransport.{u} :=
  mirrorValidHubTransport_of_dscore_mirror
    (mirrorDscoreTransport_of_dscore2_mirror h2)

theorem mirrorValidHubTransport_iff_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u})
    (G : Hypermap.{u}) (x : G.Dart) :
    ValidHub G.mirror x ↔ ValidHub G x :=
  mirrorValidHubTransport_iff
    (mirrorValidHubTransport_of_dscore2_mirror h2) G x


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
