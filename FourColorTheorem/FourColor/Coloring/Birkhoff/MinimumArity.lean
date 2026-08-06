import FourColorTheorem.FourColor.Coloring.Birkhoff.RingAdjacency
import FourColorTheorem.FourColor.Configuration.QuizEmbedding.Base

/-! The short-ring coloring and minimum face-arity theorem. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- Coq's explicit coloring of a cycle of length at most four: alternating
colors one and two, with color three at the final vertex of a triangle. -/
private def shortRingColor (n i : Nat) : Color :=
  if n = 3 ∧ i = 2 then Color.three
  else if i = 0 ∨ i = 2 then Color.one else Color.two

private theorem shortRingColor_ne_zero (n i : Nat) :
    shortRingColor n i ≠ Color.zero := by
  unfold shortRingColor
  split
  · intro h
    cases h
  · split <;> intro h <;> cases h

private theorem shortRingColor_ne_of_cyclic
    {n i j : Nat}
    (hn : 0 < n) (hn4 : n ≤ 4)
    (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hcyclic :
      j = (i + (n - 1)) % n ∨ j = (i + 1) % n) :
    shortRingColor n j ≠ shortRingColor n i := by
  have hnCases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hnCases with rfl | rfl | rfl | rfl
  · omega
  · have hiCases : i = 0 ∨ i = 1 := by omega
    have hjCases : j = 0 ∨ j = 1 := by omega
    rcases hiCases with rfl | rfl <;>
      rcases hjCases with rfl | rfl <;> simp_all [shortRingColor]
  · have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hiCases with rfl | rfl | rfl <;>
      rcases hjCases with rfl | rfl | rfl <;> simp_all [shortRingColor]
  · have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hiCases with rfl | rfl | rfl | rfl <;>
      rcases hjCases with rfl | rfl | rfl | rfl <;>
        simp_all [shortRingColor]

/-- The explicit face color used in Coq `min_arity`. -/
private noncomputable def spokeRingShortColor
    (G : Hypermap.{u}) (x y : G.Dart) : Color := by
  classical
  exact if PermReachable G.face x y then Color.zero
    else shortRingColor (spokeRing G x).length
      (G.firstFaceHitIndex (spokeRing G x) y)

private theorem spokeRingShortColor_face
    (G : Hypermap.{u}) (x y : G.Dart) :
    spokeRingShortColor G x (G.face y) = spokeRingShortColor G x y := by
  classical
  have hyFace : PermReachable G.face y (G.face y) :=
    PermReachable.forward G.face y
  have hindex := G.firstFaceHitIndex_eq_of_faceReachable
    (s := spokeRing G x) hyFace
  by_cases hxy : PermReachable G.face x y
  · have hxFace : PermReachable G.face x (G.face y) :=
      PermReachable.trans G.face hxy hyFace
    simp [spokeRingShortColor, hxy, hxFace]
  · have hxFace : ¬ PermReachable G.face x (G.face y) := by
      intro h
      exact hxy (PermReachable.trans G.face h
        (PermReachable.symm G.face hyFace))
    simp [spokeRingShortColor, hxy, hxFace, hindex]

/-- Coq `birkhoff.v::min_arity`: every face of a connected cubic minimal
counterexample has arity at least five. -/
theorem minArity
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (x : G.Dart) :
    5 ≤ G.arity x := by
  classical
  by_contra hnotFive
  have harityFour : G.arity x ≤ 4 := by omega
  let r := spokeRing G x
  have hr : G.SimpleRLinkCycle r := by
    simpa [r] using spokeRing_simpleRLinkCycle hG hconnected hcubic x
  have hrlen : r.length = G.arity x := by
    simp [r]
  have hrlenFour : r.length ≤ 4 := by omega
  have hrlenPos : 0 < r.length := by
    rw [hrlen]
    exact G.arity_pos x
  have hnotNontrivial : ¬ G.NontrivialRing 0 r := by
    have hBirkhoff := Birkhoff hG hconnected hcubic r (by omega) hr
    have hrNotFive : r.length ≠ 5 := by omega
    simpa [hrNotFive] using hBirkhoff
  have hnoOutside : ∀ y : G.Dart, ¬ G.DiskFC r y := by
    intro y hy
    apply hnotNontrivial
    rw [Hypermap.nontrivialRing_zero_iff]
    constructor
    · refine ⟨x, ?_⟩
      have := (diskF_spokeRing_iff hG hcubic x x).2
        (PermReachable.refl G.face x)
      simpa [r] using this
    · exact ⟨y, hy⟩
  have hfaceBand : ∀ y : G.Dart,
      ¬ PermReachable G.face x y → G.FaceBand r y := by
    intro y hxy
    by_contra hnotBand
    by_cases hyDisk : G.DiskN r y
    · have hyF : G.DiskF r y := ⟨hyDisk, hnotBand⟩
      have hxy' := (diskF_spokeRing_iff hG hcubic x y).1 (by
        simpa [r] using hyF)
      exact hxy hxy'
    · exact hnoOutside y ⟨hyDisk, hnotBand⟩
  apply hG.false_of_fourColorable
  refine ⟨spokeRingShortColor G x, ?_⟩
  constructor
  · intro y
    by_cases hxy : PermReachable G.face x y
    · have hxEdge : ¬ PermReachable G.face x (G.edge y) := by
        intro h
        exact hG.bridgeless y
          (PermReachable.trans G.face
            (PermReachable.symm G.face hxy) h)
      simp [spokeRingShortColor, hxy, hxEdge,
        shortRingColor_ne_zero]
    · by_cases hxEdge : PermReachable G.face x (G.edge y)
      · have hnonzero := shortRingColor_ne_zero r.length
          (G.firstFaceHitIndex r y)
        simpa [spokeRingShortColor, hxy, hxEdge, r] using
          (Ne.symm hnonzero)
      · have hyBand : G.FaceBand r y := hfaceBand y hxy
        have hedgeBand : G.FaceBand r (G.edge y) :=
          hfaceBand (G.edge y) hxEdge
        let i1 := G.firstFaceHitIndex r y
        let i2 := G.firstFaceHitIndex r (G.edge y)
        have hi1 : i1 < r.length := by
          exact G.firstFaceHitIndex_lt_length_of_faceBand hyBand
        have hi2 : i2 < r.length := by
          exact G.firstFaceHitIndex_lt_length_of_faceBand hedgeBand
        let y1 : G.Dart := r.get ⟨i1, hi1⟩
        let y2 : G.Dart := r.get ⟨i2, hi2⟩
        have hy1Mem : y1 ∈ r :=
          G.firstFaceHitIndex_get_mem hyBand
        have hy2Mem : y2 ∈ r :=
          G.firstFaceHitIndex_get_mem hedgeBand
        have hy1Reach : PermReachable G.face y1 y :=
          G.firstFaceHitIndex_get_faceReachable hyBand
        have hy2Reach : PermReachable G.face y2 (G.edge y) :=
          G.firstFaceHitIndex_get_faceReachable hedgeBand
        have hadj : G.RingAdj y1 y2 :=
          ⟨y, hy1Reach, PermReachable.symm G.face hy2Reach⟩
        have hneighbors := chordless_spokeRing hG hconnected hcubic x
          y1 (by simpa [r] using hy1Mem)
          y2 (by simpa [r] using hy2Mem) hadj
        have hsimple : G.FaceSimple r := hr.2
        have hnodup : r.Nodup := hsimple.nodup
        have hi1Source :
            G.firstFaceHitIndex r y1 = i1 := by
          dsimp [y1]
          exact G.firstFaceHitIndex_eq_of_faceSimple_get hsimple hi1
        have hi2Source :
            G.firstFaceHitIndex r y2 = i2 := by
          dsimp [y2]
          exact G.firstFaceHitIndex_eq_of_faceSimple_get hsimple hi2
        have hi1ToSource :
            i1 = G.firstFaceHitIndex r y1 := by
          simpa [i1] using
            G.firstFaceHitIndex_eq_of_faceReachable (s := r) hy1Reach
        have hi2ToSource :
            i2 = G.firstFaceHitIndex r y2 := by
          simpa [i2] using
            G.firstFaceHitIndex_eq_of_faceReachable (s := r) hy2Reach
        have hprevIndex :
            G.firstFaceHitIndex r (r.prev y1 hy1Mem) =
              (i1 + (r.length - 1)) % r.length := by
          dsimp [y1]
          rw [List.prev_getElem r hnodup i1 hi1]
          exact G.firstFaceHitIndex_eq_of_faceSimple_get hsimple
            (Nat.mod_lt _ hrlenPos)
        have hnextIndex :
            G.firstFaceHitIndex r (r.next y1 hy1Mem) =
              (i1 + 1) % r.length := by
          dsimp [y1]
          rw [List.next_getElem r hnodup i1 hi1]
          exact G.firstFaceHitIndex_eq_of_faceSimple_get hsimple
            (Nat.mod_lt _ hrlenPos)
        have hcyclic :
            i2 = (i1 + (r.length - 1)) % r.length ∨
              i2 = (i1 + 1) % r.length := by
          rcases hneighbors with hprev | hnext
          · left
            calc
              i2 = G.firstFaceHitIndex r y2 := hi2ToSource
              _ = G.firstFaceHitIndex r (r.prev y1 hy1Mem) := by rw [hprev]
              _ = (i1 + (r.length - 1)) % r.length := hprevIndex
          · right
            calc
              i2 = G.firstFaceHitIndex r y2 := hi2ToSource
              _ = G.firstFaceHitIndex r (r.next y1 hy1Mem) := by rw [hnext]
              _ = (i1 + 1) % r.length := hnextIndex
        have hy1y2 : y1 ≠ y2 := by
          intro h
          apply Hypermap.Bridgeless.not_ringAdj_self
            (G := G) hG.bridgeless y1
          simpa [h] using hadj
        have hi1i2 : i1 ≠ i2 := by
          intro h
          apply hy1y2
          dsimp [y1, y2]
          exact congrArg (fun k : Fin r.length => r.get k) (Fin.ext h)
        have hcolors := shortRingColor_ne_of_cyclic
          hrlenPos hrlenFour hi1 hi2 hi1i2 hcyclic
        simpa [spokeRingShortColor, hxy, hxEdge, r, i1, i2] using hcolors
  · intro y
    exact spokeRingShortColor_face G x y

/-- The unconditional minimal-counterexample face-arity interface supplied by
Coq `min_arity` together with the already-proved connectedness and cubicity
reductions. -/
theorem faceArityGeFiveMinimalCounterexamples_proved :
    Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u} := by
  intro G hG x
  exact minArity hG
    (Unavoidability.connectedMinimalCounterexamples_proved G hG)
    (Unavoidability.cubicMinimalCounterexamples_proved G hG) x

/-- Unconditional short-face exclusion for minimal counterexamples. -/
theorem noShortFaceOrbitsMinimalCounterexamples_proved :
    Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u} :=
  Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
    faceArityGeFiveMinimalCounterexamples_proved


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
