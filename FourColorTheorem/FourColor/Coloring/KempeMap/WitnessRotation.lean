import FourColorTheorem.FourColor.Coloring.KempeMap.RotationGeometry

/-!
Kempe witnesses and transport under boundary rotation.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The chromogram half of Kempe closure at one particular trace. -/
def KempeWitness
    (G : Hypermap.{u}) (r : List G.Dart) (et : ColSeq) : Prop :=
  ∃ w : Chromogram,
    Chromogram.matchg [] et w = true ∧
      ∀ et', Chromogram.matchg [] et' w = true -> G.RingTrace r et'

/-- Trace-level form of Coq's `gram_rot` step. -/
theorem KempeWitness.rotate_one
    (G : Hypermap.{u}) {r : List G.Dart} {et : ColSeq}
    (hwit : G.KempeWitness r et) :
    G.KempeWitness (r.rotate 1) (ColSeq.rot1 et) := by
  rcases hwit with ⟨w, hw, hall⟩
  refine ⟨Chromogram.gramRot w, ?_, ?_⟩
  · rw [Chromogram.matchGramRot]
    exact hw
  · intro et' het'
    let et0 := colSeqUnrot1 et'
    have hrot : ColSeq.rot1 et0 = et' := colSeq_rot1_unrot1 et'
    have hw0 : Chromogram.matchg [] et0 w = true := by
      rw [← Chromogram.matchGramRot et0 w, hrot]
      exact het'
    simpa [hrot] using RingTrace.rotate_one (G := G) (hall et0 hw0)

/-- Iterated trace-level boundary rotation. -/
theorem KempeWitness.rotate
    (G : Hypermap.{u}) {r : List G.Dart} {et : ColSeq}
    (hwit : G.KempeWitness r et) (n : Nat) :
    G.KempeWitness (r.rotate n) ((ColSeq.rot1^[n]) et) := by
  induction n with
  | zero => simpa using hwit
  | succ n ih =>
      have hnext := KempeWitness.rotate_one (G := G) ih
      simpa [List.rotate_rotate, Nat.succ_eq_add_one,
        Function.iterate_succ_apply'] using hnext

/-- The trace of a coloring along an iteratively rotated boundary is the
iterated one-place rotation of its original trace. -/
theorem trace_colorsOn_rotate
    (G : Hypermap.{u}) (k : G.Dart -> Color) (r : List G.Dart) (n : Nat) :
    ColSeq.trace (G.colorsOn k (r.rotate n)) =
      (ColSeq.rot1^[n]) (ColSeq.trace (G.colorsOn k r)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← List.rotate_rotate r n 1, G.colorsOn_rotate_one,
        ColSeq.trace_rot1, ih]
      rw [show n + 1 = n.succ by omega,
        Function.iterate_succ_apply']

/-- Right-rotating a color word before taking its trace gives its right trace,
the identity used for Coq's recursive `rotr 1 s` boundary. -/
theorem trace_colSeqUnrot1 (cs : ColSeq) :
    ColSeq.trace (colSeqUnrot1 cs) = ColSeq.urtrace cs := by
  rw [← ColSeq.urtrace_rot1 (colSeqUnrot1 cs), colSeq_rot1_unrot1]

/-- Tracing a coloring around a right-rotated boundary yields the original
right trace. -/
theorem trace_colorsOn_listUnrot1
    (G : Hypermap.{u}) (k : G.Dart -> Color) (r : List G.Dart) :
    ColSeq.trace (G.colorsOn k (listUnrot1 r)) =
      ColSeq.urtrace (r.map k) := by
  change ColSeq.trace ((listUnrot1 r).map k) =
    ColSeq.urtrace (r.map k)
  rw [map_listUnrot1]
  change ColSeq.trace (colSeqUnrot1 (r.map k)) =
    ColSeq.urtrace (r.map k)
  exact trace_colSeqUnrot1 _

/-- Elementary color-word identity behind the fixed-face branch of Coq
`Kempe_map`. -/
theorem urtrace_cons_cons_of_tail_last
    (a b : Color) (cs : ColSeq)
    (hlast : (b :: cs).getLastD b = b) :
    ColSeq.urtrace (a :: b :: cs) =
      (a + b) :: (a + b) :: ColSeq.urtrace cs := by
  cases cs with
  | nil => simp [ColSeq.urtrace, ColSeq.pairSums, Color.add_comm]
  | cons c cs =>
      simp only [ColSeq.urtrace, ColSeq.pairSums_cons]
      simp only [List.getLastD_cons] at hlast ⊢
      rw [hlast]
      simp [Color.add_comm]

/-- Coq's `trace_r` calculation in the fixed-face branch, stated on the
right-rotated source boundary. -/
theorem Coloring.urtrace_aligned_of_face_fixed
    (G : Hypermap.{u}) (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    {k : G.Dart -> Color} (hk : G.Coloring k)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hfixed : G.face z = z) :
    let e1 := k z + k (G.node z)
    e1 ≠ Color.zero ∧
      ColSeq.urtrace ((z :: G.node z :: p).map k) =
        e1 :: e1 :: ColSeq.urtrace (p.map k) := by
  dsimp only
  have hnodeEdge : G.node z = G.edge z := by
    rw [← Plain.node_face_eq_edge (G := G) hplain z, hfixed]
  have hnodeLast :
      G.node ((G.node z :: p).getLastD (G.node z)) = z := by
    simpa [List.getLastD] using hcycle.2
  have hnodeFaceEdge : G.node (G.face (G.edge z)) = z := by
    rw [Plain.node_face_eq_edge (G := G) hplain (G.edge z),
      Plain.edge_edge (G := G) hplain z]
  have hlast :
      (G.node z :: p).getLastD (G.node z) = G.face (G.edge z) := by
    apply G.node.injective
    rw [hnodeLast, hnodeFaceEdge]
  have hlastColor :
      ((G.node z :: p).map k).getLastD (k (G.node z)) =
        k (G.node z) := by
    calc
      ((G.node z :: p).map k).getLastD (k (G.node z)) =
          k ((G.node z :: p).getLastD (G.node z)) := by
        simpa using
          (List.getLastD_map (f := k) (l := G.node z :: p)
            (a := G.node z))
      _ = k (G.face (G.edge z)) := congrArg k hlast
      _ = k (G.edge z) := Coloring.face_eq (G := G) hk (G.edge z)
      _ = k (G.node z) := congrArg k hnodeEdge.symm
  constructor
  · intro hzero
    apply Coloring.ne_edge (G := G) hk z
    rw [← hnodeEdge]
    exact (Color.add_eq_zero_iff_eq (k z) (k (G.node z))).mp hzero
  · change ColSeq.urtrace (k z :: k (G.node z) :: p.map k) = _
    exact urtrace_cons_cons_of_tail_last _ _ _ hlastColor


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
