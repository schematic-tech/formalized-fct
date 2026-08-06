import FourColorTheorem.FourColor.Hypermap.EulerTree
import FourColorTheorem.FourColor.Coloring.Kempe
import FourColorTheorem.FourColor.Coloring.RingTrace
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
Rotation invariance of perimeter geometry and ring-trace closure.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The exact geometric hypothesis called
`ucycle_planar_plain_quasicubic` in Coq `kempe.v`. -/
structure CyclePlanarPlainQuasicubic
    (G : Hypermap.{u}) (r : List G.Dart) : Prop where
  cycle : FunctionCycle G.node r
  nodup : r.Nodup
  eulerPlanar : G.EulerPlanar
  plain : G.Plain
  quasicubic : G.Quasicubic r

/-- Function cycles are invariant under cyclic list rotation. -/
theorem functionCycle_rotate
    {α : Type _} [DecidableEq α]
    {f : α -> α} {r : List α}
    (hc : FunctionCycle f r) (hn : r.Nodup) (n : Nat) :
    FunctionCycle f (r.rotate n) := by
  have hnr : (r.rotate n).Nodup := List.nodup_rotate.mpr hn
  apply FunctionCycle.of_eq_next hnr
  intro x hx
  have hx0 : x ∈ r := List.mem_rotate.mp hx
  calc
    f x = r.next x hx0 := hc.eq_next hn x hx0
    _ = List.formPerm r x :=
      (List.formPerm_apply_mem_eq_next hn x hx0).symm
    _ = List.formPerm (r.rotate n) x := by
      rw [List.formPerm_rotate r hn n]
    _ = (r.rotate n).next x hx :=
      List.formPerm_apply_mem_eq_next hnr x hx

/-- The full perimeter geometry is invariant under cyclic rotation. -/
def CyclePlanarPlainQuasicubic.rotate
    (G : Hypermap.{u}) {r : List G.Dart}
    (geo : CyclePlanarPlainQuasicubic G r) (n : Nat) :
    CyclePlanarPlainQuasicubic G (r.rotate n) where
  cycle := functionCycle_rotate geo.cycle geo.nodup n
  nodup := List.nodup_rotate.mpr geo.nodup
  eulerPlanar := geo.eulerPlanar
  plain := geo.plain
  quasicubic := by
    intro x hx
    exact geo.quasicubic x (by
      simpa [List.mem_rotate] using hx)

/-- Rotate a nonempty perimeter to the exact `z :: node z :: p` form used by
Coq `Kempe_map`.  The second dart is forced by the function-cycle law. -/
theorem CyclePlanarPlainQuasicubic.exists_aligned
    (G : Hypermap.{u}) {r : List G.Dart}
    (geo : CyclePlanarPlainQuasicubic G r)
    {z : G.Dart} (hz : z ∈ r) (hnode : G.node z ≠ z) :
    ∃ n p, n ≤ r.length ∧ r.rotate n = z :: G.node z :: p := by
  rcases (List.mem_iff_append).mp hz with ⟨pre, post, hsplit⟩
  have hrot : r.rotate pre.length = z :: (post ++ pre) := by
    rw [hsplit, List.rotate_append_length_eq]
    simp
  have hcycle := functionCycle_rotate geo.cycle geo.nodup pre.length
  rw [hrot] at hcycle
  cases htail : post ++ pre with
  | nil =>
      have hc : FunctionCycle G.node [z] := by
        simpa [htail] using hcycle
      have : G.node z = z := hc.2
      exact False.elim (hnode this)
  | cons y ys =>
      have hc : FunctionCycle G.node (z :: y :: ys) := by
        simpa [htail] using hcycle
      have hp : FunctionPath G.node z (y :: ys) := hc.1
      have hzy : G.node z = y := hp.1
      subst y
      refine ⟨pre.length, ys, ?_, by simpa [htail] using hrot⟩
      rw [hsplit]
      simp

/-- `ColSeq.rot1` is the ordinary one-place list rotation. -/
theorem colSeq_rot1_eq_rotate (cs : ColSeq) :
    ColSeq.rot1 cs = cs.rotate 1 := by
  cases cs <;> simp [ColSeq.rot1]

/-- Generic right rotation by one, expressed using `List.rotate`. -/
def listUnrot1 {α : Type _} (xs : List α) : List α :=
  xs.rotate (xs.length - 1)

/-- Canonical inverse to one-place `ColSeq.rot1`. -/
def colSeqUnrot1 (cs : ColSeq) : ColSeq :=
  listUnrot1 cs

@[simp]
theorem list_rotate_one_unrot1 {α : Type _} (xs : List α) :
    (listUnrot1 xs).rotate 1 = xs := by
  rw [listUnrot1, List.rotate_rotate]
  cases xs with
  | nil => simp
  | cons x xs =>
      rw [Nat.sub_add_cancel (by simp), List.rotate_length]

@[simp]
theorem colSeq_rot1_unrot1 (cs : ColSeq) :
    ColSeq.rot1 (colSeqUnrot1 cs) = cs := by
  rw [colSeqUnrot1, colSeq_rot1_eq_rotate,
    list_rotate_one_unrot1]

theorem map_listUnrot1 {α β : Type _} (f : α -> β) (xs : List α) :
    (listUnrot1 xs).map f = listUnrot1 (xs.map f) := by
  simp [listUnrot1, List.map_rotate]

/-- Reading colors commutes with one-place boundary rotation. -/
theorem colorsOn_rotate_one
    (G : Hypermap.{u}) (k : G.Dart -> Color) (r : List G.Dart) :
    G.colorsOn k (r.rotate 1) = ColSeq.rot1 (G.colorsOn k r) := by
  change (r.rotate 1).map k = ColSeq.rot1 (r.map k)
  rw [List.map_rotate, colSeq_rot1_eq_rotate]

/-- A ring trace rotates with its boundary. -/
theorem RingTrace.rotate_one
    (G : Hypermap.{u}) {r : List G.Dart} {et : ColSeq}
    (htrace : G.RingTrace r et) :
    G.RingTrace (r.rotate 1) (ColSeq.rot1 et) := by
  rcases htrace with ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  rw [G.colorsOn_rotate_one, ColSeq.trace_rot1]

/-- Coq's one-step `gram_rot` transport: Kempe closure of a boundary implies
Kempe closure of its one-place rotation. -/
theorem kempeClosed_ringTrace_rotate_one
    (G : Hypermap.{u}) (r : List G.Dart)
    (hclosed : Chromogram.KempeClosed (G.RingTrace r)) :
    Chromogram.KempeClosed (G.RingTrace (r.rotate 1)) := by
  intro et htrace
  constructor
  · intro g
    exact RingTrace.perm (G := G) htrace g
  · rcases htrace with ⟨k, hk, het⟩
    let et0 := ColSeq.trace (G.colorsOn k r)
    have htrace0 : G.RingTrace r et0 := ⟨k, hk, rfl⟩
    have hetRot : et = ColSeq.rot1 et0 := by
      rw [het, G.colorsOn_rotate_one, ColSeq.trace_rot1]
    rcases (hclosed et0 htrace0).2 with ⟨w, hw, hall⟩
    refine ⟨Chromogram.gramRot w, ?_, ?_⟩
    · rw [hetRot, Chromogram.matchGramRot]
      exact hw
    · intro et' het'
      let et0' := colSeqUnrot1 et'
      have hrot : ColSeq.rot1 et0' = et' := colSeq_rot1_unrot1 et'
      have hw' : Chromogram.matchg [] et0' w = true := by
        rw [← Chromogram.matchGramRot et0' w, hrot]
        exact het'
      have htrace0' := hall et0' hw'
      simpa [hrot] using RingTrace.rotate_one (G := G) htrace0'

/-- Iterated boundary-rotation transport for Kempe closure. -/
theorem kempeClosed_ringTrace_rotate
    (G : Hypermap.{u}) (r : List G.Dart)
    (hclosed : Chromogram.KempeClosed (G.RingTrace r)) (n : Nat) :
    Chromogram.KempeClosed (G.RingTrace (r.rotate n)) := by
  induction n with
  | zero => simpa using hclosed
  | succ n ih =>
      have hnext := kempeClosed_ringTrace_rotate_one G (r.rotate n) ih
      simpa [List.rotate_rotate, Nat.succ_eq_add_one] using hnext


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
