import FourColorTheorem.FourColor.Coloring.CFColorMap.KSemantics
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- One reverse rotation cancels one backward pointer rotation. -/
theorem reverseRotate_rotate_one (P : PointedHypermap) :
    (P.rotate 1).reverseRotate = P := by
  cases P with
  | mk G p =>
      change PointedHypermap.mk G
        (G.node ((PointedHypermap.mk G p).rotate 1).point) =
          PointedHypermap.mk G p
      rw [PointedHypermap.mk.injEq, rotate_one_point]
      simp

theorem k_rotate_one (P : PointedHypermap) :
    (P.rotate 1).k = P.n.rotate 1 := by
  unfold k
  rw [reverseRotate_rotate_one]

theorem u_n_eq_y (P : PointedHypermap) :
    P.u.n = P.y := by
  cases P
  rfl

theorem y_n_eq_h (P : PointedHypermap) :
    P.y.n = P.h := by
  cases P
  rfl

/-- The primitive word used by Coq `cpexpand1` for `Y` has exactly the same
pointed-map semantics as the derived `Y` constructor. -/
theorem foldr_step_expandStep_y (P : PointedHypermap) :
    (CProg.expandStep CpStep.y).foldr step P = P.y := by
  change ((P.u.rotate 1).k).reverseRotate = P.y
  rw [k_rotate_one, reverseRotate_rotate_one, u_n_eq_y]

/-- The primitive word used by Coq `cpexpand1` for `H` has exactly the same
pointed-map semantics as the derived `H` constructor. -/
theorem foldr_step_expandStep_h (P : PointedHypermap) :
    (CProg.expandStep CpStep.h).foldr step P = P.h := by
  change (((P.u.rotate 1).k).k).reverseRotate = P.h
  rw [k_rotate_one, u_n_eq_y, k_rotate_one,
    reverseRotate_rotate_one, y_n_eq_h]

/-- Repointing forward once is rotation by `n-1` on an exact nonempty ring. -/
theorem reverseRotate_eq_rotate_pred_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n) :
    P.reverseRotate = P.rotate (n - 1) := by
  cases P with
  | mk G p =>
      have hpoint : G.node p =
          ((PointedHypermap.mk G p).rotate (n - 1)).point := by
        rw [rotate_point, hcycle.nodeOrder_eq]
        have hexp : n - (n - 1) = 1 := by omega
        rw [hexp]
        rfl
      exact congrArg (PointedHypermap.mk G) hpoint

theorem ringCycle_reverseRotate
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n) :
    RingCycle P.reverseRotate n := by
  rw [reverseRotate_eq_rotate_pred_of_ringCycle hcycle hpos]
  exact rotate_ringCycle hcycle

/-- Pointed-map form of the semantic rotation branch. -/
theorem ringTrace_rotate
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) et) (r : Nat) :
    (P.rotate r).map.RingTrace
      (ringDarts (P.rotate r) n) (CProg.rotateLeft r et) := by
  change P.map.RingTrace (ringDarts (P.rotate r) n)
    (CProg.rotateLeft r et)
  rw [rotate_ringDarts_eq_rotateLeft_of_ringCycle P r n hcycle]
  have hlen : et.length = n :=
    by simpa [ringDarts] using
      Hypermap.RingTrace.length (G := P.map) htrace
  by_cases hr : r ≤ n
  · rw [CProg.rotateLeft_eq_rotate_of_le (by
        simpa [ringDarts] using hr),
      CProg.rotateLeft_eq_rotate_of_le (by simpa [hlen] using hr)]
    exact htrace.rotate_boundary r
  · have hnr : n ≤ r := Nat.le_of_not_ge hr
    rw [CProg.rotateLeft_oversize (by simpa [ringDarts] using hnr),
      CProg.rotateLeft_oversize (by simpa [hlen] using hnr)]
    exact htrace

/-- Every entry of a coloring trace on a nontrivial ring cycle is nonzero.
An arbitrary occurrence is rotated to the head and reduced to
`ringTrace_head_ne_zero`. -/
theorem ringTrace_not_mem_zero
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) et) :
    Color.zero ∉ et := by
  intro hzero
  have split : ∀ {xs : ColSeq}, Color.zero ∈ xs →
      ∃ pre post, xs = pre ++ Color.zero :: post := by
    intro xs hx
    induction xs with
    | nil => simp at hx
    | cons x xs ih =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨[], xs, rfl⟩
        · rcases ih hx with ⟨pre, post, hsplit⟩
          exact ⟨x :: pre, post, by simp [hsplit]⟩
  rcases split hzero with ⟨pre, post, rfl⟩
  have hrot := ringTrace_rotate hcycle htrace pre.length
  have hrot' :
      (P.rotate pre.length).map.RingTrace
        (ringDarts (P.rotate pre.length) n)
        (Color.zero :: post ++ pre) := by
    rw [CProg.rotateLeft_eq_rotate_of_le (by simp)] at hrot
    simpa [List.rotate_append_length_eq] using hrot
  exact ringTrace_head_ne_zero hsize hrot' rfl

/-- Converse to arbitrary pointer rotation. -/
theorem ringTrace_rotate_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) {et : ColSeq}
    (htrace : (P.rotate r).map.RingTrace
      (ringDarts (P.rotate r) n) et) :
    P.map.RingTrace (ringDarts P n) (CProg.rotateRight r et) := by
  rcases htrace.exists_coloring with ⟨k, hk, hkt⟩
  let oldTrace := ColSeq.trace (P.map.colorsOn k (ringDarts P n))
  have hrot : et = CProg.rotateLeft r oldTrace := by
    calc
      et = ColSeq.trace
          (P.map.colorsOn k (ringDarts (P.rotate r) n)) := hkt.symm
      _ = ColSeq.trace
          (P.map.colorsOn k (CProg.rotateLeft r (ringDarts P n))) := by
        rw [rotate_ringDarts_eq_rotateLeft_of_ringCycle P r n hcycle]
      _ = CProg.rotateLeft r oldTrace := by
        rw [Hypermap.colorsOn_rotateLeft, ColSeq.trace_rotateLeft]
  refine ⟨k, hk, ?_⟩
  rw [hrot, CProg.rotateRight_rotateLeft]

/-- Coq's `R'` trace transport: forward repointing right-rotates a nontrivial
boundary trace by one place. -/
theorem ringTrace_reverseRotate
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) et) :
    P.reverseRotate.map.RingTrace
      (ringDarts P.reverseRotate n) (CProg.rotateRight 1 et) := by
  have hlen : et.length = n := by
    simpa using Hypermap.RingTrace.length (G := P.map) htrace
  have hright : CProg.rotateRight 1 et = et.rotate (n - 1) := by
    rw [CProg.rotateRight_eq_rotate, hlen]
  rw [reverseRotate_eq_rotate_pred_of_ringCycle hcycle (by omega), hright]
  change P.map.RingTrace (ringDarts (P.rotate (n - 1)) n)
    (et.rotate (n - 1))
  rw [rotate_ringDarts_eq_rotateLeft_of_ringCycle P (n - 1) n hcycle,
    CProg.rotateLeft_eq_rotate_of_le (by
      simp [ringDarts])]
  exact htrace.rotate_boundary (n - 1)

/-- Forward repointing followed by one backward repointing is the identity. -/
theorem rotate_reverseRotate_one (P : PointedHypermap) :
    P.reverseRotate.rotate 1 = P := by
  cases P with
  | mk G p =>
      change PointedHypermap.mk G
          ((PointedHypermap.mk G (G.node p)).rotate 1).point =
        PointedHypermap.mk G p
      rw [PointedHypermap.mk.injEq, rotate_one_point]
      simp

/-- Converse to `ringTrace_reverseRotate`: rotate the resulting trace once to
recover the trace before forward repointing. -/
theorem ringTrace_reverseRotate_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {et : ColSeq}
    (htrace : P.reverseRotate.map.RingTrace
      (ringDarts P.reverseRotate n) et) :
    P.map.RingTrace (ringDarts P n) (CProg.rotateLeft 1 et) := by
  have hcycleR := ringCycle_reverseRotate hcycle hpos
  have htraceR := ringTrace_rotate hcycleR htrace 1
  rw [rotate_reverseRotate_one] at htraceR
  exact htraceR

/-- Converse to one backward pointer rotation. -/
theorem ringTrace_rotate_one_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {et : ColSeq}
    (htrace : (P.rotate 1).map.RingTrace
      (ringDarts (P.rotate 1) n) et) :
    P.map.RingTrace (ringDarts P n) (CProg.rotateRight 1 et) := by
  have hcycleR : RingCycle (P.rotate 1) n := rotate_ringCycle hcycle
  have htraceR := ringTrace_reverseRotate hcycleR hsize htrace
  rw [reverseRotate_rotate_one] at htraceR
  exact htraceR


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
