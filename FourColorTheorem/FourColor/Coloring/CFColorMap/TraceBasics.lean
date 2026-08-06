
import FourColorTheorem.FourColor.Coloring.CFColor
import FourColorTheorem.FourColor.Reducibility.ProgramMap
import FourColorTheorem.FourColor.Coloring.RingTrace

/-!
Semantic correctness of construction-program colour trees.

This ports the map-colouring half of Gonthier's `cfcolor.v`.  The executable
tree transformers live in `CFColor`; this file connects them to colourings of
the semantic maps from `ProgramMap`.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

/-- Coq `coloring_proper_cpring`: a proper face coloring rules out a
one-dart node orbit at every possible ring head. -/
theorem Coloring.properRingHead
    {G : Hypermap} {k : G.Dart → Color}
    (hk : G.Coloring k) (x : G.Dart) :
    G.ProperRingHead x := by
  unfold ProperRingHead
  intro hx
  apply Coloring.edge_ne (G := G) hk x
  calc
    k (G.edge x) = k (G.face (G.edge x)) :=
      (Coloring.face_eq (G := G) hk (G.edge x)).symm
    _ = k (G.node.symm x) := by rw [G.face_edge_eq_node_symm]
    _ = k x := congrArg k (by
      apply G.node.injective
      simpa using hx)

/-- Pull a face coloring back along a dart map that preserves source faces
and sends each source edge to the target edge up to face reachability. -/
theorem Coloring.pullback_of_edge_faceReachable
    {G H : Hypermap} {k : H.Dart → Color}
    (hk : H.Coloring k) (f : G.Dart → H.Dart)
    (hedge : ∀ x, PermReachable H.face
      (H.edge (f x)) (f (G.edge x)))
    (hface : ∀ x, PermReachable H.face (f x) (f (G.face x))) :
    G.Coloring (fun x => k (f x)) := by
  constructor
  · intro x
    have hedgeColor := Coloring.eq_of_face_reachable (G := H) hk (hedge x)
    intro heq
    exact Coloring.edge_ne (G := H) hk (f x) (hedgeColor.symm.trans heq)
  · intro x
    exact Coloring.eq_of_face_reachable (G := H) hk (hface x)

/-- Reading colors after mapping darts is pointwise, independently of how the
mapped darts were constructed. -/
theorem colorsOn_map_of_apply
    (G : Hypermap) {D : Type*} (k : G.Dart → Color)
    (f : D → G.Dart) (c : D → Color)
    (h : ∀ x, k (f x) = c x) (r : List D) :
    G.colorsOn k (r.map f) = r.map c := by
  change List.map k (List.map f r) = List.map c r
  rw [List.map_map]
  exact List.map_congr_left (fun x _ => h x)

end Hypermap

namespace ColSeq

/-- Inserting a face of xor difference `e` twice into a cyclic color word
prefixes its edge trace by `e,e`. -/
theorem trace_insert_xor_pair (a e : Color) (tail : ColSeq) :
    trace (a :: (e + a) :: a :: tail) =
      e :: e :: trace (a :: tail) := by
  simp [trace_cons, pairSums, Color.add_comm e a]
  rw [Color.add_comm a e]
  simp

/-- Deleting the middle of three consecutive face colors contracts the first
two edge colors by xor.  This is the list identity used in Coq's
`cpcolor1K_correct`. -/
theorem trace_erase_middle (a b c : Color) (tail : ColSeq) :
    trace (a :: c :: tail) =
      ((a + b) + (b + c)) :: (trace (a :: b :: c :: tail)).drop 2 := by
  rw [trace_cons, trace_cons]
  simp only [List.cons_append, pairSums_cons]
  simp [Color.add_assoc]

/-- If the first and third region colors agree, deleting the first two
regions deletes exactly the first two entries of the cyclic edge trace.  This
is the list identity in Coq's `cpcolor1A_correct`. -/
theorem trace_drop_two_of_first_eq_third
    (a b c : Color) (tail : ColSeq) (hac : a = c) :
    trace (c :: tail) = (trace (a :: b :: c :: tail)).drop 2 := by
  subst c
  cases tail with
  | nil =>
      simp [trace, ptrace, ctrace, pairSums, sum, Color.add_comm b a]
  | cons d tail =>
      simp [trace_cons, pairSums, pairSums_append_singleton]

/-- Cyclic traces commute with ordinary left rotation. -/
theorem trace_rotate (cs : ColSeq) : ∀ n : Nat,
    trace (cs.rotate n) = (trace cs).rotate n
  | 0 => by simp
  | n + 1 => by
      rw [show cs.rotate (n + 1) = (cs.rotate n).rotate 1 by
        rw [List.rotate_rotate]]
      rw [show (trace cs).rotate (n + 1) =
          ((trace cs).rotate n).rotate 1 by
        rw [List.rotate_rotate]]
      have hrot1 (xs : ColSeq) : rot1 xs = xs.rotate 1 := by
        cases xs <;> simp [rot1]
      rw [← hrot1 (cs.rotate n), trace_rot1,
        hrot1 (trace (cs.rotate n)), trace_rotate cs n]

theorem trace_rotateLeft (cs : ColSeq) (n : Nat) :
    trace (CProg.rotateLeft n cs) =
      CProg.rotateLeft n (trace cs) := by
  by_cases h : n ≤ cs.length
  · rw [CProg.rotateLeft_eq_rotate_of_le h,
      CProg.rotateLeft_eq_rotate_of_le (by
        simpa [ColSeq.length_trace] using h)]
    exact trace_rotate cs n
  · have hov : cs.length ≤ n := Nat.le_of_not_ge h
    rw [CProg.rotateLeft_oversize hov,
      CProg.rotateLeft_oversize (by
        simpa [ColSeq.length_trace] using hov)]

end ColSeq

namespace CProg

theorem rotateRight_one_append_singleton {α : Type _}
    (x : α) (xs : List α) :
    rotateRight 1 (xs ++ [x]) = x :: xs := by
  cases xs with
  | nil => simp [rotateRight]
  | cons y ys =>
      calc
        rotateRight 1 ((y :: ys) ++ [x]) =
            rotateRight 1 (rotateLeft 1 (x :: y :: ys)) := by
              rw [rotateLeft_one_cons]
        _ = x :: y :: ys := rotateRight_rotateLeft 1 (x :: y :: ys)

end CProg

end FourColor

end Schematic.Math.GraphTheory
