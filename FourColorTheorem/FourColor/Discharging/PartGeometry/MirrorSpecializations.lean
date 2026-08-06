import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorRecursion

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem exactFitp_eq_false_of_arity_ne_size
    {p : Part} {x : G.Dart}
    (h : G.arity x ≠ p.size) :
    exactFitp G x p = false := by
  simp [exactFitp, h]

theorem exactFitp_eq_false_of_pentagonal_size_lt_five
    (hG : G.Pentagonal) {p : Part} {x : G.Dart}
    (hsize : p.size < 5) :
    exactFitp G x p = false := by
  exact exactFitp_eq_false_of_arity_ne_size (G := G) (p := p) (x := x) (by
    intro hx
    have hge : 5 ≤ G.arity x :=
      Hypermap.arity_ge_five_of_pentagonal hG x
    omega)

theorem exactFitp_mirror_of_pentagonal_size_lt_five
    (hG : G.Pentagonal) (p : Part) (x : G.Dart)
    (hsize : p.size < 5) :
    exactFitp G x p = exactFitp G.mirror x (mirror p) := by
  rw [exactFitp_eq_false_of_pentagonal_size_lt_five
    (G := G) hG (p := p) (x := x) hsize]
  have hmirrorSize : (mirror p).size < 5 := by
    simpa using hsize
  rw [exactFitp_eq_false_of_pentagonal_size_lt_five
    (G := G.mirror) hG.mirror (p := mirror p) (x := x) hmirrorSize]

theorem exactFitp_mirror_part_of_pentagonal_size_lt_five
    (hG : G.Pentagonal) (p : Part) (x : G.Dart)
    (hsize : p.size < 5) :
    exactFitp G x (mirror p) = exactFitp G.mirror x p := by
  have hmirrorSize : (mirror p).size < 5 := by
    simpa [size_mirror] using hsize
  have h := exactFitp_mirror_of_pentagonal_size_lt_five
    (G := G) hG (mirror p) x hmirrorSize
  simpa [mirror_mirror] using h

end

end Part

end FourColor

end Schematic.Math.GraphTheory
