import FourColorTheorem.FourColor.Coloring.CFColorMap.USemantics
import FourColorTheorem.FourColor.Coloring.CFColorMap.KSemantics
import FourColorTheorem.FourColor.Coloring.CFColorMap.Rotation
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Exact ring-cycle preservation for derived `Y`, obtained through Coq's
primitive expansion word. -/
theorem ringCycle_y_via_expand
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n) :
    RingCycle P.y (n + 1) := by
  have hU : RingCycle P.u (n + 2) := ringCycle_u hcycle hpos
  have hR : RingCycle (P.u.rotate 1) (n + 2) := rotate_ringCycle hU
  have hK := ringCycle_k hR (by omega : 2 < n + 2)
  have hsize : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hsize] at hK
  have hRR := ringCycle_reverseRotate hK (by omega : 0 < n + 1)
  have hy := foldr_step_expandStep_y P
  change ((P.u.rotate 1).k).reverseRotate = P.y at hy
  rw [hy] at hRR
  exact hRR

/-- Exact ring-cycle preservation for derived `H`, likewise obtained through
the two primitive K contractions in Coq's expansion word. -/
theorem ringCycle_h_via_expand
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n) :
    RingCycle P.h n := by
  have hU : RingCycle P.u (n + 2) := ringCycle_u hcycle (by omega)
  have hR : RingCycle (P.u.rotate 1) (n + 2) := rotate_ringCycle hU
  have hK1 := ringCycle_k hR (by omega : 2 < n + 2)
  have hs1 : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hs1] at hK1
  have hK2 := ringCycle_k hK1 (by omega : 2 < n + 1)
  have hs2 : n + 1 - 2 + 1 = n := by omega
  rw [hs2] at hK2
  have hRR := ringCycle_reverseRotate hK2 (by omega : 0 < n)
  have hh := foldr_step_expandStep_h P
  change (((P.u.rotate 1).k).k).reverseRotate = P.h at hh
  rw [hh] at hRR
  exact hRR

/-- One of the two color choices in Coq's expanded `Y` constructor. -/
theorem ringTrace_y_choice
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {e c d : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: et))
    (hc0 : c ≠ Color.zero) (hce : c ≠ e) (hsum : c + e = d) :
    P.y.map.RingTrace (ringDarts P.y (n + 1)) (c :: d :: et) := by
  have hU := ringTrace_u_of_ringTrace hcycle hpos htrace hc0
  have hcycleU : RingCycle P.u (n + 2) := ringCycle_u hcycle hpos
  have hR0 := ringTrace_rotate hcycleU hU 1
  have hrotate :
      CProg.rotateLeft 1 (c :: c :: e :: et) =
        c :: e :: (et ++ [c]) := by
    simp
  rw [hrotate] at hR0
  have hcycleR : RingCycle (P.u.rotate 1) (n + 2) :=
    rotate_ringCycle hcycleU
  have hK0 := ringTrace_k_of_ringTrace hcycleR
    (by omega : 2 < n + 2) hR0 hce
  have hs : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hs] at hK0
  have hcycleK0 := ringCycle_k hcycleR (by omega : 2 < n + 2)
  rw [hs] at hcycleK0
  have hRR := ringTrace_reverseRotate hcycleK0 (by omega) hK0
  have hrrTrace :
      CProg.rotateRight 1 ((c + e) :: (et ++ [c])) =
        c :: (c + e) :: et := by
    change CProg.rotateRight 1 (((c + e) :: et) ++ [c]) = _
    exact CProg.rotateRight_one_append_singleton c ((c + e) :: et)
  rw [hrrTrace] at hRR
  have hy := foldr_step_expandStep_y P
  change ((P.u.rotate 1).k).reverseRotate = P.y at hy
  rw [hy, hsum] at hRR
  exact hRR

theorem ringTrace_y_left
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: et))
    (he : e ≠ Color.zero) :
    P.y.map.RingTrace (ringDarts P.y (n + 1))
      (EdgePerm.p231 e :: EdgePerm.p312 e :: et) := by
  apply ringTrace_y_choice hcycle hpos htrace
  · intro h
    apply he
    exact EdgePerm.injective EdgePerm.p231 (by simpa using h)
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · cases e <;> simp [EdgePerm.apply] at he ⊢

theorem ringTrace_y_right
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: et))
    (he : e ≠ Color.zero) :
    P.y.map.RingTrace (ringDarts P.y (n + 1))
      (EdgePerm.p312 e :: EdgePerm.p231 e :: et) := by
  apply ringTrace_y_choice hcycle hpos htrace
  · intro h
    apply he
    exact EdgePerm.injective EdgePerm.p312 (by simpa using h)
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · cases e <;> simp [EdgePerm.apply] at he ⊢

/-- Converse expanded `Y` semantics before quotienting the two possible
nonzero color choices by the fixed edge permutations. -/
theorem ringTrace_y_raw_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {ety : ColSeq}
    (htrace : P.y.map.RingTrace (ringDarts P.y (n + 1)) ety) :
    ∃ c e et,
      c ≠ Color.zero ∧ e ≠ Color.zero ∧ c ≠ e ∧
      P.map.RingTrace (ringDarts P n) (e :: et) ∧
      ety = c :: (c + e) :: et := by
  have hUcycle : RingCycle P.u (n + 2) :=
    ringCycle_u hcycle (by omega)
  have hRcycle : RingCycle (P.u.rotate 1) (n + 2) :=
    rotate_ringCycle hUcycle
  have hKcycle := ringCycle_k hRcycle (by omega : 2 < n + 2)
  have hs : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hs] at hKcycle
  have hy := foldr_step_expandStep_y P
  change ((P.u.rotate 1).k).reverseRotate = P.y at hy
  rw [← hy] at htrace
  have hKtrace := ringTrace_reverseRotate_elim hKcycle (by omega) htrace
  rw [← hs] at hKtrace
  rcases ringTrace_k_elim hRcycle (by omega : 2 < n + 2) hKtrace with
    ⟨a, b, rest, hab, hRtrace, hKout⟩
  have hUtrace := ringTrace_rotate_one_elim hUcycle (by omega) hRtrace
  rcases ringTrace_u_elim hcycle (by omega) hUtrace with
    ⟨c, source, hc, hsource, hUout⟩
  have hsourceLen := Hypermap.RingTrace.length (G := P.map) hsource
  rw [length_ringDarts] at hsourceLen
  cases hsourceEq : source with
  | nil =>
      simp [hsourceEq] at hsourceLen
      omega
  | cons e et =>
      have hsource' :
          P.map.RingTrace (ringDarts P n) (e :: et) := by
        simpa [hsourceEq] using hsource
      have he : e ≠ Color.zero := ringTrace_head_ne_zero hsize hsource'
      have hOld :
          a :: b :: rest = c :: e :: (et ++ [c]) := by
        calc
          a :: b :: rest =
              CProg.rotateLeft 1
                (CProg.rotateRight 1 (a :: b :: rest)) :=
            (CProg.rotateLeft_rotateRight 1 (a :: b :: rest)).symm
          _ = CProg.rotateLeft 1 (c :: c :: e :: et) := by
            rw [hUout, hsourceEq]
          _ = c :: e :: (et ++ [c]) := by
            simp [CProg.rotateLeft_one_cons]
      have ha : a = c := (List.cons.inj hOld).1
      have htail : b :: rest = e :: (et ++ [c]) :=
        (List.cons.inj hOld).2
      have hb : b = e := (List.cons.inj htail).1
      have hrest : rest = et ++ [c] := (List.cons.inj htail).2
      subst a
      subst b
      rw [hrest] at hKout
      have hfinal : ety = c :: (c + e) :: et := by
        calc
          ety = CProg.rotateRight 1 (CProg.rotateLeft 1 ety) :=
            (CProg.rotateRight_rotateLeft 1 ety).symm
          _ = CProg.rotateRight 1 ((c + e) :: (et ++ [c])) := by
            rw [hKout]
          _ = c :: (c + e) :: et := by
            change CProg.rotateRight 1 (((c + e) :: et) ++ [c]) = _
            exact CProg.rotateRight_one_append_singleton c ((c + e) :: et)
      exact ⟨c, e, et, hc, he, hab, hsource', hfinal⟩

/-- Every `Y` ring trace is exactly one of the two optimized Coq branches. -/
theorem ringTrace_y_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {ety : ColSeq}
    (htrace : P.y.map.RingTrace (ringDarts P.y (n + 1)) ety) :
    ∃ e et,
      e ≠ Color.zero ∧
      P.map.RingTrace (ringDarts P n) (e :: et) ∧
      (ety = EdgePerm.p231 e :: EdgePerm.p312 e :: et ∨
        ety = EdgePerm.p312 e :: EdgePerm.p231 e :: et) := by
  rcases ringTrace_y_raw_elim hcycle hsize htrace with
    ⟨c, e, et, hc, he, hce, hsource, hfinal⟩
  refine ⟨e, et, he, hsource, ?_⟩
  cases e <;> cases c <;>
    simp_all [EdgePerm.apply]

/-- One color choice in Coq's expanded `H` constructor. -/
theorem ringTrace_h_choice
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {e1 e2 c d : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et))
    (hc0 : c ≠ Color.zero) (hc1 : c ≠ e1)
    (hc12 : c + e1 ≠ e2) (hsum : (c + e1) + e2 = d) :
    P.h.map.RingTrace (ringDarts P.h n) (c :: d :: et) := by
  have hU := ringTrace_u_of_ringTrace hcycle (by omega) htrace hc0
  have hcycleU : RingCycle P.u (n + 2) := ringCycle_u hcycle (by omega)
  have hR0 := ringTrace_rotate hcycleU hU 1
  have hrotate :
      CProg.rotateLeft 1 (c :: c :: e1 :: e2 :: et) =
        c :: e1 :: e2 :: (et ++ [c]) := by
    simp
  rw [hrotate] at hR0
  have hcycleR : RingCycle (P.u.rotate 1) (n + 2) :=
    rotate_ringCycle hcycleU
  have hK10 := ringTrace_k_of_ringTrace hcycleR
    (by omega : 2 < n + 2) hR0 hc1
  have hs1 : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hs1] at hK10
  have hcycleK10 := ringCycle_k hcycleR (by omega : 2 < n + 2)
  rw [hs1] at hcycleK10
  have hK20 := ringTrace_k_of_ringTrace hcycleK10
    (by omega : 2 < n + 1) hK10 hc12
  have hs2 : n + 1 - 2 + 1 = n := by omega
  rw [hs2] at hK20
  have hcycleK20 := ringCycle_k hcycleK10 (by omega : 2 < n + 1)
  rw [hs2] at hcycleK20
  have hRR := ringTrace_reverseRotate hcycleK20 hsize hK20
  have hrrTrace :
      CProg.rotateRight 1 (((c + e1) + e2) :: (et ++ [c])) =
        c :: ((c + e1) + e2) :: et := by
    change CProg.rotateRight 1 ((((c + e1) + e2) :: et) ++ [c]) = _
    exact CProg.rotateRight_one_append_singleton c
      (((c + e1) + e2) :: et)
  rw [hrrTrace] at hRR
  have hh := foldr_step_expandStep_h P
  change (((P.u.rotate 1).k).k).reverseRotate = P.h at hh
  rw [hh, hsum] at hRR
  exact hRR

theorem ringTrace_h_equal_left
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: e :: et))
    (he : e ≠ Color.zero) :
    P.h.map.RingTrace (ringDarts P.h n)
      (EdgePerm.p231 e :: EdgePerm.p231 e :: et) := by
  apply ringTrace_h_choice hcycle hsize htrace
  · intro h
    apply he
    exact EdgePerm.injective EdgePerm.p231 (by simpa using h)
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · simp

theorem ringTrace_h_equal_right
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: e :: et))
    (he : e ≠ Color.zero) :
    P.h.map.RingTrace (ringDarts P.h n)
      (EdgePerm.p312 e :: EdgePerm.p312 e :: et) := by
  apply ringTrace_h_choice hcycle hsize htrace
  · intro h
    apply he
    exact EdgePerm.injective EdgePerm.p312 (by simpa using h)
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · cases e <;> simp [EdgePerm.apply] at he ⊢
  · simp

theorem ringTrace_h_unequal
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {e1 e2 : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et))
    (he1 : e1 ≠ Color.zero) (he2 : e2 ≠ Color.zero)
    (hne : e1 ≠ e2) :
    P.h.map.RingTrace (ringDarts P.h n) (e2 :: e1 :: et) := by
  apply ringTrace_h_choice hcycle hsize htrace he2 hne.symm
  · cases e1 <;> cases e2 <;>
      simp at he1 he2 hne ⊢
  · simp [Color.add_comm e2 e1]

/-- Converse expanded `H` semantics before reducing the available fresh color
to the optimized equal-head and unequal-head branches. -/
theorem ringTrace_h_raw_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {eth : ColSeq}
    (htrace : P.h.map.RingTrace (ringDarts P.h n) eth) :
    ∃ c e1 e2 et,
      c ≠ Color.zero ∧ e1 ≠ Color.zero ∧ e2 ≠ Color.zero ∧
      c ≠ e1 ∧ c + e1 ≠ e2 ∧
      P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) ∧
      eth = c :: ((c + e1) + e2) :: et := by
  have hUcycle : RingCycle P.u (n + 2) :=
    ringCycle_u hcycle (by omega)
  have hRcycle : RingCycle (P.u.rotate 1) (n + 2) :=
    rotate_ringCycle hUcycle
  have hK1cycle := ringCycle_k hRcycle (by omega : 2 < n + 2)
  have hs1 : n + 2 - 2 + 1 = n + 1 := by omega
  rw [hs1] at hK1cycle
  have hK2cycle := ringCycle_k hK1cycle (by omega : 2 < n + 1)
  have hs2 : n + 1 - 2 + 1 = n := by omega
  rw [hs2] at hK2cycle
  have hh := foldr_step_expandStep_h P
  change (((P.u.rotate 1).k).k).reverseRotate = P.h at hh
  rw [← hh] at htrace
  have hK2trace := ringTrace_reverseRotate_elim hK2cycle (by omega) htrace
  rw [← hs2] at hK2trace
  rcases ringTrace_k_elim hK1cycle (by omega : 2 < n + 1) hK2trace with
    ⟨d1, d2, rest2, hd, hK1trace, hK2out⟩
  rw [← hs1] at hK1trace
  rcases ringTrace_k_elim hRcycle (by omega : 2 < n + 2) hK1trace with
    ⟨a, b, rest1, hab, hRtrace, hK1out⟩
  have hd1 : d1 = a + b := (List.cons.inj hK1out).1
  have hrest1 : d2 :: rest2 = rest1 := (List.cons.inj hK1out).2
  subst d1
  rw [← hrest1] at hRtrace
  have hUtrace := ringTrace_rotate_one_elim hUcycle (by omega) hRtrace
  rcases ringTrace_u_elim hcycle (by omega) hUtrace with
    ⟨c, source, hc, hsource, hUout⟩
  have hsourceLen := Hypermap.RingTrace.length (G := P.map) hsource
  rw [length_ringDarts] at hsourceLen
  cases hsourceEq : source with
  | nil =>
      simp [hsourceEq] at hsourceLen
      omega
  | cons e1 sourceTail =>
      cases htailEq : sourceTail with
      | nil =>
          simp [hsourceEq, htailEq] at hsourceLen
          omega
      | cons e2 et =>
          have hsource' :
              P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) := by
            simpa [hsourceEq, htailEq] using hsource
          have he1 : e1 ≠ Color.zero :=
            ringTrace_head_ne_zero hsize hsource'
          have hsourceRot := ringTrace_rotate hcycle hsource' 1
          have hsourceRot' :
              (P.rotate 1).map.RingTrace
                (ringDarts (P.rotate 1) n) (e2 :: (et ++ [e1])) := by
            simpa using hsourceRot
          have he2 : e2 ≠ Color.zero :=
            ringTrace_head_ne_zero hsize hsourceRot'
          have hOld :
              a :: b :: d2 :: rest2 =
                c :: e1 :: e2 :: (et ++ [c]) := by
            calc
              a :: b :: d2 :: rest2 =
                  CProg.rotateLeft 1
                    (CProg.rotateRight 1 (a :: b :: d2 :: rest2)) :=
                (CProg.rotateLeft_rotateRight 1
                  (a :: b :: d2 :: rest2)).symm
              _ = CProg.rotateLeft 1 (c :: c :: e1 :: e2 :: et) := by
                rw [hUout, hsourceEq, htailEq]
              _ = c :: e1 :: e2 :: (et ++ [c]) := by
                simp [CProg.rotateLeft_one_cons]
          have ha : a = c := (List.cons.inj hOld).1
          have ht1 : b :: d2 :: rest2 = e1 :: e2 :: (et ++ [c]) :=
            (List.cons.inj hOld).2
          have hb : b = e1 := (List.cons.inj ht1).1
          have ht2 : d2 :: rest2 = e2 :: (et ++ [c]) :=
            (List.cons.inj ht1).2
          have hd2 : d2 = e2 := (List.cons.inj ht2).1
          have hrest2 : rest2 = et ++ [c] := (List.cons.inj ht2).2
          subst a
          subst b
          subst d2
          rw [hrest2] at hK2out
          have hfinal : eth = c :: ((c + e1) + e2) :: et := by
            calc
              eth = CProg.rotateRight 1 (CProg.rotateLeft 1 eth) :=
                (CProg.rotateRight_rotateLeft 1 eth).symm
              _ = CProg.rotateRight 1
                  (((c + e1) + e2) :: (et ++ [c])) := by
                rw [hK2out]
              _ = c :: ((c + e1) + e2) :: et := by
                change CProg.rotateRight 1
                  ((((c + e1) + e2) :: et) ++ [c]) = _
                exact CProg.rotateRight_one_append_singleton c
                  (((c + e1) + e2) :: et)
          exact ⟨c, e1, e2, et, hc, he1, he2, hab, hd,
            hsource', hfinal⟩

/-- Every `H` ring trace is exactly one of the three branches implemented by
Coq's optimized coloring transformer. -/
theorem ringTrace_h_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 1 < n)
    {eth : ColSeq}
    (htrace : P.h.map.RingTrace (ringDarts P.h n) eth) :
    ∃ e1 e2 et,
      e1 ≠ Color.zero ∧ e2 ≠ Color.zero ∧
      P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) ∧
      (if e1 = e2 then
        eth = EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: et ∨
          eth = EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: et
       else
        eth = e2 :: e1 :: et) := by
  rcases ringTrace_h_raw_elim hcycle hsize htrace with
    ⟨c, e1, e2, et, hc, he1, he2, hc1, hc12, hsource, hfinal⟩
  refine ⟨e1, e2, et, he1, he2, hsource, ?_⟩
  cases e1 <;> cases e2 <;> cases c <;>
    simp_all [EdgePerm.apply]

/-- Any witnessed map coloring makes the dynamically sized ring nontrivial. -/
theorem Hypermap.RingTrace.nodeOrder_gt_one
    {P : PointedHypermap} {r : List P.map.Dart} {et : ColSeq}
    (htrace : P.map.RingTrace r et) :
    1 < P.nodeOrder := by
  rcases htrace.exists_coloring with ⟨k, hk, _⟩
  exact (nodeOrder_ringCycle P).one_lt_of_properRingHead
    (hk.properRingHead P.point)

/-- Restrict a `Y` coloring to the embedded old darts. -/
noncomputable def restrictYColor
    (P : PointedHypermap) (ky : P.y.map.Dart → Color) :
    P.map.Dart → Color :=
  fun x => ky (P.yOld x)

theorem restrictYColor_coloring
    {P : PointedHypermap} {ky : P.y.map.Dart → Color}
    (hky : P.y.map.Coloring ky) :
    P.map.Coloring (restrictYColor P ky) := by
  apply Hypermap.Coloring.pullback_of_edge_faceReachable hky P.yOld
  · intro x
    rw [P.yOld_edge]
    exact PermReachable.refl P.y.map.face _
  · intro x
    exact P.yOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)

/-- Restrict an `H` coloring to the embedded old darts. -/
noncomputable def restrictHColor
    (P : PointedHypermap) (kh : P.h.map.Dart → Color) :
    P.map.Dart → Color :=
  fun x => kh (P.hOld x)

theorem restrictHColor_coloring
    {P : PointedHypermap} {kh : P.h.map.Dart → Color}
    (hkh : P.h.map.Coloring kh) :
    P.map.Coloring (restrictHColor P kh) := by
  apply Hypermap.Coloring.pullback_of_edge_faceReachable hkh P.hOld
  · intro x
    rw [P.hOld_edge]
    exact PermReachable.refl P.h.map.face _
  · intro x
    exact P.hOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)

/-- Short branch of Coq `cpcolor1A_correct`: on a two-dart ring, `A`
preserves exactly the same coloring traces. -/
theorem ringTrace_a_iff_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) {et : ColSeq} :
    P.a.map.RingTrace (ringDarts P.a 2) et ↔
      P.map.RingTrace (ringDarts P 2) et := by
  have hedge := a_edge_eq_of_ringCycle_eq_two hcycle hsize
  have hface := a_face_eq_of_ringCycle_eq_two hcycle hsize
  have hdarts := ringDarts_a_eq_of_ringCycle_eq_two hcycle hsize
  constructor
  · rintro ⟨k, hk, htrace⟩
    refine ⟨k, ?_, ?_⟩
    · constructor
      · intro x
        rw [← hedge]
        exact Hypermap.Coloring.edge_ne (G := P.a.map) hk x
      · intro x
        rw [← hface]
        exact Hypermap.Coloring.face_eq (G := P.a.map) hk x
    · rw [← hdarts]
      exact htrace
  · rintro ⟨k, hk, htrace⟩
    refine ⟨k, ?_, ?_⟩
    · constructor
      · intro x
        rw [hedge]
        exact Hypermap.Coloring.edge_ne (G := P.map) hk x
      · intro x
        rw [hface]
        exact Hypermap.Coloring.face_eq (G := P.map) hk x
    · rw [hdarts]
      exact htrace

/-- The short `K` branch in Coq is empty: extending a two-dart ring would
make the fresh edge lie in one face, contradicting a proper coloring. -/
theorem not_coloring_k_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    ¬ P.k.map.FourColorable := by
  have hface := hcycle.face_edge_eq_node_of_eq_two hsize
  have hnodeNode : P.map.node (P.map.node P.point) = P.point := by
    simpa using (congrArg P.map.node hface).symm
  have hnotLong :
      ¬ P.map.LongRingHead (P.map.node P.point) := by
    intro hlong
    apply hlong
    rw [Hypermap.face_edge_eq_node_symm]
    calc
      P.map.node.symm (P.map.node P.point) = P.point := by simp
      _ = P.map.node (P.map.node P.point) := hnodeNode.symm
  rintro ⟨k, hk⟩
  have hne : k (ExtDart.newEdge : P.k.map.Dart) ≠ k ExtDart.new := by
    simpa using Hypermap.Coloring.edge_ne (G := P.k.map) hk
      (ExtDart.new : P.k.map.Dart)
  have heq := Hypermap.Coloring.face_eq (G := P.k.map) hk
    (ExtDart.newEdge : P.k.map.Dart)
  have heq' : k (ExtDart.new : P.k.map.Dart) = k ExtDart.newEdge := by
    change
      k (Hypermap.ExtensionN.face P.map (P.map.node P.point)
          ExtDart.newEdge) = k ExtDart.newEdge at heq
    rw [Hypermap.ExtensionN.face_newEdge, if_neg hnotLong] at heq
    exact heq
  exact hne heq'.symm


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
