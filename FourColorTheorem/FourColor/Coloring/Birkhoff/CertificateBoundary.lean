import FourColorTheorem.FourColor.Coloring.BirkhoffCheck
import FourColorTheorem.FourColor.Coloring.CFColorMap
import FourColorTheorem.FourColor.Hypermap.QuasicubicEuler
import FourColorTheorem.FourColor.Hypermap.RevSnip
import FourColorTheorem.FourColor.Hypermap.Sew

/-!
Semantic soundness of the executable Birkhoff ring certificates.

This follows `fourcolor-coq/theories/proof/birkhoff.v`.  The first layer below
is Coq's numerical `chkbP` argument: an admitted cubic basis map is strictly
smaller than the complementary snip map.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- The backwards-node orbit stored by `RingCycle` is an explicit
`FunctionCycle` for the inverse node permutation. -/
theorem ringCycle_functionCycleNodeSymm
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) :
    FunctionCycle P.map.node.symm (ringDarts P n) := by
  by_cases hn : n = 0
  · subst n
    simp [ringDarts, FunctionCycle]
  apply FunctionCycle.of_eq_next hcycle.nodup
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hin : i < n := by simpa [ringDarts] using hi
  have hnext := List.next_getElem (ringDarts P n) hcycle.nodup i hi
  rw [hnext]
  simp only [ringDarts, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range]
  rw [← iteratePerm_succ_right]
  by_cases hisucc : i + 1 < n
  · rw [Nat.mod_eq_of_lt hisucc]
  · have hisuccEq : i + 1 = n := by omega
    rw [hisuccEq, Nat.mod_self]
    simpa [RingPeriod] using hcycle.period

/-- Every Coq `cubic_prog` has a ring of size at least two. -/
theorem CProg.one_lt_ringSize_of_cubic :
    ∀ {cp : CProg}, CProg.cubic cp = true → 1 < CProg.ringSize cp
  | [], _ => by decide
  | s :: cp, hcp => by
      cases s with
      | rotate n =>
          have ht := CProg.cubic_cons_tail hcp
          simpa [CProg.ringSize] using one_lt_ringSize_of_cubic ht
      | reverseRotate => simp [CProg.cubic] at hcp
      | y =>
          have ht := CProg.cubic_cons_tail hcp
          have ih := one_lt_ringSize_of_cubic ht
          simp [CProg.ringSize]
          omega
      | h =>
          have ht := CProg.cubic_cons_tail hcp
          simpa [CProg.ringSize] using one_lt_ringSize_of_cubic ht
      | u =>
          have ht := CProg.cubic_cons_tail hcp
          have ih := one_lt_ringSize_of_cubic ht
          simp [CProg.ringSize]
      | k => simp [CProg.cubic] at hcp
      | a => simp [CProg.cubic] at hcp

/-- Coq `cycle_rev_cpring` specialized to the exact executable ring size of
every `cubic_prog`. -/
theorem cpRingCycle_of_cubic :
    ∀ {cp : CProg}, CProg.cubic cp = true → cpRingCycle cp
  | [], _ => cpRingCycle_nil
  | s :: cp, hcp => by
      cases s with
      | rotate n =>
          have ht := CProg.cubic_cons_tail hcp
          exact cpRingCycle_rotate (cpRingCycle_of_cubic ht)
      | reverseRotate => simp [CProg.cubic] at hcp
      | y =>
          have ht := CProg.cubic_cons_tail hcp
          exact cpRingCycle_y (cpRingCycle_of_cubic ht)
            (cpmap_cubicGeometry_of_cubic ht).proper
            (CProg.one_lt_ringSize_of_cubic ht)
      | h =>
          have ht := CProg.cubic_cons_tail hcp
          have hcycle := cpRingCycle_of_cubic ht
          have hproper := (cpmap_cubicGeometry_of_cubic ht).proper
          by_cases htwo : CProg.ringSize cp = 2
          · exact cpRingCycle_h_of_ringSize_eq_two hcycle hproper htwo
          · have hgt : 2 < CProg.ringSize cp := by
              have := CProg.one_lt_ringSize_of_cubic ht
              omega
            exact cpRingCycle_h hcycle hproper
              (ringCycle_longRingHead_of_two_lt hcycle hgt) hgt
      | u =>
          have ht := CProg.cubic_cons_tail hcp
          exact cpRingCycle_u (cpRingCycle_of_cubic ht)
      | k => simp [CProg.cubic] at hcp
      | a => simp [CProg.cubic] at hcp

/-- Reversing an inverse-permutation cycle gives a forward-permutation cycle,
the `cycle_rev_cpring` orientation used by Coq's sewing argument. -/
theorem functionCycle_reverse_of_symm
    {α : Type _} [DecidableEq α] {σ : Equiv.Perm α} {r : List α}
    (hcycle : FunctionCycle σ.symm r) (hnodup : r.Nodup) :
    FunctionCycle σ r.reverse := by
  apply FunctionCycle.of_eq_next (List.nodup_reverse.mpr hnodup)
  intro x hxrev
  have hx : x ∈ r := List.mem_reverse.mp hxrev
  have hprev : r.prev x hx ∈ r := List.prev_mem r x hx
  have hstep : σ.symm (r.prev x hx) = x := by
    calc
      σ.symm (r.prev x hx) = r.next (r.prev x hx) hprev :=
        hcycle.eq_next hnodup _ hprev
      _ = x := List.next_prev r hnodup x hx
  have hsigma : σ x = r.prev x hx := by
    apply σ.symm.injective
    rw [σ.symm_apply_apply, hstep]
  calc
    σ x = r.prev x hx := hsigma
    _ = r.reverse.next x hxrev :=
      (List.next_reverse_eq_prev r hnodup x hx).symm

/-- Coq `rotr 1 (rev (cpring Gr))`. -/
noncomputable def basisBoundary (cp : CProg) : List (cpmap cp).map.Dart :=
  Hypermap.rotateRightOne (cpRing cp).reverse

@[simp]
theorem basisBoundary_length (cp : CProg) :
    (basisBoundary cp).length = CProg.ringSize cp := by
  simp [basisBoundary]

theorem basisBoundary_nodup
    {cp : CProg} (hcp : CProg.cubic cp = true) :
    (basisBoundary cp).Nodup := by
  have hcycle := cpRingCycle_of_cubic hcp
  exact List.nodup_rotate.mpr (List.nodup_reverse.mpr hcycle.nodup)

theorem basisBoundary_cycle
    {cp : CProg} (hcp : CProg.cubic cp = true) :
    FunctionCycle (cpmap cp).map.node (basisBoundary cp) := by
  have hcycle := cpRingCycle_of_cubic hcp
  have hrev : FunctionCycle (cpmap cp).map.node (cpRing cp).reverse :=
    functionCycle_reverse_of_symm
      (ringCycle_functionCycleNodeSymm hcycle) hcycle.nodup
  unfold basisBoundary Hypermap.rotateRightOne
  exact Hypermap.functionCycle_rotate hrev
    (List.nodup_reverse.mpr hcycle.nodup) ((cpRing cp).reverse.length - 1)

/-- Undo the exact orientation used by the sewn basis boundary.  This is the
list/trace algebra in Coq `birkhoff.v` lines 275--279. -/
theorem ringTrace_rotateRightOne_reverse_elim
    {G : Hypermap.{u}} {r : List G.Dart} {et : ColSeq} {e : Color}
    (hr : r ≠ []) (hlen : (et ++ [e]).length = r.length)
    (htrace : G.RingTrace (Hypermap.rotateRightOne r.reverse)
      (ColSeq.rot1 (et ++ [e]).reverse)) :
    G.RingTrace r (e :: et) := by
  have hrev := htrace.reverse_boundary
  have hboundaryReverse :
      (Hypermap.rotateRightOne r.reverse).reverse = r.rotate 1 := by
    unfold Hypermap.rotateRightOne
    rw [List.reverse_rotate, List.length_reverse]
    have hpos : 0 < r.length := List.length_pos_iff_ne_nil.mpr hr
    rw [Nat.mod_eq_of_lt (by omega : r.length - 1 < r.length)]
    rw [Nat.sub_sub_self (by omega : 1 ≤ r.length)]
    simp
  have htraceRot : G.RingTrace (r.rotate 1) (et ++ [e]) := by
    rw [hboundaryReverse] at hrev
    simpa [ColSeq.rot1] using hrev
  have hrot := htraceRot.rotate_boundary (r.length - 1)
  have hboundary : (r.rotate 1).rotate (r.length - 1) = r := by
    rw [List.rotate_rotate]
    have hpos : 0 < r.length := List.length_pos_iff_ne_nil.mpr hr
    rw [show 1 + (r.length - 1) = r.length by omega,
      List.rotate_length]
  have htraceSeq : (et ++ [e]).rotate (r.length - 1) = e :: et := by
    rw [← hlen]
    simp only [List.length_append, List.length_singleton]
    rw [show et.length + 1 - 1 = et.length by omega,
      List.rotate_append_length_eq]
    rfl
  rw [hboundary, htraceSeq] at hrot
  exact hrot

/-- The exact sewing interface constructed in Coq `chkbP`. -/
noncomputable def basisSewBoundary
    {G : Hypermap.{u}} {r : List G.Dart} {h m : Nat} {cp : CProg}
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1)
    (hcheck : checkBasisProgram h m cp = true) :
    Hypermap.SewBoundary
      (G.snipDisk r hplanar hr) (cpmap cp).map
      (Hypermap.snipdRing hplanar hr) (basisBoundary cp) where
  cycleD := Hypermap.cycle_snipdRing hplanar hr
  faceSimpleD := Hypermap.faceSimple_snipdRing hplanar hr
  cycleR := basisBoundary_cycle (checkBasisProgram_spec hcheck).1
  nodupR := basisBoundary_nodup (checkBasisProgram_spec hcheck).1
  length_eq := by
    have hdisk : (Hypermap.snipdRing hplanar hr).length = r.length := by
      simpa only [List.length_map] using
        congrArg List.length (Hypermap.map_snipdRing hplanar hr)
    calc
      (Hypermap.snipdRing hplanar hr).length = r.length := hdisk
      _ = h + 1 := hrlen
      _ = (cpRing cp).length := (checkBasisProgram_spec hcheck).2.2.symm
      _ = (basisBoundary cp).length := by simp

/-- The strict cardinality estimate in Coq `birkhoff.v::chkbP`.  The
configuration check bounds the basis map, while `quasicubicEuler` computes the
complementary snip map from its outside faces. -/
theorem basisMap_card_lt_snipRemainder
    {G : Hypermap.{u}} {r : List G.Dart} {h m : Nat} {cp : CProg}
    (hplanar : G.EulerPlanar) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1) (hnt : G.NontrivialRing m r)
    (hplain : (G.snipRemainder r hplanar hr).Plain)
    (hquasi : (G.snipRemainder r hplanar hr).Quasicubic
      (Hypermap.sniprRing hplanar hr))
    (hconnected : (G.snipRemainder r hplanar hr).Connected)
    (hcheck : checkBasisProgram h m cp = true) :
    Fintype.card (cpmap cp).map.Dart <
      Fintype.card (G.snipRemainder r hplanar hr).Dart := by
  let Gr := G.snipRemainder r hplanar hr
  let bGr := Hypermap.sniprRing hplanar hr
  have hbLen : bGr.length = r.length := by
    calc
      bGr.length = (bGr.map Hypermap.snipr).length := by simp
      _ = r.reverse.length := congrArg List.length
        (Hypermap.map_sniprRing hplanar hr)
      _ = r.length := List.length_reverse
  have hbNonempty : bGr ≠ [] := by
    intro hb
    have : bGr.length = 0 := by simp [hb]
    omega
  have heuler :=
    (Gr.quasicubicEuler
      (Hypermap.cycle_sniprRing hplanar hr)
      (Hypermap.sniprRing_nodup hplanar hr)
      hplain hquasi hconnected).1
      (Hypermap.snipRemainder_eulerPlanar hplanar hr)
  have hfaces := Hypermap.snipRemainder_faceOrbitCount hplanar hr
  have hbound := (checkBasisProgram_spec hcheck).2.1
  have houtside := hnt.2
  change 6 * ((if bGr = [] then 0 else 1) + Gr.faceOrbitCount) =
      Fintype.card Gr.Dart + (2 * bGr.length + 12) at heuler
  change Gr.faceOrbitCount =
      G.FaceOrbitCountOf (G.DiskFC r) + r.length at hfaces
  change Fintype.card (cpmap cp).map.Dart + 1 <
      6 * m + 4 * h at hbound
  change Fintype.card (cpmap cp).map.Dart < Fintype.card Gr.Dart
  simp only [if_neg hbNonempty] at heuler
  omega

/-- Coq `cpmap_cubic`, with the perimeter expressed by the actual sewing
boundary rather than by the pointed node orbit predicate. -/
theorem cpmap_quasicubic_basisBoundary
    {cp : CProg} (hcp : CProg.cubic cp = true) :
    (cpmap cp).map.Quasicubic (basisBoundary cp) := by
  have hcycle := cpRingCycle_of_cubic hcp
  have hquasi := cpmap_quasicubic_of_cubic hcp
  intro x hx
  apply hquasi x
  intro hon
  apply hx
  unfold basisBoundary Hypermap.rotateRightOne
  apply List.mem_rotate.mpr
  apply List.mem_reverse.mpr
  exact hcycle.mem_ringDarts_of_onRing
    (by have := CProg.one_lt_ringSize_of_cubic hcp; omega) hon

end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
