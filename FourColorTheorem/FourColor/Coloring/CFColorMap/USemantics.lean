import FourColorTheorem.FourColor.Coloring.CFColorMap.PrimitiveExtensions
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Backwards node iteration through the fresh `U` corner agrees with the old
ring iteration until the old ring closes. -/
theorem u_iterate_node_symm_point_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (i : Nat) (hi : i < n) :
    iteratePerm P.u.map.node.symm (i + 1) P.u.point =
      P.uOld (iteratePerm P.map.node.symm i (P.map.node P.point)) := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      have hi' : i < n := by omega
      have hproper : P.ProperRingHead := by
        have hn : n = (n - 2) + 2 := by omega
        have hnodup := hcycle.nodup
        rw [hn, ringDarts_succ_succ] at hnodup
        simp only [List.nodup_cons] at hnodup
        intro heq
        apply hnodup.1
        exact List.mem_cons.mpr (Or.inl heq.symm)
      have hne :
          iteratePerm P.map.node.symm i (P.map.node P.point) ≠
            P.map.node (P.map.node P.point) := by
        cases i with
        | zero =>
            intro heq
            apply hproper
            exact P.map.node.injective heq
        | succ j =>
            have havoid :
                iteratePerm P.map.node.symm j P.point ≠
                  P.map.node (P.map.node P.point) :=
              hcycle.avoids_node_node_point_before_last (k := j) (by omega)
            simpa [iteratePerm_succ] using havoid
      rw [iteratePerm_succ_right P.u.map.node.symm (i + 1) P.u.point,
        ih hi']
      change
        (if iteratePerm P.map.node.symm i (P.map.node P.point) =
              P.map.node (P.map.node P.point) then ExtDart.newEdge
          else ExtDart.old
            (P.map.node.symm
              (iteratePerm P.map.node.symm i
                (P.map.node P.point)))) =
          ExtDart.old
            (iteratePerm P.map.node.symm (i + 1)
              (P.map.node P.point))
      rw [if_neg hne, iteratePerm_succ_right]

/-- Coq `cpring_ecpU`, for an exact finite old ring cycle. -/
theorem ringDarts_u_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) :
    ringDarts P.u (n + 2) =
      ExtDart.newEdge :: ExtDart.new :: (ringDarts P n).map P.uOld := by
  rw [ringDarts_succ_succ]
  change
    ExtDart.newEdge :: ExtDart.new ::
        (List.range n).map
          (fun i => iteratePerm P.u.map.node.symm (i + 1) P.u.point) =
      ExtDart.newEdge :: ExtDart.new ::
        ((List.range n).map
          (fun i => iteratePerm P.map.node.symm i
            (P.map.node P.point))).map P.uOld
  simp only [List.map_map, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i hi
  exact u_iterate_node_symm_point_of_ringCycle hcycle i
    (List.mem_range.mp hi)

/-- The `U` constructor preserves the exact ring-cycle invariant while adding
two fresh boundary darts. -/
theorem ringCycle_u
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n) :
    RingCycle P.u (n + 2) where
  pos := by omega
  period := by
    have hlast :
        iteratePerm P.map.node.symm (n - 1) (P.map.node P.point) =
          P.map.node (P.map.node P.point) := by
      have hp := hcycle.period
      unfold RingPeriod at hp
      have hn : n = (n - 1) + 1 := by omega
      rw [hn, iteratePerm_succ_right] at hp
      apply P.map.node.symm.injective
      simpa using hp
    have hulast :=
      u_iterate_node_symm_point_of_ringCycle hcycle (n - 1) (by omega)
    have hn : n - 1 + 1 = n := by omega
    rw [hn, hlast] at hulast
    unfold RingPeriod
    have htotal : n + 2 = (n + 1) + 1 := by omega
    rw [htotal, iteratePerm_succ]
    change iteratePerm P.u.map.node.symm (n + 1) P.u.point =
      P.u.map.node P.u.point
    rw [iteratePerm_succ_right, hulast]
    change
      (if P.map.node (P.map.node P.point) =
            P.map.node (P.map.node P.point) then ExtDart.newEdge
        else ExtDart.old
          (P.map.node.symm (P.map.node (P.map.node P.point)))) =
        ExtDart.newEdge
    rw [if_pos rfl]
  nodup := by
    rw [ringDarts_u_of_ringCycle hcycle]
    have hold := hcycle.nodup.map (uOld_injective P)
    apply List.pairwise_cons.mpr
    constructor
    · intro a ha
      rcases List.mem_cons.mp ha with hnew | holdMem
      · subst a
        exact ExtDart.new_ne_newEdge.symm
      · rcases List.mem_map.mp holdMem with ⟨x, _hx, rfl⟩
        exact (ExtDart.old_ne_newEdge x).symm
    · apply List.pairwise_cons.mpr
      constructor
      · intro a ha
        rcases List.mem_map.mp ha with ⟨x, _hx, rfl⟩
        exact (ExtDart.old_ne_new x).symm
      · exact hold

/-- Program-level form of Coq `cpring_ecpU`. -/
theorem cpRing_u_of_ringCycle
    {cp : CProg} (hcycle : cpRingCycle cp) :
    cpRing (CpStep.u :: cp) =
      ExtDart.newEdge :: ExtDart.new ::
        (cpRing cp).map (cpmap cp).uOld := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_u] using
    ringDarts_u_of_ringCycle hcycle

theorem cpRingCycle_u
    {cp : CProg} (hcycle : cpRingCycle cp) :
    cpRingCycle (CpStep.u :: cp) := by
  exact ringCycle_u hcycle (CProg.ringSize_pos cp)

/-- The exact color word on the extended `U` ring. -/
theorem colorsOn_extensionUColor_ringDarts
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (k : P.map.Dart → Color) (e : Color) :
    P.u.map.colorsOn
        (Hypermap.extensionUColor P.map P.point k e)
        (ringDarts P.u (n + 2)) =
      k (P.map.node P.point) ::
        (e + k (P.map.node P.point)) ::
          P.map.colorsOn k (ringDarts P n) := by
  rw [ringDarts_u_of_ringCycle hcycle]
  change
    Hypermap.extensionUColor P.map P.point k e ExtDart.newEdge ::
        Hypermap.extensionUColor P.map P.point k e ExtDart.new ::
          P.u.map.colorsOn (Hypermap.extensionUColor P.map P.point k e)
            ((ringDarts P n).map P.uOld) = _
  apply congrArg₂ List.cons rfl
  apply congrArg₂ List.cons rfl
  exact Hypermap.colorsOn_map_of_apply _ _ _ _ (fun _ => rfl) _

/-- Trace equation in Coq `cpcolor1U_correct`: `U` prefixes the old ring
trace by the selected nonzero edge color twice. -/
theorem trace_extensionUColor_ringDarts
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    (k : P.map.Dart → Color) (e : Color) :
    ColSeq.trace
        (P.u.map.colorsOn
          (Hypermap.extensionUColor P.map P.point k e)
          (ringDarts P.u (n + 2))) =
      e :: e :: ColSeq.trace (P.map.colorsOn k (ringDarts P n)) := by
  rw [colorsOn_extensionUColor_ringDarts hcycle]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [ringDarts_succ]
  change ColSeq.trace
      (k (P.map.node P.point) ::
        (e + k (P.map.node P.point)) ::
          k (P.map.node P.point) ::
            P.map.colorsOn k
              ((List.range m).map
                (fun i => iteratePerm P.map.node.symm i P.point))) = _
  exact ColSeq.trace_insert_xor_pair _ _ _

/-- Semantic `CpU` branch: every old coloring and nonzero selected edge color
produces the exact trace accepted by `cpColorStep CpStep.u`. -/
theorem ringTrace_cpRing_u_of_coloring
    {cp : CProg} (hcycle : cpRingCycle cp)
    {k : (cpmap cp).map.Dart → Color}
    (hk : (cpmap cp).map.Coloring k) {e : Color}
    (he : e ≠ Color.zero) :
    (cpmap (CpStep.u :: cp)).map.RingTrace
      (cpRing (CpStep.u :: cp))
      (e :: e ::
        ColSeq.trace ((cpmap cp).map.colorsOn k (cpRing cp))) := by
  let ku : (cpmap (CpStep.u :: cp)).map.Dart → Color :=
    Hypermap.extensionUColor (cpmap cp).map (cpmap cp).point k e
  refine ⟨ku, ?_, ?_⟩
  · exact Hypermap.extensionUColor_coloring hk he
  · apply Eq.symm
    change ColSeq.trace
        ((cpmap (CpStep.u :: cp)).map.colorsOn ku
          (ringDarts (cpmap cp).u (CProg.ringSize cp + 2))) = _
    exact trace_extensionUColor_ringDarts hcycle
      (CProg.ringSize_pos cp) k e

/-- Generic pointed-map form of semantic `CpU` soundness. -/
theorem ringTrace_u_of_ringTrace
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) et)
    {e : Color} (he : e ≠ Color.zero) :
    P.u.map.RingTrace (ringDarts P.u (n + 2)) (e :: e :: et) := by
  rcases htrace.exists_coloring with ⟨k, hk, hkt⟩
  let ku : P.u.map.Dart → Color :=
    Hypermap.extensionUColor P.map P.point k e
  refine ⟨ku, Hypermap.extensionUColor_coloring hk he, ?_⟩
  apply Eq.symm
  rw [trace_extensionUColor_ringDarts hcycle hpos k e, hkt]

/-- Restrict an arbitrary coloring of `U` to its old darts. -/
def restrictUColor
    (P : PointedHypermap) (ku : P.u.map.Dart → Color) :
    P.map.Dart → Color :=
  fun x => ku (P.uOld x)

theorem restrictUColor_coloring
    {P : PointedHypermap} {ku : P.u.map.Dart → Color}
    (hku : P.u.map.Coloring ku) :
    P.map.Coloring (restrictUColor P ku) := by
  apply Hypermap.Coloring.pullback_of_edge_faceReachable hku P.uOld
  · intro x
    rw [P.uOld_edge]
    exact PermReachable.refl P.u.map.face _
  · intro x
    exact P.uOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)

/-- Every coloring of `U` is exactly the canonical extension of its old-dart
restriction, with the fresh edge difference as parameter. -/
theorem extensionUColor_restrict_eq
    {P : PointedHypermap} {ku : P.u.map.Dart → Color}
    (hku : P.u.map.Coloring ku) :
    let k := restrictUColor P ku
    let e := ku ExtDart.new + ku ExtDart.newEdge
    Hypermap.extensionUColor P.map P.point k e = ku := by
  dsimp only
  have hboundary :
      restrictUColor P ku (P.map.node P.point) =
        ku ExtDart.newEdge := by
    have hface := Hypermap.Coloring.face_eq (G := P.u.map) hku
      (ExtDart.newEdge : P.u.map.Dart)
    simpa [restrictUColor] using hface
  funext x
  cases x with
  | new =>
      change
        ku ExtDart.new + ku ExtDart.newEdge +
            restrictUColor P ku (P.map.node P.point) =
          ku ExtDart.new
      rw [hboundary]
      simp
  | newEdge =>
      exact hboundary
  | old x =>
      rfl

theorem extensionUColor_restrict_edge_ne_zero
    {P : PointedHypermap} {ku : P.u.map.Dart → Color}
    (hku : P.u.map.Coloring ku) :
    ku ExtDart.new + ku ExtDart.newEdge ≠ Color.zero := by
  intro hzero
  have heq : ku ExtDart.new = ku ExtDart.newEdge :=
    (Color.add_eq_zero_iff_eq _ _).1 hzero
  exact Hypermap.Coloring.edge_ne (G := P.u.map) hku
    (ExtDart.new : P.u.map.Dart) (by simpa using heq.symm)

/-- Converse semantic `U` branch: every extended coloring uniquely exposes a
nonzero duplicated prefix and an old-map ring trace. -/
theorem ringTrace_u_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hpos : 0 < n)
    {etu : ColSeq}
    (htrace : P.u.map.RingTrace (ringDarts P.u (n + 2)) etu) :
    ∃ e et,
      e ≠ Color.zero ∧
      P.map.RingTrace (ringDarts P n) et ∧
      etu = e :: e :: et := by
  rcases htrace.exists_coloring with ⟨ku, hku, hkt⟩
  let k := restrictUColor P ku
  let e := ku ExtDart.new + ku ExtDart.newEdge
  let et := ColSeq.trace (P.map.colorsOn k (ringDarts P n))
  refine ⟨e, et, extensionUColor_restrict_edge_ne_zero hku,
    ⟨k, restrictUColor_coloring hku, rfl⟩, ?_⟩
  have hcanon := extensionUColor_restrict_eq hku
  dsimp only at hcanon
  calc
    etu = ColSeq.trace (P.u.map.colorsOn ku (ringDarts P.u (n + 2))) :=
      hkt.symm
    _ = ColSeq.trace
        (P.u.map.colorsOn
          (Hypermap.extensionUColor P.map P.point k e)
          (ringDarts P.u (n + 2))) := by rw [hcanon]
    _ = e :: e :: et :=
      trace_extensionUColor_ringDarts hcycle hpos k e


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
