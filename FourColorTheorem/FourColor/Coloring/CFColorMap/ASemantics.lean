import FourColorTheorem.FourColor.Coloring.CFColorMap.KSemantics
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Restrict an `A` coloring to the source map.  Although `A` rewires the
edge and face permutations, every source adjacency and face step is still
represented in the merged map. -/
noncomputable def restrictAColor
    (P : PointedHypermap) (ka : P.a.map.Dart → Color) :
    P.map.Dart → Color :=
  fun x => ka (P.aOld x)

theorem restrictAColor_coloring
    {P : PointedHypermap} {ka : P.a.map.Dart → Color}
    (hka : P.a.map.Coloring ka) :
    P.map.Coloring (restrictAColor P ka) := by
  apply Hypermap.Coloring.pullback_of_edge_faceReachable hka P.aOld
  · intro x
    exact P.aOld_edge_faceReachable_edge x
  · intro x
    exact P.aOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)

/-- Semantic `A` branch: equal first two edge differences allow the first two
boundary regions to be merged, leaving the tail trace. -/
theorem ringTrace_a_of_ringTrace
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: e :: et)) :
    P.a.map.RingTrace (ringDarts P.a (n - 2)) et := by
  rcases htrace.exists_coloring with ⟨k, hk, hkt⟩
  have hpairs := ringTrace_head_pair_of_eq
    (P := P) hsize k hkt
  have hmerge :
      k (P.map.node P.point) =
        k (P.map.face (P.map.edge P.point)) := by
    have hraw :
        k (P.map.node P.point) + k P.point =
          k P.point + k (P.map.face (P.map.edge P.point)) := by
      rw [hpairs.1, hpairs.2]
    have hcancel := congrArg (fun z => z + k P.point) hraw
    simpa [Color.add_assoc, Color.add_comm, Color.add_left_comm] using hcancel
  have hka : P.a.map.Coloring k :=
    Hypermap.extensionAColoring hk
      (ringCycle_longRingHead_of_two_lt hcycle hsize) hmerge
  have hn : n = (n - 3) + 3 := by omega
  let tailColors : ColSeq :=
    P.map.colorsOn k
      ((List.range (n - 3)).map
        (fun i => iteratePerm P.map.node.symm (i + 2) P.point))
  have hcolors : P.map.colorsOn k (ringDarts P n) =
      k (P.map.node P.point) :: k P.point ::
        k (P.map.face (P.map.edge P.point)) :: tailColors := by
    rw [hn, ringDarts_succ_succ_succ]
    simp [Hypermap.colorsOn, tailColors]
  have hdropTrace :
      ColSeq.trace ((P.map.colorsOn k (ringDarts P n)).drop 2) = et := by
    rw [hcolors]
    change ColSeq.trace
      (k (P.map.face (P.map.edge P.point)) :: tailColors) = et
    rw [ColSeq.trace_drop_two_of_first_eq_third _ _ _ _ hmerge]
    rw [← hcolors, hkt]
    rfl
  refine ⟨k, hka, ?_⟩
  apply Eq.symm
  rw [ringDarts_a_eq_drop_two P hcycle hsize]
  change ColSeq.trace (List.map k ((ringDarts P n).drop 2)) = et
  rw [List.map_drop]
  exact hdropTrace

/-- Converse semantic `A` branch: every coloring after the merge restricts
to a source coloring whose first two edge differences agree. -/
theorem ringTrace_a_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    {eta : ColSeq}
    (htrace : P.a.map.RingTrace (ringDarts P.a (n - 2)) eta) :
    ∃ e1 e2 et,
      e1 = e2 ∧
      P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) ∧
      eta = et := by
  rcases htrace.exists_coloring with ⟨ka, hka, hakt⟩
  let k := restrictAColor P ka
  let oldTrace := ColSeq.trace (P.map.colorsOn k (ringDarts P n))
  have hk : P.map.Coloring k := restrictAColor_coloring hka
  have hold : P.map.RingTrace (ringDarts P n) oldTrace := ⟨k, hk, rfl⟩
  have hlen : oldTrace.length = n := by
    simpa using Hypermap.RingTrace.length (G := P.map) hold
  cases hot : oldTrace with
  | nil => simp [hot] at hlen; omega
  | cons e1 rest =>
      cases hrest : rest with
      | nil => simp [hot, hrest] at hlen; omega
      | cons e2 et =>
          have hold' :
              P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) := by
            simpa [hot, hrest] using hold
          have hsource :
              ColSeq.trace (P.map.colorsOn k (ringDarts P n)) =
                e1 :: e2 :: et := by
            simp [oldTrace, hot, hrest]
          have hpairs := ringTrace_head_pair_of_eq
            (P := P) hsize k hsource
          have hmerge :
              k (P.map.node P.point) =
                k (P.map.face (P.map.edge P.point)) := by
            have hm := Hypermap.Coloring.eq_of_face_reachable
              (G := P.a.map) hka
              (Hypermap.extensionA_faceReachable_node_x0_face_edge_x0
                (G := P.map) P.point)
            simpa [k, restrictAColor] using hm.symm
          have heq : e1 = e2 := by
            rw [← hpairs.1, ← hpairs.2, hmerge, Color.add_comm]
          have hn : n = (n - 3) + 3 := by omega
          let tailColors : ColSeq :=
            P.map.colorsOn k
              ((List.range (n - 3)).map
                (fun i => iteratePerm P.map.node.symm (i + 2) P.point))
          have hcolors : P.map.colorsOn k (ringDarts P n) =
              k (P.map.node P.point) :: k P.point ::
                k (P.map.face (P.map.edge P.point)) :: tailColors := by
            rw [hn, ringDarts_succ_succ_succ]
            simp [Hypermap.colorsOn, tailColors]
          have hdropTrace :
              ColSeq.trace ((P.map.colorsOn k (ringDarts P n)).drop 2) = et := by
            rw [hcolors]
            change ColSeq.trace
              (k (P.map.face (P.map.edge P.point)) :: tailColors) = et
            rw [ColSeq.trace_drop_two_of_first_eq_third _ _ _ _ hmerge]
            rw [← hcolors, hsource]
            rfl
          have hout : eta = et := by
            calc
              eta = ColSeq.trace
                  (P.a.map.colorsOn ka (ringDarts P.a (n - 2))) := hakt.symm
              _ = ColSeq.trace
                  ((P.map.colorsOn k (ringDarts P n)).drop 2) := by
                rw [ringDarts_a_eq_drop_two P hcycle hsize]
                change ColSeq.trace (List.map ka ((ringDarts P n).drop 2)) = _
                rw [List.map_drop]
                rfl
              _ = et := hdropTrace
          exact ⟨e1, e2, et, heq, hold', hout⟩


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
