import FourColorTheorem.FourColor.Coloring.CFColorMap.PrimitiveExtensions
namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- The coloring on Coq `ecpK P`, obtained by applying the primitive `N`
coloring at `node point`. -/
def kColor
    (P : PointedHypermap) (k : P.map.Dart → Color) :
    P.k.map.Dart → Color :=
  Hypermap.extensionNColor P.map (P.map.node P.point) k

@[simp]
theorem kColor_old
    (P : PointedHypermap) (k : P.map.Dart → Color) (x : P.map.Dart) :
    kColor P k (P.kOld x) = k x :=
  rfl

/-- Coq `cpcolor1K_correct`, at the level of the one-step map coloring.  The
algorithm's unequal first two boundary trace entries are exactly the condition
which makes the fresh `K` edge properly colored. -/
theorem kColor_coloring
    {P : PointedHypermap} {k : P.map.Dart → Color}
    (hk : P.map.Coloring k)
    (hne :
      k (P.map.node P.point) + k P.point ≠
        k P.point + k (P.map.face (P.map.edge P.point))) :
    P.k.map.Coloring (kColor P k) := by
  have hlong : P.map.LongRingHead (P.map.node P.point) := by
    intro hshort
    have hperiod : P.map.node (P.map.node P.point) = P.point := by
      have hleft :
          P.map.face (P.map.edge (P.map.node P.point)) = P.point := by
        rw [Hypermap.face_edge_eq_node_symm]
        simp
      exact hshort ▸ hleft
    have hprev :
        P.map.face (P.map.edge P.point) = P.map.node P.point := by
      rw [Hypermap.face_edge_eq_node_symm]
      apply P.map.node.injective
      simpa using hperiod.symm
    apply hne
    rw [hprev, Color.add_comm (k P.point)]
  have hfresh :
      k (P.map.node P.point) ≠
        k (P.map.node.symm (P.map.node.symm (P.map.node P.point))) := by
    simp only [P.map.node.symm_apply_apply]
    intro heq
    apply hne
    rw [Hypermap.face_edge_eq_node_symm, heq,
      Color.add_comm (k P.point)]
  exact Hypermap.extensionNColor_coloring hk hlong hfresh

/-- A ring cycle of length at least three supplies exactly the long-corner
hypothesis used by Coq's `ecpK` construction at `node point`. -/
theorem longRingHead_node_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    P.map.LongRingHead (P.map.node P.point) := by
  unfold Hypermap.LongRingHead
  simpa using
    hcycle.avoids_node_node_point_before_last (k := 0) (by omega)

/-- The distinguished dart of `ecpK` is the old dart two positions beyond
the source ring head.  This is the pointer calculation hidden by Coq's final
`ecpR 1`. -/
theorem k_point_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    P.k.point = P.kOld (P.map.node.symm P.point) := by
  have hlong := longRingHead_node_of_ringCycle hcycle hsize
  unfold k
  rw [rotate_one_point]
  change Hypermap.ExtensionN.nodeInvFun P.map (P.map.node P.point)
      ExtDart.new = ExtDart.old (P.map.node.symm P.point)
  simp [Hypermap.ExtensionN.nodeInvFun, hlong]

@[simp]
theorem k_node_point (P : PointedHypermap) :
    P.k.map.node P.k.point = ExtDart.new := by
  unfold k
  rw [rotate_one_point]
  change
    Hypermap.ExtensionN.node P.map (P.map.node P.point)
      ((Hypermap.ExtensionN.node P.map
        (P.map.node P.point)).symm ExtDart.new) = ExtDart.new
  simp

/-- Backwards node iteration on `ecpK` is old-ring iteration with its first
two boundary darts omitted. -/
theorem k_iterate_node_symm_point_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    (i : Nat) (hi : i < n - 2) :
    iteratePerm P.k.map.node.symm i P.k.point =
      P.kOld (iteratePerm P.map.node.symm (i + 1) P.point) := by
  induction i with
  | zero =>
      simpa using k_point_of_ringCycle hcycle hsize
  | succ i ih =>
      have hi' : i < n - 2 := by omega
      have hpoint :
          iteratePerm P.map.node.symm (i + 1) P.point ≠ P.point :=
        hcycle.avoids_point_before_last_of_pos (k := i + 1)
          (by omega) (by omega)
      have hnodeNode :
          iteratePerm P.map.node.symm (i + 1) P.point ≠
            P.map.node (P.map.node P.point) :=
        hcycle.avoids_node_node_point_before_last (k := i + 1)
          (by omega)
      rw [iteratePerm_succ_right P.k.map.node.symm i P.k.point,
        ih hi']
      change
        Hypermap.ExtensionN.nodeInvFun P.map (P.map.node P.point)
            (ExtDart.old
              (iteratePerm P.map.node.symm (i + 1) P.point)) =
          ExtDart.old
            (iteratePerm P.map.node.symm (i + 1 + 1) P.point)
      simp only [Hypermap.ExtensionN.nodeInvFun]
      rw [if_neg (by
        simpa [Hypermap.face_edge_eq_node_symm] using hpoint)]
      rw [if_neg hnodeNode, iteratePerm_succ_right]
      rw [show i + 1 + 1 = (i + 1) + 1 by omega,
        iteratePerm_succ_right, iteratePerm_succ_right]

/-- Coq `cpring_ecpK`: `K` contracts the first two old boundary intervals,
so its ring is `new :: map old (drop 2 oldRing)`. -/
theorem ringDarts_k_of_ringCycle
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    ringDarts P.k (n - 2 + 1) =
      ExtDart.new :: ((ringDarts P n).drop 2).map P.kOld := by
  have hn : n = (n - 2) + 2 := by omega
  rw [ringDarts_succ, hn, drop_two_ringDarts_succ_succ]
  simp only [k_node_point, List.map_map, Nat.add_sub_cancel]
  apply congrArg (List.cons ExtDart.new)
  apply List.map_congr_left
  intro i hi
  exact k_iterate_node_symm_point_of_ringCycle hcycle hsize i
    (List.mem_range.mp hi)

/-- The K contraction preserves an exact simple ring cycle and shortens it by
one dart. -/
theorem ringCycle_k
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    RingCycle P.k (n - 2 + 1) := by
  have hpointNe :
      P.map.node (P.map.node P.point) ≠ P.point := by
    exact (hcycle.avoids_node_node_point_before_last (k := 0)
      (by omega)).symm
  have hlast :
      iteratePerm P.map.node.symm (n - 2) P.point =
        P.map.node (P.map.node P.point) := by
    have hp := hcycle.period
    unfold RingPeriod at hp
    have hn : n = (n - 1) + 1 := by omega
    rw [hn, iteratePerm_succ_right] at hp
    have hp' :
        iteratePerm P.map.node.symm (n - 1)
            (P.map.node P.point) =
          P.map.node (P.map.node P.point) := by
      apply P.map.node.symm.injective
      simpa using hp
    have hn' : n - 1 = (n - 2) + 1 := by omega
    rw [hn', iteratePerm_succ] at hp'
    simpa using hp'
  refine { pos := by omega, period := ?_, nodup := ?_ }
  · unfold RingPeriod
    have hsizeK : n - 2 + 1 = (n - 2) + 1 := rfl
    rw [hsizeK, iteratePerm_succ]
    rw [Equiv.symm_apply_apply]
    change iteratePerm P.k.map.node.symm (n - 2) P.k.point =
      P.k.map.node P.k.point
    have hpred : n - 2 = (n - 3) + 1 := by omega
    have hidx : n - 3 + 1 = n - 2 := by omega
    rw [hpred, iteratePerm_succ_right,
      k_iterate_node_symm_point_of_ringCycle hcycle hsize (n - 3)
        (by omega), hidx, hlast, k_node_point]
    change
      Hypermap.ExtensionN.nodeInvFun P.map (P.map.node P.point)
          (ExtDart.old (P.map.node (P.map.node P.point))) =
        ExtDart.new
    simp [Hypermap.ExtensionN.nodeInvFun,
      Hypermap.face_edge_eq_node_symm, hpointNe]
  · rw [ringDarts_k_of_ringCycle hcycle hsize]
    have hold : ((ringDarts P n).drop 2).Nodup :=
      List.Pairwise.drop (i := 2) hcycle.nodup
    have hmapped := hold.map (fun _ _ h => ExtDart.old_injective h)
    apply List.pairwise_cons.mpr
    constructor
    · intro a ha
      rcases List.mem_map.mp ha with ⟨x, _hx, rfl⟩
      exact (ExtDart.old_ne_new x).symm
    · exact hmapped

/-- Program-level Coq `cpring_ecpK`. -/
theorem cpRing_k_of_ringCycle
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 2 < CProg.ringSize cp) :
    cpRing (CpStep.k :: cp) =
      ExtDart.new :: ((cpRing cp).drop 2).map (cpmap cp).kOld := by
  simpa [cpRing, CProg.ringSize, cpmap_cons, step_k] using
    ringDarts_k_of_ringCycle hcycle hsize

theorem cpRingCycle_k
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 2 < CProg.ringSize cp) :
    cpRingCycle (CpStep.k :: cp) := by
  exact ringCycle_k hcycle hsize

/-- The exact color word on the contracted `K` ring. -/
theorem colorsOn_kColor_ringDarts
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    (k : P.map.Dart → Color) :
    P.k.map.colorsOn (kColor P k) (ringDarts P.k (n - 2 + 1)) =
      k (P.map.node P.point) ::
        (P.map.colorsOn k (ringDarts P n)).drop 2 := by
  rw [ringDarts_k_of_ringCycle hcycle hsize]
  change
    Hypermap.extensionNColor P.map (P.map.node P.point) k ExtDart.new ::
        P.k.map.colorsOn (kColor P k)
          (((ringDarts P n).drop 2).map P.kOld) = _
  apply congrArg₂ List.cons rfl
  calc
    P.k.map.colorsOn (kColor P k)
        (((ringDarts P n).drop 2).map P.kOld) =
      ((ringDarts P n).drop 2).map k :=
        Hypermap.colorsOn_map_of_apply _ _ _ _ (fun _ => rfl) _
    _ = (P.map.colorsOn k (ringDarts P n)).drop 2 := List.map_drop

/-- Trace equation in Coq `cpcolor1K_correct`: contracting the middle of the
first three face colors xors the first two source edge colors. -/
theorem trace_kColor_ringDarts_of_eq
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    (k : P.map.Dart → Color) {e1 e2 : Color} {et : ColSeq}
    (htrace :
      ColSeq.trace (P.map.colorsOn k (ringDarts P n)) =
        e1 :: e2 :: et) :
    ColSeq.trace
        (P.k.map.colorsOn (kColor P k)
          (ringDarts P.k (n - 2 + 1))) =
      (e1 + e2) :: et := by
  have hn : n = (n - 3) + 3 := by omega
  rw [colorsOn_kColor_ringDarts hcycle hsize]
  rw [hn, ringDarts_succ_succ_succ] at htrace ⊢
  let tail : ColSeq :=
    P.map.colorsOn k
      ((List.range (n - 3)).map
        (fun i => iteratePerm P.map.node.symm (i + 2) P.point))
  change ColSeq.trace
      (k (P.map.node P.point) :: k P.point ::
        k (P.map.face (P.map.edge P.point)) :: tail) =
      e1 :: e2 :: et at htrace
  have hheads := htrace
  rw [ColSeq.trace_cons] at hheads
  simp only [List.cons_append, ColSeq.pairSums_cons] at hheads
  have he1 : k (P.map.node P.point) + k P.point = e1 :=
    (List.cons.inj hheads).1
  have he2 :
      k P.point + k (P.map.face (P.map.edge P.point)) = e2 :=
    (List.cons.inj (List.cons.inj hheads).2).1
  change ColSeq.trace
      (k (P.map.node P.point) ::
        k (P.map.face (P.map.edge P.point)) :: tail) = _
  rw [ColSeq.trace_erase_middle
    (k (P.map.node P.point)) (k P.point)
      (k (P.map.face (P.map.edge P.point))) tail]
  rw [htrace]
  rw [he1, he2]
  simp

/-- The first two entries of a ring trace are the two edge differences at the
pointed corner. -/
theorem ringTrace_head_pair_of_eq
    {P : PointedHypermap} {n : Nat}
    (hsize : 2 < n) (k : P.map.Dart → Color)
    {e1 e2 : Color} {et : ColSeq}
    (htrace :
      ColSeq.trace (P.map.colorsOn k (ringDarts P n)) =
        e1 :: e2 :: et) :
    k (P.map.node P.point) + k P.point = e1 ∧
      k P.point + k (P.map.face (P.map.edge P.point)) = e2 := by
  have hn : n = (n - 3) + 3 := by omega
  rw [hn, ringDarts_succ_succ_succ] at htrace
  let tail : ColSeq :=
    P.map.colorsOn k
      ((List.range (n - 3)).map
        (fun i => iteratePerm P.map.node.symm (i + 2) P.point))
  change ColSeq.trace
      (k (P.map.node P.point) :: k P.point ::
        k (P.map.face (P.map.edge P.point)) :: tail) =
      e1 :: e2 :: et at htrace
  rw [ColSeq.trace_cons] at htrace
  simp only [List.cons_append, ColSeq.pairSums_cons] at htrace
  exact ⟨List.cons.inj htrace |>.1,
    List.cons.inj (List.cons.inj htrace |>.2) |>.1⟩

/-- Every first edge color of a ring trace with at least two boundary darts is
nonzero. -/
theorem ringTrace_head_ne_zero
    {P : PointedHypermap} {n : Nat} (hsize : 1 < n)
    {e : Color} {et : ColSeq}
    (htrace : P.map.RingTrace (ringDarts P n) (e :: et)) :
    e ≠ Color.zero := by
  rcases htrace.exists_coloring with ⟨k, hk, hkt⟩
  have hn : n = (n - 2) + 2 := by omega
  rw [hn, ringDarts_succ_succ] at hkt
  let tail : ColSeq :=
    P.map.colorsOn k
      ((List.range (n - 2)).map
        (fun i => iteratePerm P.map.node.symm (i + 1) P.point))
  change ColSeq.trace
      (k (P.map.node P.point) :: k P.point :: tail) = e :: et at hkt
  rw [ColSeq.trace_cons] at hkt
  simp only [List.cons_append, ColSeq.pairSums_cons] at hkt
  have he : k (P.map.node P.point) + k P.point = e :=
    List.cons.inj hkt |>.1
  have hne : k (P.map.node P.point) ≠ k P.point := by
    intro hsame
    apply Hypermap.Coloring.edge_ne (G := P.map) hk
      (P.map.node P.point)
    calc
      k (P.map.edge (P.map.node P.point)) =
          k (P.map.face (P.map.edge (P.map.node P.point))) :=
        (Hypermap.Coloring.face_eq (G := P.map) hk _).symm
      _ = k P.point := by
        rw [Hypermap.face_edge_eq_node_symm]
        simp
      _ = k (P.map.node P.point) := hsame.symm
  intro hzero
  apply hne
  apply (Color.add_eq_zero_iff_eq _ _).mp
  rw [he, hzero]

/-- Semantic `CpK` branch, exactly matching Coq's guarded trace contraction. -/
theorem ringTrace_cpRing_k_of_coloring
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 2 < CProg.ringSize cp)
    {k : (cpmap cp).map.Dart → Color}
    (hk : (cpmap cp).map.Coloring k)
    {e1 e2 : Color} {et : ColSeq}
    (hne : e1 ≠ e2)
    (htrace :
      ColSeq.trace ((cpmap cp).map.colorsOn k (cpRing cp)) =
        e1 :: e2 :: et) :
    (cpmap (CpStep.k :: cp)).map.RingTrace
      (cpRing (CpStep.k :: cp)) ((e1 + e2) :: et) := by
  let kk : (cpmap (CpStep.k :: cp)).map.Dart → Color :=
    kColor (cpmap cp) k
  have hpairs := ringTrace_head_pair_of_eq
    (P := cpmap cp) hsize k htrace
  have hkFresh :
      k ((cpmap cp).map.node (cpmap cp).point) + k (cpmap cp).point ≠
        k (cpmap cp).point +
          k ((cpmap cp).map.face
            ((cpmap cp).map.edge (cpmap cp).point)) := by
    rw [hpairs.1, hpairs.2]
    exact hne
  refine ⟨kk, ?_, ?_⟩
  · exact kColor_coloring hk hkFresh
  · apply Eq.symm
    change ColSeq.trace
        ((cpmap (CpStep.k :: cp)).map.colorsOn kk
          (ringDarts (cpmap cp).k
            (CProg.ringSize cp - 2 + 1))) = _
    exact trace_kColor_ringDarts_of_eq hcycle hsize k htrace

/-- Generic pointed-map form of semantic `CpK` soundness. -/
theorem ringTrace_k_of_ringTrace
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    {e1 e2 : Color} {et : ColSeq}
    (htrace :
      P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et))
    (hne : e1 ≠ e2) :
    P.k.map.RingTrace (ringDarts P.k (n - 2 + 1))
      ((e1 + e2) :: et) := by
  rcases htrace.exists_coloring with ⟨k, hk, hkt⟩
  have hpairs := ringTrace_head_pair_of_eq
    (P := P) hsize k hkt
  have hkFresh :
      k (P.map.node P.point) + k P.point ≠
        k P.point + k (P.map.face (P.map.edge P.point)) := by
    rw [hpairs.1, hpairs.2]
    exact hne
  let kk : P.k.map.Dart → Color := kColor P k
  refine ⟨kk, kColor_coloring hk hkFresh, ?_⟩
  apply Eq.symm
  exact trace_kColor_ringDarts_of_eq hcycle hsize k hkt

/-- Restrict an arbitrary coloring of `K` to old darts. -/
def restrictKColor
    (P : PointedHypermap) (kk : P.k.map.Dart → Color) :
    P.map.Dart → Color :=
  fun x => kk (P.kOld x)

theorem restrictKColor_coloring
    {P : PointedHypermap} {kk : P.k.map.Dart → Color}
    (hkk : P.k.map.Coloring kk) :
    P.map.Coloring (restrictKColor P kk) := by
  apply Hypermap.Coloring.pullback_of_edge_faceReachable hkk P.kOld
  · intro x
    change PermReachable P.k.map.face
      (P.k.map.edge (P.kOld x)) (P.k.map.edge (P.kOld x))
    exact PermReachable.refl P.k.map.face _
  · intro x
    exact P.kOld_faceReachable_of_faceReachable
      (PermReachable.forward P.map.face x)

/-- Every coloring of `K` is the canonical `extensionNColor` of its old-dart
restriction. -/
theorem kColor_restrict_eq
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    {kk : P.k.map.Dart → Color}
    (hkk : P.k.map.Coloring kk) :
    kColor P (restrictKColor P kk) = kk := by
  have hlong := longRingHead_node_of_ringCycle hcycle hsize
  have hnew :
      restrictKColor P kk (P.map.node P.point) = kk ExtDart.new := by
    have hface := Hypermap.Coloring.face_eq (G := P.k.map) hkk
      (ExtDart.new : P.k.map.Dart)
    simpa [restrictKColor] using hface
  have hnewEdge :
      restrictKColor P kk
          (P.map.node.symm
            (P.map.node.symm (P.map.node P.point))) =
        kk ExtDart.newEdge := by
    have hface := Hypermap.Coloring.face_eq (G := P.k.map) hkk
      (ExtDart.newEdge : P.k.map.Dart)
    change
      kk
          (Hypermap.ExtensionN.face P.map (P.map.node P.point)
            ExtDart.newEdge) =
        kk ExtDart.newEdge at hface
    have hfaceNewEdge :=
      Hypermap.ExtensionN.face_newEdge P.map (P.map.node P.point)
    rw [hfaceNewEdge, if_pos hlong] at hface
    simpa [restrictKColor, Hypermap.face_edge_eq_node_symm] using hface
  funext x
  cases x with
  | new => exact hnew
  | newEdge => exact hnewEdge
  | old x => rfl

/-- Converse semantic `K` branch: every K coloring comes from an old trace
whose first two entries are unequal, and contracts them by xor. -/
theorem ringTrace_k_elim
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n)
    {etk : ColSeq}
    (htrace :
      P.k.map.RingTrace (ringDarts P.k (n - 2 + 1)) etk) :
    ∃ e1 e2 et,
      e1 ≠ e2 ∧
      P.map.RingTrace (ringDarts P n) (e1 :: e2 :: et) ∧
      etk = (e1 + e2) :: et := by
  rcases htrace.exists_coloring with ⟨kk, hkk, hkkt⟩
  let k := restrictKColor P kk
  let oldTrace := ColSeq.trace (P.map.colorsOn k (ringDarts P n))
  have hk : P.map.Coloring k := restrictKColor_coloring hkk
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
          have hcanon := kColor_restrict_eq hcycle hsize hkk
          have hfresh := Hypermap.Coloring.edge_ne (G := P.k.map) hkk
            (ExtDart.new : P.k.map.Dart)
          rw [← hcanon] at hfresh
          change
            k (P.map.node.symm
                (P.map.node.symm (P.map.node P.point))) ≠
              k (P.map.node P.point) at hfresh
          simp only [P.map.node.symm_apply_apply] at hfresh
          have hne : e1 ≠ e2 := by
            intro heq
            have hraw :
                k (P.map.node P.point) + k P.point =
                  k P.point + k (P.map.face (P.map.edge P.point)) := by
              rw [hpairs.1, hpairs.2, heq]
            apply hfresh
            rw [Hypermap.face_edge_eq_node_symm] at hraw
            have hcancel := congrArg (fun z => z + k P.point) hraw
            have hac :
                k (P.map.node P.point) =
                  k (P.map.node.symm P.point) := by
              simpa [Color.add_assoc, Color.add_comm,
                Color.add_left_comm] using hcancel
            exact hac.symm
          refine ⟨e1, e2, et, hne, hold', ?_⟩
          calc
            etk = ColSeq.trace
                (P.k.map.colorsOn kk
                  (ringDarts P.k (n - 2 + 1))) := hkkt.symm
            _ = ColSeq.trace
                (P.k.map.colorsOn (kColor P k)
                  (ringDarts P.k (n - 2 + 1))) := by rw [hcanon]
            _ = (e1 + e2) :: et :=
              trace_kColor_ringDarts_of_eq hcycle hsize k hsource


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
