import FourColorTheorem.FourColor.Reducibility.ProgramMap.Steps

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- A size-indexed semantic ring list for a pointed construction map.

For `cpmap cp` this is used at size `CProg.ringSize cp`; it starts with
`node point`, then moves backwards around the node orbit.  This matches the
orientation of Coq's `cpring`, whose nontrivial rings begin
`node x :: x :: ...`. -/
def ringDarts (P : PointedHypermap) (n : Nat) : List P.map.Dart :=
  (List.range n).map
    (fun i => iteratePerm P.map.node.symm i (P.map.node P.point))

@[simp]
theorem length_ringDarts (P : PointedHypermap) (n : Nat) :
    (ringDarts P n).length = n := by
  simp [ringDarts]

@[simp]
theorem ringDarts_zero (P : PointedHypermap) :
    ringDarts P 0 = [] := by
  rfl

theorem ringDarts_succ (P : PointedHypermap) (n : Nat) :
    ringDarts P (n + 1) =
      P.map.node P.point ::
        (List.range n).map
          (fun i => iteratePerm P.map.node.symm i P.point) := by
  unfold ringDarts
  rw [List.range_succ_eq_map]
  simp [iteratePerm_succ]

theorem ringDarts_succ_succ (P : PointedHypermap) (n : Nat) :
    ringDarts P (n + 2) =
      P.map.node P.point :: P.point ::
        (List.range n).map
          (fun i => iteratePerm P.map.node.symm (i + 1) P.point) := by
  rw [show n + 2 = (n + 1) + 1 by omega, ringDarts_succ]
  rw [List.range_succ_eq_map]
  simp [iteratePerm_succ]

theorem ringDarts_succ_succ_succ (P : PointedHypermap) (n : Nat) :
    ringDarts P (n + 3) =
      P.map.node P.point :: P.point ::
        P.map.face (P.map.edge P.point) ::
          (List.range n).map
            (fun i => iteratePerm P.map.node.symm (i + 2) P.point) := by
  rw [show n + 3 = (n + 1) + 2 by omega, ringDarts_succ_succ]
  rw [List.range_succ_eq_map]
  simp [iteratePerm_succ, Hypermap.face_edge_eq_node_symm]

theorem drop_one_ringDarts_succ (P : PointedHypermap) (n : Nat) :
    (ringDarts P (n + 1)).drop 1 =
      (List.range n).map
        (fun i => iteratePerm P.map.node.symm i P.point) := by
  rw [ringDarts_succ]
  rfl

theorem drop_two_ringDarts_succ_succ (P : PointedHypermap) (n : Nat) :
    (ringDarts P (n + 2)).drop 2 =
      (List.range n).map
        (fun i => iteratePerm P.map.node.symm (i + 1) P.point) := by
  rw [ringDarts_succ_succ]
  rfl

theorem drop_two_ringDarts_y_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (n : Nat)
    (hnode : ∀ k : Nat, k + 1 < n →
      iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point)
    (hnodeNode : ∀ k : Nat, k + 1 < n →
      iteratePerm P.map.node.symm k P.point ≠
        P.map.node (P.map.node P.point)) :
    (ringDarts P.y (n + 2)).drop 2 =
      ((ringDarts P (n + 1)).drop 1).map P.yOld := by
  rw [drop_two_ringDarts_succ_succ, drop_one_ringDarts_succ]
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  exact y_iterate_node_symm_succ_point_of_avoids_heads P hproper i
    (fun k hk => hnode k (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) hi'))
    (fun k hk => hnodeNode k
      (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) hi'))

theorem drop_two_ringDarts_h_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    (n : Nat)
    (hpoint : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠ P.point)
    (hnode : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point)
    (hnodeNode : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠
        P.map.node (P.map.node P.point)) :
    (ringDarts P.h (n + 2)).drop 2 =
      ((ringDarts P (n + 2)).drop 2).map P.hOld := by
  rw [drop_two_ringDarts_succ_succ, drop_two_ringDarts_succ_succ]
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  exact h_iterate_node_symm_succ_point_of_avoids_heads P hproper hlong i
    (fun k hkpos hk => hpoint k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))
    (fun k hkpos hk => hnode k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))
    (fun k hkpos hk => hnodeNode k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))

theorem ringDarts_y_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (n : Nat)
    (hnode : ∀ k : Nat, k + 1 < n →
      iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point)
    (hnodeNode : ∀ k : Nat, k + 1 < n →
      iteratePerm P.map.node.symm k P.point ≠
        P.map.node (P.map.node P.point)) :
    ringDarts P.y (n + 2) =
      P.y.map.node P.y.point :: P.y.point ::
        ((ringDarts P (n + 1)).drop 1).map P.yOld := by
  rw [ringDarts_succ_succ, drop_one_ringDarts_succ]
  simp only [List.map_map]
  apply congrArg (fun tail =>
    P.y.map.node P.y.point :: P.y.point :: tail)
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  exact y_iterate_node_symm_succ_point_of_avoids_heads P hproper i
    (fun k hk => hnode k (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) hi'))
    (fun k hk => hnodeNode k
      (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) hi'))

theorem ringDarts_h_of_avoids_heads
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    (n : Nat)
    (hpoint : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠ P.point)
    (hnode : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point)
    (hnodeNode : ∀ k : Nat, 0 < k → k < n →
      iteratePerm P.map.node.symm k P.point ≠
        P.map.node (P.map.node P.point)) :
    ringDarts P.h (n + 2) =
      P.h.map.node P.h.point :: P.h.point ::
        ((ringDarts P (n + 2)).drop 2).map P.hOld := by
  rw [ringDarts_succ_succ, drop_two_ringDarts_succ_succ]
  simp only [List.map_map]
  apply congrArg (fun tail =>
    P.h.map.node P.h.point :: P.h.point :: tail)
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  exact h_iterate_node_symm_succ_point_of_avoids_heads P hproper hlong i
    (fun k hkpos hk => hpoint k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))
    (fun k hkpos hk => hnode k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))
    (fun k hkpos hk => hnodeNode k hkpos
      (Nat.lt_of_lt_of_le hk (Nat.succ_le_of_lt hi')))

/-- The advertised ring length closes the backwards node orbit from the first
ring representative `node point`. -/
def RingPeriod (P : PointedHypermap) (n : Nat) : Prop :=
  iteratePerm P.map.node.symm n (P.map.node P.point) = P.map.node P.point

theorem RingPeriod.point_period
    {P : PointedHypermap} {n : Nat}
    (hperiod : RingPeriod P n) :
    iteratePerm P.map.node.symm n P.point = P.point := by
  apply P.map.node.injective
  rw [apply_iteratePerm_symm P.map.node n P.point]
  exact hperiod

/-- Exact finite ring invariant: the advertised length closes the backwards
node orbit and the listed representatives do not repeat before closure. -/
structure RingCycle (P : PointedHypermap) (n : Nat) : Prop where
  pos : 0 < n
  period : RingPeriod P n
  nodup : (ringDarts P n).Nodup

/-- The actual node orbit of every pointed hypermap is an exact ring cycle.
This is the Lean counterpart of Coq's dynamically sized `cpring`. -/
theorem nodeOrder_ringCycle (P : PointedHypermap) :
    RingCycle P P.nodeOrder where
  pos := P.nodeOrder_pos
  period := P.nodeOrder_period
  nodup := by
    unfold ringDarts
    apply List.Nodup.map_on
    · intro i hi j hj hij
      have hi' : i < P.nodeOrder := List.mem_range.mp hi
      have hj' : j < P.nodeOrder := List.mem_range.mp hj
      exact
        (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
          (f := (P.map.node.symm : P.map.Dart → P.map.Dart))
          (x := P.map.node P.point) hi' hj').mp (by
            simpa [iteratePerm_eq_iterate] using hij)
    · exact List.nodup_range

theorem ringDarts_isChain (P : PointedHypermap) (n : Nat) :
    List.IsChain (fun a b => P.map.node.symm a = b) (ringDarts P n) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [ringDarts, List.length_map, List.length_range] at hi ⊢
  simp only [List.getElem_map, List.getElem_range]
  exact (iteratePerm_succ_right P.map.node.symm i
    (P.map.node P.point)).symm

theorem RingCycle.one_lt_of_properRingHead
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hproper : P.ProperRingHead) :
    1 < n := by
  by_contra hn
  have hpos := hcycle.pos
  have hnOne : n = 1 := by omega
  subst n
  have hperiod := hcycle.period
  simp [RingPeriod, iteratePerm_succ] at hperiod
  exact hproper hperiod

theorem RingCycle.face_edge_eq_node_of_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    P.map.face (P.map.edge P.point) = P.map.node P.point := by
  subst n
  rw [Hypermap.face_edge_eq_node_symm]
  have hperiod := hcycle.period
  simp only [RingPeriod, iteratePerm_succ, iteratePerm_zero,
    P.map.node.symm_apply_apply] at hperiod
  exact hperiod

/-- On a two-dart ring, Coq's `ecpA` node permutation is unchanged. -/
theorem a_node_eq_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    P.a.map.node = P.map.node := by
  have hface := hcycle.face_edge_eq_node_of_eq_two hsize
  have hnodeNode : P.map.node (P.map.node P.point) = P.point := by
    simpa using (congrArg P.map.node hface).symm
  ext x
  change Hypermap.extensionANode P.map P.point x = P.map.node x
  simp [Hypermap.extensionANode_apply, hnodeNode]

/-- On a two-dart ring, Coq's `ecpA` edge permutation is unchanged. -/
theorem a_edge_eq_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    P.a.map.edge = P.map.edge := by
  classical
  have hface := hcycle.face_edge_eq_node_of_eq_two hsize
  have hnodeNode : P.map.node (P.map.node P.point) = P.point := by
    simpa using (congrArg P.map.node hface).symm
  by_cases hreach :
      PermReachable P.map.face (P.map.edge P.point)
        (P.map.node P.point)
  · change Hypermap.extensionAEdge P.map P.point = P.map.edge
    simp [Hypermap.extensionAEdge, hreach, hnodeNode]
  · change Hypermap.extensionAEdge P.map P.point = P.map.edge
    simp [Hypermap.extensionAEdge, hreach]

/-- On a two-dart ring, Coq's `ecpA` face permutation is unchanged. -/
theorem a_face_eq_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    P.a.map.face = P.map.face := by
  have hedge := a_edge_eq_of_ringCycle_eq_two hcycle hsize
  have hnode := a_node_eq_of_ringCycle_eq_two hcycle hsize
  have hedgeRaw :
      Hypermap.extensionAEdge P.map P.point = P.map.edge := by
    simpa using hedge
  have hnodeRaw :
      Hypermap.extensionANode P.map P.point = P.map.node := by
    simpa using hnode
  ext x
  change Hypermap.extensionAFace P.map P.point x = P.map.face x
  unfold Hypermap.extensionAFace
  rw [hedgeRaw, hnodeRaw]
  simpa [Equiv.trans_apply] using
    (Hypermap.face_edge_eq_node_symm
      (G := P.map) (P.map.edge.symm x)).symm

/-- On a two-dart ring, the pointer chosen by Coq's `ecpA` is unchanged. -/
theorem a_point_eq_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    P.a.point = P.point := by
  have hedge := a_edge_eq_of_ringCycle_eq_two hcycle hsize
  have hface := a_face_eq_of_ringCycle_eq_two hcycle hsize
  have hperiod := hcycle.period.point_period
  subst n
  change P.a.map.face
      (P.a.map.edge (P.map.face (P.map.edge P.point))) = P.point
  rw [hface, hedge]
  calc
    P.map.face (P.map.edge (P.map.face (P.map.edge P.point))) =
        P.map.node.symm (P.map.face (P.map.edge P.point)) :=
      Hypermap.face_edge_eq_node_symm
        (G := P.map) (P.map.face (P.map.edge P.point))
    _ = P.map.node.symm (P.map.node.symm P.point) := by
      rw [Hypermap.face_edge_eq_node_symm]
    _ = P.point := by
      simpa only [RingPeriod, iteratePerm_succ, iteratePerm_zero] using hperiod

/-- Exact short branch of Coq `cpring_ecpA`: a two-dart ring is retained. -/
theorem ringDarts_a_eq_of_ringCycle_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    ringDarts P.a 2 = ringDarts P 2 := by
  have hnode := a_node_eq_of_ringCycle_eq_two hcycle hsize
  have hpoint := a_point_eq_of_ringCycle_eq_two hcycle hsize
  have hnodeRaw : P.a.map.node = P.map.node := hnode
  have hpointRaw : P.a.point = P.point := hpoint
  unfold ringDarts
  rw [hnodeRaw, hpointRaw]
  rfl

/-- The retained two-dart `A` ring is again an exact ring cycle. -/
theorem ringCycle_a_of_eq_two
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : n = 2) :
    RingCycle P.a 2 := by
  subst n
  have hnode := a_node_eq_of_ringCycle_eq_two hcycle rfl
  have hpoint := a_point_eq_of_ringCycle_eq_two hcycle rfl
  have hdarts := ringDarts_a_eq_of_ringCycle_eq_two hcycle rfl
  refine ⟨by decide, ?_, ?_⟩
  · unfold RingPeriod
    rw [hnode, hpoint]
    exact hcycle.period
  · simpa [hdarts] using hcycle.nodup

theorem RingCycle.isChain_append_head
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) :
    List.IsChain (fun a b => P.map.node.symm a = b)
      (ringDarts P n ++ [P.map.node P.point]) := by
  apply (ringDarts_isChain P n).append (.singleton _)
  have hlast :
      (ringDarts P n).getLast? =
        some (iteratePerm P.map.node.symm (n - 1)
          (P.map.node P.point)) := by
    rw [ringDarts, List.getLast?_map, List.getLast?_range]
    simp [Nat.ne_of_gt hcycle.pos]
  intro x hx y hy
  rw [hlast] at hx
  simp only [Option.mem_some_iff] at hx
  simp only [List.head?_singleton, Option.mem_some_iff] at hy
  subst x
  subst y
  rw [← iteratePerm_succ_right]
  have hpos : 0 < n := hcycle.pos
  have hindex : n - 1 + 1 = n := by omega
  rw [hindex]
  exact hcycle.period

theorem RingCycle.nodeOrder_eq
    {P : PointedHypermap} {n : Nat} (hP : RingCycle P n) :
    P.nodeOrder = n := by
  let q := P.nodeOrder
  have hqpos : 0 < q := P.nodeOrder_pos
  have hqperiod :
      iteratePerm P.map.node.symm q (P.map.node P.point) =
        P.map.node P.point := by
    rw [iteratePerm_eq_iterate]
    exact Function.iterate_minimalPeriod
  have hqle : q ≤ n := by
    have hnperiod : Function.IsPeriodicPt
        (P.map.node.symm : P.map.Dart → P.map.Dart) n
        (P.map.node P.point) := by
      change ((P.map.node.symm : P.map.Dart → P.map.Dart)^[n])
        (P.map.node P.point) = P.map.node P.point
      rw [← iteratePerm_eq_iterate]
      exact hP.period
    exact Function.IsPeriodicPt.minimalPeriod_le hP.pos hnperiod
  apply Nat.le_antisymm hqle
  by_contra hnot
  have hqlt : q < n := Nat.lt_of_not_ge hnot
  let L := ringDarts P n
  have hqidx : q < L.length := by simpa [L, ringDarts] using hqlt
  have h0idx : 0 < L.length := by simp [L, ringDarts, hP.pos]
  have heq : L[q] = L[0] := by
    simp [L, ringDarts, hqperiod]
  have hqzero := (List.Nodup.getElem_inj_iff hP.nodup
    (i := q) (j := 0) (hi := hqidx) (hj := h0idx)).1 heq
  omega

private theorem iteratePerm_symm_eq_iteratePerm_sub_of_period
    {α : Type u} (σ : Equiv.Perm α) {x : α} {m n : Nat}
    (hn : n ≤ m) (hperiod : iteratePerm σ m x = x) :
    iteratePerm σ.symm n x = iteratePerm σ (m - n) x := by
  simpa only [iteratePerm_eq_iterate] using
    Equiv.symm_iterate_eq_iterate_sub_of_period σ hn
      (by simpa only [iteratePerm_eq_iterate] using hperiod)

theorem RingCycle.node_period
    {P : PointedHypermap} {n : Nat} (hP : RingCycle P n) :
    iteratePerm P.map.node n P.point = P.point := by
  have hinv : iteratePerm P.map.node.symm n P.point = P.point :=
    hP.period.point_period
  simp only [iteratePerm_eq_iterate] at hinv ⊢
  calc
    (P.map.node : P.map.Dart → P.map.Dart)^[n] P.point =
        (P.map.node : P.map.Dart → P.map.Dart)^[n]
          ((P.map.node.symm : P.map.Dart → P.map.Dart)^[n] P.point) := by
      rw [hinv]
    _ = P.point := Equiv.iterate_apply_symm_iterate_self P.map.node n P.point

theorem rotate_point_eq_iteratePerm_symm_of_lt
    {P : PointedHypermap} {n r : Nat}
    (hP : RingCycle P n) (hr : r < n) :
    (P.rotate r).point = iteratePerm P.map.node.symm r P.point := by
  rw [rotate_point, hP.nodeOrder_eq]
  exact (iteratePerm_symm_eq_iteratePerm_sub_of_period P.map.node
    (Nat.le_of_lt hr) hP.node_period).symm

theorem rotate_ringDarts_eq_rotateLeft_of_ringCycle
    (P : PointedHypermap) (r n : Nat) (hP : RingCycle P n) :
    ringDarts (P.rotate r) n = CProg.rotateLeft r (ringDarts P n) := by
  by_cases hr : r < n
  · have hpoint := rotate_point_eq_iteratePerm_symm_of_lt hP hr
    have hshift :
        ringDarts (P.rotate r) n =
          (List.range n).map
            (fun i => iteratePerm P.map.node.symm (r + i)
              (P.map.node P.point)) := by
      unfold ringDarts
      apply List.map_congr_left
      intro i _hi
      change iteratePerm P.map.node.symm i
          (P.map.node (P.rotate r).point) =
        iteratePerm P.map.node.symm (r + i) (P.map.node P.point)
      rw [hpoint, apply_iteratePerm_symm P.map.node r P.point]
      exact (iteratePerm_add_right P.map.node.symm r i
        (P.map.node P.point)).symm
    rw [hshift]
    change
      (List.range n).map
          (fun i => iteratePerm P.map.node.symm (r + i)
            (P.map.node P.point)) =
        CProg.rotateLeft r
          ((List.range n).map
            (fun i => iteratePerm P.map.node.symm i
              (P.map.node P.point)))
    exact CProg.map_range_shift_eq_rotateLeft_of_mod_period_of_lt
      (fun i => iteratePerm P.map.node.symm i (P.map.node P.point)) hr
      (fun i => iteratePerm_mod_eq_of_period P.map.node.symm hP.period)
  · have hnr : n ≤ r := Nat.le_of_not_gt hr
    have horder : P.nodeOrder ≤ r := by rw [hP.nodeOrder_eq]; exact hnr
    rw [CProg.rotateLeft_oversize (by simpa [ringDarts] using hnr)]
    cases P with
    | mk G p =>
        simp [ringDarts, rotate, Nat.sub_eq_zero_of_le horder]
        intro _a _ha
        rfl

theorem RingPeriod.node_mem_ringDarts
    {P : PointedHypermap} {n : Nat}
    (hperiod : RingPeriod P n)
    (hpos : 0 < n)
    {x : P.map.Dart}
    (hx : x ∈ ringDarts P n) :
    P.map.node x ∈ ringDarts P n := by
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  have hiN : i < n := List.mem_range.mp hi
  cases i with
  | zero =>
      have hn : n = (n - 1) + 1 := by omega
      have hp := hperiod
      unfold RingPeriod at hp
      rw [hn, iteratePerm_succ_right] at hp
      have hlast :
          iteratePerm P.map.node.symm (n - 1) (P.map.node P.point) =
            P.map.node (P.map.node P.point) := by
        apply P.map.node.symm.injective
        simpa using hp
      exact List.mem_map.mpr
        ⟨n - 1, List.mem_range.mpr (by omega), hlast⟩
  | succ i =>
      exact List.mem_map.mpr
        ⟨i, List.mem_range.mpr (by omega), by
          rw [iteratePerm_succ_right]
          simp⟩

theorem RingPeriod.node_symm_mem_ringDarts
    {P : PointedHypermap} {n : Nat}
    (hperiod : RingPeriod P n)
    (hpos : 0 < n)
    {x : P.map.Dart}
    (hx : x ∈ ringDarts P n) :
    P.map.node.symm x ∈ ringDarts P n := by
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  have hiN : i < n := List.mem_range.mp hi
  by_cases hnext : i + 1 < n
  · exact List.mem_map.mpr
      ⟨i + 1, List.mem_range.mpr hnext, by
        rw [iteratePerm_succ_right]⟩
  · have hin : i + 1 = n := by omega
    have hp := hperiod
    unfold RingPeriod at hp
    rw [← hin, iteratePerm_succ_right] at hp
    exact List.mem_map.mpr
      ⟨0, List.mem_range.mpr hpos, by simpa using hp.symm⟩

theorem RingCycle.mem_ringDarts_of_onRing
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n)
    (hpos : 0 < n)
    {x : P.map.Dart}
    (hx : P.OnRing x) :
    x ∈ ringDarts P n := by
  have hstart : P.map.node P.point ∈ ringDarts P n :=
    List.mem_map.mpr
      ⟨0, List.mem_range.mpr hpos, by simp⟩
  have hpoint : P.point ∈ ringDarts P n := by
    simpa using hcycle.period.node_symm_mem_ringDarts hpos hstart
  induction hx with
  | refl => exact hpoint
  | @tail b c _hpb hbc ih =>
      cases hbc with
      | forward => exact hcycle.period.node_mem_ringDarts hpos ih
      | backward => exact hcycle.period.node_symm_mem_ringDarts hpos ih

theorem RingCycle.avoids_node_point_before_last
    {P : PointedHypermap} {n k : Nat}
    (hP : RingCycle P n)
    (hk : k < n - 1) :
    iteratePerm P.map.node.symm k P.point ≠ P.map.node P.point := by
  have hn : 0 < n := by omega
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  have hnodup := hP.nodup
  rw [ringDarts_succ] at hnodup
  have hnot :
      P.map.node P.point ∉
        (List.range m).map
          (fun i => iteratePerm P.map.node.symm i P.point) := by
    have hhead :
        (∀ i < m,
          ¬ iteratePerm P.map.node.symm i P.point =
            P.map.node P.point) ∧
          ((List.range m).map
            (fun i => iteratePerm P.map.node.symm i P.point)).Nodup := by
      simpa [List.nodup_cons] using hnodup
    intro hmem
    rcases List.mem_map.mp hmem with ⟨i, hi, heq⟩
    exact hhead.1 i (List.mem_range.mp hi) heq
  have hk' : k < m := by
    simpa using hk
  have hmem :
      iteratePerm P.map.node.symm k P.point ∈
        (List.range m).map
          (fun i => iteratePerm P.map.node.symm i P.point) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩
  intro h
  exact hnot (by simpa [h] using hmem)

/-- A ring cycle of length greater than two witnesses Coq's `long_cpring`
hypothesis. -/
theorem ringCycle_longRingHead_of_two_lt
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    P.LongRingHead := by
  unfold LongRingHead Hypermap.LongRingHead
  rw [Hypermap.face_edge_eq_node_symm]
  simpa [iteratePerm_succ] using
    hcycle.avoids_node_point_before_last (k := 1) (by omega)

theorem RingCycle.avoids_point_before_last_of_pos
    {P : PointedHypermap} {n k : Nat}
    (hP : RingCycle P n)
    (hkpos : 0 < k)
    (hk : k < n - 1) :
    iteratePerm P.map.node.symm k P.point ≠ P.point := by
  have hn : 0 < n := by omega
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  have hnodup := hP.nodup
  rw [ringDarts_succ] at hnodup
  have htail :
      ((List.range m).map
        (fun i => iteratePerm P.map.node.symm i P.point)).Nodup := by
    have hhead :
        (∀ i < m,
          ¬ iteratePerm P.map.node.symm i P.point =
            P.map.node P.point) ∧
          ((List.range m).map
            (fun i => iteratePerm P.map.node.symm i P.point)).Nodup := by
      simpa [List.nodup_cons] using hnodup
    exact hhead.2
  let L : List P.map.Dart :=
    (List.range m).map
      (fun i => iteratePerm P.map.node.symm i P.point)
  have hk' : k < m := by
    simpa using hk
  have h0 : 0 < L.length := by
    simp [L]
    omega
  have hki : k < L.length := by
    simpa [L] using hk'
  have hget :
      L[k] = iteratePerm P.map.node.symm k P.point := by
    simp [L]
  have hget0 : L[0] = P.point := by
    simp [L]
  intro hEq
  have hidx : k = 0 := by
    have heqGet : L[k] = L[0] := by
      simpa [hget, hget0] using hEq
    exact (List.Nodup.getElem_inj_iff
      (by simpa [L] using htail)
      (i := k) (j := 0) (hi := hki) (hj := h0)).1 heqGet
  omega

theorem RingCycle.avoids_node_node_point_before_last
    {P : PointedHypermap} {n k : Nat}
    (hP : RingCycle P n)
    (hk : k + 1 < n - 1) :
    iteratePerm P.map.node.symm k P.point ≠
      P.map.node (P.map.node P.point) := by
  have hn : 0 < n := by omega
  let L : List P.map.Dart := ringDarts P n
  have hi : k + 1 < L.length := by
    simp [L, ringDarts]
    omega
  have hj : n - 1 < L.length := by
    simp [L, ringDarts]
    omega
  have hperiodN := hP.period
  unfold RingPeriod at hperiodN
  have hnEq : n = (n - 1) + 1 := by
    omega
  rw [hnEq, iteratePerm_succ_right] at hperiodN
  have hlastval :
      iteratePerm P.map.node.symm (n - 1) (P.map.node P.point) =
        P.map.node (P.map.node P.point) := by
    simpa using congrArg P.map.node hperiodN
  have hgeti : L[k + 1] = iteratePerm P.map.node.symm k P.point := by
    change (((List.range n).map
      (fun i => iteratePerm P.map.node.symm i (P.map.node P.point)))[k + 1]) =
      iteratePerm P.map.node.symm k P.point
    rw [List.getElem_map]
    simp [iteratePerm_succ]
  have hgetj : L[n - 1] = P.map.node (P.map.node P.point) := by
    change (((List.range n).map
      (fun i => iteratePerm P.map.node.symm i (P.map.node P.point)))[n - 1]) =
      P.map.node (P.map.node P.point)
    rw [List.getElem_map]
    simp [hlastval]
  intro hEq
  have hidx : k + 1 = n - 1 := by
    have heqGet : L[k + 1] = L[n - 1] := by
      simpa [hgeti, hgetj] using hEq
    exact (List.Nodup.getElem_inj_iff hP.nodup
      (i := k + 1) (j := n - 1) (hi := hi) (hj := hj)).1 heqGet
  omega

/-- Up to the shortened ring length, inverse-node iteration in `ecpA` is
source iteration shifted past the two merged ring darts.  This is the
indexwise core of Coq `cpring_ecpA`. -/
theorem a_iterate_node_symm_eq
    (P : PointedHypermap) {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    ∀ i : Nat, i < n - 2 →
      iteratePerm P.a.map.node.symm i (P.a.map.node P.a.point) =
        iteratePerm P.map.node.symm (i + 1) P.point := by
  intro i hi
  induction i with
  | zero =>
      rw [iteratePerm_zero, a_node_point_eq_face_edge]
      simp [iteratePerm_succ, Hypermap.face_edge_eq_node_symm]
  | succ i ih =>
      have hi' : i < n - 2 := by omega
      have ih' := ih hi'
      calc
        iteratePerm P.a.map.node.symm (i + 1)
            (P.a.map.node P.a.point) =
            P.a.map.node.symm
              (iteratePerm P.a.map.node.symm i
                (P.a.map.node P.a.point)) :=
          iteratePerm_succ_right P.a.map.node.symm i _
        _ = P.a.map.node.symm
              (iteratePerm P.map.node.symm (i + 1) P.point) := by
          exact congrArg P.a.map.node.symm ih'
        _ = P.map.node.symm
              (iteratePerm P.map.node.symm (i + 1) P.point) := by
          exact P.a_node_symm_apply_of_ne
            (hcycle.avoids_point_before_last_of_pos
              (k := i + 1) (by omega) (by omega))
            (hcycle.avoids_node_node_point_before_last
              (k := i + 1) (by omega))
        _ = iteratePerm P.map.node.symm (i + 1 + 1) P.point :=
          (iteratePerm_succ_right P.map.node.symm (i + 1) _).symm

/-- Coq `cpring_ecpA` on an exact semantic ring: the A merge removes the
first two source boundary darts. -/
theorem ringDarts_a_eq_drop_two
    (P : PointedHypermap) {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    ringDarts P.a (n - 2) = (ringDarts P n).drop 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
  rw [show 2 + m - 2 = m by omega]
  rw [show 2 + m = m + 2 by omega, drop_two_ringDarts_succ_succ]
  unfold ringDarts
  apply List.map_congr_left
  intro i hi
  have hi' : i < m := List.mem_range.mp hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    P.a_iterate_node_symm_eq hcycle hsize i (by omega)

/-- The `A` merge preserves the exact ring cycle while deleting its first two
boundary darts. -/
theorem ringCycle_a
    {P : PointedHypermap} {n : Nat}
    (hcycle : RingCycle P n) (hsize : 2 < n) :
    RingCycle P.a (n - 2) := by
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
    have hn : n - 2 = (n - 3) + 1 := by omega
    rw [hn, iteratePerm_succ_right]
    rw [P.a_iterate_node_symm_eq hcycle hsize (n - 3) (by omega)]
    rw [show n - 3 + 1 = n - 2 by omega, hlast]
    change (Hypermap.extensionA P.map P.point).node.symm
        (P.map.node (P.map.node P.point)) = P.a.map.node P.a.point
    rw [Hypermap.extensionA_node_symm_node_node]
    rw [P.a_node_point_eq_face_edge, Hypermap.face_edge_eq_node_symm]
  · rw [ringDarts_a_eq_drop_two P hcycle hsize]
    exact hcycle.nodup.drop

theorem base_ringPeriod :
    RingPeriod base (CProg.ringSize []) := by
  rfl

theorem base_ringCycle :
    RingCycle base (CProg.ringSize []) where
  pos := by decide
  period := base_ringPeriod
  nodup := by decide

theorem rotate_ringPeriod
    {P : PointedHypermap} {n r : Nat}
    (hP : RingPeriod P n) :
    RingPeriod (P.rotate r) n := by
  unfold RingPeriod at hP ⊢
  let d := P.nodeOrder - r
  change iteratePerm P.map.node.symm n
      (P.map.node (iteratePerm P.map.node d P.point)) =
    P.map.node (iteratePerm P.map.node d P.point)
  rw [iteratePerm_apply_comm P.map.node d P.point,
    iteratePerm_symm_iteratePerm_comm P.map.node n d,
    hP]

theorem rotate_ringCycle
    {P : PointedHypermap} {n r : Nat}
    (hP : RingCycle P n) :
    RingCycle (P.rotate r) n where
  pos := hP.pos
  period := rotate_ringPeriod (r := r) hP.period
  nodup := by
    rw [rotate_ringDarts_eq_rotateLeft_of_ringCycle P r n hP]
    change (CProg.rotateLeft r (ringDarts P n)).Nodup
    exact (CProg.nodup_rotateLeft r (ringDarts P n)).2 hP.nodup

theorem reverseRotate_ringPeriod
    {P : PointedHypermap} {n : Nat}
    (hP : RingPeriod P n) :
    RingPeriod P.reverseRotate n := by
  unfold RingPeriod at hP ⊢
  change iteratePerm P.map.node.symm n (P.map.node (P.map.node P.point)) =
    P.map.node (P.map.node P.point)
  calc
    iteratePerm P.map.node.symm n (P.map.node (P.map.node P.point)) =
        P.map.node (iteratePerm P.map.node.symm n (P.map.node P.point)) := by
        exact (apply_iteratePerm_symm P.map.node n
          (P.map.node P.point)).symm
    _ = P.map.node (P.map.node P.point) := by
        rw [hP]


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
