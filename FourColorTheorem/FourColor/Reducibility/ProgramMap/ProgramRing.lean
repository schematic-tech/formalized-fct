import FourColorTheorem.FourColor.Reducibility.ProgramMap.RingCycle

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
/-- Semantic ring representatives of a construction program, sized by the
syntax recurrence.  This is the Lean-side entry point for Coq `cpring
(cpmap cp)` while the orbit-size theorem is being ported. -/
noncomputable def cpRing (cp : CProg) : List (cpmap cp).map.Dart :=
  ringDarts (cpmap cp) (CProg.ringSize cp)

theorem cpRing_eq_nodePoint_cons_drop_one (cp : CProg) :
    cpRing cp =
      (cpmap cp).map.node (cpmap cp).point :: (cpRing cp).drop 1 := by
  have hpos : 0 < CProg.ringSize cp := CProg.ringSize_pos cp
  cases hsize : CProg.ringSize cp with
  | zero =>
      omega
  | succ n =>
      rw [cpRing, hsize]
      rw [ringDarts_succ]
      simp

theorem cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
    {cp : CProg} (hsize : 1 < CProg.ringSize cp) :
    cpRing cp =
      (cpmap cp).map.node (cpmap cp).point ::
        (cpmap cp).point ::
          (cpRing cp).drop 2 := by
  cases h : CProg.ringSize cp with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ k =>
          rw [cpRing, h]
          rw [ringDarts_succ_succ]
          simp

theorem cpRing_drop_one_eq_point_cons_drop_two_of_ringSize_gt_one
    {cp : CProg} (hsize : 1 < CProg.ringSize cp) :
    (cpRing cp).drop 1 =
      (cpmap cp).point :: (cpRing cp).drop 2 := by
  rw [cpRing_eq_nodePoint_point_cons_drop_two_of_ringSize_gt_one
    (cp := cp) hsize]
  simp

theorem cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
    {cp : CProg} (hsize : 2 < CProg.ringSize cp) :
    cpRing cp =
      (cpmap cp).map.node (cpmap cp).point ::
        (cpmap cp).point ::
          (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) ::
            (cpRing cp).drop 3 := by
  have hsize' :
      CProg.ringSize cp = (CProg.ringSize cp - 3) + 3 := by
    omega
  rw [cpRing, hsize', ringDarts_succ_succ_succ]
  rfl

theorem cpRing_drop_two_eq_faceEdge_cons_drop_three_of_ringSize_gt_two
    {cp : CProg} (hsize : 2 < CProg.ringSize cp) :
    (cpRing cp).drop 2 =
      (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) ::
        (cpRing cp).drop 3 := by
  rw [cpRing_eq_nodePoint_point_faceEdge_cons_drop_three_of_ringSize_gt_two
    (cp := cp) hsize]
  rfl

@[simp]
theorem length_cpRing (cp : CProg) :
    (cpRing cp).length = CProg.ringSize cp := by
  simp [cpRing]

@[simp]
theorem cpRing_nil :
    cpRing [] = [false, true] := by
  rfl

/-- Program-level exact ring-cycle invariant at the syntactic ring size. -/
def cpRingCycle (cp : CProg) : Prop :=
  RingCycle (cpmap cp) (CProg.ringSize cp)

theorem cpRingCycle_a
    {cp : CProg} (hcycle : cpRingCycle cp)
    (hsize : 2 < CProg.ringSize cp) :
    cpRingCycle (CpStep.a :: cp) := by
  simpa [cpRingCycle, CProg.ringSize, hsize, cpmap_cons, step_a] using
    ringCycle_a hcycle hsize

theorem cpRing_y_eq_of_avoids_heads
    {cp : CProg}
    (hproper : (cpmap cp).ProperRingHead)
    (hnode : ∀ k : Nat, k + 1 < CProg.ringSize cp - 1 →
      iteratePerm (cpmap cp).map.node.symm k (cpmap cp).point ≠
        (cpmap cp).map.node (cpmap cp).point)
    (hnodeNode : ∀ k : Nat, k + 1 < CProg.ringSize cp - 1 →
      iteratePerm (cpmap cp).map.node.symm k (cpmap cp).point ≠
        (cpmap cp).map.node ((cpmap cp).map.node (cpmap cp).point)) :
    cpRing (CpStep.y :: cp) =
      (cpmap (CpStep.y :: cp)).map.node
          (cpmap (CpStep.y :: cp)).point ::
        (cpmap (CpStep.y :: cp)).point ::
          ((cpRing cp).drop 1).map (fun x => (cpmap cp).yOld x) := by
  let P := cpmap cp
  have hpos : 0 < CProg.ringSize cp := CProg.ringSize_pos cp
  have hleft :
      CProg.ringSize cp + 1 = (CProg.ringSize cp - 1) + 2 := by
    omega
  have hright :
      CProg.ringSize cp = (CProg.ringSize cp - 1) + 1 := by
    omega
  change ringDarts P.y (CProg.ringSize cp + 1) =
    P.y.map.node P.y.point :: P.y.point ::
      ((ringDarts P (CProg.ringSize cp)).drop 1).map
        (fun x => P.yOld x)
  rw [hleft, hright]
  exact ringDarts_y_of_avoids_heads P hproper (CProg.ringSize cp - 1)
    hnode hnodeNode

theorem cpRing_h_eq_of_avoids_heads
    {cp : CProg}
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp)
    (hpoint : ∀ k : Nat, 0 < k → k < CProg.ringSize cp - 2 →
      iteratePerm (cpmap cp).map.node.symm k (cpmap cp).point ≠
        (cpmap cp).point)
    (hnode : ∀ k : Nat, 0 < k → k < CProg.ringSize cp - 2 →
      iteratePerm (cpmap cp).map.node.symm k (cpmap cp).point ≠
        (cpmap cp).map.node (cpmap cp).point)
    (hnodeNode : ∀ k : Nat, 0 < k → k < CProg.ringSize cp - 2 →
      iteratePerm (cpmap cp).map.node.symm k (cpmap cp).point ≠
        (cpmap cp).map.node ((cpmap cp).map.node (cpmap cp).point)) :
    cpRing (CpStep.h :: cp) =
      (cpmap (CpStep.h :: cp)).map.node
          (cpmap (CpStep.h :: cp)).point ::
        (cpmap (CpStep.h :: cp)).point ::
          ((cpRing cp).drop 2).map (fun x => (cpmap cp).hOld x) := by
  let P := cpmap cp
  have hlen :
      CProg.ringSize cp = (CProg.ringSize cp - 2) + 2 := by
    omega
  change ringDarts P.h (CProg.ringSize cp) =
    P.h.map.node P.h.point :: P.h.point ::
      ((ringDarts P (CProg.ringSize cp)).drop 2).map
        (fun x => P.hOld x)
  rw [hlen]
  exact ringDarts_h_of_avoids_heads P hproper hlong
    (CProg.ringSize cp - 2) hpoint hnode hnodeNode

theorem cpRing_y_eq_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead) :
    cpRing (CpStep.y :: cp) =
      (cpmap (CpStep.y :: cp)).map.node
          (cpmap (CpStep.y :: cp)).point ::
        (cpmap (CpStep.y :: cp)).point ::
          ((cpRing cp).drop 1).map (fun x => (cpmap cp).yOld x) :=
  cpRing_y_eq_of_avoids_heads hproper
    (fun k hk =>
      RingCycle.avoids_node_point_before_last hcycle
        (by omega))
    (fun k hk =>
      RingCycle.avoids_node_node_point_before_last hcycle hk)

theorem cpRing_h_eq_of_ringCycle
    {cp : CProg}
    (hcycle : cpRingCycle cp)
    (hproper : (cpmap cp).ProperRingHead)
    (hlong : (cpmap cp).LongRingHead)
    (hsize : 2 < CProg.ringSize cp) :
    cpRing (CpStep.h :: cp) =
      (cpmap (CpStep.h :: cp)).map.node
          (cpmap (CpStep.h :: cp)).point ::
        (cpmap (CpStep.h :: cp)).point ::
          ((cpRing cp).drop 2).map (fun x => (cpmap cp).hOld x) :=
  cpRing_h_eq_of_avoids_heads hproper hlong hsize
    (fun k hkpos hk =>
      RingCycle.avoids_point_before_last_of_pos hcycle hkpos
        (by omega))
    (fun k _hkpos hk =>
      RingCycle.avoids_node_point_before_last hcycle
        (by omega))
    (fun k _hkpos hk =>
      RingCycle.avoids_node_node_point_before_last hcycle
        (by omega))


end Schematic.Math.GraphTheory.FourColor.PointedHypermap
