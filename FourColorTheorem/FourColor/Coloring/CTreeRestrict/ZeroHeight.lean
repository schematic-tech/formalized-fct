import FourColorTheorem.FourColor.Coloring.CTreeRestrict.LeafPartition

/-! Correctness and size bounds for height-zero trace-tree restriction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem restrict_nil_partition (h : Nat) (t : CTree) :
    Partition t (restrict h t Restriction.nil) := by
  rw [restrict_nil]
  exact partition_self_empty t

theorem restrict_zero_leafOf_partition
    (r : Restriction) (n1 n2 n3 : Nat) :
    Partition (node (leafOf n1) (leafOf n2) (leafOf n3))
      (restrict 0 (node (leafOf n1) (leafOf n2) (leafOf n3)) r) := by
  cases r with
  | nil =>
      exact restrict_nil_partition 0
        (node (leafOf n1) (leafOf n2) (leafOf n3))
  | cons bs gt r =>
      change Partition (node (leafOf n1) (leafOf n2) (leafOf n3))
        (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
            (Restriction.cons bs gt r);
          leafPair (leafOf n1) (leafOf n2) (leafOf n3)
            dec.1 dec.2.1 dec.2.2)
      rw [decrLeaves_leafOf]
      exact leafPair_leafOf_partition n1 n2 n3
        (Restriction.sub (Restriction.cons bs gt r) [Color.one])
        (Restriction.sub (Restriction.cons bs gt r) [Color.two])
        (Restriction.sub (Restriction.cons bs gt r) [Color.three])

theorem restrict_zero_leafOf_sub_left
    (r : Restriction) (n1 n2 n3 : Nat) (et : ColSeq) :
    sub (restrict 0
      (node (leafOf n1) (leafOf n2) (leafOf n3)) r).left et =
      sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et -
        Restriction.sub r et := by
  cases r with
  | nil =>
      rw [restrict_nil]
      cases et with
      | nil =>
          simp [Restriction.sub, sub]
      | cons e et =>
          cases e with
          | zero =>
              simp [Restriction.sub, sub]
          | one =>
              cases et with
              | nil =>
                  cases n1 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
          | two =>
              cases et with
              | nil =>
                  cases n2 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
          | three =>
              cases et with
              | nil =>
                  cases n3 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
  | cons bs gt r =>
      change
        sub
          (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
              (Restriction.cons bs gt r);
            (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
              dec.1 dec.2.1 dec.2.2).left) et =
          sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et -
            Restriction.sub (Restriction.cons bs gt r) et
      simp [decrLeaves_leafOf, leafPair]
      cases et with
      | nil =>
          simp [sub_cons, sub]
      | cons e et =>
          cases e with
          | zero =>
              simp [sub_cons, sub]
          | one =>
              cases et with
              | nil =>
                  simp [sub_cons, sub]
              | cons e et =>
                  simp [sub_cons, sub]
          | two =>
              cases et with
              | nil =>
                  simp [sub_cons, sub]
              | cons e et =>
                  simp [sub_cons, sub]
          | three =>
              cases et with
              | nil =>
                  simp [sub_cons, sub]
              | cons e et =>
                  simp [sub_cons, sub]

theorem restrict_zero_leafOf_sub_right
    (r : Restriction) (n1 n2 n3 : Nat) (et : ColSeq) :
    sub (restrict 0
      (node (leafOf n1) (leafOf n2) (leafOf n3)) r).right et =
      if sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et ≤
          Restriction.sub r et then
        sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et
      else
        0 := by
  cases r with
  | nil =>
      rw [restrict_nil]
      cases et with
      | nil =>
          simp [Restriction.sub, sub]
      | cons e et =>
          cases e with
          | zero =>
              simp [Restriction.sub, sub]
          | one =>
              cases et with
              | nil =>
                  cases n1 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
          | two =>
              cases et with
              | nil =>
                  cases n2 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
          | three =>
              cases et with
              | nil =>
                  cases n3 <;> simp [Restriction.sub, sub]
              | cons e et =>
                  simp [Restriction.sub, sub]
  | cons bs gt r =>
      change
        sub
          (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
              (Restriction.cons bs gt r);
            (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
              dec.1 dec.2.1 dec.2.2).right) et =
          if sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et ≤
              Restriction.sub (Restriction.cons bs gt r) et then
            sub (node (leafOf n1) (leafOf n2) (leafOf n3)) et
          else
            0
      simp [decrLeaves_leafOf, leafPair]
      cases et with
      | nil =>
          simp [sub_cons, sub]
      | cons e et =>
          cases e with
          | zero =>
              simp [sub_cons, sub]
          | one =>
              cases et with
              | nil =>
                  by_cases h :
                    n1 ≤ Restriction.sub (Restriction.cons bs gt r)
                      [Color.one] <;>
                    simp [sub_cons, sub, isEmpty_leafOf,
                      Nat.sub_eq_zero_iff_le, h]
              | cons e et =>
                  by_cases h :
                    isEmpty (leafOf
                      (n1 - Restriction.sub (Restriction.cons bs gt r)
                        [Color.one])) = true <;>
                    simp [sub_cons, sub, h]
          | two =>
              cases et with
              | nil =>
                  by_cases h :
                    n2 ≤ Restriction.sub (Restriction.cons bs gt r)
                      [Color.two] <;>
                    simp [sub_cons, sub, isEmpty_leafOf,
                      Nat.sub_eq_zero_iff_le, h]
              | cons e et =>
                  by_cases h :
                    isEmpty (leafOf
                      (n2 - Restriction.sub (Restriction.cons bs gt r)
                        [Color.two])) = true <;>
                    simp [sub_cons, sub, h]
          | three =>
              cases et with
              | nil =>
                  by_cases h :
                    n3 ≤ Restriction.sub (Restriction.cons bs gt r)
                      [Color.three] <;>
                    simp [sub_cons, sub, isEmpty_leafOf,
                      Nat.sub_eq_zero_iff_le, h]
              | cons e et =>
                  by_cases h :
                    isEmpty (leafOf
                      (n3 - Restriction.sub (Restriction.cons bs gt r)
                        [Color.three])) = true <;>
                    simp [sub_cons, sub, h]

theorem restrict_zero_leafOf_proper
    (r : Restriction) (n1 n2 n3 : Nat)
    (hproper : Proper 1 (node (leafOf n1) (leafOf n2) (leafOf n3))) :
    Proper 1
        (restrict 0 (node (leafOf n1) (leafOf n2) (leafOf n3)) r).left ∧
      Proper 1
        (restrict 0 (node (leafOf n1) (leafOf n2) (leafOf n3)) r).right := by
  cases r with
  | nil =>
      rw [restrict_nil]
      exact ⟨hproper, proper_empty 1⟩
  | cons bs gt r =>
      change
        Proper 1
            (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                (Restriction.cons bs gt r);
              (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                dec.1 dec.2.1 dec.2.2).left) ∧
          Proper 1
            (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                (Restriction.cons bs gt r);
              (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                dec.1 dec.2.1 dec.2.2).right)
      rw [decrLeaves_leafOf]
      exact leafPair_leafOf_proper n1 n2 n3
        (Restriction.sub (Restriction.cons bs gt r) [Color.one])
        (Restriction.sub (Restriction.cons bs gt r) [Color.two])
        (Restriction.sub (Restriction.cons bs gt r) [Color.three])

theorem restrict_zero_node_partition_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) :
    Partition (node lf1 lf2 lf3) (restrict 0 (node lf1 lf2 lf3) r) := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_partition r (sub lf1 []) (sub lf2 []) (sub lf3 [])

theorem restrict_zero_node_sub_left_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) (et : ColSeq) :
    sub (restrict 0 (node lf1 lf2 lf3) r).left et =
      sub (node lf1 lf2 lf3) et - Restriction.sub r et := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_sub_left r (sub lf1 []) (sub lf2 []) (sub lf3 []) et

theorem restrict_zero_node_sub_right_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) (et : ColSeq) :
    sub (restrict 0 (node lf1 lf2 lf3) r).right et =
      if sub (node lf1 lf2 lf3) et ≤ Restriction.sub r et then
        sub (node lf1 lf2 lf3) et
      else
        0 := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_sub_right r (sub lf1 []) (sub lf2 []) (sub lf3 []) et

theorem restrict_zero_node_proper_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) :
      Proper 1 (restrict 0 (node lf1 lf2 lf3) r).left ∧
      Proper 1 (restrict 0 (node lf1 lf2 lf3) r).right := by
  rcases hproper with ⟨hnonempty, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  have hpLeaf :
      Proper 1
        (node (leafOf (sub lf1 [])) (leafOf (sub lf2 []))
          (leafOf (sub lf3 []))) := by
    rw [← e1, ← e2, ← e3]
    exact ⟨hnonempty, h1, h2, h3⟩
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_proper r (sub lf1 []) (sub lf2 []) (sub lf3 [])
    hpLeaf

theorem leafPair_leafOf_left_size_le
    (n1 n2 n3 k1 k2 k3 : Nat) :
    size
        (leafPair
          (leafOf n1) (leafOf n2) (leafOf n3)
          (leafOf (n1 - k1)) (leafOf (n2 - k2))
          (leafOf (n3 - k3))).left ≤
      size (node (leafOf n1) (leafOf n2) (leafOf n3)) := by
  rw [leafPair_spec, size_cons]
  simp only [size_node]
  have h1 := size_leafOf_sub_le n1 k1
  have h2 := size_leafOf_sub_le n2 k2
  have h3 := size_leafOf_sub_le n3 k3
  omega

theorem leafPair_leafOf_right_size_le
    (n1 n2 n3 k1 k2 k3 : Nat) :
    size
        (leafPair
          (leafOf n1) (leafOf n2) (leafOf n3)
          (leafOf (n1 - k1)) (leafOf (n2 - k2))
          (leafOf (n3 - k3))).right ≤
      size (node (leafOf n1) (leafOf n2) (leafOf n3)) := by
  rw [leafPair_spec, size_cons]
  simp only [size_node]
  have h1 :
      size
          (if isEmpty (leafOf (n1 - k1)) then leafOf n1 else empty) ≤
        size (leafOf n1) := by
    by_cases h : isEmpty (leafOf (n1 - k1)) = true <;> simp [h]
  have h2 :
      size
          (if isEmpty (leafOf (n2 - k2)) then leafOf n2 else empty) ≤
        size (leafOf n2) := by
    by_cases h : isEmpty (leafOf (n2 - k2)) = true <;> simp [h]
  have h3 :
      size
          (if isEmpty (leafOf (n3 - k3)) then leafOf n3 else empty) ≤
        size (leafOf n3) := by
    by_cases h : isEmpty (leafOf (n3 - k3)) = true <;> simp [h]
  omega

theorem restrict_zero_leafOf_left_size_le
    (r : Restriction) (n1 n2 n3 : Nat) :
    size (restrict 0
        (node (leafOf n1) (leafOf n2) (leafOf n3)) r).left ≤
      size (node (leafOf n1) (leafOf n2) (leafOf n3)) := by
  cases r with
  | nil =>
      rw [restrict_nil]
  | cons bs gt r =>
      change
        size
            (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                (Restriction.cons bs gt r);
              (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                dec.1 dec.2.1 dec.2.2).left) ≤
          size (node (leafOf n1) (leafOf n2) (leafOf n3))
      rw [decrLeaves_leafOf]
      exact leafPair_leafOf_left_size_le n1 n2 n3
        (Restriction.sub (Restriction.cons bs gt r) [Color.one])
        (Restriction.sub (Restriction.cons bs gt r) [Color.two])
        (Restriction.sub (Restriction.cons bs gt r) [Color.three])

theorem restrict_zero_leafOf_right_size_le
    (r : Restriction) (n1 n2 n3 : Nat) :
    size (restrict 0
        (node (leafOf n1) (leafOf n2) (leafOf n3)) r).right ≤
      size (node (leafOf n1) (leafOf n2) (leafOf n3)) := by
  cases r with
  | nil =>
      rw [restrict_nil]
      simp
  | cons bs gt r =>
      change
        size
            (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                (Restriction.cons bs gt r);
              (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                dec.1 dec.2.1 dec.2.2).right) ≤
          size (node (leafOf n1) (leafOf n2) (leafOf n3))
      rw [decrLeaves_leafOf]
      exact leafPair_leafOf_right_size_le n1 n2 n3
        (Restriction.sub (Restriction.cons bs gt r) [Color.one])
        (Restriction.sub (Restriction.cons bs gt r) [Color.two])
        (Restriction.sub (Restriction.cons bs gt r) [Color.three])

theorem restrict_zero_node_left_size_le_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) :
    size (restrict 0 (node lf1 lf2 lf3) r).left ≤
      size (node lf1 lf2 lf3) := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_left_size_le r
    (sub lf1 []) (sub lf2 []) (sub lf3 [])

theorem restrict_zero_node_right_size_le_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) :
    size (restrict 0 (node lf1 lf2 lf3) r).right ≤
      size (node lf1 lf2 lf3) := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_right_size_le r
    (sub lf1 []) (sub lf2 []) (sub lf3 [])

theorem size_leafOf_partition_sub (n k : Nat) :
    size (leafOf n) =
      size (leafOf (n - k)) +
        size (if isEmpty (leafOf (n - k)) then leafOf n else empty) := by
  cases hsub : n - k with
  | zero =>
      cases n <;> simp [isEmpty, leafOf]
  | succ m =>
      cases n with
      | zero =>
          simp at hsub
      | succ n =>
          simp [isEmpty, leafOf]

theorem leafPair_leafOf_size_partition
    (n1 n2 n3 k1 k2 k3 : Nat) :
    size (node (leafOf n1) (leafOf n2) (leafOf n3)) =
      size
          (leafPair
            (leafOf n1) (leafOf n2) (leafOf n3)
            (leafOf (n1 - k1)) (leafOf (n2 - k2))
            (leafOf (n3 - k3))).left +
        size
          (leafPair
            (leafOf n1) (leafOf n2) (leafOf n3)
            (leafOf (n1 - k1)) (leafOf (n2 - k2))
            (leafOf (n3 - k3))).right := by
  rw [leafPair_spec, size_cons, size_cons]
  simp only [size_node]
  have h1 := size_leafOf_partition_sub n1 k1
  have h2 := size_leafOf_partition_sub n2 k2
  have h3 := size_leafOf_partition_sub n3 k3
  omega

theorem restrict_zero_leafOf_size_partition
    (r : Restriction) (n1 n2 n3 : Nat) :
    size (node (leafOf n1) (leafOf n2) (leafOf n3)) =
      size (restrict 0
        (node (leafOf n1) (leafOf n2) (leafOf n3)) r).left +
        size (restrict 0
          (node (leafOf n1) (leafOf n2) (leafOf n3)) r).right := by
  cases r with
  | nil =>
      rw [restrict_nil]
      simp
  | cons bs gt r =>
      change
        size (node (leafOf n1) (leafOf n2) (leafOf n3)) =
          size
              (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                  (Restriction.cons bs gt r);
                (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                  dec.1 dec.2.1 dec.2.2).left) +
            size
              (let dec := decrLeaves (leafOf n1) (leafOf n2) (leafOf n3)
                  (Restriction.cons bs gt r);
                (leafPair (leafOf n1) (leafOf n2) (leafOf n3)
                  dec.1 dec.2.1 dec.2.2).right)
      rw [decrLeaves_leafOf]
      exact leafPair_leafOf_size_partition n1 n2 n3
        (Restriction.sub (Restriction.cons bs gt r) [Color.one])
        (Restriction.sub (Restriction.cons bs gt r) [Color.two])
        (Restriction.sub (Restriction.cons bs gt r) [Color.three])

theorem restrict_zero_node_size_partition_of_proper
    (r : Restriction) {lf1 lf2 lf3 : CTree}
    (hproper : Proper 1 (node lf1 lf2 lf3)) :
    size (node lf1 lf2 lf3) =
      size (restrict 0 (node lf1 lf2 lf3) r).left +
        size (restrict 0 (node lf1 lf2 lf3) r).right := by
  rcases hproper with ⟨_, h1, h2, h3⟩
  have e1 := proper_zero_eq_leafOf_sub_nil h1
  have e2 := proper_zero_eq_leafOf_sub_nil h2
  have e3 := proper_zero_eq_leafOf_sub_nil h3
  rw [e1, e2, e3]
  exact restrict_zero_leafOf_size_partition r
    (sub lf1 []) (sub lf2 []) (sub lf3 [])

end CTree

end FourColor

end Schematic.Math.GraphTheory
