import FourColorTheorem.FourColor.Coloring.CTreeRestrict.ZeroHeight

/-! General partition and size theorems for trace-tree restriction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem restrict_size_partition_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) :
    size t =
      size (restrict h t r).left + size (restrict h t r).right := by
  induction h generalizing t r with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_size_partition_of_proper r hproper
  | succ h ih =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨_, h1, h2, h3⟩
          cases r with
          | nil =>
              rw [restrict_nil]
              simp
          | cons bs gt r' =>
              change
                size (node t1 t2 t3) =
                  size
                      (Restriction.split
                        (fun r1 r2 r3 =>
                          consPairs
                            (restrict h t1 r1)
                            (restrict h t2 r2)
                            (restrict h t3 r3))
                        Restriction.nil Restriction.nil Restriction.nil
                        (Restriction.cons bs gt r')).left +
                    size
                      (Restriction.split
                        (fun r1 r2 r3 =>
                          consPairs
                            (restrict h t1 r1)
                            (restrict h t2 r2)
                            (restrict h t3 r3))
                        Restriction.nil Restriction.nil Restriction.nil
                        (Restriction.cons bs gt r')).right
              rw [Restriction.split_eq]
              simp only [consPairs_left, consPairs_right, size_cons, size_node]
              have hs1 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.one) h1
              have hs2 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.two) h2
              have hs3 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.three) h3
              omega

theorem restrict_left_size_le_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) :
    size (restrict h t r).left ≤ size t := by
  induction h generalizing t r with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_left_size_le_of_proper r hproper
  | succ h ih =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨_, h1, h2, h3⟩
          cases r with
          | nil =>
              rw [restrict_nil]
          | cons bs gt r' =>
              change
                size
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).left ≤
                  size (node t1 t2 t3)
              rw [Restriction.split_eq]
              simp only [consPairs_left, size_cons, size_node]
              have hs1 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.one) h1
              have hs2 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.two) h2
              have hs3 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.three) h3
              omega

theorem restrict_right_size_le_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) :
    size (restrict h t r).right ≤ size t := by
  induction h generalizing t r with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_right_size_le_of_proper r hproper
  | succ h ih =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨_, h1, h2, h3⟩
          cases r with
          | nil =>
              rw [restrict_nil]
              simp
          | cons bs gt r' =>
              change
                size
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).right ≤
                  size (node t1 t2 t3)
              rw [Restriction.split_eq]
              simp only [consPairs_right, size_cons, size_node]
              have hs1 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.one) h1
              have hs2 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.two) h2
              have hs3 :=
                ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.three) h3
              omega

theorem restrict_partition_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) :
    Partition t (restrict h t r) := by
  induction h generalizing t r with
  | zero =>
      cases t with
      | empty =>
          cases r <;>
            simpa [restrict, emptyPair] using partition_self_empty empty
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_partition_of_proper r hproper
  | succ h ih =>
      cases t with
      | empty =>
          cases r <;>
            simpa [restrict, emptyPair] using partition_self_empty empty
      | leaf lf =>
          simp [Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨_, h1, h2, h3⟩
          cases r with
          | nil =>
              exact restrict_nil_partition (h + 1) (node t1 t2 t3)
          | cons bs gt r' =>
              change
                Partition (node t1 t2 t3)
                  (Restriction.split
                    (fun r1 r2 r3 =>
                      consPairs
                        (restrict h t1 r1)
                        (restrict h t2 r2)
                        (restrict h t3 r3))
                    Restriction.nil Restriction.nil Restriction.nil
                    (Restriction.cons bs gt r'))
              rw [Restriction.split_eq]
              exact consPairs_partition
                (ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.one) h1)
                (ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.two) h2)
                (ih (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.three) h3)

theorem restrict_proper_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) :
    Proper (h + 1) (restrict h t r).left ∧
      Proper (h + 1) (restrict h t r).right := by
  induction h generalizing t r with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair, proper_empty]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_proper_of_proper r hproper
  | succ h ih =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair, proper_empty]
      | leaf lf =>
          simp [Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨_, h1, h2, h3⟩
          cases r with
          | nil =>
              rw [restrict_nil]
              exact ⟨⟨by assumption, h1, h2, h3⟩, proper_empty (h + 2)⟩
          | cons bs gt r' =>
              change
                Proper (h + 2)
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).left ∧
                  Proper (h + 2)
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).right
              rw [Restriction.split_eq]
              have p1 := ih
                (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.one) h1
              have p2 := ih
                (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.two) h2
              have p3 := ih
                (Restriction.splitColor
                  (Restriction.cons bs gt r') Color.three) h3
              constructor
              · rw [consPairs_left]
                exact proper_cons p1.1 p2.1 p3.1
              · rw [consPairs_right]
                exact proper_cons p1.2 p2.2 p3.2

theorem restrict_nil_left (h : Nat) (t : CTree) :
    (restrict h t Restriction.nil).left = t := by
  rw [restrict_nil]

theorem restrict_nil_right (h : Nat) (t : CTree) :
    (restrict h t Restriction.nil).right = empty := by
  rw [restrict_nil]

theorem restrict_nil_sub_left (h : Nat) (t : CTree) (et : ColSeq) :
    sub (restrict h t Restriction.nil).left et = sub t et := by
  rw [restrict_nil_left]

theorem restrict_nil_sub_right (h : Nat) (t : CTree) (et : ColSeq) :
    sub (restrict h t Restriction.nil).right et = 0 := by
  rw [restrict_nil_right]
  exact sub_empty et

theorem sub_sub_splitColor_eq_sub_sub_cons
    {h : Nat} {t : CTree} (ht : Proper (h + 1) t)
    (r : Restriction) (c : Color) (et : ColSeq) :
    sub t et - Restriction.sub (Restriction.splitColor r c) et =
      sub t et - Restriction.sub r (c :: et) := by
  cases et with
  | nil =>
      simp [sub_nil_of_proper_succ ht]
  | cons e et =>
      rw [Restriction.splitColor_sub_cons]

theorem sub_le_splitColor_eq_sub_le_cons
    {h : Nat} {t : CTree} (ht : Proper (h + 1) t)
    (r : Restriction) (c : Color) (et : ColSeq) :
    (sub t et ≤ Restriction.sub (Restriction.splitColor r c) et) =
      (sub t et ≤ Restriction.sub r (c :: et)) := by
  cases et with
  | nil =>
      simp [sub_nil_of_proper_succ ht]
  | cons e et =>
      rw [Restriction.splitColor_sub_cons]

end CTree

end FourColor

end Schematic.Math.GraphTheory
