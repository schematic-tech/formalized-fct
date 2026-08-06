import FourColorTheorem.FourColor.Coloring.CTreeRestrict.GeneralPartition

/-! Exact multiplicity and membership formulas for trace-tree restriction. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem restrict_sub_left_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) (et : ColSeq) :
    sub (restrict h t r).left et =
      sub t et - Restriction.sub r et := by
  induction h generalizing t r et with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_sub_left_of_proper r hproper et
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
              simp [Restriction.sub]
          | cons bs gt r' =>
              change
                sub
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).left et =
                  sub (node t1 t2 t3) et -
                    Restriction.sub (Restriction.cons bs gt r') et
              rw [Restriction.split_eq]
              cases et with
              | nil =>
                  simp [sub_cons, sub]
              | cons c et =>
                  cases c with
                  | zero =>
                      simp [sub_cons, sub, Restriction.sub_zero_cons]
                  | one =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.one) h1 et,
                        sub_sub_splitColor_eq_sub_sub_cons h1
                          (Restriction.cons bs gt r') Color.one et]
                  | two =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.two) h2 et,
                        sub_sub_splitColor_eq_sub_sub_cons h2
                          (Restriction.cons bs gt r') Color.two et]
                  | three =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.three) h3 et,
                        sub_sub_splitColor_eq_sub_sub_cons h3
                          (Restriction.cons bs gt r') Color.three et]

theorem restrict_sub_right_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) (et : ColSeq) :
    sub (restrict h t r).right et =
      if sub t et ≤ Restriction.sub r et then
        sub t et
      else
        0 := by
  induction h generalizing t r et with
  | zero =>
      cases t with
      | empty =>
          cases r <;> simp [restrict, emptyPair]
      | leaf lf =>
          simp [Proper] at hproper
      | node lf1 lf2 lf3 =>
          exact restrict_zero_node_sub_right_of_proper r hproper et
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
              rw [restrict_nil_sub_right]
              generalize hn : sub (node t1 t2 t3) et = n
              cases n <;> simp [Restriction.sub]
          | cons bs gt r' =>
              change
                sub
                    (Restriction.split
                      (fun r1 r2 r3 =>
                        consPairs
                          (restrict h t1 r1)
                          (restrict h t2 r2)
                          (restrict h t3 r3))
                      Restriction.nil Restriction.nil Restriction.nil
                      (Restriction.cons bs gt r')).right et =
                  if sub (node t1 t2 t3) et ≤
                      Restriction.sub (Restriction.cons bs gt r') et then
                    sub (node t1 t2 t3) et
                  else
                    0
              rw [Restriction.split_eq]
              cases et with
              | nil =>
                  simp [sub_cons, sub]
              | cons c et =>
                  cases c with
                  | zero =>
                      simp [sub_cons, sub, Restriction.sub_zero_cons]
                  | one =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.one) h1 et,
                        sub_le_splitColor_eq_sub_le_cons h1
                          (Restriction.cons bs gt r') Color.one et]
                  | two =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.two) h2 et,
                        sub_le_splitColor_eq_sub_le_cons h2
                          (Restriction.cons bs gt r') Color.two et]
                  | three =>
                      simp [sub_cons, sub,
                        ih (Restriction.splitColor
                          (Restriction.cons bs gt r') Color.three) h3 et,
                        sub_le_splitColor_eq_sub_le_cons h3
                          (Restriction.cons bs gt r') Color.three et]

theorem restrict_left_mem_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) (et : ColSeq) :
    mem (restrict h t r).left et =
      decide (Restriction.sub r et < sub t et) := by
  unfold mem
  rw [restrict_sub_left_of_proper h r hproper et]
  by_cases hlt : Restriction.sub r et < sub t et
  · have hne : sub t et - Restriction.sub r et ≠ 0 :=
      Nat.sub_ne_zero_of_lt hlt
    simp [hne, hlt]
  · have hle : sub t et ≤ Restriction.sub r et := Nat.le_of_not_gt hlt
    have hzero : sub t et - Restriction.sub r et = 0 :=
      Nat.sub_eq_zero_of_le hle
    simp [hzero, hlt]

theorem restrict_right_mem_of_proper
    (h : Nat) {t : CTree} (r : Restriction)
    (hproper : Proper (h + 1) t) (et : ColSeq) :
    mem (restrict h t r).right et =
      (mem t et && decide (sub t et ≤ Restriction.sub r et)) := by
  unfold mem
  rw [restrict_sub_right_of_proper h r hproper et]
  by_cases hle : sub t et ≤ Restriction.sub r et
  · simp [hle]
  · simp [hle]

end CTree

end FourColor

end Schematic.Math.GraphTheory
