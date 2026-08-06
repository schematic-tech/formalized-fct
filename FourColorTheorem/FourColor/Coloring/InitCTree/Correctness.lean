import FourColorTheorem.FourColor.Coloring.InitCTree.PruningSemantics

/-! Properness and final specification of initial trace trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree
theorem proper_addDyck
    (m n : Nat) {lf : CTree}
    (hlf : Proper 0 lf) :
    Proper 0 (addDyck m n lf) := by
  induction n generalizing m lf with
  | zero =>
      simpa [addDyck, Proper] using hlf
  | succ n ih =>
      unfold addDyck
      let step := fun acc i => addDyck (i + 1) n acc
      have hfold :
          ∀ (xs : List Nat) (acc : CTree),
            Proper 0 acc → Proper 0 (xs.foldl step acc) := by
        intro xs
        induction xs with
        | nil =>
            intro acc hacc
            exact hacc
        | cons i xs ihxs =>
            intro acc hacc
            exact ihxs (step acc i) (ih (i + 1) hacc)
      exact hfold (List.range (m + 1)) lf hlf

theorem tableSub_leafTableFrom_proper_zero :
    ∀ {lf : CTree}, Proper 0 lf → (n h i : Nat) → (b : Bool) →
      Proper 0 (tableSub (leafTableFrom lf n h) i b)
  | lf, hlf, n, 0, i, b => by
      change Proper 0 (tableSub ([] : Table) i b)
      cases i <;> cases b <;>
        simp [tableSub, pairSub, emptyPair, proper_empty]
  | lf, hlf, n, 1, i, b => by
      change Proper 0 (tableSub [⟨lf, lf⟩] i b)
      cases i <;> cases b <;>
        simp [tableSub, pairSub, emptyPair, hlf, proper_empty]
  | lf, hlf, n, h + 2, i, b => by
      cases i with
      | zero =>
          cases b <;> simp [leafTableFrom, tableSub, pairSub, hlf]
      | succ i =>
          cases i with
          | zero =>
              cases b <;> simp [leafTableFrom, tableSub, pairSub, hlf,
                proper_empty]
          | succ i =>
              simpa [leafTableFrom, tableSub, pairSub] using
                tableSub_leafTableFrom_proper_zero
                  (proper_addDyck 2 n hlf) (n + 1) h i b

theorem tableSub_leafTable_proper_zero
    (h i : Nat) (b : Bool) :
    Proper 0 (tableSub (leafTable h) i b) := by
  cases i with
  | zero =>
      cases b <;> simp [leafTable, tableSub, pairSub, proper_empty,
        proper_simpleLeaf]
  | succ i =>
      simpa [leafTable, tableSub, pairSub] using
        tableSub_leafTableFrom_proper_zero proper_simpleLeaf 0 h i b

theorem tableSub_leafTableFrom_eq :
    ∀ (n h i : Nat) (b : Bool), i < h →
      tableSub (leafTableFrom (leafOf (dyck (2 * n + 2))) n h) i b =
        leafTableTreeSpec (2 * n + 1 + i) b
  | n, 0, i, b, hi => by
      omega
  | n, 1, i, b, hi => by
      have hi0 : i = 0 := by omega
      subst i
      cases b <;>
        simp [leafTableFrom, tableSub, pairSub, leafTableTreeSpec,
          Color.cons, Color.bit1]
  | n, h + 2, i, b, hi => by
      cases i with
      | zero =>
          cases b <;>
            simp [leafTableFrom, tableSub, pairSub, leafTableTreeSpec,
              Color.cons, Color.bit1]
      | succ i =>
          cases i with
          | zero =>
              cases b <;>
                simp [leafTableFrom, tableSub, pairSub, leafTableTreeSpec,
                  Color.cons, Color.bit1]
          | succ i =>
              have hi' : i < h := by omega
              have hrec :=
                tableSub_leafTableFrom_eq (n + 1) h i b hi'
              have hadd :
                  addDyck 2 n (leafOf (dyck (2 + 2 * n))) =
                    leafOf (dyck (2 + 2 * (n + 1))) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  addDyck_leafOf_dyck_step n
              have hidx :
                  i + (1 + 2 * (n + 1)) =
                    i + (1 + (2 + 2 * n)) := by
                omega
              simpa [leafTableFrom, tableSub, pairSub,
                hadd, hidx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hrec

theorem tableSub_leafTable_eq
    (h i : Nat) (b : Bool) (hi : i ≤ h) :
    tableSub (leafTable h) i b = leafTableTreeSpec i b := by
  cases i with
  | zero =>
      cases b <;>
        simp [leafTable, tableSub, pairSub, leafTableTreeSpec,
          simpleLeaf, leafOf, Color.cons, Color.bit1]
  | succ i =>
      cases h with
      | zero =>
          omega
      | succ h =>
          have hi' : i < h + 1 := by omega
          have hrec := tableSub_leafTableFrom_eq 0 (h + 1) i b hi'
          simpa [leafTable, tableSub, pairSub, simpleLeaf, leafOf,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

theorem sub_leafTable_spec_nil
    (h i : Nat) (b : Bool) (hi : i ≤ h) :
    sub (tableSub (leafTable h) i b) [] =
      tableSubSpec 0 i b [] := by
  rw [tableSub_leafTable_eq h i b hi]
  cases hb : i.bodd <;> cases b <;>
    simp [leafTableTreeSpec, tableSubSpec, hb, Color.cons, Color.bit1]

theorem sub_leafTable_cons
    (h i : Nat) (b : Bool) (e : Color) (et : ColSeq) :
    sub (tableSub (leafTable h) i b) (e :: et) = 0 :=
  sub_cons_of_proper_zero (tableSub_leafTable_proper_zero h i b) e et

theorem sub_leafTable_spec_cons
    (h i : Nat) (b : Bool) (e : Color) (et : ColSeq) :
    sub (tableSub (leafTable h) i b) (e :: et) =
      tableSubSpec 0 i b (e :: et) := by
  rw [sub_leafTable_cons]
  simp [tableSubSpec]

theorem sub_leafTable_spec
    (h i : Nat) (b : Bool) (hi : i ≤ h) :
    ∀ et, sub (tableSub (leafTable h) i b) et = tableSubSpec 0 i b et
  | [] => sub_leafTable_spec_nil h i b hi
  | e :: et => sub_leafTable_spec_cons h i b e et

theorem sub_iterate_mergeTable_leafTable_spec
    (n h : Nat) :
    ∀ i, i < (iterate n mergeTable (leafTable h)).length → ∀ b et,
      sub (tableSub (iterate n mergeTable (leafTable h)) i b) et =
        tableSubSpec n i b et := by
  intro i hi b et
  have hiter :=
    sub_iterate_mergeTable_spec n 0 (leafTable h)
      (by
        intro i hi b et
        have hi_le : i ≤ h := by
          rw [length_leafTable] at hi
          omega
        simpa using sub_leafTable_spec h i b hi_le et)
      i hi b et
  simpa using hiter

theorem sub_initTree (h : Nat) (et : ColSeq) :
    sub (initTree h) et = initSubSpec h et := by
  cases h with
  | zero =>
      exact sub_initTree_zero et
  | succ h =>
      unfold initTree
      rw [show h + 1 - 1 = h by omega]
      generalize htabEq :
        iterate h mergeTable (leafTable (h + 1)) = tab
      have hlen : tab.length = 2 := by
        rw [← htabEq, length_iterate_mergeTable_leafTable]
        omega
      have htabSub :
          ∀ i, i < tab.length → ∀ b et,
            sub (tableSub tab i b) et = tableSubSpec h i b et := by
        intro i hi b et
        have hi' : i < (iterate h mergeTable (leafTable (h + 1))).length := by
          simpa [htabEq] using hi
        simpa [htabEq] using
          sub_iterate_mergeTable_leafTable_spec h (h + 1) i hi' b et
      cases tab with
      | nil =>
          simp at hlen
      | cons pt0 rest =>
          cases rest with
          | nil =>
              simp at hlen
          | cons pt1 rest =>
              cases rest with
              | cons pt2 rest =>
                  simp at hlen
              | nil =>
                  cases pt0 with
                  | mk t0 t1 =>
                      cases pt1 with
                      | mk t2 t3 =>
                          cases et with
                          | nil =>
                              rw [sub_cons]
                              simp [sub, initSubSpec]
                          | cons e et =>
                              rw [sub_cons]
                              cases e with
                              | zero =>
                                  simp [sub, initSubSpec, ColSeq.ctrace,
                                    ColSeq.sum]
                              | one =>
                                  change sub (prune1 t1) et =
                                    initSubSpec (h + 1) (Color.one :: et)
                                  have ht1 :
                                      sub t1 et =
                                        tableSubSpec h 0 true et := by
                                    simpa [tableSub, pairSub] using
                                      htabSub 0 (by simp) true et
                                  rw [sub_prune1_eq_if_evenTrace_one, ht1]
                                  exact tableSubSpec_init_one h et
                              | two =>
                                  change sub (prune2 t2) et =
                                    initSubSpec (h + 1) (Color.two :: et)
                                  have ht2 :
                                      sub t2 et =
                                        tableSubSpec h 1 false et := by
                                    simpa [tableSub, pairSub] using
                                      htabSub 1 (by simp) false et
                                  rw [sub_prune2_eq_if_evenTrace_two, ht2]
                                  exact tableSubSpec_init_two h et
                              | three =>
                                  change sub (prune3 t3) et =
                                    initSubSpec (h + 1) (Color.three :: et)
                                  have ht3 :
                                      sub t3 et =
                                        tableSubSpec h 1 true et := by
                                    simpa [tableSub, pairSub] using
                                      htabSub 1 (by simp) true et
                                  rw [sub_prune3_eq_if_evenTrace_three, ht3]
                                  exact tableSubSpec_init_three h et

theorem sub_leafTable_spec_zero_nil
    (h : Nat) (b : Bool) :
    sub (tableSub (leafTable h) 0 b) [] =
      tableSubSpec 0 0 b [] := by
  cases b <;> rfl

theorem sub_leafTable_spec_one_nil
    (h : Nat) (b : Bool) :
    sub (tableSub (leafTable h.succ) 1 b) [] =
      tableSubSpec 0 1 b [] := by
  cases h <;> cases b <;> rfl

theorem sub_leafTable_spec_two_nil
    (h : Nat) (b : Bool) :
    sub (tableSub (leafTable h.succ.succ) 2 b) [] =
      tableSubSpec 0 2 b [] := by
  cases b <;> rfl

theorem sub_leafTable_spec_three_nil
    (h : Nat) (b : Bool) :
    sub (tableSub (leafTable h.succ.succ.succ) 3 b) [] =
      tableSubSpec 0 3 b [] := by
  cases h <;> cases b <;> rfl

theorem tableSub_mergeTableAux_proper_succ
    {h : Nat} (prev : Pair) (tab : Table)
    (hprev_left : Proper h prev.left)
    (hprev_right : Proper h prev.right)
    (htab : ∀ i b, Proper h (tableSub tab i b)) :
    ∀ i b, Proper (h + 1) (tableSub (mergeTableAux prev tab) i b) := by
  induction tab generalizing prev with
  | nil =>
      intro i b
      cases i <;> cases b <;>
        simp [mergeTableAux, tableSub, pairSub, emptyPair, proper_empty]
  | cons pt tab ih =>
      intro i b
      cases i with
      | zero =>
          have hp :=
            mergePair_proper hprev_left hprev_right
              (htab 0 false) (htab 0 true)
          cases b
          · simpa [mergeTableAux, tableSub, pairSub] using hp.1
          · simpa [mergeTableAux, tableSub, pairSub] using hp.2
      | succ i =>
          have hpt_left : Proper h pt.left := by
            simpa [tableSub, pairSub] using htab 0 false
          have hpt_right : Proper h pt.right := by
            simpa [tableSub, pairSub] using htab 0 true
          have htail : ∀ i b, Proper h (tableSub tab i b) := by
            intro i b
            simpa [tableSub, pairSub] using htab (i + 1) b
          simpa [mergeTableAux, tableSub, pairSub] using
            ih pt hpt_left hpt_right htail i b

theorem tableSub_mergeTable_proper_succ
    {h : Nat} (tab : Table)
    (htab : ∀ i b, Proper h (tableSub tab i b)) :
    ∀ i b, Proper (h + 1) (tableSub (mergeTable tab) i b) := by
  cases tab with
  | nil =>
      intro i b
      cases i <;> cases b <;>
        simp [mergeTable, tableSub, pairSub, emptyPair, proper_empty]
  | cons line tab =>
      exact tableSub_mergeTableAux_proper_succ line tab
        (by simpa [tableSub, pairSub] using htab 0 false)
        (by simpa [tableSub, pairSub] using htab 0 true)
        (by
          intro i b
          simpa [tableSub, pairSub] using htab (i + 1) b)

theorem proper_prune1 :
    ∀ {h : Nat} {t : CTree}, Proper h t → Proper h (prune1 t)
  | h, empty, _ => proper_empty h
  | 0, leaf lf, hlf => by
      simpa [prune1, Proper] using hlf
  | h + 1, leaf lf, hlf => by
      simp [Proper] at hlf
  | 0, node t1 t2 t3, hnode => by
      simp [Proper] at hnode
  | h + 1, node t1 t2 t3, hnode => by
      rcases hnode with ⟨_, h1, h2, _h3⟩
      exact proper_cons (proper_prune1 h1) h2 (proper_empty h)

theorem proper_prune2 :
    ∀ {h : Nat} {t : CTree}, Proper h t → Proper h (prune2 t)
  | h, empty, _ => proper_empty h
  | 0, leaf lf, hlf => by
      simpa [prune2, Proper] using hlf
  | h + 1, leaf lf, hlf => by
      simp [Proper] at hlf
  | 0, node t1 t2 t3, hnode => by
      simp [Proper] at hnode
  | h + 1, node t1 t2 t3, hnode => by
      rcases hnode with ⟨_, _h1, h2, h3⟩
      exact proper_cons (proper_empty h) (proper_prune2 h2) h3

theorem proper_prune3 :
    ∀ {h : Nat} {t : CTree}, Proper h t → Proper h (prune3 t)
  | h, empty, _ => proper_empty h
  | 0, leaf lf, hlf => by
      simpa [prune3, Proper] using hlf
  | h + 1, leaf lf, hlf => by
      simp [Proper] at hlf
  | 0, node t1 t2 t3, hnode => by
      simp [Proper] at hnode
  | h + 1, node t1 t2 t3, hnode => by
      rcases hnode with ⟨_, h1, _h2, h3⟩
      exact proper_cons h1 (proper_empty h) (proper_prune3 h3)

theorem tableSub_iterate_mergeTable_proper
    (n h : Nat) (tab : Table)
    (htab : ∀ i b, Proper h (tableSub tab i b)) :
    ∀ i b, Proper (h + n) (tableSub (iterate n mergeTable tab) i b) := by
  induction n with
  | zero =>
      intro i b
      simpa using htab i b
  | succ n ih =>
      intro i b
      have hstep :=
        tableSub_mergeTable_proper_succ (iterate n mergeTable tab) ih i b
      simpa [iterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hstep

theorem proper_initTree (h : Nat) :
    Proper h (initTree h) := by
  cases h with
  | zero =>
      simp [proper_empty]
  | succ h =>
      unfold initTree
      rw [show h + 1 - 1 = h by omega]
      generalize htabEq :
        iterate h mergeTable (leafTable (h + 1)) = tab
      have htab :
          ∀ i b, Proper h (tableSub tab i b) := by
        intro i b
        rw [← htabEq]
        simpa using
          tableSub_iterate_mergeTable_proper h 0 (leafTable (h + 1))
            (tableSub_leafTable_proper_zero (h + 1)) i b
      cases tab with
      | nil =>
          exact proper_empty (h + 1)
      | cons pt0 rest =>
          cases rest with
          | nil =>
              exact proper_empty (h + 1)
          | cons pt1 rest =>
              exact proper_cons
                (proper_prune1
                  (by simpa [tableSub, pairSub] using htab 0 true))
                (proper_prune2
                  (by simpa [tableSub, pairSub] using htab 1 false))
                (proper_prune3
                  (by simpa [tableSub, pairSub] using htab 1 true))

end CTree

end FourColor

end Schematic.Math.GraphTheory
