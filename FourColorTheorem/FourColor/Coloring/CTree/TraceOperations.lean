import FourColorTheorem.FourColor.Coloring.CTree.Properness

/-! Union, rotation, and singleton-trace semantics for trace-coloring trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

theorem mem_union :
    ∀ {h : Nat} {t u : CTree} (et : ColSeq),
      Proper h t → Proper h u →
        mem (union t u) et = (mem t et || mem u et)
  | 0, t, u, et, ht, hu => by
      cases t <;> cases u <;> cases et <;>
        simp [union, Proper, simpleLeaf, mem, sub] at ht hu ⊢
  | h + 1, t, u, et, ht, hu => by
      cases t with
      | empty =>
          simp [union, mem_empty]
      | leaf lf =>
          simp [Proper] at ht
      | node t1 t2 t3 =>
          rcases ht with ⟨_, ht1, ht2, ht3⟩
          cases u with
          | empty =>
              simp [union, mem_empty]
          | leaf lf =>
              simp [Proper] at hu
          | node u1 u2 u3 =>
              rcases hu with ⟨_, hu1, hu2, hu3⟩
              cases et with
              | nil =>
                  change
                    mem (cons (union t1 u1) (union t2 u2) (union t3 u3)) [] =
                      (mem (node t1 t2 t3) [] || mem (node u1 u2 u3) [])
                  rw [mem_cons]
                  rfl
              | cons e et =>
                  cases e with
                  | zero =>
                      change
                        mem (cons (union t1 u1) (union t2 u2) (union t3 u3))
                            (Color.zero :: et) =
                          (mem (node t1 t2 t3) (Color.zero :: et) ||
                            mem (node u1 u2 u3) (Color.zero :: et))
                      rw [mem_cons]
                      rfl
                  | one =>
                      change
                        mem (cons (union t1 u1) (union t2 u2) (union t3 u3))
                            (Color.one :: et) =
                          (mem (node t1 t2 t3) (Color.one :: et) ||
                            mem (node u1 u2 u3) (Color.one :: et))
                      rw [mem_cons]
                      change mem (union t1 u1) et = (mem t1 et || mem u1 et)
                      exact mem_union (h := h) (t := t1) (u := u1) et ht1 hu1
                  | two =>
                      change
                        mem (cons (union t1 u1) (union t2 u2) (union t3 u3))
                            (Color.two :: et) =
                          (mem (node t1 t2 t3) (Color.two :: et) ||
                            mem (node u1 u2 u3) (Color.two :: et))
                      rw [mem_cons]
                      change mem (union t2 u2) et = (mem t2 et || mem u2 et)
                      exact mem_union (h := h) (t := t2) (u := u2) et ht2 hu2
                  | three =>
                      change
                        mem (cons (union t1 u1) (union t2 u2) (union t3 u3))
                            (Color.three :: et) =
                          (mem (node t1 t2 t3) (Color.three :: et) ||
                            mem (node u1 u2 u3) (Color.three :: et))
                      rw [mem_cons]
                      change mem (union t3 u3) et = (mem t3 et || mem u3 et)
                      exact mem_union (h := h) (t := t3) (u := u3) et ht3 hu3

theorem mem_union_eq_true_iff
    {h : Nat} {t u : CTree} {et : ColSeq}
    (ht : Proper h t) (hu : Proper h u) :
    mem (union t u) et = true ↔
      mem t et = true ∨ mem u et = true := by
  rw [mem_union (h := h) (t := t) (u := u) et ht hu]
  simp

theorem mem_union_left
    {h : Nat} {t u : CTree} {et : ColSeq}
    (ht : Proper h t) (hu : Proper h u)
    (hmem : mem t et = true) :
    mem (union t u) et = true :=
  (mem_union_eq_true_iff (h := h) (t := t) (u := u) (et := et)
    ht hu).2 (Or.inl hmem)

theorem mem_union_right
    {h : Nat} {t u : CTree} {et : ColSeq}
    (ht : Proper h t) (hu : Proper h u)
    (hmem : mem u et = true) :
    mem (union t u) et = true :=
  (mem_union_eq_true_iff (h := h) (t := t) (u := u) (et := et)
    ht hu).2 (Or.inr hmem)

theorem proper_consE
    {h : Nat} {t : CTree}
    (ht : Proper h t) (e : Color) :
    Proper (h + 1) (consE e t) := by
  cases e with
  | zero =>
      simp [consE, cons0]
  | one =>
      exact proper_cons ht (proper_empty h) (proper_empty h)
  | two =>
      exact proper_cons (proper_empty h) ht (proper_empty h)
  | three =>
      exact proper_cons (proper_empty h) (proper_empty h) ht

theorem proper_ofTtail (et : ColSeq) :
    Proper et.length (ofTtail et) := by
  induction et with
  | nil =>
      exact proper_simpleLeaf
  | cons e et ih =>
      simpa [ofTtail] using proper_consE ih e

theorem proper_rotL : ∀ {h : Nat} {t : CTree}, Proper h t → Proper h (rotL t)
  | h, empty, _ => proper_empty h
  | 0, leaf lf, hlf => by
      simpa [rotL, Proper] using hlf
  | _ + 1, leaf _, hlf => by
      simp [Proper] at hlf
  | 0, node _ _ _, hnode => by
      simp [Proper] at hnode
  | h + 1, node t1 t2 t3, hnode => by
      rcases hnode with ⟨_, h1, h2, h3⟩
      exact proper_cons (proper_rotL h3) (proper_rotL h1) (proper_rotL h2)

theorem proper_rotR : ∀ {h : Nat} {t : CTree}, Proper h t → Proper h (rotR t)
  | h, empty, _ => proper_empty h
  | 0, leaf lf, hlf => by
      simpa [rotR, Proper] using hlf
  | _ + 1, leaf _, hlf => by
      simp [Proper] at hlf
  | 0, node _ _ _, hnode => by
      simp [Proper] at hnode
  | h + 1, node t1 t2 t3, hnode => by
      rcases hnode with ⟨_, h1, h2, h3⟩
      exact proper_cons (proper_rotR h2) (proper_rotR h3) (proper_rotR h1)

theorem size_rotL :
    ∀ (t : CTree), size (rotL t) = size t
  | empty => rfl
  | leaf _ => rfl
  | node t1 t2 t3 => by
      rw [rotL, size_cons]
      simp only [size_node, size_rotL t1, size_rotL t2, size_rotL t3]
      omega

theorem size_rotR :
    ∀ (t : CTree), size (rotR t) = size t
  | empty => rfl
  | leaf _ => rfl
  | node t1 t2 t3 => by
      rw [rotR, size_cons]
      simp only [size_node, size_rotR t1, size_rotR t2, size_rotR t3]
      omega

theorem sub_rotL :
    ∀ (t : CTree) (et : ColSeq),
      sub (rotL t) et = sub t (ColSeq.perm EdgePerm.p312 et)
  | empty, et => by
      cases et <;> simp [rotL, ColSeq.perm]
  | leaf lf, et => by
      cases et with
      | nil => rfl
      | cons e et =>
          cases e <;> rfl
  | node t1 t2 t3, [] => by
      simp [rotL, ColSeq.perm, sub_cons, sub]
  | node t1 t2 t3, Color.zero :: et => by
      simp [rotL, ColSeq.perm, EdgePerm.apply, sub_cons, sub]
  | node t1 t2 t3, Color.one :: et => by
      simpa [rotL, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotL t3 et
  | node t1 t2 t3, Color.two :: et => by
      simpa [rotL, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotL t1 et
  | node t1 t2 t3, Color.three :: et => by
      simpa [rotL, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotL t2 et

theorem mem_rotL (t : CTree) (et : ColSeq) :
    mem (rotL t) et = mem t (ColSeq.perm EdgePerm.p312 et) := by
  simp [mem, sub_rotL]

theorem sub_rotR :
    ∀ (t : CTree) (et : ColSeq),
      sub (rotR t) et = sub t (ColSeq.perm EdgePerm.p231 et)
  | empty, et => by
      cases et <;> simp [rotR, ColSeq.perm]
  | leaf lf, et => by
      cases et with
      | nil => rfl
      | cons e et =>
          cases e <;> rfl
  | node t1 t2 t3, [] => by
      simp [rotR, ColSeq.perm, sub_cons, sub]
  | node t1 t2 t3, Color.zero :: et => by
      simp [rotR, ColSeq.perm, EdgePerm.apply, sub_cons, sub]
  | node t1 t2 t3, Color.one :: et => by
      simpa [rotR, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotR t2 et
  | node t1 t2 t3, Color.two :: et => by
      simpa [rotR, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotR t3 et
  | node t1 t2 t3, Color.three :: et => by
      simpa [rotR, ColSeq.perm, EdgePerm.apply, sub_cons, sub] using sub_rotR t1 et

theorem mem_rotR (t : CTree) (et : ColSeq) :
    mem (rotR t) et = mem t (ColSeq.perm EdgePerm.p231 et) := by
  simp [mem, sub_rotR]

theorem proper_consRot
    {h : Nat} {t : CTree}
    (ht : Proper h t) :
    Proper (h + 1) (consRot t) := by
  exact proper_cons ht (proper_rotL ht) (proper_rotR ht)

theorem mem_consRot (t : CTree) (et : ColSeq) :
    mem (consRot t) et = mem t (ColSeq.ttail et) := by
  cases et with
  | nil =>
      change mem (cons t (rotL t) (rotR t)) [] = mem t (ColSeq.ttail [])
      rw [mem_cons]
      simp [ColSeq.ttail, ColSeq.ProperTrace, ColSeq.headColor,
        mem, sub]
  | cons e et =>
      cases e with
      | zero =>
          change mem (cons t (rotL t) (rotR t)) (Color.zero :: et) =
            mem t (ColSeq.ttail (Color.zero :: et))
          rw [mem_cons]
          simp [ColSeq.ttail, ColSeq.ProperTrace, ColSeq.headColor,
            mem_zero_of_mem]
      | one =>
          change mem (cons t (rotL t) (rotR t)) (Color.one :: et) =
            mem t (ColSeq.ttail (Color.one :: et))
          rw [mem_cons]
          simp [ColSeq.ttail, ColSeq.ProperTrace, ColSeq.headColor,
            EdgePerm.edgeRot, ColSeq.perm_id, mem, sub]
      | two =>
          change mem (cons t (rotL t) (rotR t)) (Color.two :: et) =
            mem t (ColSeq.ttail (Color.two :: et))
          rw [mem_cons]
          change mem (rotL t) et = mem t (ColSeq.perm EdgePerm.p312 et)
          exact mem_rotL t et
      | three =>
          change mem (cons t (rotL t) (rotR t)) (Color.three :: et) =
            mem t (ColSeq.ttail (Color.three :: et))
          rw [mem_cons]
          change mem (rotR t) et = mem t (ColSeq.perm EdgePerm.p231 et)
          exact mem_rotR t et

theorem unionRotLR_spec :
    ∀ (t u : CTree), unionRotLR t u = union (rotL t) (rotR u)
  | node t1 t2 t3, node u1 u2 u3 => by
      simp [unionRotLR, rotL, rotR, union_cons_cons,
        unionRotLR_spec t3 u2, unionRotLR_spec t1 u3,
        unionRotLR_spec t2 u1]
  | node _ _ _, leaf _ => rfl
  | node _ _ _, empty => rfl
  | leaf _, node _ _ _ => rfl
  | leaf _, leaf _ => rfl
  | leaf _, empty => rfl
  | empty, node _ _ _ => rfl
  | empty, leaf _ => rfl
  | empty, empty => rfl

theorem rotLR_spec (t : CTree) :
    rotLR t = union (rotL t) (rotR t) := by
  exact unionRotLR_spec t t

theorem size_rotLR_le (t : CTree) :
    size (rotLR t) ≤ 2 * size t := by
  rw [rotLR_spec]
  have h := size_union_le_add (rotL t) (rotR t)
  rw [size_rotL, size_rotR] at h
  omega

theorem proper_rotLR
    {h : Nat} {t : CTree}
    (ht : Proper h t) :
    Proper h (rotLR t) := by
  rw [rotLR_spec]
  exact proper_union (proper_rotL ht) (proper_rotR ht)

theorem mem_rotLR
    {h : Nat} {t : CTree}
    (ht : Proper h t) (et : ColSeq) :
    mem (rotLR t) et =
      (mem t (ColSeq.perm EdgePerm.p312 et) ||
        mem t (ColSeq.perm EdgePerm.p231 et)) := by
  rw [rotLR_spec]
  rw [mem_union (h := h) (t := rotL t) (u := rotR t)
    et (proper_rotL ht) (proper_rotR ht)]
  rw [mem_rotL, mem_rotR]

theorem sub_consE_same
    {e : Color} (hne : e ≠ Color.zero) (t : CTree) (et : ColSeq) :
    sub (consE e t) (e :: et) = sub t et := by
  cases e with
  | zero => exact False.elim (hne rfl)
  | one =>
      cases t <;> rfl
  | two =>
      cases t <;> rfl
  | three =>
      cases t <;> rfl

theorem consE_ne_empty_of_ne_empty
    {e : Color} {t : CTree}
    (hne : e ≠ Color.zero) (ht : t ≠ empty) :
    consE e t ≠ empty := by
  cases e with
  | zero => exact False.elim (hne rfl)
  | one =>
      cases t <;> simp [consE, cons1, cons] at ht ⊢
  | two =>
      cases t <;> simp [consE, cons2, cons] at ht ⊢
  | three =>
      cases t <;> simp [consE, cons3, cons] at ht ⊢

theorem mem_consE_of_ne_empty
    {e : Color} {t : CTree}
    (hne : e ≠ Color.zero) (ht : t ≠ empty) (et : ColSeq) :
    mem (consE e t) et =
      match et with
      | [] => false
      | c :: cs => if c = e then mem t cs else false := by
  cases et with
  | nil =>
      cases e with
      | zero => exact False.elim (hne rfl)
      | one =>
          cases t <;> simp [consE, cons1, cons, mem, sub] at ht ⊢
      | two =>
          cases t <;> simp [consE, cons2, cons, mem, sub] at ht ⊢
      | three =>
          cases t <;> simp [consE, cons3, cons, mem, sub] at ht ⊢
  | cons c cs =>
      cases e with
      | zero => exact False.elim (hne rfl)
      | one =>
          cases c <;> cases t <;>
            simp [consE, cons1, cons, mem, sub] at ht ⊢
      | two =>
          cases c <;> cases t <;>
            simp [consE, cons2, cons, mem, sub] at ht ⊢
      | three =>
          cases c <;> cases t <;>
            simp [consE, cons3, cons, mem, sub] at ht ⊢

theorem sub_ofTtail_self_of_not_mem_zero :
    ∀ {et : ColSeq}, Color.zero ∉ et → sub (ofTtail et) et = 1
  | [], _ => rfl
  | e :: et, hzero => by
      have hne : e ≠ Color.zero := by
        intro he
        exact hzero (by simp [he])
      have htail : Color.zero ∉ et := by
        intro hz
        exact hzero (by simp [hz])
      change sub (consE e (ofTtail et)) (e :: et) = 1
      rw [sub_consE_same hne, sub_ofTtail_self_of_not_mem_zero htail]

theorem mem_ofTtail_self_of_not_mem_zero
    {et : ColSeq}
    (hzero : Color.zero ∉ et) :
    mem (ofTtail et) et = true := by
  simp [mem, sub_ofTtail_self_of_not_mem_zero hzero]

theorem ofTtail_ne_empty_of_not_mem_zero :
    ∀ {et : ColSeq}, Color.zero ∉ et → ofTtail et ≠ empty
  | [], _ => by
      simp [ofTtail, simpleLeaf]
  | e :: et, hzero => by
      have hne : e ≠ Color.zero := by
        intro he
        exact hzero (by simp [he])
      have htail : Color.zero ∉ et := by
        intro hz
        exact hzero (by simp [hz])
      change consE e (ofTtail et) ≠ empty
      exact consE_ne_empty_of_ne_empty hne
        (ofTtail_ne_empty_of_not_mem_zero htail)

theorem mem_ofTtail_iff :
    ∀ {et et' : ColSeq}, Color.zero ∉ et →
      (mem (ofTtail et) et' = true ↔ et' = et)
  | [], et', _ => by
      cases et' <;> simp [ofTtail, simpleLeaf, mem, sub]
  | e :: et, et', hzero => by
      have hne : e ≠ Color.zero := by
        intro he
        exact hzero (by simp [he])
      have htail : Color.zero ∉ et := by
        intro hz
        exact hzero (by simp [hz])
      have htne := ofTtail_ne_empty_of_not_mem_zero htail
      cases et' with
      | nil =>
          change mem (consE e (ofTtail et)) [] = true ↔ [] = e :: et
          simp [mem_consE_of_ne_empty hne htne]
      | cons e' et'' =>
          change mem (consE e (ofTtail et)) (e' :: et'') = true ↔
            e' :: et'' = e :: et
          by_cases heq : e' = e
          · subst e'
            simp [mem_consE_of_ne_empty hne htne,
              mem_ofTtail_iff (et := et) (et' := et'') htail]
          · simp [mem_consE_of_ne_empty hne htne, heq]

theorem ofTtail_eq_empty_of_mem_zero :
    ∀ {et : ColSeq}, Color.zero ∈ et → ofTtail et = empty
  | [], hzero => by
      simp at hzero
  | e :: et, hzero => by
      by_cases he : e = Color.zero
      · subst e
        rfl
      · have htail : Color.zero ∈ et := by
          have he' : Color.zero ≠ e := by
            intro h
            exact he h.symm
          simpa [he'] using hzero
        have ih := ofTtail_eq_empty_of_mem_zero htail
        cases e with
        | zero => exact False.elim (he rfl)
        | one =>
            change consE Color.one (ofTtail et) = empty
            rw [ih]
            rfl
        | two =>
            change consE Color.two (ofTtail et) = empty
            rw [ih]
            rfl
        | three =>
            change consE Color.three (ofTtail et) = empty
            rw [ih]
            rfl

theorem mem_ofTtail_iff_total (et et' : ColSeq) :
    mem (ofTtail et) et' = true ↔ Color.zero ∉ et ∧ et' = et := by
  by_cases hzero : Color.zero ∈ et
  · rw [ofTtail_eq_empty_of_mem_zero hzero]
    simp [hzero]
  · constructor
    · intro hmem
      exact ⟨hzero, (mem_ofTtail_iff (et := et) (et' := et') hzero).1 hmem⟩
    · rintro ⟨_, rfl⟩
      exact mem_ofTtail_self_of_not_mem_zero hzero

end CTree

end FourColor

end Schematic.Math.GraphTheory
