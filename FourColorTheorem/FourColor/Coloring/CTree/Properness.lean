import FourColorTheorem.FourColor.Coloring.CTree.BasicSemantics

/-! Uniform-depth properness and size bounds for trace-coloring trees. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CTree

@[simp]
theorem proper_empty (h : Nat) :
    Proper h empty := by
  cases h <;> trivial

theorem proper_leafOf (n : Nat) :
    Proper 0 (leafOf n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simpa [leafOf, Proper] using ih

theorem proper_zero_eq_leafOf_sub_nil
    {t : CTree} (ht : Proper 0 t) :
    t = leafOf (sub t []) := by
  induction t with
  | empty =>
      rfl
  | leaf lf ih =>
      calc
        leaf lf = leaf (leafOf (sub lf [])) := by
          exact congrArg leaf (ih ht)
        _ = leafOf (sub (leaf lf) []) := rfl
  | node t1 t2 t3 ih1 ih2 ih3 =>
      simp [Proper] at ht

theorem proper_simpleLeaf :
    Proper 0 simpleLeaf := by
  simp [simpleLeaf, Proper]

theorem proper_cons
    {h : Nat} {t1 t2 t3 : CTree}
    (h1 : Proper h t1) (h2 : Proper h t2) (h3 : Proper h t3) :
    Proper (h + 1) (cons t1 t2 t3) := by
  cases t1 <;> cases t2 <;> cases t3 <;>
    simp [cons, Proper, emptyNode] at h1 h2 h3 ⊢
  all_goals
    first
    | exact h1
    | exact h2
    | exact h3
    | repeat' constructor <;> first | assumption | trivial

theorem proper_union :
    ∀ {h : Nat} {t u : CTree}, Proper h t → Proper h u → Proper h (union t u)
  | 0, t, u, ht, hu => by
      cases t <;> cases u <;> simp [union, Proper] at ht hu ⊢
      all_goals first | exact ht | exact hu | exact proper_simpleLeaf
  | h + 1, t, u, ht, hu => by
      cases t with
      | empty =>
          simpa [union] using hu
      | leaf lf =>
          simp [Proper] at ht
      | node t1 t2 t3 =>
          cases u with
          | empty =>
              simpa [union] using ht
          | leaf lf =>
              simp [Proper] at hu
          | node u1 u2 u3 =>
              rcases ht with ⟨_, ht1, ht2, ht3⟩
              rcases hu with ⟨_, hu1, hu2, hu3⟩
              exact proper_cons
                (proper_union ht1 hu1)
                (proper_union ht2 hu2)
                (proper_union ht3 hu3)

theorem length_of_mem_of_proper :
    ∀ {h : Nat} {t : CTree} {et : ColSeq},
      Proper h t → mem t et = true → et.length = h
  | _, empty, et, _, hmem => by
      simp [mem, sub_empty] at hmem
  | 0, leaf lf, [], _, _ => rfl
  | 0, leaf lf, c :: et, hproper, hmem => by
      simp [mem, sub] at hmem
  | h + 1, leaf lf, et, hproper, _ => by
      simp [Proper] at hproper
  | 0, node t1 t2 t3, et, hproper, _ => by
      simp [Proper] at hproper
  | h + 1, node t1 t2 t3, [], hproper, hmem => by
      simp [mem, sub] at hmem
  | h + 1, node t1 t2 t3, Color.zero :: et, hproper, hmem => by
      simp [mem, sub] at hmem
  | h + 1, node t1 t2 t3, Color.one :: et, hproper, hmem => by
      rcases hproper with ⟨_, ht1, _, _⟩
      have hlen := length_of_mem_of_proper ht1 hmem
      simp [hlen]
  | h + 1, node t1 t2 t3, Color.two :: et, hproper, hmem => by
      rcases hproper with ⟨_, _, ht2, _⟩
      have hlen := length_of_mem_of_proper ht2 hmem
      simp [hlen]
  | h + 1, node t1 t2 t3, Color.three :: et, hproper, hmem => by
      rcases hproper with ⟨_, _, _, ht3⟩
      have hlen := length_of_mem_of_proper ht3 hmem
      simp [hlen]

theorem not_mem_zero_of_mem :
    ∀ {t : CTree} {et : ColSeq}, mem t et = true → Color.zero ∉ et
  | empty, et, hmem => by
      simp [mem, sub_empty] at hmem
  | leaf lf, [], _ => by
      simp
  | leaf lf, c :: et, hmem => by
      simp [mem, sub] at hmem
  | node t1 t2 t3, [], _ => by
      simp
  | node t1 t2 t3, Color.zero :: et, hmem => by
      simp [mem, sub] at hmem
  | node t1 t2 t3, Color.one :: et, hmem => by
      have htail := not_mem_zero_of_mem (t := t1) (et := et) hmem
      simpa using htail
  | node t1 t2 t3, Color.two :: et, hmem => by
      have htail := not_mem_zero_of_mem (t := t2) (et := et) hmem
      simpa using htail
  | node t1 t2 t3, Color.three :: et, hmem => by
      have htail := not_mem_zero_of_mem (t := t3) (et := et) hmem
      simpa using htail

theorem eq_empty_of_proper_size_zero :
    ∀ {h : Nat} {t : CTree}, Proper h t → size t = 0 → t = empty
  | _, empty, _, _ => rfl
  | 0, leaf lf, _, hsize => by
      simp at hsize
  | h + 1, leaf lf, hproper, _ => by
      simp [Proper] at hproper
  | 0, node t1 t2 t3, hproper, _ => by
      simp [Proper] at hproper
  | h + 1, node t1 t2 t3, hproper, hsize => by
      rcases hproper with ⟨hnonempty, ht1, ht2, ht3⟩
      have hs1 : size t1 = 0 := by
        simp only [size_node] at hsize
        omega
      have hs2 : size t2 = 0 := by
        simp only [size_node] at hsize
        omega
      have hs3 : size t3 = 0 := by
        simp only [size_node] at hsize
        omega
      have e1 := eq_empty_of_proper_size_zero ht1 hs1
      have e2 := eq_empty_of_proper_size_zero ht2 hs2
      have e3 := eq_empty_of_proper_size_zero ht3 hs3
      subst t1
      subst t2
      subst t3
      simp [emptyNode] at hnonempty

theorem size_le_pow_three_of_proper :
    ∀ {h : Nat} {t : CTree}, Proper h t → size t ≤ 3 ^ h
  | h, empty, _ => by
      simp
  | 0, leaf lf, _ => by
      simp
  | h + 1, leaf lf, hproper => by
      simp [Proper] at hproper
  | 0, node t1 t2 t3, hproper => by
      simp [Proper] at hproper
  | h + 1, node t1 t2 t3, hproper => by
      rcases hproper with ⟨_, ht1, ht2, ht3⟩
      have h1 := size_le_pow_three_of_proper ht1
      have h2 := size_le_pow_three_of_proper ht2
      have h3 := size_le_pow_three_of_proper ht3
      calc
        size (node t1 t2 t3)
            ≤ 3 ^ h + (3 ^ h + 3 ^ h) := by
              simp only [size_node]
              omega
        _ = 3 ^ h * 3 := by omega
        _ = 3 ^ (h + 1) := by
              simp [Nat.pow_add]

theorem size_eq_zero_of_no_mem :
    ∀ (t : CTree), (∀ et : ColSeq, mem t et = false) → size t = 0
  | empty, _ => rfl
  | leaf lf, hmem => by
      have h := hmem []
      simp [mem, sub] at h
  | node t1 t2 t3, hmem => by
      have h1 : size t1 = 0 :=
        size_eq_zero_of_no_mem t1 (by
          intro et
          have h := hmem (Color.one :: et)
          simpa [mem, sub] using h)
      have h2 : size t2 = 0 :=
        size_eq_zero_of_no_mem t2 (by
          intro et
          have h := hmem (Color.two :: et)
          simpa [mem, sub] using h)
      have h3 : size t3 = 0 :=
        size_eq_zero_of_no_mem t3 (by
          intro et
          have h := hmem (Color.three :: et)
          simpa [mem, sub] using h)
      simp [h1, h2, h3]

theorem eq_empty_of_proper_no_mem
    {h : Nat} {t : CTree}
    (ht : Proper h t)
    (hmem : ∀ et : ColSeq, mem t et = false) :
    t = empty :=
  eq_empty_of_proper_size_zero ht (size_eq_zero_of_no_mem t hmem)

end CTree

end FourColor

end Schematic.Math.GraphTheory
