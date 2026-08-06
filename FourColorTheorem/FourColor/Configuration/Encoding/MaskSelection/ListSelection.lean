import FourColorTheorem.FourColor.Configuration.Encoding.MaskSelection.MaskDefinitions

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask
/-- Select elements under a Boolean mask.  This is the syntax-level counterpart
of MathComp's `mask`. -/
def select {α : Type _} : List Bool → List α → List α
  | b :: bs, x :: xs => if b then x :: select bs xs else select bs xs
  | _, _ => []

theorem length_select_le {α : Type _} :
    ∀ (mask : List Bool) (xs : List α), (select mask xs).length ≤ xs.length
  | [], xs => by
      simp [select]
  | _ :: _, [] => by
      simp [select]
  | b :: bs, _ :: xs => by
      by_cases hb : b = true
      · simp [select, hb]
        exact length_select_le bs xs
      · have hbfalse : b = false := by
          cases b <;> simp at hb ⊢
        simp [select, hbfalse]
        exact Nat.le_trans (length_select_le bs xs) (Nat.le_succ xs.length)

theorem mem_of_mem_select {α : Type _} :
    ∀ {mask : List Bool} {xs : List α} {x : α},
      x ∈ select mask xs → x ∈ xs
  | [], xs, x, hx => by
      simp [select] at hx
  | _ :: _, [], x, hx => by
      simp [select] at hx
  | b :: bs, y :: ys, x, hx => by
      cases b <;> simp [select] at hx ⊢
      · exact Or.inr (mem_of_mem_select hx)
      · rcases hx with rfl | hx
        · simp
        · exact Or.inr (mem_of_mem_select hx)

theorem select_map {α β : Type _} (f : α → β) :
    ∀ (mask : List Bool) (xs : List α),
      select mask (xs.map f) = (select mask xs).map f
  | [], _xs => by
      simp [select]
  | _ :: _, [] => by
      simp [select]
  | b :: bs, x :: xs => by
      cases b <;> simp [select, select_map f bs xs]

theorem select_map_tail {α β : Type _} (f : α → β) :
    ∀ (mask : List Bool) (xs : List α),
      select mask ((xs.map f).tail) = (select mask xs.tail).map f
  | [], _xs => by
      simp [select]
  | _ :: _, [] => by
      simp [select]
  | mask, _ :: xs => by
      simpa using select_map f mask xs

theorem select_map_drop {α β : Type _} (f : α → β) (n : Nat)
    (mask : List Bool) (xs : List α) :
    select mask ((xs.map f).drop n) = (select mask (xs.drop n)).map f := by
  simpa [List.map_drop] using select_map f mask (xs.drop n)

/-- A mask made only of `false` bits selects no entries. -/
theorem select_replicate_false {α : Type _} :
    ∀ (n : Nat) (xs : List α),
      select (List.replicate n false) xs = []
  | 0, xs => by
      simp [select]
  | n + 1, [] => by
      simp [select]
  | n + 1, _ :: xs => by
      change select (false :: List.replicate n false) (_ :: xs) = []
      simp [select, select_replicate_false n xs]

/-- A full-length mask made only of `true` bits selects the whole list. -/
theorem select_replicate_true_length {α : Type _} :
    ∀ xs : List α, select (List.replicate xs.length true) xs = xs
  | [] => by
      simp [select]
  | x :: xs => by
      change select (true :: List.replicate xs.length true) (x :: xs) =
        x :: xs
      simp [select, select_replicate_true_length xs]

/-- A matching all-true mask selects the whole list. -/
theorem select_eq_self_of_all_true {α : Type _} :
    ∀ (mask : List Bool) (xs : List α),
      xs.length = mask.length →
        (∀ b ∈ mask, b = true) →
          select mask xs = xs
  | [], [], _hlen, _hall => by
      simp [select]
  | [], _ :: _, hlen, _hall => by
      simp at hlen
  | _ :: _, [], hlen, _hall => by
      simp at hlen
  | b :: bs, x :: xs, hlen, hall => by
      have hb : b = true := hall b (by simp)
      have htail : ∀ c ∈ bs, c = true := by
        intro c hc
        exact hall c (by simp [hc])
      have hlenTail : xs.length = bs.length := by
        simpa using Nat.succ.inj hlen
      simp [select, hb, select_eq_self_of_all_true bs xs hlenTail htail]

/-- Mapping a constant over a list produces a replicate list of the same
length. -/
theorem map_const_eq_replicate {α β : Type _} (b : β) :
    ∀ xs : List α, xs.map (fun _ => b) = List.replicate xs.length b
  | [] => by
      simp
  | _ :: xs => by
      change b :: xs.map (fun _ => b) = b :: List.replicate xs.length b
      simp [map_const_eq_replicate b xs]

/-- A one-hot mask over `range xs.length` selects exactly the indexed element,
if that index is in range. -/
theorem select_kernelIndex_getElem? {α : Type _} :
    ∀ (xs : List α) (i : Nat),
      select ((List.range xs.length).map (fun j => j == i)) xs =
        match xs[i]? with
        | some x => [x]
        | none => []
  | [], i => by
      simp [select]
  | x :: xs, 0 => by
      change select ((List.range (xs.length + 1)).map (fun j => j == 0))
          (x :: xs) =
        match (x :: xs)[0]? with
        | some x => [x]
        | none => []
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      have hmap :
          List.map ((fun j => j == 0) ∘ Nat.succ) (List.range xs.length) =
            List.map (fun _ : Nat => false) (List.range xs.length) := by
        apply List.map_congr_left
        intro j _hj
        simp
      rw [hmap]
      simp [select]
      exact select_replicate_false xs.length xs
  | x :: xs, i + 1 => by
      change select ((List.range (xs.length + 1)).map (fun j => j == i + 1))
          (x :: xs) =
        match (x :: xs)[i + 1]? with
        | some x => [x]
        | none => []
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      have hmap :
          List.map ((fun j => j == i + 1) ∘ Nat.succ)
              (List.range xs.length) =
            List.map (fun j => j == i) (List.range xs.length) := by
        apply List.map_congr_left
        intro j _hj
        simp
      rw [hmap]
      simp [select, select_kernelIndex_getElem? xs i,
        List.getElem?_cons_succ]

/-- Split a mask selection across matching list concatenation. -/
theorem select_append_of_length {α : Type _} :
    ∀ (mask₁ mask₂ : List Bool) (xs₁ xs₂ : List α),
      xs₁.length = mask₁.length →
      select (mask₁ ++ mask₂) (xs₁ ++ xs₂) =
        select mask₁ xs₁ ++ select mask₂ xs₂
  | [], mask₂, [], xs₂, _h => by
      simp [select]
  | [], mask₂, _ :: xs₁, xs₂, h => by
      simp at h
  | b :: mask₁, mask₂, [], xs₂, h => by
      simp at h
  | b :: mask₁, mask₂, x :: xs₁, xs₂, h => by
      have hlen : xs₁.length = mask₁.length := by
        simpa using Nat.succ.inj h
      cases b <;>
        simp [select, select_append_of_length mask₁ mask₂ xs₁ xs₂ hlen]

theorem select_take_append_drop_of_length {α : Type _}
    (k : Nat) {mask : List Bool} {xs : List α}
    (h : xs.length = mask.length) :
    select mask xs =
      select (mask.take k) (xs.take k) ++
        select (mask.drop k) (xs.drop k) := by
  calc
    select mask xs =
        select (mask.take k ++ mask.drop k)
          (xs.take k ++ xs.drop k) := by
      rw [List.take_append_drop, List.take_append_drop]
    _ =
        select (mask.take k) (xs.take k) ++
          select (mask.drop k) (xs.drop k) := by
      exact select_append_of_length (mask.take k) (mask.drop k)
        (xs.take k) (xs.drop k) (by simp [h])

theorem mem_select_rotateLeft_iff_of_length {α : Type _}
    (n : Nat) {mask : List Bool} {xs : List α} {x : α}
    (h : xs.length = mask.length) :
    x ∈ select (CProg.rotateLeft n mask) (CProg.rotateLeft n xs) ↔
      x ∈ select mask xs := by
  let k := n
  have hrot :
      select (CProg.rotateLeft n mask) (CProg.rotateLeft n xs) =
        select (mask.drop k) (xs.drop k) ++
          select (mask.take k) (xs.take k) := by
    simpa [CProg.rotateLeft, k] using
      select_append_of_length (mask.drop k) (mask.take k)
        (xs.drop k) (xs.take k) (by simp [h])
  have hbase :=
    select_take_append_drop_of_length (α := α) k (mask := mask)
      (xs := xs) h
  rw [hrot, hbase, List.mem_append, List.mem_append]
  exact or_comm

theorem mem_select_rotateRight_iff_of_length {α : Type _}
    (n : Nat) {mask : List Bool} {xs : List α} {x : α}
    (h : xs.length = mask.length) :
    x ∈ select (CProg.rotateRight n mask) (CProg.rotateRight n xs) ↔
      x ∈ select mask xs := by
  simpa [CProg.rotateRight, CProg.rotateLeft, h] using
    mem_select_rotateLeft_iff_of_length (α := α)
      (mask.length - n) h

theorem mem_select_rotateRight_mask_rotateLeft_values_iff_of_length
    {α : Type _} (n : Nat) {mask : List Bool} {xs : List α} {x : α}
    (h : xs.length = mask.length) :
    x ∈ select (CProg.rotateRight n mask) xs ↔
      x ∈ select mask (CProg.rotateLeft n xs) := by
  by_cases hn : n ≤ mask.length
  · let k := mask.length - n
    have hlen₁ : (xs.take n).length = (mask.drop k).length := by
      simp [k, h, hn]
      omega
    have hlen₂ : (xs.drop n).length = (mask.take k).length := by
      simp [k, h]
    have hleft :
        select (CProg.rotateRight n mask) xs =
          select (mask.drop k) (xs.take n) ++
            select (mask.take k) (xs.drop n) := by
      calc
        select (CProg.rotateRight n mask) xs =
            select (mask.drop k ++ mask.take k)
              (xs.take n ++ xs.drop n) := by
          rw [List.take_append_drop n xs]
          simp [CProg.rotateRight, k]
        _ = select (mask.drop k) (xs.take n) ++
              select (mask.take k) (xs.drop n) :=
          select_append_of_length (mask.drop k) (mask.take k)
            (xs.take n) (xs.drop n) hlen₁
    have hright :
        select mask (CProg.rotateLeft n xs) =
          select (mask.take k) (xs.drop n) ++
            select (mask.drop k) (xs.take n) := by
      calc
        select mask (CProg.rotateLeft n xs) =
            select (mask.take k ++ mask.drop k)
              (xs.drop n ++ xs.take n) := by
          rw [List.take_append_drop k mask]
          rfl
        _ = select (mask.take k) (xs.drop n) ++
              select (mask.drop k) (xs.take n) :=
          select_append_of_length (mask.take k) (mask.drop k)
            (xs.drop n) (xs.take n) hlen₂
    rw [hleft, hright, List.mem_append, List.mem_append]
    exact or_comm
  · have hnmask : mask.length ≤ n := Nat.le_of_not_ge hn
    have hnxs : xs.length ≤ n := by simpa [h] using hnmask
    rw [CProg.rotateLeft_oversize hnxs]
    simp [CProg.rotateRight, Nat.sub_eq_zero_of_le hnmask]

end CfMask

end FourColor

end Schematic.Math.GraphTheory
