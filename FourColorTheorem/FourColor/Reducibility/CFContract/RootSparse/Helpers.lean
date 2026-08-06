import FourColorTheorem.FourColor.Reducibility.CFContract.ContractBand

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

namespace CFContract.Internal

/-- Select values at positions where both Boolean masks are true. This is
the list-valued counterpart of the filtered intersection in Coq's four-edge
triad argument. -/
def selectBoth {α : Type _} :
    List Bool → List Bool → List α → List α
  | b :: bs, c :: cs, x :: xs =>
      if b && c then x :: selectBoth bs cs xs else selectBoth bs cs xs
  | _, _, _ => []

theorem selectBoth_sublist {α : Type _} :
    ∀ (m t : List Bool) (xs : List α),
      (selectBoth m t xs).Sublist xs
  | _m, _t, [] => by simp [selectBoth]
  | [], _t, _x :: xs => List.nil_sublist (_ :: xs)
  | _b :: _bs, [], _x :: xs => List.nil_sublist (_ :: xs)
  | b :: bs, c :: cs, x :: xs => by
      cases b <;> cases c
      · exact (selectBoth_sublist bs cs xs).cons x
      · exact (selectBoth_sublist bs cs xs).cons x
      · exact (selectBoth_sublist bs cs xs).cons x
      · exact (selectBoth_sublist bs cs xs).cons_cons x

theorem mem_selectBoth_masks {α : Type _} :
    ∀ {m t : List Bool} {xs : List α} {z : α},
      m.length = t.length →
      m.length = xs.length →
      z ∈ selectBoth m t xs →
      z ∈ CfMask.select m xs ∧ z ∈ CfMask.select t xs
  | [], t, xs, z, _hmt, _hmx, hz => by simp [selectBoth] at hz
  | _b :: _bs, [], _xs, _z, hmt, _hmx, _hz => by simp at hmt
  | _b :: _bs, _c :: _cs, [], _z, _hmt, hmx, _hz => by simp at hmx
  | b :: bs, c :: cs, x :: xs, z, hmt, hmx, hz => by
      have hmt' : bs.length = cs.length := by simpa using hmt
      have hmx' : bs.length = xs.length := by simpa using hmx
      cases b <;> cases c
      · have hrec := mem_selectBoth_masks hmt' hmx' hz
        simpa [selectBoth, CfMask.select] using hrec
      · have hrec := mem_selectBoth_masks hmt' hmx' hz
        exact ⟨by simpa [CfMask.select] using hrec.1,
          by simp [CfMask.select, hrec.2]⟩
      · have hrec := mem_selectBoth_masks hmt' hmx' hz
        exact ⟨by simp [CfMask.select, hrec.1],
          by simpa [CfMask.select] using hrec.2⟩
      · have hz' : z = x ∨ z ∈ selectBoth bs cs xs := by
          simpa [selectBoth] using hz
        rcases hz' with rfl | hz'
        · simp [CfMask.select]
        · have hrec := mem_selectBoth_masks hmt' hmx' hz'
          exact ⟨by simp [CfMask.select, hrec.1],
            by simp [CfMask.select, hrec.2]⟩

theorem length_selectBoth_eq_countTrue_select {α : Type _} :
    ∀ (m t : List Bool) (xs : List α),
      m.length = t.length →
      m.length = xs.length →
      (selectBoth m t xs).length =
        CfMask.countTrue (CfMask.select m t)
  | [], t, xs, hmt, hmx => by
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using hmt.symm)
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hmx.symm)
      subst t
      subst xs
      rfl
  | _b :: _bs, [], _xs, hmt, _hmx => by simp at hmt
  | _b :: _bs, _c :: _cs, [], _hmt, hmx => by simp at hmx
  | b :: bs, c :: cs, x :: xs, hmt, hmx => by
      have hmt' : bs.length = cs.length := by simpa using hmt
      have hmx' : bs.length = xs.length := by simpa using hmx
      cases b <;> cases c <;>
        simp [selectBoth, CfMask.select, CfMask.countTrue,
          length_selectBoth_eq_countTrue_select bs cs xs hmt' hmx',
          Nat.add_comm]

theorem exists_mem_select_not_mem_of_false_mem {α : Type _} :
    ∀ {m t : List Bool} {xs : List α},
      m.length = t.length →
      m.length = xs.length →
      xs.Nodup →
      false ∈ CfMask.select m t →
      ∃ z : α, z ∈ CfMask.select m xs ∧
        z ∉ CfMask.select t xs
  | [], t, xs, _hmt, _hmx, _hxs, hfalse => by
      simp [CfMask.select] at hfalse
  | _b :: _bs, [], _xs, hmt, _hmx, _hxs, _hfalse => by simp at hmt
  | _b :: _bs, _c :: _cs, [], _hmt, hmx, _hxs, _hfalse => by simp at hmx
  | b :: bs, c :: cs, x :: xs, hmt, hmx, hxs, hfalse => by
      have hmt' : bs.length = cs.length := by simpa using hmt
      have hmx' : bs.length = xs.length := by simpa using hmx
      have hxnot : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
      cases b <;> cases c
      · have hrec := exists_mem_select_not_mem_of_false_mem
          hmt' hmx' hxs' (by simpa [CfMask.select] using hfalse)
        rcases hrec with ⟨z, hzm, hzt⟩
        exact ⟨z, by simpa [CfMask.select] using hzm,
          by simpa [CfMask.select] using hzt⟩
      · have hrec := exists_mem_select_not_mem_of_false_mem
          hmt' hmx' hxs' (by simpa [CfMask.select] using hfalse)
        rcases hrec with ⟨z, hzm, hzt⟩
        have hzx : z ≠ x := by
          intro h
          subst z
          exact hxnot (CfMask.mem_of_mem_select hzm)
        exact ⟨z, by simpa [CfMask.select] using hzm,
          by simpa [CfMask.select, hzx] using hzt⟩
      · exact ⟨x, by simp [CfMask.select], by
          intro hx
          exact hxnot (CfMask.mem_of_mem_select
            (by simpa [CfMask.select] using hx))⟩
      · have hfalse' : false ∈ CfMask.select bs cs := by
          simpa [CfMask.select] using hfalse
        have hrec := exists_mem_select_not_mem_of_false_mem
          hmt' hmx' hxs' hfalse'
        rcases hrec with ⟨z, hzm, hzt⟩
        have hzx : z ≠ x := by
          intro h
          subst z
          exact hxnot (CfMask.mem_of_mem_select hzm)
        exact ⟨z, by simpa [CfMask.select, hzx] using hzm,
          by simpa [CfMask.select, hzx] using hzt⟩

theorem exists_three_prefix_of_two_lt_length {α : Type _}
    {xs : List α} (h : 2 < xs.length) :
    ∃ a b c rest, xs = a :: b :: c :: rest := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      cases xs with
      | nil => simp at h
      | cons b xs =>
          cases xs with
          | nil => simp at h
          | cons c rest => exact ⟨a, b, c, rest, rfl⟩

end CFContract.Internal

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
