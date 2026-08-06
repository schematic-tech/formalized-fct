import FourColorTheorem.FourColor.Configuration.Encoding.MaskSelection.ListSelection

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask
/-- Count true entries in a Boolean list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countTrue bs

theorem countTrue_append :
    ∀ (xs ys : List Bool),
      countTrue (xs ++ ys) = countTrue xs + countTrue ys
  | [], ys => by
      simp [countTrue]
  | x :: xs, ys => by
      cases x
      · simp [countTrue, countTrue_append xs ys]
      · simp [countTrue, countTrue_append xs ys, Nat.add_assoc]

theorem length_select_eq_countTrue_of_length {α : Type _} :
    ∀ (mask : List Bool) (xs : List α),
      xs.length = mask.length →
      (select mask xs).length = countTrue mask
  | [], [], _h => by
      simp [select, countTrue]
  | [], _ :: _, h => by
      simp at h
  | _ :: _, [], h => by
      simp at h
  | b :: bs, _ :: xs, h => by
      have hlen : xs.length = bs.length := by
        simpa using Nat.succ.inj h
      cases b
      · simp [select, countTrue,
          length_select_eq_countTrue_of_length bs xs hlen]
      · simp [select, countTrue,
          length_select_eq_countTrue_of_length bs xs hlen, Nat.add_comm]

theorem countFalse_eq_countTrue_map_not :
    ∀ mask : List Bool,
      CProg.countFalse mask = countTrue (mask.map Bool.not)
  | [] => rfl
  | b :: mask => by
      cases b <;>
        simp [CProg.countFalse, countTrue,
          countFalse_eq_countTrue_map_not mask]

theorem length_select_map_not_of_length {α : Type _}
    (mask : List Bool) (xs : List α) (h : xs.length = mask.length) :
    (select (mask.map Bool.not) xs).length = CProg.countFalse mask := by
  rw [countFalse_eq_countTrue_map_not,
    length_select_eq_countTrue_of_length]
  simpa using h

/-- Coq's `map_rot`/`mask_rot` calculation in the `cfctr` rotation branch.
The surviving boundary values are rotated by the number of uncontracted
entries in the moved mask prefix. -/
theorem rotateLeft_select_map_not_rotateRight {α : Type _}
    (n : Nat) (mask : List Bool) (xs : List α)
    (h : xs.length = mask.length) :
    CProg.rotateLeft
        (CProg.countFalse ((CProg.rotateRight n mask).take n))
        (select ((CProg.rotateRight n mask).map Bool.not) xs) =
      select (mask.map Bool.not) (CProg.rotateLeft n xs) := by
  by_cases hn : n ≤ mask.length
  · let k := mask.length - n
    have hdropMask : (mask.drop k).length = n := by
      simp [k]
      omega
    have htakeMask : (mask.take k).length = k := by
      simp [k]
    have htakeXs : (xs.take n).length = n := by
      simp [h, hn]
    have hdropXs : (xs.drop n).length = k := by
      simp [k, h]
    have hright :
        CProg.rotateRight n mask = mask.drop k ++ mask.take k := by
      rfl
    have htakeRight :
        (CProg.rotateRight n mask).take n = mask.drop k := by
      rw [hright]
      simp [hdropMask]
    have hselected :
        select ((CProg.rotateRight n mask).map Bool.not) xs =
          select ((mask.drop k).map Bool.not) (xs.take n) ++
            select ((mask.take k).map Bool.not) (xs.drop n) := by
      calc
        select ((CProg.rotateRight n mask).map Bool.not) xs =
            select (((mask.drop k).map Bool.not) ++
                ((mask.take k).map Bool.not))
              (xs.take n ++ xs.drop n) := by
            rw [hright, List.map_append, List.take_append_drop]
        _ = select ((mask.drop k).map Bool.not) (xs.take n) ++
              select ((mask.take k).map Bool.not) (xs.drop n) :=
            select_append_of_length _ _ _ _ (by
              simpa only [List.length_map] using
                htakeXs.trans hdropMask.symm)
    have htarget :
        select (mask.map Bool.not) (CProg.rotateLeft n xs) =
          select ((mask.take k).map Bool.not) (xs.drop n) ++
            select ((mask.drop k).map Bool.not) (xs.take n) := by
      calc
        select (mask.map Bool.not) (CProg.rotateLeft n xs) =
            select (((mask.take k).map Bool.not) ++
                ((mask.drop k).map Bool.not))
              (xs.drop n ++ xs.take n) := by
            rw [← List.map_append, List.take_append_drop]
            rfl
        _ = select ((mask.take k).map Bool.not) (xs.drop n) ++
              select ((mask.drop k).map Bool.not) (xs.take n) :=
            select_append_of_length _ _ _ _ (by
              simpa only [List.length_map] using
                hdropXs.trans htakeMask.symm)
    let front := select ((mask.drop k).map Bool.not) (xs.take n)
    let back := select ((mask.take k).map Bool.not) (xs.drop n)
    have hcount :
        CProg.countFalse ((CProg.rotateRight n mask).take n) =
          front.length := by
      rw [htakeRight]
      exact (length_select_map_not_of_length (mask.drop k) (xs.take n)
        (htakeXs.trans hdropMask.symm)).symm
    rw [hselected, htarget, hcount]
    change CProg.rotateLeft front.length (front ++ back) = back ++ front
    simp [CProg.rotateLeft]
  · have hoversize : mask.length ≤ n := Nat.le_of_not_ge hn
    have hxoversize : xs.length ≤ n := by simpa [h] using hoversize
    rw [CProg.rotateLeft_oversize hxoversize]
    have hright : CProg.rotateRight n mask = mask := by
      simp [CProg.rotateRight, Nat.sub_eq_zero_of_le hoversize]
    rw [hright, (List.take_eq_self_iff mask).2 hoversize]
    have hlen := length_select_map_not_of_length mask xs h
    rw [← hlen]
    exact CProg.rotateLeft_oversize (by rfl)

end CfMask

end FourColor

end Schematic.Math.GraphTheory
