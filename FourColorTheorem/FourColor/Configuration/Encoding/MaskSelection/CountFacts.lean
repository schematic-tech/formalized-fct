import FourColorTheorem.FourColor.Configuration.Encoding.MaskSelection.CombinedSelection

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask
theorem countTrue_le_length :
    ∀ bs : List Bool, countTrue bs ≤ bs.length
  | [] => by
      simp [countTrue]
  | b :: bs => by
      cases b
      · simp [countTrue]
        exact Nat.le_trans (countTrue_le_length bs) (Nat.le_succ bs.length)
      · have h := countTrue_le_length bs
        simp [countTrue]
        omega

theorem countTrue_eq_zero_iff :
    ∀ bs : List Bool, countTrue bs = 0 ↔ ∀ b ∈ bs, b = false
  | [] => by
      simp [countTrue]
  | b :: bs => by
      cases b <;> simp [countTrue, countTrue_eq_zero_iff bs]

theorem countTrue_pos_iff_exists_true :
    ∀ bs : List Bool, 0 < countTrue bs ↔ true ∈ bs
  | [] => by
      simp [countTrue]
  | b :: bs => by
      cases b
      · simpa [countTrue] using countTrue_pos_iff_exists_true bs
      · constructor
        · intro _
          simp
        · intro _
          simp [countTrue]
          omega

theorem countTrue_add_countFalse :
    ∀ bs : List Bool, countTrue bs + CProg.countFalse bs = bs.length
  | [] => by
      simp [countTrue, CProg.countFalse]
  | b :: bs => by
      cases b
      · have ih := countTrue_add_countFalse bs
        simp [countTrue, CProg.countFalse]
        omega
      · have ih := countTrue_add_countFalse bs
        simp [countTrue, CProg.countFalse]
        omega

theorem countFalse_add_countTrue (bs : List Bool) :
    CProg.countFalse bs + countTrue bs = bs.length := by
  simpa [Nat.add_comm] using countTrue_add_countFalse bs

theorem countFalse_eq_length_sub_countTrue (bs : List Bool) :
    CProg.countFalse bs = bs.length - countTrue bs := by
  have h := countTrue_add_countFalse bs
  omega

theorem countTrue_eq_length_sub_countFalse (bs : List Bool) :
    countTrue bs = bs.length - CProg.countFalse bs := by
  have h := countTrue_add_countFalse bs
  omega

theorem countFalse_eq_zero_iff (bs : List Bool) :
    CProg.countFalse bs = 0 ↔ ∀ b ∈ bs, b = true :=
  CProg.countFalse_eq_zero_iff bs

theorem countFalse_pos_iff_exists_false :
    ∀ bs : List Bool, 0 < CProg.countFalse bs ↔ false ∈ bs
  | [] => by
      simp [CProg.countFalse]
  | b :: bs => by
      cases b
      · constructor
        · intro _
          simp
        · intro _
          simp [CProg.countFalse]
          omega
      · simpa [CProg.countFalse] using countFalse_pos_iff_exists_false bs

/-- True iff a Boolean list contains a false entry. -/
def hasFalse : List Bool → Bool
  | [] => false
  | b :: bs => (!b) || hasFalse bs

theorem hasFalse_eq_false_iff :
    ∀ bs : List Bool, hasFalse bs = false ↔ ∀ b ∈ bs, b = true
  | [] => by
      simp [hasFalse]
  | b :: bs => by
      cases b <;> simp [hasFalse, hasFalse_eq_false_iff bs]

theorem hasFalse_eq_true_iff :
    ∀ bs : List Bool, hasFalse bs = true ↔ false ∈ bs
  | [] => by
      simp [hasFalse]
  | b :: bs => by
      cases b <;> simp [hasFalse, hasFalse_eq_true_iff bs]

theorem hasFalse_eq_true_iff_countFalse_pos (bs : List Bool) :
    hasFalse bs = true ↔ 0 < CProg.countFalse bs := by
  constructor
  · intro h
    exact (countFalse_pos_iff_exists_false bs).2
      ((hasFalse_eq_true_iff bs).1 h)
  · intro h
    exact (hasFalse_eq_true_iff bs).2
      ((countFalse_pos_iff_exists_false bs).1 h)

theorem countTrue_contractMask_eq_zero_iff
    (cp : CProg) (refs : List Nat) :
    countTrue (CProg.contractMask cp refs) = 0 ↔
      ∀ k, k < CProg.contractEdgeSize cp → k ∉ refs := by
  constructor
  · intro h k hk href
    have htrue : true ∈ CProg.contractMask cp refs :=
      (CProg.true_mem_contractMask_iff cp refs).2 ⟨k, hk, href⟩
    have hall := (countTrue_eq_zero_iff (CProg.contractMask cp refs)).1 h
    simpa using hall true htrue
  · intro h
    exact (countTrue_eq_zero_iff (CProg.contractMask cp refs)).2
      (by
        intro b hb
        cases b
        · rfl
        · rcases (CProg.true_mem_contractMask_iff cp refs).1 hb with
            ⟨k, hk, href⟩
          exact False.elim (h k hk href))

theorem countTrue_contractMaskRec_eq_length_selectedContractIndicesRec
    (refs : List Nat) :
    ∀ (i n : Nat),
      countTrue (CProg.contractMaskRec refs i n) =
        (CProg.selectedContractIndicesRec refs i n).length
  | i, 0 => by
      simp [CProg.contractMaskRec, CProg.selectedContractIndicesRec,
        countTrue]
  | i, n + 1 => by
      have ih :=
        countTrue_contractMaskRec_eq_length_selectedContractIndicesRec
          refs (i + 1) n
      by_cases h : i ∈ refs
      · simp [CProg.contractMaskRec, CProg.selectedContractIndicesRec,
          countTrue, h, ih, Nat.add_comm]
      · simp [CProg.contractMaskRec, CProg.selectedContractIndicesRec,
          countTrue, h, ih]

theorem countTrue_contractMask_eq_length_selectedContractIndices
    (cp : CProg) (refs : List Nat) :
    countTrue (CProg.contractMask cp refs) =
      (CProg.selectedContractIndices cp refs).length := by
  simp [CProg.contractMask, CProg.selectedContractIndices,
    countTrue_contractMaskRec_eq_length_selectedContractIndicesRec]

theorem countFalse_contractMask_eq_zero_iff
    (cp : CProg) (refs : List Nat) :
    CProg.countFalse (CProg.contractMask cp refs) = 0 ↔
      ∀ k, k < CProg.contractEdgeSize cp → k ∈ refs := by
  constructor
  · intro h k hk
    by_cases href : k ∈ refs
    · exact href
    · have hfalse : false ∈ CProg.contractMask cp refs :=
        (CProg.false_mem_contractMask_iff cp refs).2 ⟨k, hk, href⟩
      have hall := (CProg.countFalse_eq_zero_iff
        (CProg.contractMask cp refs)).1 h
      exact False.elim (by simpa using hall false hfalse)
  · intro h
    exact (CProg.countFalse_eq_zero_iff (CProg.contractMask cp refs)).2
      (by
        intro b hb
        cases b
        · rcases (CProg.false_mem_contractMask_iff cp refs).1 hb with
            ⟨k, hk, href⟩
          exact False.elim (href (h k hk))
        · rfl)

theorem hasFalse_contractMask_iff
    (cp : CProg) (refs : List Nat) :
    hasFalse (CProg.contractMask cp refs) = true ↔
      ∃ k, k < CProg.contractEdgeSize cp ∧ k ∉ refs := by
  rw [hasFalse_eq_true_iff, CProg.false_mem_contractMask_iff]


end CfMask

end FourColor

end Schematic.Math.GraphTheory
