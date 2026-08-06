import FourColorTheorem.FourColor.Configuration.Encoding.MaskAdjustment

/-! Kernel-triad selection and valid contract masks. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask

/-- Selected ring/kernel entries used by one kernel triad test. -/
def triadSelected (contractMask : CfMask) (cp : CProg) (i : Nat) :
    List Bool :=
  let target := adjMask (kernelSingleton cp i) cp
  select contractMask.ring target.ring ++
    select contractMask.kernel target.kernel

theorem triadSelected_eq_selectMask
    (contractMask : CfMask) (cp : CProg) (i : Nat) :
    triadSelected contractMask cp i =
      selectMask contractMask
        (adjMask (kernelSingleton cp i) cp).ring
        (adjMask (kernelSingleton cp i) cp).kernel := by
  simp [triadSelected, selectMask]

theorem mem_of_mem_triadSelected
    {contractMask : CfMask} {cp : CProg} {i : Nat} {b : Bool}
    (hb : b ∈ triadSelected contractMask cp i) :
    b ∈ (adjMask (kernelSingleton cp i) cp).ring ∨
      b ∈ (adjMask (kernelSingleton cp i) cp).kernel := by
  rw [triadSelected_eq_selectMask] at hb
  exact mem_of_mem_selectMask hb

theorem length_triadSelected_le
    (contractMask : CfMask) (cp : CProg) (i : Nat) :
    (triadSelected contractMask cp i).length ≤
      (adjMask (kernelSingleton cp i) cp).ring.length +
        (adjMask (kernelSingleton cp i) cp).kernel.length := by
  rw [triadSelected_eq_selectMask]
  exact length_selectMask_le contractMask
    (adjMask (kernelSingleton cp i) cp).ring
    (adjMask (kernelSingleton cp i) cp).kernel

theorem cpadj_proper_kernelSingleton (cp : CProg) (i : Nat) :
    Proper cp (adjMask (kernelSingleton cp i) cp) :=
  cpadj_proper cp (kernelSingleton cp i)
    (proper_kernelSingleton cp i)

theorem length_triadSelected_eq_countTrue_of_proper
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (hm : Proper cp contractMask) :
    (triadSelected contractMask cp i).length =
      countTrue contractMask.ring + countTrue contractMask.kernel := by
  have htarget := cpadj_proper_kernelSingleton cp i
  rw [triadSelected_eq_selectMask]
  exact length_selectMask_eq_countTrue_of_lengths contractMask
    (by rw [htarget.1, hm.1])
    (by rw [htarget.2, hm.2])

/-- One kernel triad test used by Coq's contract validity checker. -/
def triadAt (contractMask : CfMask) (cp : CProg) (i : Nat) : Bool :=
  hasFalse (triadSelected contractMask cp i) &&
    (2 < countTrue (triadSelected contractMask cp i))

/-- Source-side witnesses extracted from a successful kernel triad test. -/
def triadAtSources (contractMask : CfMask) (cp : CProg) (i : Nat) :
    Prop :=
  (false ∈ select contractMask.ring
      (adjMask (kernelSingleton cp i) cp).ring ∨
    false ∈ select contractMask.kernel
      (adjMask (kernelSingleton cp i) cp).kernel) ∧
  (true ∈ select contractMask.ring
      (adjMask (kernelSingleton cp i) cp).ring ∨
    true ∈ select contractMask.kernel
      (adjMask (kernelSingleton cp i) cp).kernel)

theorem mem_triadSelected_iff
    {contractMask : CfMask} {cp : CProg} {i : Nat} {b : Bool} :
    b ∈ triadSelected contractMask cp i ↔
      b ∈ select contractMask.ring
        (adjMask (kernelSingleton cp i) cp).ring ∨
      b ∈ select contractMask.kernel
        (adjMask (kernelSingleton cp i) cp).kernel := by
  simp [triadSelected]

/-- Kernel triad search used by Coq's contract validity checker. -/
def triad (contractMask : CfMask) (cp : CProg) : Nat → Bool
  | 0 => false
  | i + 1 =>
      if triadAt contractMask cp i then
        true
      else
        triad contractMask cp i

theorem triadAt_hasFalse
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    hasFalse (triadSelected contractMask cp i) = true := by
  unfold triadAt at h
  simp at h
  exact h.1

theorem triadAt_countTrue_gt_two
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    2 < countTrue (triadSelected contractMask cp i) := by
  unfold triadAt at h
  simp at h
  exact h.2

theorem triadAt_contractMask_countTrue_gt_two_of_proper
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (hm : Proper cp contractMask)
    (h : triadAt contractMask cp i = true) :
    2 < countTrue contractMask.ring + countTrue contractMask.kernel := by
  have htriad := triadAt_countTrue_gt_two h
  have hle := countTrue_le_length (triadSelected contractMask cp i)
  have hlen := length_triadSelected_eq_countTrue_of_proper
    (contractMask := contractMask) (cp := cp) (i := i) hm
  omega

theorem triadAt_exists_false
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    false ∈ triadSelected contractMask cp i :=
  (hasFalse_eq_true_iff (triadSelected contractMask cp i)).1
    (triadAt_hasFalse h)

theorem triadAt_countTrue_pos
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    0 < countTrue (triadSelected contractMask cp i) :=
  Nat.lt_trans (by decide : 0 < 2) (triadAt_countTrue_gt_two h)

theorem triadAt_exists_true
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    true ∈ triadSelected contractMask cp i :=
  (countTrue_pos_iff_exists_true (triadSelected contractMask cp i)).1
    (triadAt_countTrue_pos h)

theorem triadAt_exists_false_source
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    false ∈ select contractMask.ring
        (adjMask (kernelSingleton cp i) cp).ring ∨
      false ∈ select contractMask.kernel
        (adjMask (kernelSingleton cp i) cp).kernel :=
  mem_triadSelected_iff.1 (triadAt_exists_false h)

theorem triadAt_exists_true_source
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    true ∈ select contractMask.ring
        (adjMask (kernelSingleton cp i) cp).ring ∨
      true ∈ select contractMask.kernel
        (adjMask (kernelSingleton cp i) cp).kernel :=
  mem_triadSelected_iff.1 (triadAt_exists_true h)

theorem triadAt_sources
    {contractMask : CfMask} {cp : CProg} {i : Nat}
    (h : triadAt contractMask cp i = true) :
    triadAtSources contractMask cp i :=
  ⟨triadAt_exists_false_source h, triadAt_exists_true_source h⟩

theorem triad_true_iff_exists_triadAt
    (contractMask : CfMask) (cp : CProg) :
    ∀ n : Nat,
      triad contractMask cp n = true ↔
        ∃ i, i < n ∧ triadAt contractMask cp i = true
  | 0 => by
      simp [triad]
  | n + 1 => by
      by_cases hAt : triadAt contractMask cp n = true
      · constructor
        · intro _
          exact ⟨n, Nat.lt_succ_self n, hAt⟩
        · intro _
          simp [triad, hAt]
      · constructor
        · intro h
          have hprev : triad contractMask cp n = true := by
            simpa [triad, hAt] using h
          rcases (triad_true_iff_exists_triadAt contractMask cp n).1 hprev with
            ⟨i, hi, htriad⟩
          exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n), htriad⟩
        · rintro ⟨i, hi, htriad⟩
          have hin : i < n := by
            by_cases hin : i < n
            · exact hin
            · have hi_le : i ≤ n := Nat.le_of_lt_succ hi
              have hni : n ≤ i := Nat.le_of_not_gt hin
              have hieq : i = n := Nat.le_antisymm hi_le hni
              exact False.elim (hAt (by simpa [hieq] using htriad))
          have hprev : triad contractMask cp n = true :=
            (triad_true_iff_exists_triadAt contractMask cp n).2
              ⟨i, hin, htriad⟩
          simpa [triad, hAt] using hprev

theorem triad_exists_triadAt_of_eq_true
    {contractMask : CfMask} {cp : CProg} {n : Nat}
    (h : triad contractMask cp n = true) :
    ∃ i, i < n ∧ triadAt contractMask cp i = true :=
  (triad_true_iff_exists_triadAt contractMask cp n).1 h

/-- Syntax-level validity predicate for a contract mask, matching Coq's
`valid_ctrm`. -/
def validContractMask (cm : List Bool) (cp : CProg) : Bool :=
  let n := countTrue cm
  if n = 4 then triad (contractBand cm cp) cp (CProg.kernelSize cp)
  else 0 < n && n ≤ 3

theorem validContractMask_countTrue_pos
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true) :
    0 < countTrue cm := by
  unfold validContractMask at h
  by_cases hfour : countTrue cm = 4
  · omega
  · simp [hfour] at h
    exact h.1

theorem validContractMask_exists_true
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true) :
    true ∈ cm :=
  (countTrue_pos_iff_exists_true cm).1
    (validContractMask_countTrue_pos h)

theorem validContractMask_countTrue_le_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true) :
    countTrue cm ≤ 4 := by
  unfold validContractMask at h
  by_cases hfour : countTrue cm = 4
  · omega
  · simp [hfour] at h
    omega

theorem validContractMask_countFalse_pos_of_length_gt_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hlen : 4 < cm.length) :
    0 < CProg.countFalse cm := by
  have hle := validContractMask_countTrue_le_four h
  have hsum := countTrue_add_countFalse cm
  omega

theorem validContractMask_exists_false_of_length_gt_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hlen : 4 < cm.length) :
    false ∈ cm :=
  (countFalse_pos_iff_exists_false cm).1
    (validContractMask_countFalse_pos_of_length_gt_four h hlen)

theorem validContractMask_hasFalse_of_length_gt_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hlen : 4 < cm.length) :
    hasFalse cm = true :=
  (hasFalse_eq_true_iff cm).2
    (validContractMask_exists_false_of_length_gt_four h hlen)

theorem validContractMask_triad_of_countTrue_eq_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hfour : countTrue cm = 4) :
    triad (contractBand cm cp) cp (CProg.kernelSize cp) = true := by
  unfold validContractMask at h
  simpa [hfour] using h

theorem validContractMask_exists_triadAt_of_countTrue_eq_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hfour : countTrue cm = 4) :
    ∃ i, i < CProg.kernelSize cp ∧
      triadAt (contractBand cm cp) cp i = true :=
  triad_exists_triadAt_of_eq_true
    (validContractMask_triad_of_countTrue_eq_four h hfour)

theorem validContractMask_exists_triadAt_sources_of_countTrue_eq_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hfour : countTrue cm = 4) :
    ∃ i, i < CProg.kernelSize cp ∧
      triadAt (contractBand cm cp) cp i = true ∧
      (false ∈ select (contractBand cm cp).ring
          (adjMask (kernelSingleton cp i) cp).ring ∨
        false ∈ select (contractBand cm cp).kernel
          (adjMask (kernelSingleton cp i) cp).kernel) ∧
      (true ∈ select (contractBand cm cp).ring
          (adjMask (kernelSingleton cp i) cp).ring ∨
        true ∈ select (contractBand cm cp).kernel
          (adjMask (kernelSingleton cp i) cp).kernel) := by
  rcases validContractMask_exists_triadAt_of_countTrue_eq_four h hfour with
    ⟨i, hi, htriad⟩
  exact
    ⟨i, hi, htriad,
      triadAt_exists_false_source htriad,
      triadAt_exists_true_source htriad⟩

theorem validContractMask_exists_triadAtSources_of_countTrue_eq_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hfour : countTrue cm = 4) :
    ∃ i, i < CProg.kernelSize cp ∧
      triadAt (contractBand cm cp) cp i = true ∧
      triadAtSources (contractBand cm cp) cp i := by
  rcases validContractMask_exists_triadAt_of_countTrue_eq_four h hfour with
    ⟨i, hi, htriad⟩
  exact ⟨i, hi, htriad, triadAt_sources htriad⟩

theorem validContractMask_countTrue_le_three_of_ne_four
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true)
    (hfour : countTrue cm ≠ 4) :
    countTrue cm ≤ 3 := by
  unfold validContractMask at h
  simp [hfour] at h
  exact h.2

theorem validContractMask_countTrue_eq_four_or_le_three
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true) :
    countTrue cm = 4 ∨ countTrue cm ≤ 3 := by
  by_cases hfour : countTrue cm = 4
  · exact Or.inl hfour
  · exact Or.inr
      (validContractMask_countTrue_le_three_of_ne_four h hfour)

theorem validContractMask_countTrue_eq_four_or_between
    {cm : List Bool} {cp : CProg}
    (h : validContractMask cm cp = true) :
    countTrue cm = 4 ∨
      (0 < countTrue cm ∧ countTrue cm ≤ 3) := by
  by_cases hfour : countTrue cm = 4
  · exact Or.inl hfour
  · exact Or.inr
      ⟨validContractMask_countTrue_pos h,
        validContractMask_countTrue_le_three_of_ne_four h hfour⟩

theorem validContractMask_selectedContractIndices_length_pos
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true) :
    0 < (CProg.selectedContractIndices cp refs).length := by
  rw [← countTrue_contractMask_eq_length_selectedContractIndices cp refs]
  exact validContractMask_countTrue_pos h

theorem validContractMask_selectedContractIndices_length_le_four
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true) :
    (CProg.selectedContractIndices cp refs).length ≤ 4 := by
  rw [← countTrue_contractMask_eq_length_selectedContractIndices cp refs]
  exact validContractMask_countTrue_le_four h

theorem validContractMask_selectedContractIndices_length_eq_four_or_between
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true) :
    (CProg.selectedContractIndices cp refs).length = 4 ∨
      (0 < (CProg.selectedContractIndices cp refs).length ∧
        (CProg.selectedContractIndices cp refs).length ≤ 3) := by
  have hcases := validContractMask_countTrue_eq_four_or_between h
  rw [countTrue_contractMask_eq_length_selectedContractIndices cp refs]
    at hcases
  exact hcases

theorem validContractMask_triad_of_selectedContractIndices_length_eq_four
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true)
    (hfour : (CProg.selectedContractIndices cp refs).length = 4) :
    triad (contractBand (CProg.contractMask cp refs) cp)
      cp (CProg.kernelSize cp) = true := by
  exact validContractMask_triad_of_countTrue_eq_four h
    (by
      rw [countTrue_contractMask_eq_length_selectedContractIndices cp refs]
      exact hfour)

theorem validContractMask_exists_triadAt_of_selectedContractIndices_length_eq_four
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true)
    (hfour : (CProg.selectedContractIndices cp refs).length = 4) :
    ∃ i, i < CProg.kernelSize cp ∧
      triadAt (contractBand (CProg.contractMask cp refs) cp) cp i = true :=
  triad_exists_triadAt_of_eq_true
    (validContractMask_triad_of_selectedContractIndices_length_eq_four h hfour)

theorem validContractMask_exists_triadAtSources_of_selectedContractIndices_length_eq_four
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true)
    (hfour : (CProg.selectedContractIndices cp refs).length = 4) :
    ∃ i, i < CProg.kernelSize cp ∧
      triadAt (contractBand (CProg.contractMask cp refs) cp) cp i = true ∧
      triadAtSources (contractBand (CProg.contractMask cp refs) cp) cp i :=
  validContractMask_exists_triadAtSources_of_countTrue_eq_four h
    (by
      rw [countTrue_contractMask_eq_length_selectedContractIndices cp refs]
      exact hfour)

theorem validContractMask_selectedContractIndices_length_le_three_of_ne_four
    {cp : CProg} {refs : List Nat}
    (h : validContractMask (CProg.contractMask cp refs) cp = true)
    (hfour : (CProg.selectedContractIndices cp refs).length ≠ 4) :
    (CProg.selectedContractIndices cp refs).length ≤ 3 := by
  rw [← countTrue_contractMask_eq_length_selectedContractIndices cp refs]
  exact validContractMask_countTrue_le_three_of_ne_four h
    (by
      intro hcount
      exact hfour (by
        rwa [countTrue_contractMask_eq_length_selectedContractIndices cp refs]
          at hcount))

end CfMask

end FourColor

end Schematic.Math.GraphTheory
