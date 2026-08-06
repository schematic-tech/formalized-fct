import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Rotate
import FourColorTheorem.Tactic.Decide

/-!
Configuration program syntax.

This ports the front, syntax-only part of Gonthier's `cfmap.v`: construction
steps, configuration programs, configuration descriptors, and the basic
well-formedness predicates.  The semantic interpretation of these programs as
hypermaps is a later layer.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- One step in a configuration-map construction program. -/
inductive CpStep
  | rotate (n : Nat)
  | reverseRotate
  | y
  | h
  | u
  | k
  | a
  deriving DecidableEq, Repr

/-- A configuration construction program.  Following the Coq development, it
is interpreted right-to-left by the semantic layer. -/
abbrev CProg := List CpStep

namespace CProg

/-- Programs consisting only of rotation, `U`, `Y`, and `H` steps. -/
def cubic : CProg → Bool
  | [] => true
  | CpStep.rotate _ :: cp => cubic cp
  | CpStep.u :: cp => cubic cp
  | CpStep.y :: cp => cubic cp
  | CpStep.h :: cp => cubic cp
  | _ => false

/-- Configuration programs: rotations, `Y`, and `H` steps, ending in `Y`. -/
def config : CProg → Bool
  | CpStep.rotate _ :: cp => config cp
  | [CpStep.y] => true
  | CpStep.y :: cp => config cp
  | CpStep.h :: cp => config cp
  | _ => false

/-- Programs with no `R'`/reverse-rotation step.  Contracted programs use
rotations, `Y`, `H`, `U`, `K`, and `A`, but never `R'`. -/
def noReverse : CProg → Bool
  | [] => true
  | CpStep.reverseRotate :: _ => false
  | _ :: cp => noReverse cp

/-- The ring-size recurrence for the program semantics. -/
def ringSize : CProg → Nat
  | [] => 2
  | CpStep.y :: cp => ringSize cp + 1
  | CpStep.u :: cp => ringSize cp + 2
  | CpStep.k :: cp => ringSize cp - 2 + 1
  | CpStep.a :: cp =>
      if 2 < ringSize cp then ringSize cp - 2 else ringSize cp
  | _ :: cp => ringSize cp

/-- Number of kernel darts recorded by the construction syntax: one per `H`
step. -/
def kernelSize : CProg → Nat
  | [] => 0
  | CpStep.h :: cp => kernelSize cp + 1
  | _ :: cp => kernelSize cp

/-- Number of contract-edge candidates recorded by a construction program.
This is Coq's `ctrmsize`: non-initial `Y` steps contribute one candidate and
`H` steps contribute three. -/
def contractEdgeSize : CProg → Nat
  | CpStep.rotate _ :: cp => contractEdgeSize cp
  | [CpStep.y] => 0
  | CpStep.y :: cp => contractEdgeSize cp + 1
  | CpStep.h :: cp => contractEdgeSize cp + 3
  | _ => 0

/-- Build the Boolean mask selected by contract-reference indices.  Out-of-range
indices are ignored because only `n` entries are produced. -/
def contractMaskRec (refs : List Nat) (i : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => (if i ∈ refs then true else false) ::
      contractMaskRec refs (i + 1) n

/-- Contract-reference mask for the contract-edge candidates of a program. -/
def contractMask (cp : CProg) (refs : List Nat) : List Bool :=
  contractMaskRec refs 0 (contractEdgeSize cp)

/-- The in-range contract-edge candidate indices selected by a reference list.
This mirrors `contractMaskRec`; duplicate references and out-of-range
references are ignored. -/
def selectedContractIndicesRec (refs : List Nat) (i : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      if i ∈ refs then
        i :: selectedContractIndicesRec refs (i + 1) n
      else
        selectedContractIndicesRec refs (i + 1) n

/-- Selected contract-edge candidate indices for a construction program. -/
def selectedContractIndices (cp : CProg) (refs : List Nat) : List Nat :=
  selectedContractIndicesRec refs 0 (contractEdgeSize cp)

/-- Coq-name alias for `ringSize`. -/
abbrev cprsize : CProg → Nat := ringSize

/-- Coq-name alias for `kernelSize`. -/
abbrev cpksize : CProg → Nat := kernelSize

/-- Coq-name alias for `contractEdgeSize`. -/
abbrev ctrmsize : CProg → Nat := contractEdgeSize

/-- Coq-name alias for `contractMask`. -/
abbrev ctrmask : CProg → List Nat → List Bool := contractMask

/-- Count `false` entries in a Boolean list. -/
def countFalse : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 1) + countFalse bs

theorem countFalse_le_length :
    ∀ bs : List Bool, countFalse bs ≤ bs.length
  | [] => by
      simp [countFalse]
  | b :: bs => by
      cases b
      · have h := countFalse_le_length bs
        simp [countFalse]
        omega
      · simp [countFalse]
        exact Nat.le_trans (countFalse_le_length bs)
          (Nat.le_succ bs.length)

theorem countFalse_eq_zero_iff :
    ∀ bs : List Bool, countFalse bs = 0 ↔ ∀ b ∈ bs, b = true
  | [] => by
      simp [countFalse]
  | b :: bs => by
      cases b <;> simp [countFalse, countFalse_eq_zero_iff bs]

theorem countFalse_eq_of_perm {bs cs : List Bool}
    (h : bs.Perm cs) :
    countFalse bs = countFalse cs := by
  induction h with
  | nil => rfl
  | cons b _ ih => simp [countFalse, ih]
  | swap b c bs => cases b <;> cases c <;> simp [countFalse]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem countFalse_pos_of_all_eq_false {bs : List Bool}
    (h : bs.all (fun b => b) = false) :
    0 < countFalse bs := by
  by_contra hzero
  have hcount : countFalse bs = 0 := Nat.eq_zero_of_not_pos hzero
  have hall : ∀ b ∈ bs, b = true := (countFalse_eq_zero_iff bs).1 hcount
  have : bs.all (fun b => b) = true := by
    simpa using hall
  exact Bool.false_ne_true (h.symm.trans this)

theorem countFalse_pos_of_false_mem {bs : List Bool}
    (h : false ∈ bs) :
    0 < countFalse bs := by
  by_contra hzero
  have hall := (countFalse_eq_zero_iff bs).1
    (Nat.eq_zero_of_not_pos hzero)
  exact Bool.false_ne_true (hall false h)

/-- Right rotation of a list, used by contract-program annotations. -/
def rotateRight {α : Type _} (n : Nat) (xs : List α) : List α :=
  let k := xs.length - n
  xs.drop k ++ xs.take k

/-- Left rotation of a list, matching MathComp's `rot`. -/
def rotateLeft {α : Type _} (n : Nat) (xs : List α) : List α :=
  xs.drop n ++ xs.take n

theorem length_rotateRight {α : Type _} (n : Nat) (xs : List α) :
    (rotateRight n xs).length = xs.length := by
  simp [rotateRight]

theorem length_rotateLeft {α : Type _} (n : Nat) (xs : List α) :
    (rotateLeft n xs).length = xs.length := by
  simp [rotateLeft]
  omega

theorem rotateLeft_eq_rotate_of_le {α : Type _}
    {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    rotateLeft n xs = xs.rotate n :=
  (List.rotate_eq_drop_append_take h).symm

theorem rotateLeft_oversize {α : Type _}
    {n : Nat} {xs : List α} (h : xs.length ≤ n) :
    rotateLeft n xs = xs := by
  simp [rotateLeft, List.drop_eq_nil_iff.mpr h,
    (List.take_eq_self_iff xs).2 h]

theorem rotateRight_eq_rotate {α : Type _} (n : Nat) (xs : List α) :
    rotateRight n xs = xs.rotate (xs.length - n) :=
  rotateLeft_eq_rotate_of_le (Nat.sub_le _ _)

theorem perm_rotateRight {α : Type _} (n : Nat) (xs : List α) :
    (rotateRight n xs).Perm xs := by
  rw [rotateRight_eq_rotate]
  exact List.rotate_perm xs (xs.length - n)

theorem rotateLeft_eq_drop_append_take_of_lt {α : Type _}
    {n : Nat} {xs : List α} :
    rotateLeft n xs = xs.drop n ++ xs.take n := by
  rfl

@[simp]
theorem rotateLeft_one_cons {α : Type _} (x : α) (xs : List α) :
    rotateLeft 1 (x :: xs) = xs ++ [x] := by
  simp [rotateLeft]

theorem map_rotateLeft {α β : Type _} (f : α → β)
    (n : Nat) (xs : List α) :
    (rotateLeft n xs).map f = rotateLeft n (xs.map f) := by
  simp [rotateLeft, List.map_drop, List.map_take]

theorem map_rotateRight {α β : Type _} (f : α → β)
    (n : Nat) (xs : List α) :
    (rotateRight n xs).map f = rotateRight n (xs.map f) := by
  simp [rotateRight]

theorem rotateRight_rotateLeft {α : Type _} (n : Nat) (xs : List α) :
    rotateRight n (rotateLeft n xs) = xs := by
  by_cases h : n ≤ xs.length
  · rw [rotateRight_eq_rotate, length_rotateLeft,
      rotateLeft_eq_rotate_of_le h, List.rotate_rotate]
    convert List.rotate_length xs using 2
    all_goals omega
  · have hov : xs.length ≤ n := Nat.le_of_not_ge h
    rw [rotateLeft_oversize hov, rotateRight_eq_rotate,
      Nat.sub_eq_zero_of_le hov]
    simp

theorem rotateLeft_rotateRight {α : Type _} (n : Nat) (xs : List α) :
    rotateLeft n (rotateRight n xs) = xs := by
  by_cases h : n ≤ xs.length
  · rw [rotateRight_eq_rotate]
    have hlen : (xs.rotate (xs.length - n)).length = xs.length :=
      List.length_rotate _ _
    rw [rotateLeft_eq_rotate_of_le (by simpa [hlen] using h),
      List.rotate_rotate]
    convert List.rotate_length xs using 2
    all_goals omega
  · have hov : xs.length ≤ n := Nat.le_of_not_ge h
    rw [rotateRight_eq_rotate, Nat.sub_eq_zero_of_le hov]
    simp [rotateLeft_oversize hov]

theorem map_range_shift_eq_rotateLeft_of_mod_period_of_lt {α : Type _}
    {n : Nat} (f : Nat → α) {r : Nat} (hr : r < n)
    (hperiod : ∀ i : Nat, f (i % n) = f i) :
    (List.range n).map (fun i => f (r + i)) =
      rotateLeft r ((List.range n).map f) := by
  rw [rotateLeft_eq_rotate_of_le (by simp; omega)]
  apply List.ext_getElem
  · simp
  · intro i _hleft _hright
    simp [List.getElem_map, List.getElem_rotate]
    have hidx : ((i + r) % n) = ((r + i) % n) := by
      rw [Nat.add_comm]
    rw [hidx]
    exact (hperiod (r + i)).symm

theorem mem_rotateRight {α : Type _} (a : α) (n : Nat) (xs : List α) :
    a ∈ rotateRight n xs ↔ a ∈ xs := by
  rw [rotateRight_eq_rotate, List.mem_rotate]

theorem mem_rotateLeft {α : Type _} (a : α) (n : Nat) (xs : List α) :
    a ∈ rotateLeft n xs ↔ a ∈ xs := by
  by_cases h : n ≤ xs.length
  · rw [rotateLeft_eq_rotate_of_le h, List.mem_rotate]
  · rw [rotateLeft_oversize (Nat.le_of_not_ge h)]

theorem not_mem_rotateRight {α : Type _} (a : α) (n : Nat) (xs : List α) :
    a ∉ rotateRight n xs ↔ a ∉ xs :=
  not_congr (mem_rotateRight a n xs)

theorem not_mem_rotateLeft {α : Type _} (a : α) (n : Nat) (xs : List α) :
    a ∉ rotateLeft n xs ↔ a ∉ xs :=
  not_congr (mem_rotateLeft a n xs)

theorem nodup_rotateLeft {α : Type _} (n : Nat) (xs : List α) :
    (rotateLeft n xs).Nodup ↔ xs.Nodup := by
  by_cases h : n ≤ xs.length
  · rw [rotateLeft_eq_rotate_of_le h, List.nodup_rotate]
  · rw [rotateLeft_oversize (Nat.le_of_not_ge h)]

theorem perm_rotateLeft {α : Type _} (n : Nat) (xs : List α) :
    (rotateLeft n xs).Perm xs := by
  by_cases h : n ≤ xs.length
  · rw [rotateLeft_eq_rotate_of_le h]
    exact List.rotate_perm xs n
  · rw [rotateLeft_oversize (Nat.le_of_not_ge h)]

theorem countFalse_rotateLeft (n : Nat) (bs : List Bool) :
    countFalse (rotateLeft n bs) = countFalse bs :=
  countFalse_eq_of_perm (perm_rotateLeft n bs)

theorem countFalse_rotateRight (n : Nat) (bs : List Bool) :
    countFalse (rotateRight n bs) = countFalse bs :=
  countFalse_eq_of_perm (perm_rotateRight n bs)

/-- Local non-sparseness test used by Coq's `cfctr`: if the pivot bit is set,
the two other bits must not overlap it; otherwise the two other bits must not
both be set. -/
def nonSparse (pivot left right : Bool) : Bool :=
  if pivot then left || right else left && right

theorem nonSparse_eq_true_iff
    (pivot left right : Bool) :
    nonSparse pivot left right = true ↔
      (pivot = true ∧ (left = true ∨ right = true)) ∨
        (pivot = false ∧ left = true ∧ right = true) := by
  cases pivot <;> cases left <;> cases right <;> simp [nonSparse]

theorem nonSparse_eq_false_iff
    (pivot left right : Bool) :
    nonSparse pivot left right = false ↔
      (pivot = true ∧ left = false ∧ right = false) ∨
        (pivot = false ∧ (left = false ∨ right = false)) := by
  cases pivot <;> cases left <;> cases right <;> simp [nonSparse]

theorem nonSparse_eq_false_of_pivot_true
    {left right : Bool}
    (h : nonSparse true left right = false) :
    left = false ∧ right = false := by
  simpa [nonSparse] using h

theorem nonSparse_eq_false_of_pivot_false
    {left right : Bool}
    (h : nonSparse false left right = false) :
    left = false ∨ right = false := by
  cases left <;> cases right <;> simp [nonSparse] at h ⊢

/-- Contract a configuration program by deleting selected ring/kernel edges.
This ports the executable `cfctr` function from `cfcontract.v`; the semantic
correctness theorem is a later layer, once configuration maps are available. -/
def contractProgram (mr mc : List Bool) : CProg → Option CProg
  | CpStep.rotate i :: cp =>
      let mr' := rotateRight i mr
      match contractProgram mr' mc cp with
      | some cpc => some (CpStep.rotate (countFalse (mr'.take i)) :: cpc)
      | none => none
  | [CpStep.y] =>
      match mr with
      | b1 :: b2 :: b3 :: _ =>
          if nonSparse b1 b2 b3 then none
          else some (if b1 || (b2 || b3) then [] else [CpStep.y])
      | _ => none
  | CpStep.y :: cp =>
      match mr, mc with
      | b1 :: b2 :: mr', b3 :: mc' =>
          if nonSparse b1 b2 b3 then none
          else
            match contractProgram (b3 :: mr') mc' cp with
            | some cpc =>
                some (if b1 || b2 then cpc
                  else (if b3 then CpStep.u else CpStep.y) :: cpc)
            | none => none
      | _, _ => none
  | CpStep.h :: cp =>
      match mr, mc with
      | b1 :: b2 :: mr', b3 :: b4 :: b5 :: mc' =>
          if nonSparse b3 b1 b4 || nonSparse b3 b2 b5 then none
          else if b1 && b2 && mr'.all (fun b => b) then none
          else
            match contractProgram (b4 :: b5 :: mr') mc' cp with
            | some cpc =>
                some
                  (if b3 then cpc
                   else if b1 then
                    if b2 then CpStep.a :: cpc
                    else if b5 then cpc else CpStep.k :: cpc
                   else if b2 then
                    if b4 then cpc else CpStep.k :: cpc
                   else if b4 then
                    if b5 then CpStep.u :: cpc else CpStep.y :: cpc
                   else if b5 then CpStep.y :: cpc else CpStep.h :: cpc)
            | none => none
      | _, _ => none
  | _ => none

theorem config_implies_cubic
    {cp : CProg}
    (hcp : config cp = true) :
    cubic cp = true := by
  induction cp with
  | nil =>
      simp [config] at hcp
  | cons s cp ih =>
      cases s <;> cases cp <;> simp [config, cubic] at hcp ⊢
      all_goals exact ih hcp

theorem noReverse_eq_true_iff_not_mem_reverse :
    ∀ cp : CProg, noReverse cp = true ↔ CpStep.reverseRotate ∉ cp
  | [] => by
      simp [noReverse]
  | s :: cp => by
      cases s <;> simp [noReverse,
        noReverse_eq_true_iff_not_mem_reverse cp]

theorem noReverse_of_not_mem_reverse
    {cp : CProg}
    (hcp : CpStep.reverseRotate ∉ cp) :
    noReverse cp = true :=
  (noReverse_eq_true_iff_not_mem_reverse cp).2 hcp

theorem ringSize_pos (cp : CProg) :
    0 < ringSize cp := by
  induction cp with
  | nil => decide
  | cons s cp ih =>
      cases s <;> simp [ringSize, ih]
      by_cases h : 2 < ringSize cp
      · simp [h]
        exact Nat.sub_pos_of_lt h
      · simp [h, ih]

/-- Well-formed configuration programs always have a nontrivial ring.  This is
the syntax-level counterpart of Coq's `cfmap_long` size consequence. -/
theorem ringSize_gt_two_of_config
    {cp : CProg}
    (hcp : config cp = true) :
    2 < ringSize cp := by
  induction cp with
  | nil =>
      simp [config] at hcp
  | cons s cp ih =>
      cases s with
      | rotate n =>
          have hcp' : config cp = true := by
            simpa [config] using hcp
          simpa [ringSize] using ih hcp'
      | reverseRotate =>
          simp [config] at hcp
      | y =>
          cases cp with
          | nil =>
              simp [ringSize]
          | cons s' cp' =>
              have hcp' : config (s' :: cp') = true := by
                simpa [config] using hcp
              have hlong : 2 < ringSize (s' :: cp') := ih hcp'
              simp [ringSize]
              omega
      | h =>
          have hcp' : config cp = true := by
            simpa [config] using hcp
          simpa [ringSize] using ih hcp'
      | u =>
          simp [config] at hcp
      | k =>
          simp [config] at hcp
      | a =>
          simp [config] at hcp

theorem kernelSize_le_length (cp : CProg) :
    kernelSize cp ≤ cp.length := by
  induction cp with
  | nil => simp [kernelSize]
  | cons s cp ih =>
      cases s <;> simp [kernelSize]
      · exact Nat.le_trans ih (Nat.le_succ cp.length)
      · exact Nat.le_trans ih (Nat.le_succ cp.length)
      · exact Nat.le_trans ih (Nat.le_succ cp.length)
      · exact ih
      · exact Nat.le_trans ih (Nat.le_succ cp.length)
      · exact Nat.le_trans ih (Nat.le_succ cp.length)
      · exact Nat.le_trans ih (Nat.le_succ cp.length)

theorem length_contractMaskRec (refs : List Nat) (i n : Nat) :
    (contractMaskRec refs i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [contractMaskRec, ih]

theorem length_contractMask (cp : CProg) (refs : List Nat) :
    (contractMask cp refs).length = contractEdgeSize cp := by
  simp [contractMask, length_contractMaskRec]

theorem length_selectedContractIndicesRec_le (refs : List Nat) :
    ∀ (i n : Nat), (selectedContractIndicesRec refs i n).length ≤ n
  | i, 0 => by
      simp [selectedContractIndicesRec]
  | i, n + 1 => by
      have ih := length_selectedContractIndicesRec_le refs (i + 1) n
      by_cases h : i ∈ refs
      · simp [selectedContractIndicesRec, h]
        omega
      · simp [selectedContractIndicesRec, h]
        exact Nat.le_trans ih (Nat.le_succ n)

theorem length_selectedContractIndices_le
    (cp : CProg) (refs : List Nat) :
    (selectedContractIndices cp refs).length ≤ contractEdgeSize cp :=
  length_selectedContractIndicesRec_le refs 0 (contractEdgeSize cp)

theorem mem_selectedContractIndicesRec_ref {refs : List Nat} :
    ∀ {i n k : Nat},
      k ∈ selectedContractIndicesRec refs i n → k ∈ refs
  | i, 0, k, h => by
      simp [selectedContractIndicesRec] at h
  | i, n + 1, k, h => by
      by_cases hi : i ∈ refs
      · simp [selectedContractIndicesRec, hi] at h
        rcases h with rfl | htail
        · exact hi
        · exact mem_selectedContractIndicesRec_ref htail
      · simp [selectedContractIndicesRec, hi] at h
        exact mem_selectedContractIndicesRec_ref h

theorem mem_selectedContractIndices_ref
    {cp : CProg} {refs : List Nat} {k : Nat}
    (h : k ∈ selectedContractIndices cp refs) :
    k ∈ refs :=
  mem_selectedContractIndicesRec_ref h

theorem mem_selectedContractIndicesRec_bounds {refs : List Nat} :
    ∀ {i n k : Nat},
      k ∈ selectedContractIndicesRec refs i n → i ≤ k ∧ k < i + n
  | i, 0, k, h => by
      simp [selectedContractIndicesRec] at h
  | i, n + 1, k, h => by
      by_cases hi : i ∈ refs
      · simp [selectedContractIndicesRec, hi] at h
        rcases h with rfl | htail
        · omega
        · have hb := mem_selectedContractIndicesRec_bounds htail
          omega
      · simp [selectedContractIndicesRec, hi] at h
        have hb := mem_selectedContractIndicesRec_bounds h
        omega

theorem mem_selectedContractIndices_lt
    {cp : CProg} {refs : List Nat} {k : Nat}
    (h : k ∈ selectedContractIndices cp refs) :
    k < contractEdgeSize cp := by
  have hb := mem_selectedContractIndicesRec_bounds h
  simpa [selectedContractIndices] using hb.2

theorem mem_selectedContractIndices_iff
    (cp : CProg) (refs : List Nat) (k : Nat) :
    k ∈ selectedContractIndices cp refs ↔
      k < contractEdgeSize cp ∧ k ∈ refs := by
  constructor
  · intro h
    exact ⟨mem_selectedContractIndices_lt h,
      mem_selectedContractIndices_ref h⟩
  · intro h
    unfold selectedContractIndices
    have hrec :
        ∀ (i n : Nat), i ≤ k → k < i + n → k ∈ refs →
          k ∈ selectedContractIndicesRec refs i n := by
      intro i n
      induction n generalizing i with
      | zero =>
          intro _ hlt _
          omega
      | succ n ih =>
          intro hik hlt href
          by_cases hki : k = i
          · subst hki
            simp [selectedContractIndicesRec, href]
          · have hik' : i + 1 ≤ k := by omega
            have hlt' : k < i + 1 + n := by omega
            by_cases hi : i ∈ refs
            · simp [selectedContractIndicesRec, hi]
              exact Or.inr (ih (i + 1) hik' hlt' href)
            · simp [selectedContractIndicesRec, hi]
              exact ih (i + 1) hik' hlt' href
    exact hrec 0 (contractEdgeSize cp) (by omega) (by simpa using h.1) h.2

theorem nodup_selectedContractIndicesRec (refs : List Nat) :
    ∀ (i n : Nat), (selectedContractIndicesRec refs i n).Nodup
  | i, 0 => by
      simp [selectedContractIndicesRec]
  | i, n + 1 => by
      have ih := nodup_selectedContractIndicesRec refs (i + 1) n
      by_cases hi : i ∈ refs
      · simp [selectedContractIndicesRec, hi, ih]
        intro hmem
        have hb := mem_selectedContractIndicesRec_bounds hmem
        omega
      · simpa [selectedContractIndicesRec, hi] using ih

theorem nodup_selectedContractIndices (cp : CProg) (refs : List Nat) :
    (selectedContractIndices cp refs).Nodup :=
  nodup_selectedContractIndicesRec refs 0 (contractEdgeSize cp)

theorem pairwise_lt_selectedContractIndicesRec (refs : List Nat) :
    ∀ (i n : Nat),
      (selectedContractIndicesRec refs i n).Pairwise (fun a b => a < b)
  | i, 0 => by
      simp [selectedContractIndicesRec]
  | i, n + 1 => by
      have ih := pairwise_lt_selectedContractIndicesRec refs (i + 1) n
      by_cases hi : i ∈ refs
      · simp [selectedContractIndicesRec, hi, ih]
        intro k hk
        have hb := mem_selectedContractIndicesRec_bounds hk
        omega
      · simpa [selectedContractIndicesRec, hi] using ih

theorem pairwise_lt_selectedContractIndices
    (cp : CProg) (refs : List Nat) :
    (selectedContractIndices cp refs).Pairwise (fun a b => a < b) :=
  pairwise_lt_selectedContractIndicesRec refs 0 (contractEdgeSize cp)

/-- Exact indexing behavior of the recursive contract-reference mask. -/
theorem getElem?_contractMaskRec (refs : List Nat) :
    ∀ (i n k : Nat),
      (contractMaskRec refs i n)[k]? =
        if k < n then
          some (if i + k ∈ refs then true else false)
        else
          none
  | i, 0, k => by
      simp [contractMaskRec]
  | i, n + 1, 0 => by
      simp [contractMaskRec]
  | i, n + 1, k + 1 => by
      have hidx : i + (k + 1) = i + 1 + k := by omega
      simp [contractMaskRec, getElem?_contractMaskRec refs (i + 1) n k,
        hidx]

theorem getElem?_contractMask (cp : CProg) (refs : List Nat) (k : Nat) :
    (contractMask cp refs)[k]? =
      if k < contractEdgeSize cp then
        some (if k ∈ refs then true else false)
      else
        none := by
  simpa [contractMask] using getElem?_contractMaskRec refs 0
    (contractEdgeSize cp) k

theorem getElem?_ctrmask (cp : CProg) (refs : List Nat) (k : Nat) :
    (ctrmask cp refs)[k]? =
      if k < ctrmsize cp then
        some (if k ∈ refs then true else false)
      else
        none :=
  getElem?_contractMask cp refs k

theorem true_mem_contractMask_iff
    (cp : CProg) (refs : List Nat) :
    true ∈ contractMask cp refs ↔
      ∃ k, k < contractEdgeSize cp ∧ k ∈ refs := by
  constructor
  · intro h
    rcases (List.mem_iff_getElem?).1 h with ⟨k, hk⟩
    have hidx := getElem?_contractMask cp refs k
    by_cases hlt : k < contractEdgeSize cp
    · rw [hk] at hidx
      by_cases href : k ∈ refs
      · exact ⟨k, hlt, href⟩
      · simp [hlt, href] at hidx
    · rw [hk] at hidx
      simp [hlt] at hidx
  · rintro ⟨k, hlt, href⟩
    exact (List.mem_iff_getElem?).2
      ⟨k, by simp [getElem?_contractMask, hlt, href]⟩

theorem true_mem_ctrmask_iff
    (cp : CProg) (refs : List Nat) :
    true ∈ ctrmask cp refs ↔
      ∃ k, k < ctrmsize cp ∧ k ∈ refs :=
  true_mem_contractMask_iff cp refs

theorem false_mem_contractMask_iff
    (cp : CProg) (refs : List Nat) :
    false ∈ contractMask cp refs ↔
      ∃ k, k < contractEdgeSize cp ∧ k ∉ refs := by
  constructor
  · intro h
    rcases (List.mem_iff_getElem?).1 h with ⟨k, hk⟩
    have hidx := getElem?_contractMask cp refs k
    by_cases hlt : k < contractEdgeSize cp
    · rw [hk] at hidx
      by_cases href : k ∈ refs
      · simp [hlt, href] at hidx
      · exact ⟨k, hlt, href⟩
    · rw [hk] at hidx
      simp [hlt] at hidx
  · rintro ⟨k, hlt, href⟩
    exact (List.mem_iff_getElem?).2
      ⟨k, by simp [getElem?_contractMask, hlt, href]⟩

theorem false_mem_ctrmask_iff
    (cp : CProg) (refs : List Nat) :
    false ∈ ctrmask cp refs ↔
      ∃ k, k < ctrmsize cp ∧ k ∉ refs :=
  false_mem_contractMask_iff cp refs

/-- Coq `size_ctrmask`. -/
theorem size_ctrmask (cp : CProg) (refs : List Nat) :
    (ctrmask cp refs).length = ctrmsize cp :=
  length_contractMask cp refs

@[simp]
theorem contractProgram_nil (mr mc : List Bool) :
    contractProgram mr mc [] = none := rfl

/-- The output boundary of `contractProgram` has exactly one entry for every
uncontracted input boundary entry.  This is the syntax-level size equation
used throughout Coq `cfctr_correct`. -/
theorem ringSize_contractProgram
    {mr mc : List Bool} {cp cpc : CProg}
    (hmr : mr.length = ringSize cp)
    (hrun : contractProgram mr mc cp = some cpc) :
    ringSize cpc = countFalse mr := by
  induction cp generalizing mr mc cpc with
  | nil =>
      simp [contractProgram] at hrun
  | cons step cp ih =>
      cases step with
      | rotate i =>
          simp only [contractProgram] at hrun
          cases hrec : contractProgram (rotateRight i mr) mc cp with
          | none => simp [hrec] at hrun
          | some cp' =>
              simp [hrec] at hrun
              subst cpc
              have hmr' : (rotateRight i mr).length = ringSize cp := by
                simpa [ringSize, length_rotateRight] using hmr
              have hout := ih hmr' hrec
              simpa [ringSize] using
                hout.trans (countFalse_rotateRight i mr)
      | reverseRotate =>
          simp [contractProgram] at hrun
      | y =>
          cases cp with
          | nil =>
              cases mr with
              | nil => simp [contractProgram] at hrun
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil => simp [contractProgram] at hrun
                  | cons b2 mr2 =>
                      cases mr2 with
                      | nil => simp [contractProgram] at hrun
                      | cons b3 mr' =>
                          have hnil : mr' = [] := by
                            have hlen : mr'.length = 0 := by
                              simpa [ringSize] using hmr
                            exact List.eq_nil_of_length_eq_zero hlen
                          subst mr'
                          cases b1 <;> cases b2 <;> cases b3 <;>
                            simp [contractProgram, nonSparse] at hrun <;>
                            subst cpc <;> decide
          | cons step' cp' =>
              cases mr with
              | nil => simp [contractProgram] at hrun
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil => simp [contractProgram] at hrun
                  | cons b2 mr' =>
                      cases mc with
                      | nil => simp [contractProgram] at hrun
                      | cons b3 mc' =>
                          by_cases hnsp : nonSparse b1 b2 b3
                          · simp [contractProgram, hnsp] at hrun
                          · cases hrec : contractProgram (b3 :: mr') mc'
                                (step' :: cp') with
                            | none => simp [contractProgram, hnsp, hrec] at hrun
                            | some cp'' =>
                                have hmr' :
                                    (b3 :: mr').length =
                                      ringSize (step' :: cp') := by
                                  simp [ringSize] at hmr ⊢
                                  omega
                                have hout := ih hmr' hrec
                                simp [contractProgram, hnsp, hrec] at hrun
                                subst cpc
                                cases b1 <;> cases b2 <;> cases b3 <;>
                                  simp [nonSparse] at hnsp ⊢ <;>
                                  simp [ringSize, countFalse] at hout ⊢ <;>
                                  omega
      | h =>
          cases mr with
          | nil => simp [contractProgram] at hrun
          | cons b1 mr1 =>
              cases mr1 with
              | nil => simp [contractProgram] at hrun
              | cons b2 mr' =>
                  cases mc with
                  | nil => simp [contractProgram] at hrun
                  | cons b3 mc1 =>
                      cases mc1 with
                      | nil => simp [contractProgram] at hrun
                      | cons b4 mc2 =>
                          cases mc2 with
                          | nil => simp [contractProgram] at hrun
                          | cons b5 mc' =>
                              by_cases hnsp :
                                  nonSparse b3 b1 b4 || nonSparse b3 b2 b5
                              · simp [contractProgram, hnsp] at hrun
                              · by_cases hall :
                                    b1 && b2 && mr'.all (fun b => b)
                                · simp [contractProgram, hnsp, hall] at hrun
                                · cases hrec :
                                      contractProgram (b4 :: b5 :: mr') mc' cp with
                                  | none =>
                                      simp [contractProgram, hnsp, hall, hrec] at hrun
                                  | some cp' =>
                                      have hmr' :
                                          (b4 :: b5 :: mr').length =
                                            ringSize cp := by
                                        simp [ringSize] at hmr ⊢
                                        omega
                                      have hout := ih hmr' hrec
                                      simp [contractProgram, hnsp, hall, hrec] at hrun
                                      subst cpc
                                      cases b1 <;> cases b2 <;> cases b3 <;>
                                        cases b4 <;> cases b5 <;>
                                        simp [nonSparse] at hnsp hall ⊢ <;>
                                        simp [ringSize, countFalse] at hout ⊢ <;>
                                        first
                                        | omega
                                        | have hpos : 0 < countFalse mr' :=
                                            countFalse_pos_of_false_mem hall
                                          have hlong : 2 < ringSize cp' := by
                                            omega
                                          simp [hlong]
                                          omega
      | u => simp [contractProgram] at hrun
      | k => simp [contractProgram] at hrun
      | a => simp [contractProgram] at hrun

theorem contractProgram_config
    {mr mc : List Bool} {cp cpc : CProg}
    (h : contractProgram mr mc cp = some cpc) :
    config cp = true := by
  induction cp generalizing mr mc cpc with
  | nil =>
      simp [contractProgram] at h
  | cons step cp ih =>
      cases step with
      | rotate i =>
          simp [contractProgram, config] at h ⊢
          cases hcp : contractProgram (rotateRight i mr) mc cp with
          | none =>
              simp [hcp] at h
          | some cp' =>
              exact ih hcp
      | reverseRotate =>
          simp [contractProgram] at h
      | y =>
          cases cp with
          | nil =>
              simp [config]
          | cons step' cp' =>
              cases mr with
              | nil =>
                  simp [contractProgram] at h
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil =>
                      simp [contractProgram] at h
                  | cons b2 mr' =>
                      cases mc with
                      | nil =>
                          simp [contractProgram] at h
                      | cons b3 mc' =>
                          simp [contractProgram, config] at h ⊢
                          by_cases hnsp : nonSparse b1 b2 b3
                          · simp [hnsp] at h
                          · simp [hnsp] at h
                            cases hcp : contractProgram (b3 :: mr') mc'
                                (step' :: cp') with
                            | none =>
                                simp [hcp] at h
                            | some cp'' =>
                                exact ih hcp
      | h =>
          cases mr with
          | nil =>
              simp [contractProgram] at h
          | cons b1 mr1 =>
              cases mr1 with
              | nil =>
                  simp [contractProgram] at h
              | cons b2 mr' =>
                  cases mc with
                  | nil =>
                      simp [contractProgram] at h
                  | cons b3 mc1 =>
                      cases mc1 with
                      | nil =>
                          simp [contractProgram] at h
                      | cons b4 mc2 =>
                          cases mc2 with
                          | nil =>
                              simp [contractProgram] at h
                          | cons b5 mc' =>
                              simp [contractProgram, config] at h ⊢
                              cases hcp : contractProgram (b4 :: b5 :: mr')
                                  mc' cp with
                              | none =>
                                  simp [hcp] at h
                              | some cp' =>
                                  exact ih hcp
      | u =>
          simp [contractProgram] at h
      | k =>
          simp [contractProgram] at h
      | a =>
          simp [contractProgram] at h

theorem contractProgram_noReverse
    {mr mc : List Bool} {cp cpc : CProg}
    (h : contractProgram mr mc cp = some cpc) :
    noReverse cpc = true := by
  induction cp generalizing mr mc cpc with
  | nil =>
      simp [contractProgram] at h
  | cons step cp ih =>
      cases step with
      | rotate i =>
          simp [contractProgram] at h
          cases hcp : contractProgram (rotateRight i mr) mc cp with
          | none =>
              simp [hcp] at h
          | some cp' =>
              have htail : noReverse cp' = true := ih hcp
              simp [hcp] at h
              cases h
              exact htail
      | reverseRotate =>
          simp [contractProgram] at h
      | y =>
          cases cp with
          | nil =>
              cases mr with
              | nil =>
                  simp [contractProgram] at h
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil =>
                      simp [contractProgram] at h
                  | cons b2 mr2 =>
                      cases mr2 with
                      | nil =>
                          simp [contractProgram] at h
                      | cons b3 mr' =>
                          simp [contractProgram] at h
                          by_cases hnsp : nonSparse b1 b2 b3
                          · simp [hnsp] at h
                          · simp [hnsp] at h
                            cases h
                            cases b1 <;> cases b2 <;> cases b3 <;>
                              simp [noReverse]
          | cons step' cp' =>
              cases mr with
              | nil =>
                  simp [contractProgram] at h
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil =>
                      simp [contractProgram] at h
                  | cons b2 mr' =>
                      cases mc with
                      | nil =>
                          simp [contractProgram] at h
                      | cons b3 mc' =>
                          simp [contractProgram] at h
                          by_cases hnsp : nonSparse b1 b2 b3
                          · simp [hnsp] at h
                          · simp [hnsp] at h
                            cases hcp :
                                contractProgram (b3 :: mr') mc'
                                  (step' :: cp') with
                            | none =>
                                simp [hcp] at h
                            | some cp'' =>
                                have htail : noReverse cp'' = true := ih hcp
                                simp [hcp] at h
                                cases h
                                cases b1 <;> cases b2 <;> cases b3 <;>
                                  simpa [noReverse] using htail
      | h =>
          cases mr with
          | nil =>
              simp [contractProgram] at h
          | cons b1 mr1 =>
              cases mr1 with
              | nil =>
                  simp [contractProgram] at h
              | cons b2 mr' =>
                  cases mc with
                  | nil =>
                      simp [contractProgram] at h
                  | cons b3 mc1 =>
                      cases mc1 with
                      | nil =>
                          simp [contractProgram] at h
                      | cons b4 mc2 =>
                          cases mc2 with
                          | nil =>
                              simp [contractProgram] at h
                          | cons b5 mc' =>
                              by_cases hnsp :
                                  nonSparse b3 b1 b4 ||
                                    nonSparse b3 b2 b5
                              · simp [contractProgram, hnsp] at h
                              · by_cases hall : b1 && b2 && mr'.all (fun b => b)
                                · simp [contractProgram, hnsp, hall] at h
                                · simp [contractProgram, hnsp, hall] at h
                                  cases hcp :
                                      contractProgram (b4 :: b5 :: mr') mc'
                                        cp with
                                  | none =>
                                      simp [hcp] at h
                                  | some cp' =>
                                      have htail : noReverse cp' = true :=
                                        ih hcp
                                      simp [hcp] at h
                                      cases h
                                      cases b3 <;> cases b1 <;>
                                        cases b2 <;> cases b4 <;>
                                        cases b5 <;>
                                        simpa [noReverse] using htail
      | u =>
          simp [contractProgram] at h
      | k =>
          simp [contractProgram] at h
      | a =>
          simp [contractProgram] at h

theorem contractProgram_not_mem_reverse
    {mr mc : List Bool} {cp cpc : CProg}
    (h : contractProgram mr mc cp = some cpc) :
    CpStep.reverseRotate ∉ cpc :=
  (noReverse_eq_true_iff_not_mem_reverse cpc).1
    (contractProgram_noReverse h)

end CProg

end FourColor

end Schematic.Math.GraphTheory
