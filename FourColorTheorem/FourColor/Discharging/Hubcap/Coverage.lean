import Mathlib.Data.List.GetD
import FourColorTheorem.FourColor.Discharging.Rules

/-!
Hubcap constraints and executable bound checkers.

This ports the executable front of Coq `hubcap.v`: the compressed hubcap
datatype, coverage tally, hub rotations, and the recursive bound checkers used
by the presentation scripts.  Correctness lemmas are ported after the remaining
score-sum API is in place.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

open Part
open PartRel

namespace Discharge

/-- Hubcap constraints on one or two score-transfer positions. -/
inductive Hubcap
  | Hubcap0
  | Hubcap1 (i : Nat) (b : Int) (tail : Hubcap)
  | Hubcap2 (i j : Nat) (b : Int) (tail : Hubcap)
  deriving DecidableEq, Repr, Inhabited

namespace Hubcap

/-- Increment the `i`th entry of a list, extending with zeros as needed. -/
def incrNth : List Nat → Nat → List Nat
  | [], 0 => [1]
  | [], i + 1 => 0 :: incrNth [] i
  | n :: ns, 0 => (n + 1) :: ns
  | n :: ns, i + 1 => n :: incrNth ns i

theorem getD_incrNth_self :
    ∀ (v : List Nat) (i : Nat),
      (incrNth v i).getD i 0 = v.getD i 0 + 1 := by
  intro v
  induction v with
  | nil =>
      intro i
      induction i with
      | zero =>
          simp [incrNth]
      | succ i ih =>
          simpa [incrNth, List.getD] using ih
  | cons n ns ih =>
      intro i
      cases i with
      | zero =>
          simp [incrNth]
      | succ i =>
          simpa [incrNth, List.getD] using ih i

theorem getD_le_getD_incrNth :
    ∀ (v : List Nat) (i j : Nat),
      v.getD j 0 ≤ (incrNth v i).getD j 0 := by
  intro v
  induction v with
  | nil =>
      intro i
      induction i with
      | zero =>
          intro j
          cases j <;> simp [incrNth]
      | succ i ih =>
          intro j
          cases j with
          | zero =>
              simp [incrNth]
          | succ j =>
              simp [incrNth]
  | cons n ns ih =>
      intro i j
      cases i with
      | zero =>
          cases j <;> simp [incrNth]
      | succ i =>
          cases j with
          | zero =>
              simp [incrNth]
          | succ j =>
              simpa [incrNth] using ih i j

theorem getD_incrNth_ne :
    ∀ (v : List Nat) (i j : Nat),
      j ≠ i → (incrNth v i).getD j 0 = v.getD j 0 := by
  intro v
  induction v with
  | nil =>
      intro i
      induction i with
      | zero =>
          intro j hji
          cases j with
          | zero => exact False.elim (hji rfl)
          | succ j => simp [incrNth]
      | succ i ih =>
          intro j hji
          cases j with
          | zero => simp [incrNth]
          | succ j =>
              have hne : j ≠ i := by
                intro h
                exact hji (by simp [h])
              simpa [incrNth, List.getD] using ih j hne
  | cons n ns ih =>
      intro i j hji
      cases i with
      | zero =>
          cases j with
          | zero => exact False.elim (hji rfl)
          | succ j => simp [incrNth]
      | succ i =>
          cases j with
          | zero => simp [incrNth]
          | succ j =>
              have hne : j ≠ i := by
                intro h
                exact hji (by simp [h])
              simpa [incrNth, List.getD] using ih i j hne

theorem getD_incrNth :
    ∀ (v : List Nat) (i j : Nat),
      (incrNth v i).getD j 0 =
        if j = i then v.getD j 0 + 1 else v.getD j 0 := by
  intro v i j
  by_cases hji : j = i
  · subst hji
    simpa using getD_incrNth_self v j
  · simpa [hji] using getD_incrNth_ne v i j hji

theorem lt_getD_of_forall_getD_incrNth_le
    {w v : List Nat} {i : Nat}
    (h : ∀ j : Nat, (incrNth w i).getD j 0 ≤ v.getD j 0) :
    w.getD i 0 < v.getD i 0 := by
  have hi := h i
  rw [getD_incrNth_self] at hi
  omega

theorem forall_getD_le_of_forall_getD_incrNth_le
    {w v : List Nat} {i : Nat}
    (h : ∀ j : Nat, (incrNth w i).getD j 0 ≤ v.getD j 0) :
    ∀ j : Nat, w.getD j 0 ≤ v.getD j 0 := by
  intro j
  exact le_trans (getD_le_getD_incrNth w i j) (h j)

theorem getD_pos_of_lt_length_of_zero_not_mem :
    ∀ {v : List Nat} {i : Nat},
      0 ∉ v → i < v.length → 0 < v.getD i 0 := by
  intro v
  induction v with
  | nil =>
      intro i _ hlt
      simp at hlt
  | cons a as ih =>
      intro i hzero hlt
      have ha : a ≠ 0 := by
        intro h
        exact hzero (by simp [h])
      have has : 0 ∉ as := by
        intro hmem
        exact hzero (by simp [hmem])
      cases i with
      | zero =>
          exact Nat.pos_of_ne_zero ha
      | succ i =>
          exact ih has (by simpa using hlt)

theorem getD_pos_of_length_eq_of_zero_not_mem
    {v : List Nat} {nhub i : Nat}
    (hlen : v.length = nhub) (hzero : 0 ∉ v) (hi : i < nhub) :
    0 < v.getD i 0 :=
  getD_pos_of_lt_length_of_zero_not_mem hzero (by simpa [hlen] using hi)

theorem lt_length_of_getD_pos {v : List Nat} {i : Nat}
    (hpos : 0 < v.getD i 0) :
    i < v.length := by
  by_contra hlt
  have hle : v.length ≤ i := Nat.le_of_not_gt hlt
  rw [List.getD_eq_default (l := v) (n := i) (d := 0) hle] at hpos
  omega

def coverMultiplicity (v : List Nat) (i : Nat) : Nat :=
  if v.getD i 0 == 1 then 2 else 1

theorem coverMultiplicity_eq_two_of_getD_eq_one
    {v : List Nat} {i : Nat}
    (h : v.getD i 0 = 1) :
    coverMultiplicity v i = 2 := by
  unfold coverMultiplicity
  split_ifs with hif
  · rfl
  · exact False.elim (hif (by simpa [List.getD] using h))

theorem coverMultiplicity_eq_one_of_getD_ne_one
    {v : List Nat} {i : Nat}
    (h : v.getD i 0 ≠ 1) :
    coverMultiplicity v i = 1 := by
  unfold coverMultiplicity
  split_ifs with hif
  · exact False.elim (h (by simpa [List.getD] using hif))
  · rfl

theorem int_coverMultiplicity_eq_if (v : List Nat) (i : Nat) :
    (coverMultiplicity v i : Int) =
      if v.getD i 0 == 1 then (2 : Int) else 1 := by
  unfold coverMultiplicity
  split_ifs <;> rfl

def coverWeight (v w : List Nat) (i : Nat) : Nat :=
  if 1 < w.getD i 0 then
    2
  else if w.getD i 0 = 0 then
    0
  else
    coverMultiplicity v i

theorem coverWeight_incrNth_self
    {v w : List Nat} {i : Nat}
    (hle : (incrNth w i).getD i 0 ≤ v.getD i 0)
    (hvi2 : v.getD i 0 ≤ 2) :
    coverWeight v (incrNth w i) i =
      coverWeight v w i + coverMultiplicity v i := by
  have hle' : w.getD i 0 + 1 ≤ v.getD i 0 := by
    rw [← getD_incrNth_self (v := w) (i := i)]
    exact hle
  unfold coverWeight coverMultiplicity
  rw [getD_incrNth_self]
  split_ifs <;> simp at * <;> omega

theorem coverWeight_incrNth_ne
    {v w : List Nat} {i j : Nat}
    (hji : j ≠ i) :
    coverWeight v (incrNth w i) j = coverWeight v w j := by
  unfold coverWeight
  rw [getD_incrNth_ne w i j hji]

theorem coverWeight_self_of_pos
    {v : List Nat} {i : Nat}
    (hpos : 0 < v.getD i 0) :
    coverWeight v v i = 2 := by
  unfold coverWeight coverMultiplicity
  split_ifs <;> simp at * <;> omega

noncomputable def weightedDbound2Sum
    (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub)
    (x : G.Dart) (v w : List Nat) : Int :=
  ∑ i : Fin nhub,
    (coverWeight v w i.1 : Int) *
      G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[i.1] x)

theorem weightedDbound2Sum_incrNth
    (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub)
    (x : G.Dart) {v w : List Nat} {i : Nat}
    (hi : i < nhub)
    (hle : (incrNth w i).getD i 0 ≤ v.getD i 0)
    (hvi2 : v.getD i 0 ≤ 2) :
    weightedDbound2Sum G rf x v (incrNth w i) =
      (coverMultiplicity v i : Int) *
          G.dbound2 rf.targetDrules rf.sourceDrules
            ((G.face : G.Dart → G.Dart)^[i] x) +
        weightedDbound2Sum G rf x v w := by
  classical
  let k : Fin nhub := ⟨i, hi⟩
  let after : Fin nhub → Int := fun j =>
    (coverWeight v (incrNth w i) j.1 : Int) *
      G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[j.1] x)
  let before : Fin nhub → Int := fun j =>
    (coverWeight v w j.1 : Int) *
      G.dbound2 rf.targetDrules rf.sourceDrules
        ((G.face : G.Dart → G.Dart)^[j.1] x)
  have hafter := Finset.add_sum_erase (Finset.univ : Finset (Fin nhub))
    after (Finset.mem_univ k)
  have hbefore := Finset.add_sum_erase (Finset.univ : Finset (Fin nhub))
    before (Finset.mem_univ k)
  have htail :
      (∑ j ∈ (Finset.univ : Finset (Fin nhub)).erase k, after j) =
        ∑ j ∈ (Finset.univ : Finset (Fin nhub)).erase k, before j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
    have hval : j.1 ≠ i := by
      intro hji
      exact hjne (Fin.ext hji)
    simp [after, before, coverWeight_incrNth_ne (v := v) (w := w)
      (i := i) (j := j.1) hval]
  have hterm :
      after k =
        before k +
          (coverMultiplicity v i : Int) *
            G.dbound2 rf.targetDrules rf.sourceDrules
              ((G.face : G.Dart → G.Dart)^[i] x) := by
    have hw := coverWeight_incrNth_self (v := v) (w := w)
      (i := i) hle hvi2
    simp [after, before, k, hw, Nat.cast_add, add_mul, add_comm]
  calc
    weightedDbound2Sum G rf x v (incrNth w i) =
        ∑ j : Fin nhub, after j := by
          simp [weightedDbound2Sum, after]
    _ = after k +
        ∑ j ∈ (Finset.univ : Finset (Fin nhub)).erase k, after j := by
          exact hafter.symm
    _ = (before k +
          (coverMultiplicity v i : Int) *
            G.dbound2 rf.targetDrules rf.sourceDrules
              ((G.face : G.Dart → G.Dart)^[i] x)) +
        ∑ j ∈ (Finset.univ : Finset (Fin nhub)).erase k, before j := by
          rw [hterm, htail]
    _ = (coverMultiplicity v i : Int) *
          G.dbound2 rf.targetDrules rf.sourceDrules
            ((G.face : G.Dart → G.Dart)^[i] x) +
        (before k +
          ∑ j ∈ (Finset.univ : Finset (Fin nhub)).erase k, before j) := by
          simp [add_assoc, add_comm]
    _ = (coverMultiplicity v i : Int) *
          G.dbound2 rf.targetDrules rf.sourceDrules
            ((G.face : G.Dart → G.Dart)^[i] x) +
        ∑ j : Fin nhub, before j := by
          rw [hbefore]
    _ = (coverMultiplicity v i : Int) *
          G.dbound2 rf.targetDrules rf.sourceDrules
            ((G.face : G.Dart → G.Dart)^[i] x) +
        weightedDbound2Sum G rf x v w := by
          simp [weightedDbound2Sum, before]

theorem weightedDbound2Sum_self_eq_two_sum
    (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub)
    (x : G.Dart) {v : List Nat}
    (hlen : v.length = nhub) (hzero : 0 ∉ v) :
    weightedDbound2Sum G rf x v v =
      2 * ∑ i : Fin nhub,
        G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[i.1] x) := by
  classical
  calc
    weightedDbound2Sum G rf x v v =
        ∑ i : Fin nhub,
          (2 : Int) *
            G.dbound2 rf.targetDrules rf.sourceDrules
              ((G.face : G.Dart → G.Dart)^[i.1] x) := by
          unfold weightedDbound2Sum
          apply Finset.sum_congr rfl
          intro i _hi
          have hpos :
              0 < v.getD i.1 0 :=
            getD_pos_of_length_eq_of_zero_not_mem
              (v := v) hlen hzero i.2
          simp [coverWeight_self_of_pos (v := v) (i := i.1) hpos]
    _ = 2 * ∑ i : Fin nhub,
        G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[i.1] x) := by
          rw [Finset.mul_sum]

theorem weightedDbound2Sum_self_eq_two_faceScoreSum
    (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub)
    (x : G.Dart) {v : List Nat}
    (hx : G.arity x = nhub)
    (hlen : v.length = nhub) (hzero : 0 ∉ v)
    (hdb :
      ∀ i : Fin nhub,
        G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[i.1] x) =
            G.dscore2 ((G.face : G.Dart → G.Dart)^[i.1] x)) :
    weightedDbound2Sum G rf x v v = 2 * G.faceScoreSum x := by
  subst nhub
  rw [weightedDbound2Sum_self_eq_two_sum
    (G := G) (rf := rf) (x := x) (hlen := hlen) (hzero := hzero)]
  rw [G.faceScoreSum_eq_sum_fin_arity x]
  apply congrArg ((HMul.hMul (2 : Int)) : Int → Int)
  apply Finset.sum_congr rfl
  intro i _hi
  exact hdb i

/-- Multiset tally of hubcap indices, represented as occurrence counts. -/
def tally : Hubcap → List Nat
  | Hubcap0 => []
  | Hubcap1 i _ hc => incrNth (tally hc) i
  | Hubcap2 i j _ hc => incrNth (incrNth (tally hc) i) j

/-- Recursive coverage check after the tally pass. -/
def coverRec (v : List Nat) (b : Int) : Hubcap → Bool
  | Hubcap0 => decide (b ≤ 0)
  | Hubcap1 i b' hc =>
      (v.getD i 0 == 1) && coverRec v (b' * 2 + b) hc
  | Hubcap2 i j b' hc =>
      let ni := v.getD i 0
      let nj := v.getD j 0
      let weight : Int := if ni == 1 then 2 else 1
      (ni == nj) && (decide (ni ≤ 2)) && coverRec v (b' * weight + b) hc

/-- Coverage check for a fixed hub size. -/
def cover (nhub : Nat) (hc : Hubcap) : Bool :=
  let b := dboundK nhub * 2 - 1
  let v := hc.tally
  (v.length == nhub) && (decide (0 ∉ v)) && coverRec v b hc

theorem cover_eq_true
    {nhub : Nat} {hc : Hubcap}
    (h : cover nhub hc = true) :
    hc.tally.length = nhub ∧ 0 ∉ hc.tally ∧
      coverRec hc.tally (dboundK nhub * 2 - 1) hc = true := by
  rcases (by simpa [cover] using h) with ⟨⟨hlen, hmem⟩, hrec⟩
  exact ⟨hlen, hmem, hrec⟩

theorem coverRec_hubcap1_eq_true
    {v : List Nat} {b b' : Int} {i : Nat} {hc : Hubcap}
    (h : coverRec v b (Hubcap1 i b' hc) = true) :
    v.getD i 0 = 1 ∧ coverRec v (b' * 2 + b) hc = true := by
  simpa [coverRec] using h

theorem coverRec_hubcap0_eq_true
    {v : List Nat} {b : Int}
    (h : coverRec v b Hubcap0 = true) :
    b ≤ 0 := by
  simpa [coverRec] using h

theorem coverRec_hubcap2_eq_true
    {v : List Nat} {b b' : Int} {i j : Nat} {hc : Hubcap}
    (h : coverRec v b (Hubcap2 i j b' hc) = true) :
    v.getD i 0 = v.getD j 0 ∧ v.getD i 0 ≤ 2 ∧
      coverRec v (b' * (if v.getD i 0 == 1 then 2 else 1) + b)
        hc = true := by
  rcases (by simpa [coverRec] using h) with ⟨⟨hij, hi2⟩, hrec⟩
  exact ⟨hij, hi2, by simpa using hrec⟩

/-- Semantic bounds represented by a hubcap, relative to a starting dart. -/
def Bounds (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub)
    (x : G.Dart) : Hubcap → Prop
  | Hubcap0 => True
  | Hubcap1 i b hc =>
      G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[i] x) ≤ b ∧
        Bounds G rf x hc
  | Hubcap2 i j b hc =>
      G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[i] x) +
        G.dbound2 rf.targetDrules rf.sourceDrules
          ((G.face : G.Dart → G.Dart)^[j] x) ≤ b ∧
        Bounds G rf x hc

theorem coverRec_weightedDbound2Sum_le
    (G : Hypermap) {nhub : Nat} (rf : DruleFork nhub) (x : G.Dart)
    {v : List Nat} (hlen : v.length = nhub) :
    ∀ {hc : Hubcap} {b : Int},
      coverRec v b hc = true →
        Bounds G rf x hc →
          (∀ j : Nat, (tally hc).getD j 0 ≤ v.getD j 0) →
            b + weightedDbound2Sum G rf x v (tally hc) ≤ 0 := by
  classical
  intro hc
  induction hc with
  | Hubcap0 =>
      intro b hcover _hbounds _hle
      have hb := coverRec_hubcap0_eq_true hcover
      simpa [tally, weightedDbound2Sum, coverWeight] using hb
  | Hubcap1 i b' hc ih =>
      intro b hcover hbounds hle
      rcases coverRec_hubcap1_eq_true hcover with ⟨hvi, hrec⟩
      rcases hbounds with ⟨hb, hboundsTail⟩
      have hleTail :
          ∀ j : Nat, (tally hc).getD j 0 ≤ v.getD j 0 :=
        forall_getD_le_of_forall_getD_incrNth_le
          (w := tally hc) (v := v) (i := i) hle
      have hih :
          b' * 2 + b + weightedDbound2Sum G rf x v (tally hc) ≤ 0 :=
        ih (b := b' * 2 + b) hrec hboundsTail hleTail
      have hi : i < nhub := by
        have hpos : 0 < v.getD i 0 := by omega
        simpa [hlen] using lt_length_of_getD_pos (v := v) hpos
      have hle_i :
          (incrNth (tally hc) i).getD i 0 ≤ v.getD i 0 := hle i
      have hinc :=
        weightedDbound2Sum_incrNth
          (G := G) (rf := rf) (x := x) (v := v) (w := tally hc)
          (i := i) hi hle_i (by omega)
      have hmult : coverMultiplicity v i = 2 := by
        unfold coverMultiplicity
        rw [hvi]
        simp
      change b + weightedDbound2Sum G rf x v (incrNth (tally hc) i) ≤ 0
      rw [hinc, hmult]
      exact le_trans (by omega) hih
  | Hubcap2 i j b' hc ih =>
      intro b hcover hbounds hle
      rcases coverRec_hubcap2_eq_true hcover with ⟨hij, hi2, hrec⟩
      rcases hbounds with ⟨hb, hboundsTail⟩
      have hleMid :
          ∀ k : Nat,
            (incrNth (tally hc) i).getD k 0 ≤ v.getD k 0 :=
        forall_getD_le_of_forall_getD_incrNth_le
          (w := incrNth (tally hc) i) (v := v) (i := j) hle
      have hleTail :
          ∀ k : Nat, (tally hc).getD k 0 ≤ v.getD k 0 :=
        forall_getD_le_of_forall_getD_incrNth_le
          (w := tally hc) (v := v) (i := i) hleMid
      have hih :
          b' * (if v.getD i 0 == 1 then 2 else 1) + b +
              weightedDbound2Sum G rf x v (tally hc) ≤ 0 :=
        ih
          (b := b' * (if v.getD i 0 == 1 then 2 else 1) + b)
          hrec hboundsTail hleTail
      have hposi : 0 < v.getD i 0 := by
        have hmidPos : 0 < (incrNth (tally hc) i).getD i 0 := by
          rw [getD_incrNth_self]
          omega
        have hfullPos :
            0 < (incrNth (incrNth (tally hc) i) j).getD i 0 :=
          lt_of_lt_of_le hmidPos
            (getD_le_getD_incrNth (incrNth (tally hc) i) j i)
        exact lt_of_lt_of_le hfullPos (hle i)
      have hposj : 0 < v.getD j 0 := by
        have hfullPos :
            0 < (incrNth (incrNth (tally hc) i) j).getD j 0 := by
          rw [getD_incrNth_self]
          omega
        exact lt_of_lt_of_le hfullPos (hle j)
      have hi : i < nhub := by
        simpa [hlen] using lt_length_of_getD_pos (v := v) hposi
      have hj : j < nhub := by
        simpa [hlen] using lt_length_of_getD_pos (v := v) hposj
      have hj2 : v.getD j 0 ≤ 2 := by omega
      have hincJ :=
        weightedDbound2Sum_incrNth
          (G := G) (rf := rf) (x := x) (v := v)
          (w := incrNth (tally hc) i) (i := j)
          hj (hle j) hj2
      have hincI :=
        weightedDbound2Sum_incrNth
          (G := G) (rf := rf) (x := x) (v := v)
          (w := tally hc) (i := i)
          hi (hleMid i) hi2
      change
        b + weightedDbound2Sum G rf x v
          (incrNth (incrNth (tally hc) i) j) ≤ 0
      rw [hincJ, hincI]
      by_cases hone : v.getD i 0 = 1
      · have honej : v.getD j 0 = 1 := by omega
        have hmi : coverMultiplicity v i = 2 :=
          coverMultiplicity_eq_two_of_getD_eq_one hone
        have hmj : coverMultiplicity v j = 2 :=
          coverMultiplicity_eq_two_of_getD_eq_one honej
        have hoptI : v[i]?.getD 0 = 1 := by
          simpa [List.getD] using hone
        have hih' :
            b' * 2 + b + weightedDbound2Sum G rf x v (tally hc) ≤ 0 := by
          simpa [hoptI] using hih
        rw [hmi, hmj]
        exact le_trans (by omega) hih'
      · have honej : v.getD j 0 ≠ 1 := by omega
        have hmi : coverMultiplicity v i = 1 :=
          coverMultiplicity_eq_one_of_getD_ne_one hone
        have hmj : coverMultiplicity v j = 1 :=
          coverMultiplicity_eq_one_of_getD_ne_one honej
        have hoptI : v[i]?.getD 0 ≠ 1 := by
          intro h
          exact hone (by simpa [List.getD] using h)
        have hih' :
            b' * 1 + b + weightedDbound2Sum G rf x v (tally hc) ≤ 0 := by
          simpa [hoptI] using hih
        rw [hmi, hmj]
        exact le_trans (by omega) hih'

end Hubcap

end Discharge

end FourColor

end Schematic.Math.GraphTheory
