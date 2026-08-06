import Schematic.Math.GraphTheory.Embedding.Trace

/-!
Chromograms and Kempe closure interfaces.

This ports the executable datatypes and predicates at the front of Gonthier's
`chromogram.v`.  The later topological theorem that ring traces of planar
plain cubic maps are Kempe-closed will build on this interface.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

/-- Symbols in the Dyck-word representation of a chromogram. -/
inductive GramSymbol
  | push
  | skip
  | pop0
  | pop1
  deriving DecidableEq

instance : Fintype GramSymbol where
  elems := {GramSymbol.push, GramSymbol.skip, GramSymbol.pop0, GramSymbol.pop1}
  complete := by
    intro s
    cases s <;> simp

/-- A chromogram word. -/
abbrev Chromogram := List GramSymbol

namespace Chromogram

/-- Balance/parity checker for a chromogram suffix. -/
def balanced : Nat → Bool → Chromogram → Bool
  | 0, b, [] => !b
  | _ + 1, _, [] => false
  | d, b, GramSymbol.push :: w => balanced (d + 1) b w
  | d, b, GramSymbol.skip :: w => balanced d (!b) w
  | 0, _, GramSymbol.pop0 :: _ => false
  | d + 1, b, GramSymbol.pop0 :: w => balanced d b w
  | 0, _, GramSymbol.pop1 :: _ => false
  | d + 1, b, GramSymbol.pop1 :: w => balanced d (!b) w

/-- Match an edge-colour trace against a chromogram with a stack of open-chord
parity bits. -/
def matchg : List Bool → ColSeq → Chromogram → Bool
  | [], [], [] => true
  | lb, e :: et, s :: w =>
      match e, s, lb with
      | Color.one, GramSymbol.skip, _ => matchg lb et w
      | Color.two, GramSymbol.push, _ => matchg (false :: lb) et w
      | Color.two, GramSymbol.pop0, false :: lb' => matchg lb' et w
      | Color.two, GramSymbol.pop1, true :: lb' => matchg lb' et w
      | Color.three, GramSymbol.push, _ => matchg (true :: lb) et w
      | Color.three, GramSymbol.pop0, true :: lb' => matchg lb' et w
      | Color.three, GramSymbol.pop1, false :: lb' => matchg lb' et w
      | _, _, _ => false
  | _, _, _ => false

@[simp]
theorem matchg_nil :
    matchg [] [] [] = true := rfl

@[simp]
theorem balanced_nil_false :
    balanced 0 false [] = true := rfl

@[simp]
theorem balanced_nil_true :
    balanced 0 true [] = false := rfl

/-- Xor-sum of a stack of parity bits. -/
def bitParity : List Bool → Bool :=
  List.foldr Bool.xor false

/-- Parity of the stack depth, computed structurally for chromogram induction. -/
def oddLength : List Bool → Bool
  | [] => false
  | _ :: lb => !oddLength lb

@[simp]
theorem bitParity_nil :
    bitParity [] = false := rfl

@[simp]
theorem bitParity_cons (b : Bool) (lb : List Bool) :
    bitParity (b :: lb) = Bool.xor b (bitParity lb) := rfl

@[simp]
theorem oddLength_nil :
    oddLength ([] : List Bool) = false := rfl

@[simp]
theorem oddLength_cons (b : Bool) (lb : List Bool) :
    oddLength (b :: lb) = !oddLength lb := rfl

theorem balanced_inj
    {w : Chromogram} {n₁ n₂ : Nat} {b₁ b₂ : Bool}
    (h₁ : balanced n₁ b₁ w = true)
    (h₂ : balanced n₂ b₂ w = true) :
    n₁ = n₂ ∧ b₁ = b₂ := by
  induction w generalizing n₁ n₂ b₁ b₂ with
  | nil =>
      cases n₁ <;> cases n₂ <;> cases b₁ <;> cases b₂ <;>
        simp [balanced] at h₁ h₂ ⊢
  | cons s w ih =>
      cases s with
      | push =>
          simp [balanced] at h₁ h₂
          rcases ih h₁ h₂ with ⟨hn, hb⟩
          have hn' : n₁.succ = n₂.succ := by
            simpa [Nat.succ_eq_add_one] using hn
          exact ⟨Nat.succ.inj hn', hb⟩
      | skip =>
          simp [balanced] at h₁ h₂
          rcases ih h₁ h₂ with ⟨hn, hb⟩
          constructor
          · exact hn
          · cases b₁ <;> cases b₂ <;> simp at hb ⊢
      | pop0 =>
          cases n₁ with
          | zero =>
              simp [balanced] at h₁
          | succ n₁ =>
              cases n₂ with
              | zero =>
                  simp [balanced] at h₂
              | succ n₂ =>
                  simp [balanced] at h₁ h₂
                  rcases ih h₁ h₂ with ⟨hn, hb⟩
                  exact ⟨congrArg Nat.succ hn, hb⟩
      | pop1 =>
          cases n₁ with
          | zero =>
              simp [balanced] at h₁
          | succ n₁ =>
              cases n₂ with
              | zero =>
                  simp [balanced] at h₂
              | succ n₂ =>
                  simp [balanced] at h₁ h₂
                  rcases ih h₁ h₂ with ⟨hn, hb⟩
                  constructor
                  · exact congrArg Nat.succ hn
                  · cases b₁ <;> cases b₂ <;> simp at hb ⊢

theorem matchg_balanced_aux
    {lb : List Bool} {et : ColSeq} {w : Chromogram}
    (hmatch : matchg lb et w = true) :
    Bool.xor (ColSeq.sum et).bit1 (oddLength lb) = false ∧
      balanced lb.length (Bool.xor (ColSeq.sum et).bit0 (bitParity lb)) w = true := by
  induction et generalizing lb w with
  | nil =>
      cases w <;> cases lb <;>
        simp [matchg, ColSeq.sum, bitParity, oddLength, balanced,
          Color.bit0, Color.bit1] at hmatch ⊢
  | cons e et ih =>
      cases w with
      | nil =>
          cases lb <;> cases e <;>
            simp [matchg] at hmatch
      | cons s w =>
          cases lb with
          | nil =>
              cases s <;> cases e <;>
                simp [matchg, ColSeq.sum, bitParity, oddLength, balanced,
                  Color.bit0, Color.bit1] at hmatch ⊢
              all_goals
                rcases ih hmatch with ⟨hbit, hbal⟩
                cases hsum : List.foldr (fun c s => c + s) Color.zero et <;>
                  simp [ColSeq.sum, hsum, Color.bit0, Color.bit1,
                    bitParity] at hbit hbal ⊢ <;>
                  exact hbal
          | cons b lb =>
              cases b <;> cases s <;> cases e <;>
                simp [matchg, ColSeq.sum, bitParity, oddLength, balanced,
                  Color.bit0, Color.bit1] at hmatch ⊢
              all_goals
                rcases ih hmatch with ⟨hbit, hbal⟩
                cases hsum : List.foldr (fun c s => c + s) Color.zero et <;>
                  simp [ColSeq.sum, hsum, Color.bit0, Color.bit1,
                    bitParity] at hbit hbal ⊢ <;>
                  first
                  | exact hbal
                  | exact ⟨hbit, hbal⟩

theorem matchg_balanced
    {et : ColSeq} {w : Chromogram}
    (hmatch : matchg [] et w = true) :
    (ColSeq.sum et).bit1 = false ∧
      balanced 0 (ColSeq.sum et).bit0 w = true := by
  simpa [bitParity, oddLength] using
    (matchg_balanced_aux (lb := []) hmatch)

theorem balanced_sum_zero
    {et : ColSeq} {w : Chromogram}
    (hbal : balanced 0 false w = true)
    (hmatch : matchg [] et w = true) :
    ColSeq.sum et = Color.zero := by
  rcases matchg_balanced hmatch with ⟨hbit₁, hbalanced⟩
  rcases balanced_inj hbalanced hbal with ⟨_, hbit₀⟩
  have hcons := Color.cons_bits (ColSeq.sum et)
  rw [hbit₁, hbit₀] at hcons
  exact hcons.symm

/-- A stack datatype used by the partial chromogram matcher. -/
inductive BitStack
  | empty
  | push0 (bs : BitStack)
  | push1 (bs : BitStack)
  deriving DecidableEq

namespace BitStack

/-- Convert a stack to its list-of-bits representation. -/
def toList : BitStack → List Bool
  | empty => []
  | push0 bs => false :: toList bs
  | push1 bs => true :: toList bs

/-- Build a stack from a list of bits. -/
def ofList : List Bool → BitStack :=
  List.foldr (fun b bs => if b then push1 bs else push0 bs) empty

/-- Swap the two non-zero edge colours recorded in stack bits. -/
def flip : BitStack → BitStack
  | empty => empty
  | push0 bs => push1 (flip bs)
  | push1 bs => push0 (flip bs)

@[simp]
theorem ofList_nil :
    ofList [] = empty := rfl

@[simp]
theorem ofList_cons_false (lb : List Bool) :
    ofList (false :: lb) = push0 (ofList lb) := rfl

@[simp]
theorem ofList_cons_true (lb : List Bool) :
    ofList (true :: lb) = push1 (ofList lb) := rfl

@[simp]
theorem toList_empty :
    toList empty = [] := rfl

@[simp]
theorem toList_push0 (bs : BitStack) :
    toList (push0 bs) = false :: toList bs := rfl

@[simp]
theorem toList_push1 (bs : BitStack) :
    toList (push1 bs) = true :: toList bs := rfl

@[simp]
theorem toList_ofList (lb : List Bool) :
    toList (ofList lb) = lb := by
  induction lb with
  | nil => rfl
  | cons b lb ih =>
      cases b <;> simp [ofList] <;> exact ih

@[simp]
theorem flip_empty :
    flip empty = empty := rfl

@[simp]
theorem flip_push0 (bs : BitStack) :
    flip (push0 bs) = push1 (flip bs) := rfl

@[simp]
theorem flip_push1 (bs : BitStack) :
    flip (push1 bs) = push0 (flip bs) := rfl

@[simp]
theorem flip_flip (bs : BitStack) :
    flip (flip bs) = bs := by
  induction bs with
  | empty => rfl
  | push0 bs ih =>
      simp [ih]
  | push1 bs ih =>
      simp [ih]

theorem toList_flip (bs : BitStack) :
    toList (flip bs) = bs.toList.map Bool.not := by
  induction bs with
  | empty => rfl
  | push0 bs ih =>
      simp [ih]
  | push1 bs ih =>
      simp [ih]

end BitStack

/-- Complete a partial chromogram by restoring the final redundant symbol. -/
def complete : Nat → Bool → Chromogram → Chromogram
  | d, b, [] =>
      [if d = 0 then GramSymbol.skip else if b then GramSymbol.pop1 else GramSymbol.pop0]
  | d, b, GramSymbol.push :: w => GramSymbol.push :: complete (d + 1) b w
  | d, b, GramSymbol.skip :: w => GramSymbol.skip :: complete d (!b) w
  | 0, b, GramSymbol.pop0 :: w => GramSymbol.pop0 :: complete 0 b w
  | d + 1, b, GramSymbol.pop0 :: w => GramSymbol.pop0 :: complete d b w
  | 0, b, GramSymbol.pop1 :: w => GramSymbol.pop1 :: complete 0 (!b) w
  | d + 1, b, GramSymbol.pop1 :: w => GramSymbol.pop1 :: complete d (!b) w

theorem complete_ne_nil (d : Nat) (b : Bool) (w : Chromogram) :
    complete d b w ≠ [] := by
  cases w with
  | nil =>
      simp [complete]
  | cons s w =>
      cases s <;> cases d <;> simp [complete]

@[simp]
theorem matchg_nil_complete (lb : List Bool) (d : Nat) (b : Bool)
    (w : Chromogram) :
    matchg lb [] (complete d b w) = false := by
  have hne := complete_ne_nil d b w
  cases hc : complete d b w with
  | nil =>
      exact False.elim (hne hc)
  | cons s cw =>
      cases lb <;> rfl

theorem dropLast_cons_of_ne_nil
    (s : GramSymbol) {w : Chromogram}
    (hw : w ≠ []) :
    (s :: w).dropLast = s :: w.dropLast := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons t w => rfl

theorem length_complete (d : Nat) (b : Bool) (w : Chromogram) :
    (complete d b w).length = w.length + 1 := by
  induction w generalizing d b with
  | nil =>
      cases d <;> cases b <;> rfl
  | cons s w ih =>
      cases s <;> cases d <;> simp [complete, ih]

theorem dropLast_complete (d : Nat) (b : Bool) (w : Chromogram) :
    (complete d b w).dropLast = w := by
  induction w generalizing d b with
  | nil =>
      cases d <;> cases b <;> rfl
  | cons s w ih =>
      cases s <;> cases d <;>
        simp [complete, dropLast_cons_of_ne_nil, complete_ne_nil, ih]

theorem complete_dropLast_of_balanced
    {d : Nat} {b : Bool} {w : Chromogram}
    (hne : w ≠ [])
    (hbal : balanced d b w = true) :
    complete d b w.dropLast = w := by
  induction w generalizing d b with
  | nil =>
      exact False.elim (hne rfl)
  | cons s w ih =>
      cases w with
      | nil =>
          cases s <;> cases d <;> cases b <;>
            simp [balanced, complete] at hbal ⊢
          all_goals
            rename_i n
            cases n <;> simp [balanced] at hbal
      | cons t w =>
          cases s <;> cases d <;>
            simp [balanced, complete] at hbal ⊢
          all_goals
            exact ih (by simp) hbal

/-- Partial chromogram matcher, using the explicit stack datatype. -/
def matchPartial : BitStack → ColSeq → Chromogram → Bool
  | BitStack.empty, [], [] => true
  | bs, e :: et, s :: w =>
      match e, s, bs with
      | Color.one, GramSymbol.skip, _ => matchPartial bs et w
      | Color.two, GramSymbol.push, _ => matchPartial (BitStack.push0 bs) et w
      | Color.two, GramSymbol.pop0, BitStack.push0 bs' => matchPartial bs' et w
      | Color.two, GramSymbol.pop1, BitStack.push1 bs' => matchPartial bs' et w
      | Color.three, GramSymbol.push, _ => matchPartial (BitStack.push1 bs) et w
      | Color.three, GramSymbol.pop0, BitStack.push1 bs' => matchPartial bs' et w
      | Color.three, GramSymbol.pop1, BitStack.push0 bs' => matchPartial bs' et w
      | _, _, _ => false
  | _, _, _ => false

@[simp]
theorem matchPartial_nil :
    matchPartial BitStack.empty [] [] = true := rfl

theorem matchPartial_eq_matchg
    (bs : BitStack) (et : ColSeq) (w : Chromogram) :
    matchPartial bs et w = matchg bs.toList et w := by
  induction et generalizing bs w with
  | nil =>
      cases w <;> cases bs <;> rfl
  | cons e et ih =>
      cases w with
      | nil =>
          cases bs <;> rfl
      | cons s w =>
          cases e <;> cases s <;> cases bs <;>
            simp [matchPartial, matchg, ih]

theorem matchPartial_empty_eq_matchg
    (et : ColSeq) (w : Chromogram) :
    matchPartial BitStack.empty et w = matchg [] et w := by
  simpa using matchPartial_eq_matchg BitStack.empty et w

theorem matchg_map_not_perm132
    (lb : List Bool) (et : ColSeq) (w : Chromogram) :
    matchg (lb.map Bool.not) (ColSeq.perm EdgePerm.p132 et) w =
      matchg lb et w := by
  induction et generalizing lb w with
  | nil =>
      cases w <;> cases lb <;> rfl
  | cons e et ih =>
      cases w with
      | nil =>
          cases lb <;> cases e <;> rfl
      | cons s w =>
          cases lb with
          | nil =>
              cases e <;> cases s <;>
                simp [ColSeq.perm, matchg, EdgePerm.apply]
              all_goals
                first
                | simpa [ColSeq.perm] using ih [] w
                | simpa [ColSeq.perm] using ih [false] w
                | simpa [ColSeq.perm] using ih [true] w
          | cons b lb =>
              cases b <;> cases e <;> cases s <;>
                simp [ColSeq.perm, matchg, EdgePerm.apply]
              all_goals
                first
                | simpa [ColSeq.perm] using ih lb w
                | simpa [ColSeq.perm] using ih (false :: lb) w
                | simpa [ColSeq.perm] using ih (true :: lb) w
                | simpa [ColSeq.perm] using ih (false :: false :: lb) w
                | simpa [ColSeq.perm] using ih (false :: true :: lb) w
                | simpa [ColSeq.perm] using ih (true :: false :: lb) w
                | simpa [ColSeq.perm] using ih (true :: true :: lb) w

theorem matchPartial_flip_perm132
    (bs : BitStack) (et : ColSeq) (w : Chromogram) :
    matchPartial bs.flip (ColSeq.perm EdgePerm.p132 et) w =
      matchPartial bs et w := by
  calc
    matchPartial bs.flip (ColSeq.perm EdgePerm.p132 et) w
        = matchg (bs.flip.toList) (ColSeq.perm EdgePerm.p132 et) w := by
            rw [matchPartial_eq_matchg]
    _ = matchg (bs.toList.map Bool.not) (ColSeq.perm EdgePerm.p132 et) w := by
            rw [BitStack.toList_flip]
    _ = matchg bs.toList et w := matchg_map_not_perm132 bs.toList et w
    _ = matchPartial bs et w := by
            rw [matchPartial_eq_matchg]

theorem matchPartial_empty_perm132
    (et : ColSeq) (w : Chromogram) :
    matchPartial BitStack.empty (ColSeq.perm EdgePerm.p132 et) w =
      matchPartial BitStack.empty et w := by
  simpa using matchPartial_flip_perm132 BitStack.empty et w

theorem matchg_etrace
    (et : ColSeq) (w : Chromogram) :
    matchg [] (ColSeq.etrace et) w = matchg [] et w := by
  by_cases heven : ColSeq.evenTrace et = true
  · rw [ColSeq.etrace_of_even heven]
  · have hfalse : ColSeq.evenTrace et = false := by
      cases h : ColSeq.evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    rw [ColSeq.etrace_of_not_even hfalse]
    simpa using matchg_map_not_perm132 [] et w

theorem matchPartial_empty_etrace
    (et : ColSeq) (w : Chromogram) :
    matchPartial BitStack.empty (ColSeq.etrace et) w =
      matchPartial BitStack.empty et w := by
  rw [matchPartial_empty_eq_matchg, matchPartial_empty_eq_matchg,
    matchg_etrace]

theorem matchg_length
    {lb : List Bool} {et : ColSeq} {w : Chromogram}
    (hmatch : matchg lb et w = true) :
    w.length = et.length := by
  induction et generalizing lb w with
  | nil =>
      cases w with
      | nil => rfl
      | cons s w =>
          simp [matchg] at hmatch
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchg] at hmatch
      | cons s w =>
          cases lb with
          | nil =>
              cases e <;> cases s <;> simp [matchg] at hmatch ⊢
              all_goals exact ih hmatch
          | cons b lb =>
              cases b <;> cases e <;> cases s <;>
                simp [matchg] at hmatch ⊢
              all_goals exact ih hmatch

theorem matchg_complete_of_ctrace
    {cw : Chromogram} {et : ColSeq}
    (hmatch : matchg [] (ColSeq.ctrace et) cw = true) :
    complete 0 false cw.dropLast = cw := by
  have hne : cw ≠ [] := by
    intro hcw
    have hlen := matchg_length hmatch
    rw [hcw, ColSeq.length_ctrace] at hlen
    exact Nat.succ_ne_zero et.length (by
      simpa [Nat.succ_eq_add_one] using hlen.symm)
  have hbal : balanced 0 false cw = true := by
    have hb := (matchg_balanced hmatch).2
    simpa [Color.bit0] using hb
  exact complete_dropLast_of_balanced hne hbal

theorem matchg_eq_complete_of_ctrace
    {cw : Chromogram} {et : ColSeq}
    (hmatch : matchg [] (ColSeq.ctrace et) cw = true) :
    cw = complete 0 false cw.dropLast :=
  (matchg_complete_of_ctrace hmatch).symm

theorem matchg_not_mem_zero
    {lb : List Bool} {et : ColSeq} {w : Chromogram}
    (hmatch : matchg lb et w = true) :
    Color.zero ∉ et := by
  induction et generalizing lb w with
  | nil =>
      simp
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchg] at hmatch
      | cons s w =>
          cases lb with
          | nil =>
              cases e <;> cases s <;> simp [matchg] at hmatch ⊢
              all_goals exact ih hmatch
          | cons b lb =>
              cases b <;> cases e <;> cases s <;>
                simp [matchg] at hmatch ⊢
              all_goals exact ih hmatch

theorem matchPartial_length
    {bs : BitStack} {et : ColSeq} {w : Chromogram}
    (hmatch : matchPartial bs et w = true) :
    w.length = et.length := by
  induction et generalizing bs w with
  | nil =>
      cases w with
      | nil => rfl
      | cons s w =>
          simp [matchPartial] at hmatch
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchPartial] at hmatch
      | cons s w =>
          cases e <;> cases s <;> cases bs <;>
            simp [matchPartial] at hmatch ⊢
          all_goals exact ih hmatch

theorem matchPartial_not_mem_zero
    {bs : BitStack} {et : ColSeq} {w : Chromogram}
    (hmatch : matchPartial bs et w = true) :
    Color.zero ∉ et := by
  induction et generalizing bs w with
  | nil =>
      simp
  | cons e et ih =>
      cases w with
      | nil =>
          simp [matchPartial] at hmatch
      | cons s w =>
          cases e <;> cases s <;> cases bs <;>
            simp [matchPartial] at hmatch ⊢
          all_goals simpa using ih hmatch

/-- A predicate is Kempe-closed when it is closed under colour permutations and
under all traces represented by a chromogram matching any of its traces. -/
def KempeClosed (P : ColSeq → Prop) : Prop :=
  ∀ et, P et →
    (∀ g : EdgePerm, P (ColSeq.perm g et)) ∧
      ∃ w : Chromogram,
        matchg [] et w = true ∧
          ∀ et', matchg [] et' w = true → P et'

/-- The Kempe co-closure of a trace with respect to a trace predicate. -/
def KempeCoclosure (P : ColSeq → Prop) (et : ColSeq) : Prop :=
  ∀ P' : ColSeq → Prop,
    KempeClosed P' → P' et →
      ∃ et', P et' ∧ P' et'

theorem KempeCoclosure.perm
    {P : ColSeq → Prop} {et : ColSeq}
    (hclose : KempeCoclosure P et) (g : EdgePerm) :
    KempeCoclosure P (ColSeq.perm g et) := by
  intro P' hclosed hP'
  have hP'et : P' et := by
    have h := (hclosed (ColSeq.perm g et) hP').1 (EdgePerm.inv g)
    simpa [ColSeq.perm_inv] using h
  exact hclose P' hclosed hP'et

end Chromogram

end FourColor

end Schematic.Math.GraphTheory
