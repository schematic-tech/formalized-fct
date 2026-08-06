import FourColorTheorem.FourColor.Coloring.Chromogram

/-!
Basic Kempe closure algebra.

The hard theorem later is that suitable planar ring-trace predicates are
Kempe-closed.  This file contains only the predicate-level algebra that is
independent of topology and configurations.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace Chromogram

/-- Negate the parity bit of the first pop symbol not matched by an earlier
push, carrying a depth counter for already-open pushes. -/
def gramNegRec : Nat → Chromogram → Chromogram
  | _, [] => []
  | n, GramSymbol.push :: w => GramSymbol.push :: gramNegRec (n + 1) w
  | n, GramSymbol.skip :: w => GramSymbol.skip :: gramNegRec n w
  | 0, GramSymbol.pop0 :: w => GramSymbol.pop1 :: w
  | 0, GramSymbol.pop1 :: w => GramSymbol.pop0 :: w
  | n + 1, GramSymbol.pop0 :: w => GramSymbol.pop0 :: gramNegRec n w
  | n + 1, GramSymbol.pop1 :: w => GramSymbol.pop1 :: gramNegRec n w

/-- Negate the parity bit of the first unmatched pop in a chromogram. -/
def gramNeg (w : Chromogram) : Chromogram :=
  gramNegRec 0 w

theorem matchGramNegRec_append
    (b : Bool) :
    ∀ (w : Chromogram) (et : ColSeq) (lb : List Bool),
      matchg (lb ++ [b]) et (gramNegRec lb.length w) =
        matchg (lb ++ [!b]) et w
  | [], [], [] => by
      cases b <;> rfl
  | [], [], a :: lb => by
      cases a <;> cases b <;> rfl
  | [], e :: et, [] => by
      cases e <;> cases b <;> rfl
  | [], e :: et, a :: lb => by
      cases e <;> cases a <;> cases b <;> rfl
  | GramSymbol.push :: w, [], [] => by
      cases b <;> rfl
  | GramSymbol.push :: w, [], a :: lb => by
      cases a <;> cases b <;> rfl
  | GramSymbol.push :: w, e :: et, lb => by
      cases e <;> simp [gramNegRec, matchg]
      · simpa using matchGramNegRec_append b w et (false :: lb)
      · simpa using matchGramNegRec_append b w et (true :: lb)
  | GramSymbol.skip :: w, [], [] => by
      cases b <;> rfl
  | GramSymbol.skip :: w, [], a :: lb => by
      cases a <;> cases b <;> rfl
  | GramSymbol.skip :: w, e :: et, lb => by
      cases e <;> simp [gramNegRec, matchg, matchGramNegRec_append b w et]
  | GramSymbol.pop0 :: w, [], [] => by
      cases b <;> rfl
  | GramSymbol.pop0 :: w, [], a :: lb => by
      cases a <;> cases b <;> rfl
  | GramSymbol.pop0 :: w, e :: et, [] => by
      cases e <;> cases b <;> rfl
  | GramSymbol.pop0 :: w, e :: et, a :: lb => by
      cases e <;> cases a <;> simp [gramNegRec, matchg,
        matchGramNegRec_append b w et]
  | GramSymbol.pop1 :: w, [], [] => by
      cases b <;> rfl
  | GramSymbol.pop1 :: w, [], a :: lb => by
      cases a <;> cases b <;> rfl
  | GramSymbol.pop1 :: w, e :: et, [] => by
      cases e <;> cases b <;> rfl
  | GramSymbol.pop1 :: w, e :: et, a :: lb => by
      cases e <;> cases a <;> simp [gramNegRec, matchg,
        matchGramNegRec_append b w et]

theorem matchGramNeg
    (b : Bool) (et : ColSeq) (w : Chromogram) :
    matchg [b] et (gramNeg w) = matchg [!b] et w := by
  simpa [gramNeg] using matchGramNegRec_append b w et []

/-- Change the next unmatched pop into a push, adjusting the next unmatched
pop so that the overall parity is inverted. -/
def gramFlipRec : Nat → Chromogram → Chromogram
  | _, [] => [GramSymbol.push]
  | n, GramSymbol.push :: w => GramSymbol.push :: gramFlipRec (n + 1) w
  | n, GramSymbol.skip :: w => GramSymbol.skip :: gramFlipRec n w
  | 0, GramSymbol.pop0 :: w => GramSymbol.push :: gramNeg w
  | 0, GramSymbol.pop1 :: w => GramSymbol.push :: w
  | n + 1, GramSymbol.pop0 :: w => GramSymbol.pop0 :: gramFlipRec n w
  | n + 1, GramSymbol.pop1 :: w => GramSymbol.pop1 :: gramFlipRec n w

/-- Flip the first unmatched pop in a chromogram. -/
def gramFlip (w : Chromogram) : Chromogram :=
  gramFlipRec 0 w

theorem matchGramFlipRec_append :
    ∀ (w : Chromogram) (et : ColSeq) (lb : List Bool),
      matchg lb et (gramFlipRec lb.length w) =
        (matchg (lb ++ [true, false]) et w ||
          matchg (lb ++ [false, true]) et w)
  | [], [], [] => rfl
  | [], [], a :: lb => by
      cases a <;> rfl
  | [], e :: et, [] => by
      cases e <;> cases et <;> rfl
  | [], e :: et, a :: lb => by
      cases e <;> cases a <;> cases et <;> rfl
  | GramSymbol.push :: w, [], [] => rfl
  | GramSymbol.push :: w, [], a :: lb => by
      cases a <;> rfl
  | GramSymbol.push :: w, e :: et, lb => by
      cases e <;> simp [gramFlipRec, matchg]
      · simpa using matchGramFlipRec_append w et (false :: lb)
      · simpa using matchGramFlipRec_append w et (true :: lb)
  | GramSymbol.skip :: w, [], [] => rfl
  | GramSymbol.skip :: w, [], a :: lb => by
      cases a <;> rfl
  | GramSymbol.skip :: w, e :: et, lb => by
      cases e <;> simp [gramFlipRec, matchg, matchGramFlipRec_append w et lb]
  | GramSymbol.pop0 :: w, [], [] => rfl
  | GramSymbol.pop0 :: w, [], a :: lb => by
      cases a <;> rfl
  | GramSymbol.pop0 :: w, e :: et, [] => by
      cases e <;> simp [gramFlipRec, matchg]
      · simpa [gramNeg] using matchGramNeg false et w
      · simpa [gramNeg] using matchGramNeg true et w
  | GramSymbol.pop0 :: w, e :: et, a :: lb => by
      cases e <;> cases a <;> simp [gramFlipRec, matchg,
        matchGramFlipRec_append w et lb]
  | GramSymbol.pop1 :: w, [], [] => rfl
  | GramSymbol.pop1 :: w, [], a :: lb => by
      cases a <;> rfl
  | GramSymbol.pop1 :: w, e :: et, [] => by
      cases e <;> simp [gramFlipRec, matchg]
  | GramSymbol.pop1 :: w, e :: et, a :: lb => by
      cases e <;> cases a <;> simp [gramFlipRec, matchg,
        matchGramFlipRec_append w et lb]

theorem matchGramFlip
    (et : ColSeq) (w : Chromogram) :
    matchg [] et (gramFlip w) =
      (matchg [true, false] et w || matchg [false, true] et w) := by
  simpa [gramFlip] using matchGramFlipRec_append w et []

/-- Reading a final `skip` symbol after a prefix only succeeds when the final
edge colour is `Color.one` and the prefix has already closed all stack entries. -/
theorem matchg_append_skip :
    ∀ (lb : List Bool) (et : ColSeq) (w : Chromogram) (e : Color),
      matchg lb (et ++ [e]) (w ++ [GramSymbol.skip]) =
        (matchg lb et w &&
          match e with
          | Color.one => true
          | _ => false)
  | lb, [], [], e => by
      cases lb <;> cases e <;> rfl
  | [], [], s :: w, e => by
      cases s <;> cases e <;> cases w <;> simp [matchg]
  | b :: lb, [], s :: w, e => by
      cases b <;> cases s <;> cases e <;> cases w <;> simp [matchg]
  | [], c :: et, [], e => by
      cases c <;> cases et <;> cases e <;> simp [matchg]
  | b :: lb, c :: et, [], e => by
      cases b <;> cases c <;> cases et <;> cases e <;> simp [matchg]
  | [], c :: et, s :: w, e => by
      cases c <;> cases s <;>
        simp [matchg, matchg_append_skip]
  | b :: lb, c :: et, s :: w, e => by
      cases b <;> cases c <;> cases s <;>
        simp [matchg, matchg_append_skip]

/-- Boolean analogue of MathComp's `belast`: `boolPrevs b [x,y] = [b,x]`. -/
def boolPrevs (fallback : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => fallback :: boolPrevs b bs

@[simp]
theorem boolPrevs_nil (fallback : Bool) :
    boolPrevs fallback [] = [] := rfl

@[simp]
theorem boolPrevs_cons (fallback b : Bool) (bs : List Bool) :
    boolPrevs fallback (b :: bs) = fallback :: boolPrevs b bs := rfl

@[simp]
theorem getLastD_cons_bool (fallback b : Bool) (bs : List Bool) :
    (b :: bs).getLastD fallback = bs.getLastD b := by
  cases bs with
  | nil => rfl
  | cons c cs =>
      simp [List.getLastD]

@[simp]
theorem getLast?_getD_cons_bool (fallback b : Bool) (bs : List Bool) :
    (b :: bs).getLast?.getD fallback = bs.getLast?.getD b := by
  cases bs with
  | nil => rfl
  | cons c cs =>
      rw [List.getLast?_cons_cons,
        List.getLast?_eq_getLast_of_ne_nil (by simp : c :: cs ≠ [])]
      simp

/-- Reading a final `pop1` after a balanced prefix leaves exactly the final
stack bit specified by the rotated edge colour. -/
theorem matchg_append_pop1_of_balanced :
    ∀ (w : Chromogram) (lb : List Bool) (b b0 : Bool) (et : ColSeq) (e : Color),
      balanced lb.length b0 w = true →
        matchg (b :: lb) (et ++ [e]) (w ++ [GramSymbol.pop1]) =
          ((decide (e = Color.cons true (!(lb.getLastD b)))) &&
            matchg (boolPrevs b lb) et w)
  | [], [], b, b0, [], e, hbal => by
      cases b0 <;> simp [balanced] at hbal
      cases b <;> cases e <;> simp [matchg, Color.cons]
  | [], [], b, b0, c :: et, e, hbal => by
      cases b0 <;> simp [balanced] at hbal
      cases b <;> cases c <;> cases et <;> cases e <;> simp [matchg, Color.cons]
  | [], b' :: lb, b, b0, et, e, hbal => by
      simp [balanced] at hbal
  | GramSymbol.push :: w, lb, b, b0, [], e, hbal => by
      cases b <;> cases e <;> simp [matchg]
  | GramSymbol.push :: w, lb, b, b0, c :: et, e, hbal => by
      cases c <;> simp [matchg, balanced] at hbal ⊢
      · simpa [getLastD_cons_bool] using
          matchg_append_pop1_of_balanced w (b :: lb) false b0 et e hbal
      · simpa [getLastD_cons_bool] using
          matchg_append_pop1_of_balanced w (b :: lb) true b0 et e hbal
  | GramSymbol.skip :: w, lb, b, b0, [], e, hbal => by
      cases b <;> cases e <;> simp [matchg]
  | GramSymbol.skip :: w, lb, b, b0, c :: et, e, hbal => by
      cases c <;> simp [matchg, balanced] at hbal ⊢
      simpa using matchg_append_pop1_of_balanced w lb b (!b0) et e hbal
  | GramSymbol.pop0 :: w, [], b, b0, et, e, hbal => by
      simp [balanced] at hbal
  | GramSymbol.pop0 :: w, b' :: lb, b, b0, [], e, hbal => by
      cases b <;> cases b' <;> cases e <;> simp [matchg]
  | GramSymbol.pop0 :: w, b' :: lb, b, b0, c :: et, e, hbal => by
      cases b <;> cases c <;>
        simp [matchg, balanced] at hbal ⊢
      all_goals
        simpa using matchg_append_pop1_of_balanced w lb b' b0 et e hbal
  | GramSymbol.pop1 :: w, [], b, b0, et, e, hbal => by
      simp [balanced] at hbal
  | GramSymbol.pop1 :: w, b' :: lb, b, b0, [], e, hbal => by
      cases b <;> cases b' <;> cases e <;> simp [matchg]
  | GramSymbol.pop1 :: w, b' :: lb, b, b0, c :: et, e, hbal => by
      cases b <;> cases c <;>
        simp [matchg, balanced] at hbal ⊢
      all_goals
        simpa using matchg_append_pop1_of_balanced w lb b' (!b0) et e hbal

/-- Whether a chromogram is balanced for one of the two possible outer
parities. -/
def hasBalanced (w : Chromogram) : Bool :=
  balanced 0 false w || balanced 0 true w

theorem matchg_eq_false_of_not_hasBalanced
    {et : ColSeq} {w : Chromogram}
    (h : hasBalanced w = false) :
    matchg [] et w = false := by
  cases hmatch : matchg [] et w
  · rfl
  · rcases matchg_balanced hmatch with ⟨_, hbal⟩
    cases hsum : (ColSeq.sum et).bit0
    · have : hasBalanced w = true := by
        rw [hsum] at hbal
        simp [hasBalanced, hbal]
      rw [h] at this
      contradiction
    · have : hasBalanced w = true := by
        rw [hsum] at hbal
        simp [hasBalanced, hbal]
      rw [h] at this
      contradiction

/-- Rotate a balanced chromogram by one perimeter edge.  This is the executable
operation from Gonthier's `gram_rot`; the matching theorem is the next Kempe
layer. -/
def gramRot (w : Chromogram) : Chromogram :=
  if hasBalanced w then
    match w with
    | GramSymbol.push :: w' => gramFlip (w' ++ [GramSymbol.pop1])
    | GramSymbol.skip :: w' => w' ++ [GramSymbol.skip]
    | _ => w
  else
    w

@[simp]
theorem gramRot_nil :
    gramRot [] = [] := by
  simp [gramRot, hasBalanced]

theorem gramRot_of_not_hasBalanced
    {w : Chromogram}
    (h : hasBalanced w = false) :
    gramRot w = w := by
  simp [gramRot, h]

theorem gramRot_push_of_hasBalanced
    {w : Chromogram}
    (h : hasBalanced (GramSymbol.push :: w) = true) :
    gramRot (GramSymbol.push :: w) = gramFlip (w ++ [GramSymbol.pop1]) := by
  simp [gramRot, h]

theorem matchGramRot_push_of_balanced
    (et : ColSeq) (w : Chromogram) (b0 : Bool)
    (hbal : balanced 1 b0 w = true) :
    matchg [] (ColSeq.rot1 et) (gramFlip (w ++ [GramSymbol.pop1])) =
      matchg [] et (GramSymbol.push :: w) := by
  cases et with
  | nil =>
      rw [matchGramFlip]
      cases w with
      | nil =>
          simp [balanced] at hbal
      | cons s w =>
          cases s <;> simp [matchg, ColSeq.rot1]
  | cons e es =>
      rw [ColSeq.rot1, matchGramFlip]
      have htf :=
        matchg_append_pop1_of_balanced w [false] true b0 es e hbal
      have hft :=
        matchg_append_pop1_of_balanced w [true] false b0 es e hbal
      rw [htf, hft]
      cases e <;> simp [matchg, Color.cons]

theorem matchGramRot_push
    (et : ColSeq) (w : Chromogram)
    (h : hasBalanced (GramSymbol.push :: w) = true) :
    matchg [] (ColSeq.rot1 et) (gramRot (GramSymbol.push :: w)) =
      matchg [] et (GramSymbol.push :: w) := by
  rw [gramRot_push_of_hasBalanced h]
  simp [hasBalanced, balanced] at h
  rcases h with hbal | hbal
  · exact matchGramRot_push_of_balanced et w false hbal
  · exact matchGramRot_push_of_balanced et w true hbal

theorem gramRot_skip_of_hasBalanced
    {w : Chromogram}
    (h : hasBalanced (GramSymbol.skip :: w) = true) :
    gramRot (GramSymbol.skip :: w) = w ++ [GramSymbol.skip] := by
  simp [gramRot, h]

theorem matchGramRot_skip
    (et : ColSeq) (w : Chromogram)
    (h : hasBalanced (GramSymbol.skip :: w) = true) :
    matchg [] (ColSeq.rot1 et) (gramRot (GramSymbol.skip :: w)) =
      matchg [] et (GramSymbol.skip :: w) := by
  rw [gramRot_skip_of_hasBalanced h]
  cases et with
  | nil =>
      cases w <;> rfl
  | cons c cs =>
      simp [ColSeq.rot1, matchg_append_skip]
      cases c <;> simp [matchg]

theorem gramRot_pop0_of_hasBalanced
    {w : Chromogram}
    (h : hasBalanced (GramSymbol.pop0 :: w) = true) :
    gramRot (GramSymbol.pop0 :: w) = GramSymbol.pop0 :: w := by
  simp [gramRot, h]

theorem gramRot_pop1_of_hasBalanced
    {w : Chromogram}
    (h : hasBalanced (GramSymbol.pop1 :: w) = true) :
    gramRot (GramSymbol.pop1 :: w) = GramSymbol.pop1 :: w := by
  simp [gramRot, h]

theorem matchGramRot
    (et : ColSeq) (w : Chromogram) :
    matchg [] (ColSeq.rot1 et) (gramRot w) = matchg [] et w := by
  by_cases h : hasBalanced w = true
  · cases w with
    | nil =>
        cases et with
        | nil => rfl
        | cons c cs =>
            cases cs <;> simp [gramRot, hasBalanced, ColSeq.rot1, matchg]
    | cons s w =>
        cases s with
        | push =>
            exact matchGramRot_push et w h
        | skip =>
            exact matchGramRot_skip et w h
        | pop0 =>
            simp [hasBalanced, balanced] at h
        | pop1 =>
            simp [hasBalanced, balanced] at h
  · have hfalse : hasBalanced w = false := by
      cases hw : hasBalanced w with
      | false => rfl
      | true => exact False.elim (h hw)
    rw [gramRot_of_not_hasBalanced hfalse]
    rw [matchg_eq_false_of_not_hasBalanced (et := ColSeq.rot1 et) hfalse]
    rw [matchg_eq_false_of_not_hasBalanced (et := et) hfalse]

theorem KempeClosed.perm
    {P : ColSeq → Prop}
    (hP : KempeClosed P)
    {et : ColSeq}
    (het : P et)
    (g : EdgePerm) :
    P (ColSeq.perm g et) :=
  (hP et het).1 g

theorem KempeClosed.chromogram
    {P : ColSeq → Prop}
    (hP : KempeClosed P)
    {et : ColSeq}
    (het : P et) :
    ∃ w : Chromogram,
      matchg [] et w = true ∧
        ∀ et', matchg [] et' w = true → P et' :=
  (hP et het).2

theorem KempeClosed.congr
    {P Q : ColSeq → Prop}
    (hPQ : ∀ et, P et ↔ Q et)
    (hP : KempeClosed P) :
    KempeClosed Q := by
  intro et hQet
  have hPet : P et := (hPQ et).2 hQet
  rcases hP et hPet with ⟨hperm, w, hmatch, hall⟩
  constructor
  · intro g
    exact (hPQ (ColSeq.perm g et)).1 (hperm g)
  · exact ⟨w, hmatch, fun et' hmatch' =>
      (hPQ et').1 (hall et' hmatch')⟩

theorem kempeClosed_congr_iff
    {P Q : ColSeq → Prop}
    (hPQ : ∀ et, P et ↔ Q et) :
    KempeClosed P ↔ KempeClosed Q := by
  constructor
  · exact KempeClosed.congr hPQ
  · exact KempeClosed.congr (fun et => (hPQ et).symm)

theorem KempeCoclosure.of_mem
    {P : ColSeq → Prop}
    {et : ColSeq}
    (het : P et) :
    KempeCoclosure P et := by
  intro P' hclosed hP'et
  exact ⟨et, het, hP'et⟩

theorem KempeCoclosure.mono
    {P Q : ColSeq → Prop}
    (hPQ : ∀ et, P et → Q et)
    {et : ColSeq}
    (hclose : KempeCoclosure P et) :
    KempeCoclosure Q et := by
  intro P' hclosed hP'et
  rcases hclose P' hclosed hP'et with ⟨et', hPet', hP'et'⟩
  exact ⟨et', hPQ et' hPet', hP'et'⟩

theorem KempeCoclosure.congr
    {P Q : ColSeq → Prop}
    (hPQ : ∀ et, P et ↔ Q et)
    {et : ColSeq}
    (hclose : KempeCoclosure P et) :
    KempeCoclosure Q et :=
  KempeCoclosure.mono (fun et hPet => (hPQ et).1 hPet) hclose

theorem kempeCoclosure_congr_iff
    {P Q : ColSeq → Prop}
    (hPQ : ∀ et, P et ↔ Q et)
    (et : ColSeq) :
    KempeCoclosure P et ↔ KempeCoclosure Q et := by
  constructor
  · exact KempeCoclosure.congr hPQ
  · exact KempeCoclosure.congr (fun et => (hPQ et).symm)

theorem KempeCoclosure.etrace
    {P : ColSeq → Prop} {et : ColSeq}
    (hclose : KempeCoclosure P et) :
    KempeCoclosure P (ColSeq.etrace et) := by
  simpa [ColSeq.etrace] using
    (Chromogram.KempeCoclosure.perm hclose (ColSeq.etracePerm et))

theorem KempeCoclosure.of_etrace
    {P : ColSeq → Prop} {et : ColSeq}
    (hclose : KempeCoclosure P (ColSeq.etrace et)) :
    KempeCoclosure P et := by
  rcases ColSeq.exists_perm_from_etrace EdgePerm.p123 et with ⟨g, hg⟩
  have hperm := Chromogram.KempeCoclosure.perm hclose g
  simpa [ColSeq.perm_id, hg] using hperm

theorem kempeCoclosure_etrace_iff
    {P : ColSeq → Prop} (et : ColSeq) :
    KempeCoclosure P (ColSeq.etrace et) ↔ KempeCoclosure P et := by
  constructor
  · exact KempeCoclosure.of_etrace
  · exact KempeCoclosure.etrace

theorem KempeCoclosure.closed_meets
    {P P' : ColSeq → Prop}
    {et : ColSeq}
    (hclose : KempeCoclosure P et)
    (hP'closed : KempeClosed P')
    (hP'et : P' et) :
    ∃ et', P et' ∧ P' et' :=
  hclose P' hP'closed hP'et

theorem KempeClosed.coclosure_of_mem
    {P : ColSeq → Prop}
    {et : ColSeq}
    (het : P et) :
    KempeCoclosure P et :=
  KempeCoclosure.of_mem het

end Chromogram

end FourColor

end Schematic.Math.GraphTheory
