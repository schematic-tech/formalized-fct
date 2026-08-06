import FourColorTheorem.FourColor.Coloring.KempeMap.WitnessRotation

/-!
Fixed and nonfixed chromogram transformations used by Kempe reduction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The two-symbol wrapper used by the fixed-face branch of Coq `Kempe_map`. -/
def fixedKempeGram (e : Color) (w : Chromogram) : Chromogram :=
  if e = Color.one then
    GramSymbol.skip :: GramSymbol.skip :: w
  else
    GramSymbol.push :: GramSymbol.pop0 :: w

theorem match_fixedKempeGram
    (e : Color) (w : Chromogram) (et : ColSeq)
    (he : e ≠ Color.zero)
    (hw : Chromogram.matchg [] et w = true) :
    Chromogram.matchg [] (e :: e :: et) (fixedKempeGram e w) = true := by
  cases e <;> simp_all [fixedKempeGram, Chromogram.matchg]

theorem match_fixedKempeGram_iff
    (seed : Color) (w : Chromogram) (et : ColSeq)
    (hseed : seed ≠ Color.zero)
    (hmatch : Chromogram.matchg [] et (fixedKempeGram seed w) = true) :
    ∃ e, e ≠ Color.zero ∧ ∃ et',
      Chromogram.matchg [] et' w = true ∧ et = e :: e :: et' := by
  rcases et with _ | ⟨a, _ | ⟨b, et'⟩⟩
  · cases seed <;> simp_all [fixedKempeGram, Chromogram.matchg]
  · cases seed <;> cases a <;>
      simp_all [fixedKempeGram, Chromogram.matchg]
  · cases seed <;> cases a <;> cases b <;>
      simp_all [fixedKempeGram, Chromogram.matchg]

/-- Color-word identity in the nonfixed-face branch. -/
theorem urtrace_nonfixed_relation_of_tail_last
    (a b c e : Color) (cs : ColSeq)
    (hlast : (b :: cs).getLastD b = e) :
    let e1 := e + a
    let e2 := e + c
    let tail := (a + b) :: ColSeq.pairSums b cs
    ColSeq.urtrace (a :: b :: cs) = e1 :: tail ∧
      ColSeq.urtrace (c :: a :: b :: cs) =
        e2 :: (e2 + e1) :: tail := by
  dsimp only
  cases cs with
  | nil =>
      simp only [List.getLastD_cons, List.getLastD_nil] at hlast
      subst e
      cases a <;> cases b <;> cases c <;>
        decide
  | cons d ds =>
      simp only [List.getLastD_cons] at hlast
      simp only [ColSeq.urtrace, ColSeq.pairSums_cons,
        List.getLastD_cons]
      rw [hlast]
      constructor
      · rfl
      · congr 2
        cases a <;> cases c <;> cases e <;> decide

/-- Coq's three-way wrapper in the nonfixed-face branch. -/
def nonfixedKempeGram : Chromogram -> Chromogram
  | s1 :: s2 :: w =>
      if s1 = GramSymbol.skip ∨ s2 = GramSymbol.skip then
        GramSymbol.push :: Chromogram.gramNeg w
      else if s2 = GramSymbol.push then
        GramSymbol.skip :: Chromogram.gramFlip w
      else
        GramSymbol.skip :: w
  | _ => []

/-- Coq `Ds12`: exactly the leading-symbol alternatives left by a matched
reduced trace whose two color difference is nonzero. -/
def nonfixedKempeAdmissible : Chromogram -> Prop
  | GramSymbol.push :: s2 :: _ => s2 ≠ GramSymbol.pop0
  | GramSymbol.skip :: GramSymbol.push :: _ => True
  | _ => False

theorem nonfixedKempeAdmissible_of_match
    (e1 e2 : Color) (tail : ColSeq) (w : Chromogram)
    (he1 : e1 ≠ Color.zero)
    (hw : Chromogram.matchg []
      (e2 :: (e2 + e1) :: tail) w = true) :
    nonfixedKempeAdmissible w := by
  rcases w with _ | ⟨s1, _ | ⟨s2, w⟩⟩
  · simp [Chromogram.matchg] at hw
  · cases s1 <;> cases e1 <;> cases e2 <;>
      simp_all [Chromogram.matchg]
  · cases s1 <;> cases s2 <;> cases e1 <;> cases e2 <;>
      simp_all [nonfixedKempeAdmissible, Chromogram.matchg]

theorem nonfixedKempeGram_ne_nil_of_admissible
    {w : Chromogram} (hadm : nonfixedKempeAdmissible w) :
    nonfixedKempeGram w ≠ [] := by
  rcases w with _ | ⟨s1, _ | ⟨s2, w⟩⟩
  · simp [nonfixedKempeAdmissible] at hadm
  · cases s1 <;> simp [nonfixedKempeAdmissible] at hadm
  · cases s1 <;> cases s2 <;>
      simp_all [nonfixedKempeAdmissible, nonfixedKempeGram]

theorem match_nonfixedKempeGram
    (e1 e2 : Color) (tail : ColSeq) (w : Chromogram)
    (he1 : e1 ≠ Color.zero)
    (hw : Chromogram.matchg []
      (e2 :: (e2 + e1) :: tail) w = true) :
    Chromogram.matchg [] (e1 :: tail) (nonfixedKempeGram w) = true := by
  rcases w with _ | ⟨s1, _ | ⟨s2, w⟩⟩
  · simp [Chromogram.matchg] at hw
  · cases s1 <;> cases e1 <;> cases e2 <;>
      simp_all [Chromogram.matchg]
  · cases s1 <;> cases s2 <;> cases e1 <;> cases e2 <;>
      simp_all [nonfixedKempeGram, Chromogram.matchg,
        Chromogram.matchGramNeg, Chromogram.matchGramFlip]

theorem match_nonfixedKempeGram_exists
    (e1 : Color) (tail : ColSeq) (w : Chromogram)
    (hadm : nonfixedKempeAdmissible w)
    (hmatch : Chromogram.matchg [] (e1 :: tail)
      (nonfixedKempeGram w) = true) :
    ∃ e2, [e2, e2 + e1].Nodup ∧
      Chromogram.matchg [] (e2 :: (e2 + e1) :: tail) w = true := by
  rcases w with _ | ⟨s1, _ | ⟨s2, w⟩⟩
  · cases e1 <;> simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
  · cases s1 <;> cases e1 <;>
      simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
  · cases s1 with
    | push =>
        cases s2 with
        | push =>
            cases e1 with
            | zero =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | one =>
                have hm :
                    Chromogram.matchg [] tail (Chromogram.gramFlip w) = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                have hor :
                    Chromogram.matchg [true, false] tail w = true ∨
                      Chromogram.matchg [false, true] tail w = true := by
                  rw [Chromogram.matchGramFlip] at hm
                  simpa [Bool.or_eq_true] using hm
                rcases hor with htf | hft
                · refine ⟨Color.two, by simp, ?_⟩
                  simpa [Chromogram.matchg] using htf
                · refine ⟨Color.three, by simp, ?_⟩
                  simpa [Chromogram.matchg] using hft
            | two =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | three =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
        | skip =>
            cases e1 with
            | zero =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | one =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | two =>
                have hm : Chromogram.matchg [false] tail
                    (Chromogram.gramNeg w) = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                rw [Chromogram.matchGramNeg] at hm
                refine ⟨Color.three, by simp, ?_⟩
                simpa [Chromogram.matchg] using hm
            | three =>
                have hm : Chromogram.matchg [true] tail
                    (Chromogram.gramNeg w) = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                rw [Chromogram.matchGramNeg] at hm
                refine ⟨Color.two, by simp, ?_⟩
                simpa [Chromogram.matchg] using hm
        | pop0 =>
            simp [nonfixedKempeAdmissible] at hadm
        | pop1 =>
            cases e1 with
            | zero =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | one =>
                have hm : Chromogram.matchg [] tail w = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                refine ⟨Color.two, by simp, ?_⟩
                simpa [Chromogram.matchg] using hm
            | two =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | three =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
    | skip =>
        cases s2 with
        | push =>
            cases e1 with
            | zero =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | one =>
                simp [nonfixedKempeGram, Chromogram.matchg] at hmatch
            | two =>
                have hm : Chromogram.matchg [false] tail
                    (Chromogram.gramNeg w) = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                rw [Chromogram.matchGramNeg] at hm
                refine ⟨Color.one, by simp, ?_⟩
                simpa [Chromogram.matchg] using hm
            | three =>
                have hm : Chromogram.matchg [true] tail
                    (Chromogram.gramNeg w) = true := by
                  simpa [nonfixedKempeGram, Chromogram.matchg] using hmatch
                rw [Chromogram.matchGramNeg] at hm
                refine ⟨Color.one, by simp, ?_⟩
                simpa [Chromogram.matchg] using hm
        | skip => simp [nonfixedKempeAdmissible] at hadm
        | pop0 => simp [nonfixedKempeAdmissible] at hadm
        | pop1 => simp [nonfixedKempeAdmissible] at hadm
    | pop0 => simp [nonfixedKempeAdmissible] at hadm
    | pop1 => simp [nonfixedKempeAdmissible] at hadm


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
