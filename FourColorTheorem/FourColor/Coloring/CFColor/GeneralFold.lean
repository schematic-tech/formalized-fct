import FourColorTheorem.FourColor.Coloring.CFColor.TraceTrees

/-!
General height and membership correctness for configuration-colouring folds.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Boundary length after one arbitrary coloring-program constructor.  This is
the construction-order form of `ringSize`, including the contracting `K` and
`A` steps omitted by the earlier cubic-only trace fold. -/
def colorStepSize : CpStep → Nat → Nat
  | CpStep.y, n => n + 1
  | CpStep.u, n => n + 2
  | CpStep.k, n => n - 2 + 1
  | CpStep.a, n => if 2 < n then n - 2 else n
  | _, n => n

/-- Height of the terminal trace tree after an arbitrary construction-order
program acts on an input boundary word. -/
def cpColorFoldHeight : CProg → Nat → Nat
  | [], n => n - 2
  | s :: cp, n => cpColorFoldHeight cp (colorStepSize s n)

/-- Variable-height version of Coq `cpcolor_proper`'s fold invariant.  Every
branch generated from a nonzero input has the same terminal height, even for
contracted programs containing `K`, `A`, or reverse rotation. -/
theorem cpColorFold_proper_of_not_mem_zero :
    ∀ (cp : CProg) {input : ColSeq}, Color.zero ∉ input →
      CTree.Proper (cpColorFoldHeight cp input.length)
        (cpColorFold cp input)
  | [], input, hzero => by
      simp only [cpColorFold, List.foldr, cpColorFoldHeight]
      cases input with
      | nil =>
          change CTree.Proper 0 CTree.empty
          exact CTree.proper_empty 0
      | cons e tail =>
          cases tail with
          | nil =>
              change CTree.Proper 0 CTree.empty
              exact CTree.proper_empty 0
          | cons e' rest =>
              have hproper : ColSeq.ProperTrace (e' :: rest) := by
                change e' ≠ Color.zero
                intro he'
                subst e'
                exact hzero (by simp)
              have hlen := ColSeq.length_etail_of_proper hproper
              have hp := cpBranch_proper (e :: e' :: rest)
              have hetail : (ColSeq.etail (e' :: rest)).length = rest.length := by
                have hlen' : (ColSeq.etail (e' :: rest)).length + 1 =
                    rest.length + 1 := by
                  simpa only [List.length_cons] using hlen
                exact Nat.add_right_cancel hlen'
              simpa [hetail] using hp
  | s :: cp, input, hzero => by
      cases s with
      | rotate n =>
          have hzero' : Color.zero ∉ CProg.rotateLeft n input :=
            (CProg.not_mem_rotateLeft Color.zero n input).2 hzero
          have hp := cpColorFold_proper_of_not_mem_zero cp hzero'
          simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
            CProg.cpColorStep, CProg.length_rotateLeft] using hp
      | reverseRotate =>
          by_cases hlen : input.length ≤ 1
          · simp [cpColorFold, cpColorFoldHeight, colorStepSize,
              CProg.cpColorStep, hlen, CTree.proper_empty]
          · have hzero' : Color.zero ∉ CProg.rotateRight 1 input :=
              (CProg.not_mem_rotateRight Color.zero 1 input).2 hzero
            have hp := cpColorFold_proper_of_not_mem_zero cp hzero'
            simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
              CProg.cpColorStep, hlen, CProg.length_rotateRight] using hp
      | y =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                CProg.cpColorStep, CTree.proper_empty]
          | cons e tail =>
              have he : e ≠ Color.zero := by
                intro he
                subst e
                exact hzero (by simp)
              have htail : Color.zero ∉ tail := by
                intro hz
                exact hzero (by simp [hz])
              have hperm (g : EdgePerm) : g e ≠ Color.zero := by
                intro hz
                exact he (EdgePerm.injective g (by simpa using hz))
              have hleft : Color.zero ∉
                  EdgePerm.p231 e :: EdgePerm.p312 e :: tail := by
                simp only [List.mem_cons, not_or]
                exact ⟨(hperm EdgePerm.p231).symm,
                  (hperm EdgePerm.p312).symm, htail⟩
              have hright : Color.zero ∉
                  EdgePerm.p312 e :: EdgePerm.p231 e :: tail := by
                simp only [List.mem_cons, not_or]
                exact ⟨(hperm EdgePerm.p312).symm,
                  (hperm EdgePerm.p231).symm, htail⟩
              have hpLeft := cpColorFold_proper_of_not_mem_zero cp hleft
              have hpRight := cpColorFold_proper_of_not_mem_zero cp hright
              simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                CProg.cpColorStep] using CTree.proper_union hpLeft hpRight
      | h =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                CProg.cpColorStep, CTree.proper_empty]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                    CProg.cpColorStep, CTree.proper_empty]
              | cons e2 rest =>
                  have he1 : e1 ≠ Color.zero := by
                    intro he
                    subst e1
                    exact hzero (by simp)
                  have he2 : e2 ≠ Color.zero := by
                    intro he
                    subst e2
                    exact hzero (by simp)
                  have hrest : Color.zero ∉ rest := by
                    intro hz
                    exact hzero (by simp [hz])
                  by_cases heq : e1 = e2
                  · subst e2
                    have hperm (g : EdgePerm) : g e1 ≠ Color.zero := by
                      intro hz
                      exact he1 (EdgePerm.injective g (by simpa using hz))
                    have hleft : Color.zero ∉
                        EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨(hperm EdgePerm.p231).symm,
                        (hperm EdgePerm.p231).symm, hrest⟩
                    have hright : Color.zero ∉
                        EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨(hperm EdgePerm.p312).symm,
                        (hperm EdgePerm.p312).symm, hrest⟩
                    have hpLeft := cpColorFold_proper_of_not_mem_zero cp hleft
                    have hpRight := cpColorFold_proper_of_not_mem_zero cp hright
                    simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                      CProg.cpColorStep, CProg.sameHead] using
                      CTree.proper_union hpLeft hpRight
                  · have hswap : Color.zero ∉ e2 :: e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨he2.symm, he1.symm, hrest⟩
                    have hp := cpColorFold_proper_of_not_mem_zero cp hswap
                    simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                      CProg.cpColorStep, heq] using hp
      | u =>
          have h1 : Color.zero ∉ Color.one :: Color.one :: input := by
            simpa using hzero
          have h2 : Color.zero ∉ Color.two :: Color.two :: input := by
            simpa using hzero
          have h3 : Color.zero ∉ Color.three :: Color.three :: input := by
            simpa using hzero
          have hp1 := cpColorFold_proper_of_not_mem_zero cp h1
          have hp2 := cpColorFold_proper_of_not_mem_zero cp h2
          have hp3 := cpColorFold_proper_of_not_mem_zero cp h3
          simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
            CProg.cpColorStep, CProg.sameHead] using
            CTree.proper_union hp1 (CTree.proper_union hp2 hp3)
      | k =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                CProg.cpColorStep, CTree.proper_empty]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                    CProg.cpColorStep, CTree.proper_empty]
              | cons e2 rest =>
                  by_cases heq : e1 = e2
                  · simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                      CProg.cpColorStep, heq, CTree.proper_empty]
                  · have hsum : e1 + e2 ≠ Color.zero := by
                      intro hz
                      exact heq ((Color.add_eq_zero_iff_eq e1 e2).1 hz)
                    have hrest : Color.zero ∉ rest := by
                      intro hz
                      exact hzero (by simp [hz])
                    have hmid : Color.zero ∉ (e1 + e2) :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨hsum ∘ Eq.symm, hrest⟩
                    have hp := cpColorFold_proper_of_not_mem_zero cp hmid
                    simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                      CProg.cpColorStep, heq] using hp
      | a =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                CProg.cpColorStep, CTree.proper_empty]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                    CProg.cpColorStep, CTree.proper_empty]
              | cons e2 rest =>
                  by_cases heq : e1 = e2
                  · subst e2
                    by_cases hrestNil : rest = []
                    · subst rest
                      have hp := cpColorFold_proper_of_not_mem_zero cp hzero
                      simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                        CProg.cpColorStep] using hp
                    · have hrest : Color.zero ∉ rest := by
                        intro hz
                        exact hzero (by simp [hz])
                      have hp := cpColorFold_proper_of_not_mem_zero cp hrest
                      have hrestPos : 0 < rest.length :=
                        List.length_pos_iff_ne_nil.mpr hrestNil
                      simpa [cpColorFold, cpColorFoldHeight, colorStepSize,
                        CProg.cpColorStep, hrestNil, hrestPos] using hp
                  · simp [cpColorFold, cpColorFoldHeight, colorStepSize,
                      CProg.cpColorStep, heq, CTree.proper_empty]

/-- Exact membership for the arbitrary-program coloring fold.  Unlike the
older fixed-height theorem, this applies after contraction steps because it
uses the input-dependent height invariant above at each union. -/
theorem cpColorFold_mem_iff_of_not_mem_zero :
    ∀ (cp : CProg) {input : ColSeq}, Color.zero ∉ input →
      ∀ out, CTree.mem (cpColorFold cp input) out = true ↔
        cpColorFoldSpec cp input out
  | [], input, _hzero, out => by
      simpa [cpColorFold, cpColorFoldSpec] using cpBranch_mem_iff input out
  | s :: cp, input, hzero, out => by
      cases s with
      | rotate n =>
          have hzero' : Color.zero ∉ CProg.rotateLeft n input :=
            (CProg.not_mem_rotateLeft Color.zero n input).2 hzero
          simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
            cpColorStepSpec] using
            cpColorFold_mem_iff_of_not_mem_zero cp hzero' out
      | reverseRotate =>
          by_cases hlen : input.length ≤ 1
          · simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
              cpColorStepSpec, hlen]
          · have hzero' : Color.zero ∉ CProg.rotateRight 1 input :=
              (CProg.not_mem_rotateRight Color.zero 1 input).2 hzero
            simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
              cpColorStepSpec, hlen] using
              cpColorFold_mem_iff_of_not_mem_zero cp hzero' out
      | y =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                cpColorStepSpec]
          | cons e tail =>
              have he : e ≠ Color.zero := by
                intro he
                subst e
                exact hzero (by simp)
              have htail : Color.zero ∉ tail := by
                intro hz
                exact hzero (by simp [hz])
              have hperm (g : EdgePerm) : g e ≠ Color.zero := by
                intro hz
                exact he (EdgePerm.injective g (by simpa using hz))
              have hleft : Color.zero ∉
                  EdgePerm.p231 e :: EdgePerm.p312 e :: tail := by
                simp only [List.mem_cons, not_or]
                exact ⟨(hperm EdgePerm.p231).symm,
                  (hperm EdgePerm.p312).symm, htail⟩
              have hright : Color.zero ∉
                  EdgePerm.p312 e :: EdgePerm.p231 e :: tail := by
                simp only [List.mem_cons, not_or]
                exact ⟨(hperm EdgePerm.p312).symm,
                  (hperm EdgePerm.p231).symm, htail⟩
              have hpLeft := cpColorFold_proper_of_not_mem_zero cp hleft
              have hpRight := cpColorFold_proper_of_not_mem_zero cp hright
              rw [show cpColorFold (CpStep.y :: cp) (e :: tail) =
                  CTree.union
                    (cpColorFold cp
                      (EdgePerm.p231 e :: EdgePerm.p312 e :: tail))
                    (cpColorFold cp
                      (EdgePerm.p312 e :: EdgePerm.p231 e :: tail)) by rfl]
              rw [CTree.mem_union_eq_true_iff hpLeft hpRight]
              change
                (CTree.mem (cpColorFold cp
                    (EdgePerm.p231 e :: EdgePerm.p312 e :: tail)) out = true ∨
                  CTree.mem (cpColorFold cp
                    (EdgePerm.p312 e :: EdgePerm.p231 e :: tail)) out = true) ↔
                (cpColorFoldSpec cp
                    (EdgePerm.p231 e :: EdgePerm.p312 e :: tail) out ∨
                  cpColorFoldSpec cp
                    (EdgePerm.p312 e :: EdgePerm.p231 e :: tail) out)
              exact or_congr
                (cpColorFold_mem_iff_of_not_mem_zero cp hleft out)
                (cpColorFold_mem_iff_of_not_mem_zero cp hright out)
      | h =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                cpColorStepSpec]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                    cpColorStepSpec]
              | cons e2 rest =>
                  have he1 : e1 ≠ Color.zero := by
                    intro he
                    subst e1
                    exact hzero (by simp)
                  have he2 : e2 ≠ Color.zero := by
                    intro he
                    subst e2
                    exact hzero (by simp)
                  have hrest : Color.zero ∉ rest := by
                    intro hz
                    exact hzero (by simp [hz])
                  by_cases heq : e1 = e2
                  · subst e2
                    have hperm (g : EdgePerm) : g e1 ≠ Color.zero := by
                      intro hz
                      exact he1 (EdgePerm.injective g (by simpa using hz))
                    have hleft : Color.zero ∉
                        EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨(hperm EdgePerm.p231).symm,
                        (hperm EdgePerm.p231).symm, hrest⟩
                    have hright : Color.zero ∉
                        EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨(hperm EdgePerm.p312).symm,
                        (hperm EdgePerm.p312).symm, hrest⟩
                    have hpLeft := cpColorFold_proper_of_not_mem_zero cp hleft
                    have hpRight := cpColorFold_proper_of_not_mem_zero cp hright
                    rw [show cpColorFold (CpStep.h :: cp)
                          (e1 :: e1 :: rest) =
                        CTree.union
                          (cpColorFold cp
                            (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest))
                          (cpColorFold cp
                            (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest)) by
                      simp [cpColorFold, CProg.cpColorStep, CProg.sameHead]]
                    rw [CTree.mem_union_eq_true_iff hpLeft hpRight]
                    simp only [cpColorFoldSpec, List.foldr, cpColorStepSpec]
                    change
                      (CTree.mem (cpColorFold cp
                          (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest)) out =
                            true ∨
                        CTree.mem (cpColorFold cp
                          (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest)) out =
                            true) ↔
                      (cpColorFoldSpec cp
                          (EdgePerm.p231 e1 :: EdgePerm.p231 e1 :: rest) out ∨
                        cpColorFoldSpec cp
                          (EdgePerm.p312 e1 :: EdgePerm.p312 e1 :: rest) out)
                    exact or_congr
                      (cpColorFold_mem_iff_of_not_mem_zero cp hleft out)
                      (cpColorFold_mem_iff_of_not_mem_zero cp hright out)
                  · have hswap : Color.zero ∉ e2 :: e1 :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨he2.symm, he1.symm, hrest⟩
                    simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                      cpColorStepSpec, heq] using
                      cpColorFold_mem_iff_of_not_mem_zero cp hswap out
      | u =>
          have h1 : Color.zero ∉ Color.one :: Color.one :: input := by
            simpa using hzero
          have h2 : Color.zero ∉ Color.two :: Color.two :: input := by
            simpa using hzero
          have h3 : Color.zero ∉ Color.three :: Color.three :: input := by
            simpa using hzero
          have hp1 := cpColorFold_proper_of_not_mem_zero cp h1
          have hp2 := cpColorFold_proper_of_not_mem_zero cp h2
          have hp3 := cpColorFold_proper_of_not_mem_zero cp h3
          rw [show cpColorFold (CpStep.u :: cp) input =
                CTree.union (cpColorFold cp (Color.one :: Color.one :: input))
                  (CTree.union
                    (cpColorFold cp (Color.two :: Color.two :: input))
                    (cpColorFold cp
                      (Color.three :: Color.three :: input))) by
            simp [cpColorFold, CProg.cpColorStep, CProg.sameHead]]
          rw [CTree.mem_union_eq_true_iff hp1 (CTree.proper_union hp2 hp3)]
          rw [CTree.mem_union_eq_true_iff hp2 hp3]
          change
            (CTree.mem (cpColorFold cp (Color.one :: Color.one :: input)) out =
                true ∨
              CTree.mem (cpColorFold cp (Color.two :: Color.two :: input)) out =
                  true ∨
                CTree.mem
                  (cpColorFold cp (Color.three :: Color.three :: input)) out =
                    true) ↔
            (cpColorFoldSpec cp (Color.one :: Color.one :: input) out ∨
              cpColorFoldSpec cp (Color.two :: Color.two :: input) out ∨
                cpColorFoldSpec cp
                  (Color.three :: Color.three :: input) out)
          exact or_congr
            (cpColorFold_mem_iff_of_not_mem_zero cp h1 out)
            (or_congr
              (cpColorFold_mem_iff_of_not_mem_zero cp h2 out)
              (cpColorFold_mem_iff_of_not_mem_zero cp h3 out))
      | k =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                cpColorStepSpec]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                    cpColorStepSpec]
              | cons e2 rest =>
                  by_cases heq : e1 = e2
                  · simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                      cpColorStepSpec, heq]
                  · have hsum : e1 + e2 ≠ Color.zero := by
                      intro hz
                      exact heq ((Color.add_eq_zero_iff_eq e1 e2).1 hz)
                    have hrest : Color.zero ∉ rest := by
                      intro hz
                      exact hzero (by simp [hz])
                    have hmid : Color.zero ∉ (e1 + e2) :: rest := by
                      simp only [List.mem_cons, not_or]
                      exact ⟨hsum ∘ Eq.symm, hrest⟩
                    simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                      cpColorStepSpec, heq] using
                      cpColorFold_mem_iff_of_not_mem_zero cp hmid out
      | a =>
          cases input with
          | nil =>
              simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                cpColorStepSpec]
          | cons e1 tail =>
              cases tail with
              | nil =>
                  simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                    cpColorStepSpec]
              | cons e2 rest =>
                  by_cases heq : e1 = e2
                  · subst e2
                    by_cases hrestNil : rest = []
                    · subst rest
                      simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                        cpColorStepSpec] using
                        cpColorFold_mem_iff_of_not_mem_zero cp hzero out
                    · have hrest : Color.zero ∉ rest := by
                        intro hz
                        exact hzero (by simp [hz])
                      simpa [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                        cpColorStepSpec, hrestNil] using
                        cpColorFold_mem_iff_of_not_mem_zero cp hrest out
                  · simp [cpColorFold, cpColorFoldSpec, CProg.cpColorStep,
                      cpColorStepSpec, heq]

end CProg

end FourColor

end Schematic.Math.GraphTheory
