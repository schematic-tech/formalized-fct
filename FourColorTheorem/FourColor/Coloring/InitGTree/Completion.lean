import FourColorTheorem.FourColor.Coloring.InitGTree.ContextCounts

/-! Completion of balanced chromograms and open-stack matching. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace GTree

set_option linter.unusedSimpArgs false in
theorem matchg_complete_eq_matchOpen_context
    (et : ColSeq) :
    ∀ (c : Color) (lb : List Bool) (b0 : Bool) (w : Chromogram),
      c.bit0 = Bool.xor b0 (Chromogram.bitParity lb) →
      c.bit1 = Chromogram.oddLength lb →
      Chromogram.balanced lb.length b0
          (Chromogram.complete lb.length b0 w) =
        true →
      Chromogram.matchg lb (et ++ [c + ColSeq.sum et])
          (Chromogram.complete lb.length b0 w) =
        matchOpen (Chromogram.BitStack.ofList lb) et w := by
  induction et with
  | nil =>
      intro c lb b0 w hc0 hc1 hbal
      cases w with
      | nil =>
          cases lb with
          | nil =>
              cases c <;> cases b0 <;>
                simp [Chromogram.complete, Chromogram.balanced,
                  Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                  Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
          | cons top lb =>
              cases lb with
              | nil =>
                  cases top <;> cases c <;> cases b0 <;>
                    simp [Chromogram.complete, Chromogram.balanced,
                      Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                      Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | cons top' lb =>
                  cases top <;> cases top' <;> cases c <;> cases b0 <;>
                    simp [Chromogram.complete, Chromogram.balanced,
                      Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                      Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
      | cons s w =>
          cases s <;> cases lb with
          | nil =>
              cases c <;> cases b0 <;>
                simp [Chromogram.complete, Chromogram.balanced,
                  Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                  Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
          | cons top lb =>
              cases top <;> cases c <;> cases b0 <;>
                simp [Chromogram.complete, Chromogram.balanced,
                  Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                  Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
  | cons e et ih =>
      intro c lb b0 w hc0 hc1 hbal
      cases w with
      | nil =>
          cases e <;> cases lb with
          | nil =>
              cases c <;> cases b0 <;>
                simp [Chromogram.complete, Chromogram.balanced,
                  Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                  Color.bit0, Color.bit1, Color.add_assoc, Color.add_left_comm] at hc0 hc1 hbal ⊢
          | cons top lb =>
              cases top <;> cases c <;> cases b0 <;>
                simp [Chromogram.complete, Chromogram.balanced,
                  Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                  Color.bit0, Color.bit1, Color.add_assoc, Color.add_left_comm] at hc0 hc1 hbal ⊢
      | cons s w =>
          cases e with
          | zero =>
              cases s <;> cases lb with
              | nil =>
                  cases c <;> cases b0 <;>
                    simp [Chromogram.complete, Chromogram.balanced,
                      Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                      Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | cons top lb =>
                  cases top <;> cases c <;> cases b0 <;>
                    simp [Chromogram.complete, Chromogram.balanced,
                      Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg, matchOpen,
                      Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
          | one =>
              cases s with
              | skip =>
                  have hrec := ih (Color.one + c) lb (!b0) w
                    (context_bit0_skip_one c lb b0 hc0)
                    (context_bit1_skip_one c lb hc1)
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced]
                        using hbal)
                  simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
              | push =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top <;> cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | pop0 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top <;> cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | pop1 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top <;> cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
          | two =>
              cases s with
              | push =>
                  have hrec := ih (Color.two + c) (false :: lb) b0 w
                    (context_bit0_push_two c lb b0 hc0)
                    (context_bit1_push_two c lb hc1)
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced]
                        using hbal)
                  simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
              | skip =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top <;> cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | pop0 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top with
                      | false =>
                          have hrec := ih (Color.two + c) lb b0 w
                            (context_bit0_pop_two_zero c lb b0 hc0)
                            (context_bit1_pop_two_zero c lb hc1)
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced]
                                using hbal)
                          simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
                      | true =>
                          cases c <;> cases b0 <;>
                            simp [Chromogram.complete, Chromogram.balanced,
                              Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | pop1 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top with
                      | false =>
                          cases c <;> cases b0 <;>
                            simp [Chromogram.complete, Chromogram.balanced,
                              Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                      | true =>
                          have hrec := ih (Color.two + c) lb (!b0) w
                            (context_bit0_pop_two_one c lb b0 hc0)
                            (context_bit1_pop_two_one c lb hc1)
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced]
                                using hbal)
                          simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
          | three =>
              cases s with
              | push =>
                  have hrec := ih (Color.three + c) (true :: lb) b0 w
                    (context_bit0_push_three c lb b0 hc0)
                    (context_bit1_push_three c lb hc1)
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced]
                        using hbal)
                  simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
              | skip =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top <;> cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
              | pop0 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top with
                      | false =>
                          cases c <;> cases b0 <;>
                            simp [Chromogram.complete, Chromogram.balanced,
                              Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                      | true =>
                          have hrec := ih (Color.three + c) lb b0 w
                            (context_bit0_pop_three_one c lb b0 hc0)
                            (context_bit1_pop_three_one c lb hc1)
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced]
                                using hbal)
                          simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
              | pop1 =>
                  cases lb with
                  | nil =>
                      cases c <;> cases b0 <;>
                        simp [Chromogram.complete, Chromogram.balanced,
                          Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢
                  | cons top lb =>
                      cases top with
                      | false =>
                          have hrec := ih (Color.three + c) lb (!b0) w
                            (context_bit0_pop_three_zero c lb b0 hc0)
                            (context_bit1_pop_three_zero c lb hc1)
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced]
                                using hbal)
                          simpa [Chromogram.complete, Chromogram.balanced, Chromogram.matchg,
                    matchOpen, Color.add_assoc, Color.add_left_comm] using hrec
                      | true =>
                          cases c <;> cases b0 <;>
                            simp [Chromogram.complete, Chromogram.balanced,
                              Chromogram.bitParity, Chromogram.oddLength, Chromogram.matchg,
                  matchOpen, Color.bit0, Color.bit1] at hc0 hc1 hbal ⊢

theorem matchg_ctrace_complete_eq_matchOpen
    (et : ColSeq) (w : Chromogram)
    (hbal :
      Chromogram.balanced 0 false
          (Chromogram.complete 0 false w) =
        true) :
    Chromogram.matchg [] (ColSeq.ctrace et)
        (Chromogram.complete 0 false w) =
      matchOpen Chromogram.BitStack.empty et w := by
  simpa [ColSeq.ctrace, Chromogram.bitParity, Chromogram.oddLength]
    using
      matchg_complete_eq_matchOpen_context et Color.zero [] false w
        rfl rfl hbal

theorem matchg_ctrace_complete_of_matchOpen_initSpec
    {h : Nat} {et : ColSeq} {w : Chromogram}
    (hspec : initSpec h w = true)
    (hmatch : matchOpen Chromogram.BitStack.empty et w = true) :
    Chromogram.matchg [] (ColSeq.ctrace et)
        (Chromogram.complete 0 false w) =
      true := by
  have hbal :
      Chromogram.balanced 0 false
          (Chromogram.complete 0 false w) =
        true := by
    simp [initSpec] at hspec
    exact hspec.2
  rw [matchg_ctrace_complete_eq_matchOpen et w hbal]
  exact hmatch

end GTree

end FourColor

end Schematic.Math.GraphTheory
