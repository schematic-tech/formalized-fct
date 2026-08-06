import FourColorTheorem.FourColor.Discharging.PartGeometry.HeadAlternatives
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem fitp_split_or_complement_of_arity_ge_five
    (hge : ∀ y : G.Dart, 5 ≤ G.arity y)
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) (x : G.Dart)
    (hfit : fitp G x p = true) :
    fitp G x (split i j k lo p) = true ∨
      fitp G x (split i j k (!lo) p) = true := by
  induction j generalizing p x with
  | zero =>
      cases i
      · cases p with
        | Pnil =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons s h p =>
            have hsplit :=
              fitp_split_head_spoke_low_or_high (G := G) k s h p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons6 h f1 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons7 h f1 f2 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons8 h f1 f2 f3 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
      · cases p with
        | Pnil =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons s h p =>
            have hsplit :=
              fitp_split_head_hat_low_or_high (G := G) k s h p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons6 h f1 p =>
            have hsplit :=
              fitp_split_head_hat6_low_or_high (G := G) k h f1 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons7 h f1 f2 p =>
            have hsplit :=
              fitp_split_head_hat7_low_or_high (G := G) k h f1 f2 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons8 h f1 f2 f3 p =>
            have hsplit :=
              fitp_split_head_hat8_low_or_high
                (G := G) k h f1 f2 f3 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
      · cases p with
        | Pnil =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons s h p =>
            cases s <;> first
              | (have hsplit :=
                    fitp_split_head_fan1_pr66_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | (have hsplit :=
                    fitp_split_head_fan1_pr77_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | (have hsplit :=
                    fitp_split_head_fan1_pr88_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons6 h f1 p =>
            have hsplit :=
              fitp_split_head_fan1_6_low_or_high (G := G) k h f1 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons7 h f1 f2 p =>
            have hsplit :=
              fitp_split_head_fan1_7_low_or_high
                (G := G) k h f1 f2 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons8 h f1 f2 f3 p =>
            have hsplit :=
              fitp_split_head_fan1_8_low_or_high
                (G := G) k h f1 f2 f3 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
      · cases p with
        | Pnil =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons s h p =>
            cases s <;> first
              | (have hsplit :=
                    fitp_split_head_fan2_pr77_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | (have hsplit :=
                    fitp_split_head_fan2_pr88_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons6 h f1 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons7 h f1 f2 p =>
            have hsplit :=
              fitp_split_head_fan2_7_low_or_high
                (G := G) k h f1 f2 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
        | Pcons8 h f1 f2 f3 p =>
            have hsplit :=
              fitp_split_head_fan2_8_low_or_high
                (G := G) k h f1 f2 f3 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
      · cases p with
        | Pnil =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons s h p =>
            cases s <;> first
              | (have hsplit :=
                    fitp_split_head_fan3_pr88_low_or_high_of_arity_ge_five
                      (G := G) hge k h p x hfit
                 cases lo
                 · rcases hsplit with hlo | hhi
                   · exact Or.inr (by simpa using hlo)
                   · exact Or.inl (by simpa using hhi)
                 · exact hsplit)
              | exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons6 h f1 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons7 h f1 f2 p =>
            exact Or.inl (by simpa [split, take, drop] using hfit)
        | Pcons8 h f1 f2 f3 p =>
            have hsplit :=
              fitp_split_head_fan3_8_low_or_high
                (G := G) k h f1 f2 f3 p x hfit
            cases lo
            · rcases hsplit with hlo | hhi
              · exact Or.inr (by simpa using hlo)
              · exact Or.inl (by simpa using hhi)
            · exact hsplit
  | succ j ih =>
      cases p with
      | Pnil =>
          exact Or.inl (by simpa [split, take, drop] using hfit)
      | Pcons s h p =>
          simp only [fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true] at hfit
          rcases hfit with ⟨⟨hs, hh⟩, ht⟩
          rcases ih p (G.face x) ht with hlo | hhi
          · exact Or.inl (by
              simpa [fitp, hs, hh] using hlo)
          · exact Or.inr (by
              simpa [fitp, hs, hh] using hhi)
      | Pcons6 h f1 p =>
          simp only [fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hfit
          rcases hfit with ⟨⟨⟨hs, hh⟩, hf1⟩, ht⟩
          rcases ih p (G.face x) ht with hlo | hhi
          · exact Or.inl (by
              simpa [fitp, hs, hh, hf1] using hlo)
          · exact Or.inr (by
              simpa [fitp, hs, hh, hf1] using hhi)
      | Pcons7 h f1 f2 p =>
          simp only [fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfit
          rcases hfit with ⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, ht⟩
          rcases ih p (G.face x) ht with hlo | hhi
          · exact Or.inl (by
              simpa [fitp, hs, hh, hf1, hf2] using hlo)
          · exact Or.inr (by
              simpa [fitp, hs, hh, hf1, hf2] using hhi)
      | Pcons8 h f1 f2 f3 p =>
          simp only [fitp] at hfit
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfit
          rcases hfit with ⟨⟨⟨⟨⟨hs, hh⟩, hf1⟩, hf2⟩, hf3⟩, ht⟩
          rcases ih p (G.face x) ht with hlo | hhi
          · exact Or.inl (by
              simpa [fitp, hs, hh, hf1, hf2, hf3] using hlo)
          · exact Or.inr (by
              simpa [fitp, hs, hh, hf1, hf2, hf3] using hhi)

end

end Part

end FourColor

end Schematic.Math.GraphTheory
