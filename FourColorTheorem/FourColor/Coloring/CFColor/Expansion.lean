import FourColorTheorem.FourColor.Coloring.CFColor.FoldSpecification

/-!
Expansion of derived configuration-program steps into primitive steps.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Colouring tree for a configuration program. -/
def cpColor (cp : CProg) : CTree :=
  CTree.consRot (cpColor0 cp.reverse)

/-- Fast colouring tree for a configuration program. -/
def cpColorFast (cp : CProg) : CTree :=
  CTree.consRot (cpColor0Fast cp.reverse)

/-- Expand the derived `Y` and `H` construction steps into primitive colouring
steps, matching Coq's `cpexpand1`. -/
def expandStep : CpStep → CProg
  | CpStep.y => [CpStep.reverseRotate, CpStep.k, CpStep.rotate 1, CpStep.u]
  | CpStep.h =>
      [CpStep.reverseRotate, CpStep.k, CpStep.k, CpStep.rotate 1, CpStep.u]
  | s => [s]

/-- Program expansion obtained by concatenating the step expansions. -/
def expand : CProg → CProg
  | [] => []
  | s :: cp => expandStep s ++ expand cp

@[simp]
theorem cpColorStep_rotate
    (n : Nat) (f : ColSeq → CTree) (et : ColSeq) :
    cpColorStep (CpStep.rotate n) f et =
      f (CProg.rotateLeft n et) := rfl

@[simp]
theorem cpColor0_rotate (n : Nat) (cp : CProg) :
    cpColor0 (CpStep.rotate n :: cp) = cpColor0 cp := rfl

@[simp]
theorem cpColor_nil :
    cpColor [] = CTree.consRot (cpBranch [Color.one, Color.one]) := rfl

theorem cpColorFoldFast_spec :
    ∀ (cp : CProg) (et : ColSeq), cpColorFoldFast cp et = cpColorFold cp et
  | [], et => cpBranchFast_spec et
  | s :: cp, et => by
      have hfun : cpColorFoldFast cp = cpColorFold cp := by
        funext et'
        exact cpColorFoldFast_spec cp et'
      change cpColorStep s (cpColorFoldFast cp) et =
        cpColorStep s (cpColorFold cp) et
      rw [hfun]

theorem cpColor0Fast_spec :
    ∀ cp : CProg, cpColor0Fast cp = cpColor0 cp
  | CpStep.rotate _ :: cp => cpColor0Fast_spec cp
  | CpStep.y :: cp => cpColorFoldFast_spec cp _
  | CpStep.u :: cp => by
      simp [cpColor0Fast, cpColor0, cpColorFoldFast_spec]
  | CpStep.h :: cp => cpColorFoldFast_spec _ _
  | CpStep.k :: cp => cpColorFoldFast_spec _ _
  | CpStep.a :: cp => cpColorFoldFast_spec _ _
  | CpStep.reverseRotate :: cp => cpColorFoldFast_spec _ _
  | [] => cpColorFoldFast_spec [] _

theorem cpColorFast_spec (cp : CProg) :
    cpColorFast cp = cpColor cp := by
  simp [cpColorFast, cpColor, cpColor0Fast_spec]

@[simp]
theorem expand_nil :
    expand [] = [] := rfl

@[simp]
theorem expand_singleton (s : CpStep) :
    expand [s] = expandStep s := by
  cases s <;> rfl

theorem expand_append (cp₁ cp₂ : CProg) :
    expand (cp₁ ++ cp₂) = expand cp₁ ++ expand cp₂ := by
  induction cp₁ with
  | nil =>
      rfl
  | cons s cp ih =>
      simp [expand, ih, List.append_assoc]

theorem expand_concat (cp : CProg) (s : CpStep) :
    expand (cp ++ [s]) = expand cp ++ expand [s] := by
  simpa using expand_append cp [s]

theorem expandStep_ne_nil (s : CpStep) :
    expandStep s ≠ [] := by
  cases s <;> simp [expandStep]

theorem expand_ne_nil_of_ne_nil :
    ∀ {cp : CProg}, cp ≠ [] → expand cp ≠ []
  | [], h => by
      exact False.elim (h rfl)
  | s :: cp, _ => by
      simp [expand, expandStep_ne_nil s]

set_option linter.unusedSimpArgs false in
theorem cpColorStep_y_expandStep_reverse_of_head_ne_zero
    (f : ColSeq → CTree) {e : Color} (he : e ≠ Color.zero)
    (et : ColSeq) :
    cpColorStep CpStep.y f (e :: et) =
      ((expandStep CpStep.y).reverse.foldr cpColorStep f) (e :: et) := by
  cases e <;> cases et <;>
    simp_all [cpColorStep, expandStep, sameHead, rotateRight, EdgePerm.apply]
  all_goals exact CTree.union_comm _ _

set_option linter.unusedSimpArgs false in
theorem cpColorStep_h_expandStep_reverse_of_heads_ne_zero
    (f : ColSeq → CTree) {e1 e2 : Color}
    (he1 : e1 ≠ Color.zero) (he2 : e2 ≠ Color.zero)
    (et : ColSeq) :
    cpColorStep CpStep.h f (e1 :: e2 :: et) =
      ((expandStep CpStep.h).reverse.foldr cpColorStep f) (e1 :: e2 :: et) := by
  cases e1 <;> cases e2 <;> cases et <;>
    simp_all [cpColorStep, expandStep, sameHead, rotateRight, EdgePerm.apply]
  all_goals exact CTree.union_comm _ _

theorem cpColorStep_expandStep_reverse_of_not_mem_zero
    (s : CpStep) (f : ColSeq → CTree) (et : ColSeq)
    (hzero : Color.zero ∉ et) :
    cpColorStep s f et =
      ((expandStep s).reverse.foldr cpColorStep f) et := by
  cases s with
  | rotate n =>
      simp [expandStep]
  | reverseRotate =>
      simp [expandStep]
  | u =>
      simp [expandStep]
  | k =>
      simp [expandStep]
  | a =>
      simp [expandStep]
  | y =>
      cases et with
      | nil =>
          simp [cpColorStep, expandStep, sameHead]
      | cons e et =>
          exact cpColorStep_y_expandStep_reverse_of_head_ne_zero
            f (et := et) (by
              intro he
              exact hzero (by simp [he]))
  | h =>
      cases et with
      | nil =>
          simp [cpColorStep, expandStep, sameHead]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep, expandStep, sameHead]
          | cons e2 et =>
              exact cpColorStep_h_expandStep_reverse_of_heads_ne_zero
                f (et := et)
                (by
                  intro he
                  exact hzero (by simp [he]))
                (by
                  intro he
                  exact hzero (by simp [he]))

set_option linter.unusedSimpArgs false in
theorem cpColorStepSpec_y_expandStep_reverse_of_head_ne_zero
    (P : ColSeq → ColSeq → Prop) {e : Color} (he : e ≠ Color.zero)
    (et et' : ColSeq) :
    cpColorStepSpec CpStep.y P (e :: et) et' ↔
      ((expandStep CpStep.y).reverse.foldr cpColorStepSpec P)
        (e :: et) et' := by
  cases e <;> cases et <;>
    simp_all [cpColorStepSpec, expandStep, rotateRight, EdgePerm.apply,
      or_comm, or_left_comm, or_assoc]

set_option linter.unusedSimpArgs false in
theorem cpColorStepSpec_h_expandStep_reverse_of_heads_ne_zero
    (P : ColSeq → ColSeq → Prop) {e1 e2 : Color}
    (he1 : e1 ≠ Color.zero) (he2 : e2 ≠ Color.zero)
    (et et' : ColSeq) :
    cpColorStepSpec CpStep.h P (e1 :: e2 :: et) et' ↔
      ((expandStep CpStep.h).reverse.foldr cpColorStepSpec P)
        (e1 :: e2 :: et) et' := by
  cases e1 <;> cases e2 <;> cases et <;>
    simp_all [cpColorStepSpec, expandStep, rotateRight, EdgePerm.apply,
      or_comm, or_left_comm, or_assoc]

theorem cpColorStepSpec_expandStep_reverse_of_not_mem_zero
    (s : CpStep) (P : ColSeq → ColSeq → Prop) (et et' : ColSeq)
    (hzero : Color.zero ∉ et) :
    cpColorStepSpec s P et et' ↔
      ((expandStep s).reverse.foldr cpColorStepSpec P) et et' := by
  cases s with
  | rotate n =>
      simp [expandStep]
  | reverseRotate =>
      simp [expandStep]
  | u =>
      simp [expandStep]
  | k =>
      simp [expandStep]
  | a =>
      simp [expandStep]
  | y =>
      cases et with
      | nil =>
          simp [cpColorStepSpec, expandStep]
      | cons e et =>
          exact cpColorStepSpec_y_expandStep_reverse_of_head_ne_zero
            P (et := et) (et' := et') (by
              intro he
              exact hzero (by simp [he]))
  | h =>
      cases et with
      | nil =>
          simp [cpColorStepSpec, expandStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec, expandStep]
          | cons e2 et =>
              exact cpColorStepSpec_h_expandStep_reverse_of_heads_ne_zero
                P (et := et) (et' := et')
                (by
                  intro he
                  exact hzero (by simp [he]))
                (by
                  intro he
                  exact hzero (by simp [he]))

set_option linter.unusedSimpArgs false in
theorem cpColorStep_congr_on_not_mem_zero
    (s : CpStep) (f g : ColSeq → CTree)
    (hfg : ∀ et, Color.zero ∉ et → f et = g et)
    (et : ColSeq) (hzero : Color.zero ∉ et) :
    cpColorStep s f et = cpColorStep s g et := by
  cases s with
  | rotate n =>
      exact hfg _ ((CProg.not_mem_rotateLeft Color.zero n et).2 hzero)
  | reverseRotate =>
      simp [cpColorStep]
      split
      · rfl
      · exact hfg _ (by rwa [not_mem_rotateRight])
  | u =>
      simp [cpColorStep, sameHead]
      rw [hfg (Color.one :: Color.one :: et) (by simp [hzero])]
      rw [hfg (Color.two :: Color.two :: et) (by simp [hzero])]
      rw [hfg (Color.three :: Color.three :: et) (by simp [hzero])]
  | k =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStep, heq]
              · have hsum : e1 + e2 ≠ Color.zero := by
                  intro hsum
                  exact heq ((Color.add_eq_zero_iff_eq e1 e2).1 hsum)
                have htail : Color.zero ∉ et := by
                  intro hz
                  exact hzero (by simp [hz])
                have hsum' : Color.zero ≠ e1 + e2 := by
                  intro h
                  exact hsum h.symm
                simp [cpColorStep, heq]
                exact hfg _ (by simp [hsum', htail])
  | y =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e et =>
          cases e <;> simp at hzero
          all_goals
            simp [cpColorStep, EdgePerm.apply]
            repeat rw [hfg _ (by simp [hzero])]
  | h =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              cases e1 <;> cases e2 <;> simp at hzero
              all_goals
                simp [cpColorStep, sameHead, EdgePerm.apply]
                repeat rw [hfg _ (by simp [hzero])]
  | a =>
      cases et with
      | nil =>
          simp [cpColorStep]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStep]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · subst e2
                simp [cpColorStep]
                split
                · exact hfg _ hzero
                · exact hfg _ (by
                    intro hz
                    exact hzero (by simp [hz]))
              · simp [cpColorStep, heq]

theorem cpColorStep_expandStep_reverse_congr_on_not_mem_zero
    (s : CpStep) (f g : ColSeq → CTree)
    (hfg : ∀ et, Color.zero ∉ et → f et = g et)
    (et : ColSeq) (hzero : Color.zero ∉ et) :
    ((expandStep s).reverse.foldr cpColorStep f) et =
      ((expandStep s).reverse.foldr cpColorStep g) et := by
  rw [← cpColorStep_expandStep_reverse_of_not_mem_zero s f et hzero,
    ← cpColorStep_expandStep_reverse_of_not_mem_zero s g et hzero]
  exact cpColorStep_congr_on_not_mem_zero s f g hfg et hzero

/-- Expansion in the order in which a reversed program is consumed by
`foldr cpColorStep`: each step is replaced by the reverse of its primitive
expansion. -/
def expandRev : CProg → CProg
  | [] => []
  | s :: cp => (expandStep s).reverse ++ expandRev cp

@[simp]
theorem expandRev_nil :
    expandRev [] = [] := rfl

@[simp]
theorem expandRev_cons (s : CpStep) (cp : CProg) :
    expandRev (s :: cp) = (expandStep s).reverse ++ expandRev cp := rfl

theorem expandRev_append (cp₁ cp₂ : CProg) :
    expandRev (cp₁ ++ cp₂) = expandRev cp₁ ++ expandRev cp₂ := by
  induction cp₁ with
  | nil =>
      rfl
  | cons s cp ih =>
      simp [expandRev, ih, List.append_assoc]

theorem expandRev_reverse_eq (cp : CProg) :
    expandRev cp.reverse = (expand cp).reverse := by
  induction cp with
  | nil =>
      rfl
  | cons s cp ih =>
      simp [expand, expandRev_append, ih, List.reverse_append]

theorem cpColorFold_expandRev_of_not_mem_zero
    (rp : CProg) (f : ColSeq → CTree) :
    ∀ et, Color.zero ∉ et →
      rp.foldr cpColorStep f et =
        (expandRev rp).foldr cpColorStep f et := by
  induction rp with
  | nil =>
      intro et hzero
      simp [expandRev]
  | cons s rp ih =>
      intro et hzero
      calc
        cpColorStep s (rp.foldr cpColorStep f) et =
            ((expandStep s).reverse.foldr cpColorStep
              (rp.foldr cpColorStep f)) et := by
          exact cpColorStep_expandStep_reverse_of_not_mem_zero s _ et hzero
        _ = ((expandStep s).reverse.foldr cpColorStep
              ((expandRev rp).foldr cpColorStep f)) et := by
          exact cpColorStep_expandStep_reverse_congr_on_not_mem_zero
            s _ _ ih et hzero
        _ = ((expandRev (s :: rp)).foldr cpColorStep f) et := by
          simp [expandRev, List.foldr_append]

theorem cpColorFold_reverse_expand_of_not_mem_zero
    (cp : CProg) (f : ColSeq → CTree) (et : ColSeq)
    (hzero : Color.zero ∉ et) :
    (cp.reverse.foldr cpColorStep f) et =
      ((expand cp).reverse.foldr cpColorStep f) et := by
  rw [← expandRev_reverse_eq cp]
  exact cpColorFold_expandRev_of_not_mem_zero cp.reverse f et hzero

set_option linter.unusedSimpArgs false in
theorem cpColorStepSpec_congr_on_not_mem_zero
    (s : CpStep) (P Q : ColSeq → ColSeq → Prop)
    (hPQ : ∀ et, Color.zero ∉ et → ∀ et', P et et' ↔ Q et et')
    (et et' : ColSeq) (hzero : Color.zero ∉ et) :
    cpColorStepSpec s P et et' ↔ cpColorStepSpec s Q et et' := by
  cases s with
  | rotate n =>
      exact hPQ _ ((CProg.not_mem_rotateLeft Color.zero n et).2 hzero) et'
  | reverseRotate =>
      simp [cpColorStepSpec]
      intro _
      exact hPQ _ (by rwa [not_mem_rotateRight]) et'
  | u =>
      simp [cpColorStepSpec]
      rw [hPQ (Color.one :: Color.one :: et) (by simp [hzero]) et']
      rw [hPQ (Color.two :: Color.two :: et) (by simp [hzero]) et']
      rw [hPQ (Color.three :: Color.three :: et) (by simp [hzero]) et']
  | k =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · simp [cpColorStepSpec, heq]
              · have hsum : e1 + e2 ≠ Color.zero := by
                  intro hsum
                  exact heq ((Color.add_eq_zero_iff_eq e1 e2).1 hsum)
                have htail : Color.zero ∉ et := by
                  intro hz
                  exact hzero (by simp [hz])
                have hsum' : Color.zero ≠ e1 + e2 := by
                  intro h
                  exact hsum h.symm
                simp [cpColorStepSpec, heq]
                exact hPQ _ (by simp [hsum', htail]) et'
  | y =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e et =>
          cases e <;> simp at hzero
          all_goals
            simp [cpColorStepSpec, EdgePerm.apply]
            repeat rw [hPQ _ (by simp [hzero]) et']
  | h =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              cases e1 <;> cases e2 <;> simp at hzero
              all_goals
                simp [cpColorStepSpec, EdgePerm.apply]
                repeat rw [hPQ _ (by simp [hzero]) et']
  | a =>
      cases et with
      | nil =>
          simp [cpColorStepSpec]
      | cons e1 et =>
          cases et with
          | nil =>
              simp [cpColorStepSpec]
          | cons e2 et =>
              by_cases heq : e1 = e2
              · subst e2
                simp [cpColorStepSpec]
                split
                · exact hPQ _ hzero et'
                · exact hPQ _ (by
                    intro hz
                    exact hzero (by simp [hz])) et'
              · simp [cpColorStepSpec, heq]

theorem cpColorStepSpec_expandStep_reverse_congr_on_not_mem_zero
    (s : CpStep) (P Q : ColSeq → ColSeq → Prop)
    (hPQ : ∀ et, Color.zero ∉ et → ∀ et', P et et' ↔ Q et et')
    (et et' : ColSeq) (hzero : Color.zero ∉ et) :
    ((expandStep s).reverse.foldr cpColorStepSpec P) et et' ↔
      ((expandStep s).reverse.foldr cpColorStepSpec Q) et et' := by
  rw [← cpColorStepSpec_expandStep_reverse_of_not_mem_zero s P et et' hzero,
    ← cpColorStepSpec_expandStep_reverse_of_not_mem_zero s Q et et' hzero]
  exact cpColorStepSpec_congr_on_not_mem_zero s P Q hPQ et et' hzero

theorem cpColorFoldSpec_expandRev_of_not_mem_zero
    (rp : CProg) (P : ColSeq → ColSeq → Prop) :
    ∀ et et', Color.zero ∉ et →
      (rp.foldr cpColorStepSpec P et et' ↔
        (expandRev rp).foldr cpColorStepSpec P et et') := by
  induction rp with
  | nil =>
      intro et et' hzero
      simp [expandRev]
  | cons s rp ih =>
      intro et et' hzero
      calc
        cpColorStepSpec s (rp.foldr cpColorStepSpec P) et et' ↔
            ((expandStep s).reverse.foldr cpColorStepSpec
              (rp.foldr cpColorStepSpec P)) et et' := by
          exact cpColorStepSpec_expandStep_reverse_of_not_mem_zero
            s _ et et' hzero
        _ ↔ ((expandStep s).reverse.foldr cpColorStepSpec
              ((expandRev rp).foldr cpColorStepSpec P)) et et' := by
          exact cpColorStepSpec_expandStep_reverse_congr_on_not_mem_zero
            s _ _ (fun et hzero et' => ih et et' hzero) et et' hzero
        _ ↔ ((expandRev (s :: rp)).foldr cpColorStepSpec P) et et' := by
          simp [expandRev, List.foldr_append]

theorem cpColorFoldSpec_reverse_expand_of_not_mem_zero
    (cp : CProg) (P : ColSeq → ColSeq → Prop) (et et' : ColSeq)
    (hzero : Color.zero ∉ et) :
    (cp.reverse.foldr cpColorStepSpec P) et et' ↔
      ((expand cp).reverse.foldr cpColorStepSpec P) et et' := by
  rw [← expandRev_reverse_eq cp]
  exact cpColorFoldSpec_expandRev_of_not_mem_zero cp.reverse P et et' hzero


end CProg

end FourColor

end Schematic.Math.GraphTheory
