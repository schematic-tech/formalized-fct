import FourColorTheorem.FourColor.Coloring.KempeTree.ClosureZero

/-!
Correctness of closure steps in the three degenerate branches.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

@[simp]
theorem step_empty_ctu
    (h : Nat) (closure : ClosureFun) (gtp : GTree.Pair) :
    step h closure ⟨CTree.empty, gtp⟩ = ⟨CTree.empty, gtp⟩ := rfl

@[simp]
theorem stepCtr_empty_ctu
    (h : Nat) (ctr : CTree) (gtp : GTree.Pair) :
    stepCtr h ctr ⟨CTree.empty, gtp⟩ = ctr := rfl

theorem step_empty_gtp_left
    (h : Nat) (closure : ClosureFun) (ctu : CTree) (gtu : GTree) :
    step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩ =
      ⟨ctu, ⟨GTree.empty, gtu⟩⟩ := by
  unfold step
  cases hctu : CTree.isEmpty ctu with
  | false =>
      simp [GTree.isEmpty]
  | true =>
      simp

theorem stepCtr_empty_gtp_left
    (h : Nat) (ctr ctu : CTree) (gtu : GTree) :
    stepCtr h ctr ⟨ctu, ⟨GTree.empty, gtu⟩⟩ = ctr := by
  unfold stepCtr
  cases hctu : CTree.isEmpty ctu with
  | false =>
      simp [GTree.isEmpty]
  | true =>
      simp

theorem step_empty_ctu_valid
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctr : CTree} {gtr gtu : GTree}
    (hvalid : Valid h P CTree.empty ctr gtr gtu) :
    Valid h P (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).ctu ctr
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.right := by
  simpa using hvalid

theorem step_empty_ctu_complete
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctr : CTree} {gtr gtu : GTree}
    (hcomplete : Complete sz P CTree.empty ctr gtr gtu) :
    Complete sz P (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).ctu ctr
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.right := by
  simpa using hcomplete

theorem step_empty_ctu_complete_of_pos
    (h sz sz' : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctr : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hcomplete : Complete sz' P CTree.empty ctr gtr gtu) :
    Complete sz P (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).ctu ctr
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.right := by
  constructor
  · left
    simpa using hsz
  · exact hcomplete.2

theorem step_empty_ctu_correct
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctr : CTree} {gtr gtu : GTree}
    (hvalid : Valid h P CTree.empty ctr gtr gtu)
    (hcomplete : Complete sz P CTree.empty ctr gtr gtu) :
    Valid h P (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).ctu ctr
        (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).ctu ctr
        (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨CTree.empty, ⟨gtr, gtu⟩⟩).gtp.right :=
  ⟨step_empty_ctu_valid h closure hvalid,
    step_empty_ctu_complete h sz closure hcomplete⟩

theorem step_empty_gtp_left_valid
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) :
    Valid h P (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).ctu ctr
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.right := by
  rw [step_empty_gtp_left]
  exact hvalid

theorem step_empty_gtp_left_complete
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtu : GTree}
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Complete sz P (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).ctu ctr
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.right := by
  rw [step_empty_gtp_left]
  exact hcomplete

theorem step_empty_gtp_left_complete_empty_ctr
    (h sz sz' : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtu : GTree}
    (hcomplete : Complete sz' P ctu CTree.empty GTree.empty gtu) :
    Complete sz P (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).ctu
      CTree.empty
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.right := by
  rw [step_empty_gtp_left]
  exact Complete.mono_of_empty_ctr_gtr hcomplete

theorem step_empty_gtp_left_correct
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu)
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Valid h P (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).ctu ctr
        (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).ctu ctr
        (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨GTree.empty, gtu⟩⟩).gtp.right :=
  ⟨step_empty_gtp_left_valid h closure hvalid,
    step_empty_gtp_left_complete h sz closure hcomplete⟩

theorem step_empty_gtp_right_of_active
    (h : Nat) (closure : ClosureFun) (ctu : CTree) (gtr : GTree)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false) :
    step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩ =
      ⟨CTree.empty, GTree.emptyPair⟩ := by
  have hright : GTree.isEmpty GTree.empty = true := rfl
  simp [step, hctu, hleft, hright]

theorem stepCtr_empty_gtp_right_of_active
    (h : Nat) (ctr ctu : CTree) (gtr : GTree)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false) :
    stepCtr h ctr ⟨ctu, ⟨gtr, GTree.empty⟩⟩ = ctr := by
  have hright : GTree.isEmpty GTree.empty = true := rfl
  simp [stepCtr, hctu, hleft, hright]

theorem step_empty_gtp_right_valid_of_active
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hvalid : Valid h P ctu ctr gtr GTree.empty) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).ctu ctr
      (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.right := by
  rw [step_empty_gtp_right_of_active h closure ctu gtr hctu hleft]
  constructor
  · exact CTree.proper_empty (h + 1)
  constructor
  · intro et
    cases ColSeq.evenTrace et <;> simp [GTree.emptyPair, GTree.sub_empty]
  constructor
  · intro et hmem
    exact Valid.ctr_mem hvalid hmem
  constructor
  · intro w hmem
    have hfalse : False := by
      change GTree.mem GTree.empty w = true at hmem
      simp at hmem
    exact False.elim hfalse
  constructor
  · intro w hmem
    have hfalse : False := by
      change GTree.mem GTree.empty w = true at hmem
      simp at hmem
    exact False.elim hfalse
  · intro w hmem hspec
    exact Valid.gtu_nonmem_complete hvalid (by simp) hspec

theorem step_empty_gtp_right_complete_of_active
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr : GTree}
    (hsz : 0 < sz)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).ctu ctr
      (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.right := by
  rw [step_empty_gtp_right_of_active h closure ctu gtr hctu hleft]
  constructor
  · left
    simpa using hsz
  · intro et _hprem
    right
    exact GTree.sub_empty Chromogram.BitStack.empty et

theorem step_empty_gtp_right_correct_of_active
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr : GTree}
    (hsz : 0 < sz)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hvalid : Valid h P ctu ctr gtr GTree.empty) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).ctu ctr
        (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).ctu ctr
        (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, GTree.empty⟩⟩).gtp.right :=
  ⟨step_empty_gtp_right_valid_of_active h closure hctu hleft hvalid,
    step_empty_gtp_right_complete_of_active h sz closure hsz hctu hleft⟩

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
