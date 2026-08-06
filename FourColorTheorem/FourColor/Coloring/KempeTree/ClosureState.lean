import FourColorTheorem.FourColor.Coloring.KempeTree.Restrictions

/-!
Closure-state definitions and their basic validity invariants.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

/-- One closure-improvement step, Coq's `ktc_step`. -/
def step (h : Nat) (closure : ClosureFun) (kr : State) : State :=
  if CTree.isEmpty kr.ctu then kr
  else if GTree.isEmpty kr.gtp.left then kr
  else if GTree.isEmpty kr.gtp.right then
    ⟨CTree.empty, GTree.emptyPair⟩
  else
    let ctp := CTree.restrict h kr.ctu (baseCRestriction kr.gtp.left)
    closure ctp.left (CTree.rotLR ctp.right) kr.gtp.right

/-- Trace tree carried by one closure-improvement step.  This is the explicit
Lean analogue of the extra `ctr` parameter threaded through Coq's
`ktr_prop`-shaped proof. -/
def stepCtr (h : Nat) (ctr : CTree) (kr : State) : CTree :=
  if CTree.isEmpty kr.ctu then ctr
  else if GTree.isEmpty kr.gtp.left then ctr
  else if GTree.isEmpty kr.gtp.right then ctr
  else
    CTree.rotLR
      (CTree.restrict h kr.ctu (baseCRestriction kr.gtp.left)).right

/-- Run a closure and then two improvement steps, Coq's `ktc_step2c`. -/
def step2c
    (stepper : State → State) (closure : ClosureFun) :
    ClosureFun :=
  fun ctu ctr gtu => stepper (stepper (closure ctu ctr gtu))

/-- Improve a closure by using `step` twice, Coq's `ktc_dostep2c`. -/
def doStep2c (h : Nat) (closure : ClosureFun) : ClosureFun :=
  step2c (step h closure) closure

/-- Iterated Kempe-tree closure, Coq's `Kempe_tree_closure`. -/
def closure (h : Nat) : Nat → ClosureFun
  | 0 =>
      fun ctu ctr gtu =>
        ⟨ctu, GTree.restrict gtu (baseGRestriction ctr)⟩
  | d + 1 => doStep2c h (closure h d)

/-- Valid intermediate closure state, matching the statement shape of Coq's
`Kempe_valid`. -/
def Valid
    (h : Nat) (P : ColSeq → Prop)
    (ctu ctr : CTree) (gtr gtu : GTree) : Prop :=
  CTree.Proper (h + 1) ctu ∧
    (∀ et : ColSeq,
      CTree.sub ctu et =
        if ColSeq.evenTrace et then
          GTree.sub gtr Chromogram.BitStack.empty et +
            GTree.sub gtu Chromogram.BitStack.empty et
        else 0) ∧
    (∀ et : ColSeq,
      CTree.mem ctr et = true →
        Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
          et.length = h + 1) ∧
    (∀ w : Chromogram,
      GTree.mem gtr w = true →
        GTree.mem gtu w = false ∧ GTree.initSpec (h + 1) w = true) ∧
    (∀ w : Chromogram,
      GTree.mem gtu w = true → GTree.initSpec (h + 1) w = true) ∧
    (∀ w : Chromogram,
      GTree.mem gtu w = false →
        GTree.initSpec (h + 1) w = true →
          ∃ et : ColSeq,
            Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
              GTree.matchOpen Chromogram.BitStack.empty et w = true)

/-- Completeness target for the closure loop, matching Coq's
`Kempe_complete`. -/
def Complete
    (sz : Nat) (P : ColSeq → Prop)
    (ctu ctr : CTree) (_gtr gtu : GTree) : Prop :=
  (CTree.size ctu < sz ∨
    (ctr = CTree.empty ∧ ∀ w : Chromogram, GTree.mem _gtr w = false)) ∧
    ∀ et : ColSeq,
      (P (ColSeq.ctrace et) ∨
        (∃ e : Color,
          CTree.mem ctu
            (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) = false)) →
        CTree.mem ctr (ColSeq.etrace et) = true ∨
          GTree.sub gtu Chromogram.BitStack.empty et = 0

/-- Exhaust the four branches of a closure step's executable control flow. -/
theorem closureState_cases
    (ctu : CTree) (gtr gtu : GTree) {motive : Prop}
    (emptyCtu : ctu = CTree.empty → motive)
    (emptyLeft : CTree.isEmpty ctu = false → gtr = GTree.empty → motive)
    (emptyRight : CTree.isEmpty ctu = false →
      GTree.isEmpty gtr = false → gtu = GTree.empty → motive)
    (active : CTree.isEmpty ctu = false →
      GTree.isEmpty gtr = false → GTree.isEmpty gtu = false → motive) :
    motive := by
  cases hctu : CTree.isEmpty ctu with
  | true => exact emptyCtu (CTree.isEmpty_eq hctu)
  | false =>
      cases hleft : GTree.isEmpty gtr with
      | true => exact emptyLeft hctu (GTree.isEmpty_eq hleft)
      | false =>
          cases hright : GTree.isEmpty gtu with
          | true => exact emptyRight hctu hleft (GTree.isEmpty_eq hright)
          | false => exact active hctu hleft hright

namespace Valid

theorem ctu_proper
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) :
    CTree.Proper (h + 1) ctu :=
  hvalid.1

theorem ctu_sub
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) (et : ColSeq) :
    CTree.sub ctu et =
      if ColSeq.evenTrace et then
        GTree.sub gtr Chromogram.BitStack.empty et +
          GTree.sub gtu Chromogram.BitStack.empty et
      else 0 :=
  hvalid.2.1 et

theorem ctr_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq}
    (hmem : CTree.mem ctr et = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
      et.length = h + 1 :=
  hvalid.2.2.1 et hmem

theorem gtr_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {w : Chromogram}
    (hmem : GTree.mem gtr w = true) :
    GTree.mem gtu w = false ∧ GTree.initSpec (h + 1) w = true :=
  hvalid.2.2.2.1 w hmem

theorem gtu_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {w : Chromogram}
    (hmem : GTree.mem gtu w = true) :
    GTree.initSpec (h + 1) w = true :=
  hvalid.2.2.2.2.1 w hmem

theorem gtu_nonmem_complete
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {w : Chromogram}
    (hmem : GTree.mem gtu w = false)
    (hspec : GTree.initSpec (h + 1) w = true) :
    ∃ et : ColSeq,
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
        GTree.matchOpen Chromogram.BitStack.empty et w = true :=
  hvalid.2.2.2.2.2 w hmem hspec

end Valid

theorem active_restrict_ctu_proper_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) :
    CTree.Proper (h + 1)
      (CTree.restrict h ctu (baseCRestriction gtr)).left :=
  restrict_baseC_left_proper_of_proper h gtr (Valid.ctu_proper hvalid)

theorem active_restrict_ctu_size_le_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) :
    CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left ≤
      CTree.size ctu :=
  restrict_baseC_left_size_le_of_proper h gtr (Valid.ctu_proper hvalid)

theorem active_restrict_ctu_size_lt_of_valid
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hsize : CTree.size ctu < sz) :
    CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left < sz := by
  have hle := active_restrict_ctu_size_le_of_valid hvalid
  omega

theorem active_restrict_ctu_size_partition_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) :
    CTree.size ctu =
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left +
        CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right :=
  restrict_baseC_size_partition_of_proper h gtr (Valid.ctu_proper hvalid)

theorem restrict_baseC_right_eq_empty_of_size_zero
    (h : Nat) {ctu : CTree} (gtr : GTree)
    (hproper : CTree.Proper (h + 1) ctu)
    (hsize :
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right = 0) :
    (CTree.restrict h ctu (baseCRestriction gtr)).right = CTree.empty :=
  CTree.eq_empty_of_proper_size_zero
    (restrict_baseC_right_proper_of_proper h gtr hproper) hsize

theorem active_restrict_right_eq_empty_of_size_zero
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hsize :
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right = 0) :
    (CTree.restrict h ctu (baseCRestriction gtr)).right = CTree.empty :=
  restrict_baseC_right_eq_empty_of_size_zero h gtr
    (Valid.ctu_proper hvalid) hsize

theorem active_restrict_ctu_size_lt_of_valid_right_pos
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hright :
      0 < CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right) :
    CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).left < sz := by
  have hsplit := active_restrict_ctu_size_partition_of_valid hvalid
  omega

theorem active_restrict_ctu_sub_eq_remaining_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) (et : ColSeq) :
    CTree.sub (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      if ColSeq.evenTrace et then
        GTree.sub gtu Chromogram.BitStack.empty et
      else
        0 := by
  rw [restrict_baseC_left_sub_of_proper h gtr
    (Valid.ctu_proper hvalid) et, Valid.ctu_sub hvalid et]
  cases heven : ColSeq.evenTrace et
  · simp
  · simp

theorem active_restrict_ctu_sub_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) (et : ColSeq) :
    CTree.sub (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      if ColSeq.evenTrace et then
        GTree.sub GTree.empty Chromogram.BitStack.empty et +
          GTree.sub gtu Chromogram.BitStack.empty et
      else
        0 := by
  rw [active_restrict_ctu_sub_eq_remaining_of_valid hvalid et]
  cases ColSeq.evenTrace et <;> simp [GTree.sub_empty]

theorem active_restrict_ctu_mem_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) (et : ColSeq) :
    CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
      (ColSeq.evenTrace et &&
        (GTree.sub gtu Chromogram.BitStack.empty et != 0)) := by
  unfold CTree.mem
  rw [active_restrict_ctu_sub_eq_remaining_of_valid hvalid et]
  cases ColSeq.evenTrace et <;> simp

theorem active_restrict_ctu_mem_true_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et =
        true) :
    ColSeq.evenTrace et = true ∧
      GTree.sub gtu Chromogram.BitStack.empty et ≠ 0 := by
  rw [active_restrict_ctu_mem_of_valid hvalid et] at hmem
  simpa using hmem

theorem active_restrict_right_mem_subs_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).right et =
        true) :
    GTree.sub gtr Chromogram.BitStack.empty et ≠ 0 ∧
      GTree.sub gtu Chromogram.BitStack.empty et = 0 := by
  rcases restrict_baseC_right_mem_true_of_proper h
      (Valid.ctu_proper hvalid) hmem with
    ⟨hctu, hle⟩
  have hctu_ne : CTree.sub ctu et ≠ 0 := by
    unfold CTree.mem at hctu
    simpa using hctu
  have hsub := Valid.ctu_sub hvalid et
  cases heven : ColSeq.evenTrace et
  · rw [heven] at hsub
    simp at hsub
    omega
  · rw [heven] at hsub
    simp at hsub
    constructor <;> omega

theorem active_restrict_rotLR_right_mem_subs_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    (GTree.sub gtr Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p312 et) ≠ 0 ∧
        GTree.sub gtu Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p312 et) = 0) ∨
      (GTree.sub gtr Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p231 et) ≠ 0 ∧
        GTree.sub gtu Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p231 et) = 0) := by
  rcases restrict_baseC_rotLR_right_mem_true_of_proper h
      (Valid.ctu_proper hvalid) hmem with
    hright | hright
  · exact Or.inl (active_restrict_right_mem_subs_of_valid hvalid hright)
  · exact Or.inr (active_restrict_right_mem_subs_of_valid hvalid hright)

private theorem active_restrict_right_mem_gtr_witness_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree} (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq}
    (hsubs : GTree.sub gtr Chromogram.BitStack.empty et ≠ 0 ∧
      GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    ∃ w : Chromogram,
      GTree.mem gtr w = true ∧ GTree.mem gtu w = false ∧
        GTree.initSpec (h + 1) w = true ∧
        GTree.matchOpen Chromogram.BitStack.empty et w = true ∧
        GTree.sub gtu Chromogram.BitStack.empty et = 0 := by
  rcases hsubs with ⟨hgtrNe, hgtuZero⟩
  rcases GTree.exists_mem_match_of_sub_ne_zero hgtrNe with
    ⟨w, hgtr, hmatch⟩
  rcases Valid.gtr_mem hvalid hgtr with ⟨hgtu, hspec⟩
  exact ⟨w, hgtr, hgtu, hspec, hmatch, hgtuZero⟩

theorem active_restrict_rotLR_right_mem_gtr_witness_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    (∃ w : Chromogram,
      GTree.mem gtr w = true ∧
        GTree.mem gtu w = false ∧
        GTree.initSpec (h + 1) w = true ∧
        GTree.matchOpen Chromogram.BitStack.empty
            (ColSeq.perm EdgePerm.p312 et) w =
          true ∧
        GTree.sub gtu Chromogram.BitStack.empty
            (ColSeq.perm EdgePerm.p312 et) =
          0) ∨
      (∃ w : Chromogram,
        GTree.mem gtr w = true ∧
          GTree.mem gtu w = false ∧
          GTree.initSpec (h + 1) w = true ∧
          GTree.matchOpen Chromogram.BitStack.empty
              (ColSeq.perm EdgePerm.p231 et) w =
            true ∧
          GTree.sub gtu Chromogram.BitStack.empty
              (ColSeq.perm EdgePerm.p231 et) =
            0) := by
  rcases active_restrict_rotLR_right_mem_subs_of_valid hvalid hmem with
    hp312 | hp231
  · exact Or.inl
      (active_restrict_right_mem_gtr_witness_of_valid hvalid hp312)
  · exact Or.inr
      (active_restrict_right_mem_gtr_witness_of_valid hvalid hp231)


end KempeTree

end FourColor

end Schematic.Math.GraphTheory
