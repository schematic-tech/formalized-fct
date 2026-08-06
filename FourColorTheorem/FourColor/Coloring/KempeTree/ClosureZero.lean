import FourColorTheorem.FourColor.Coloring.KempeTree.Trees

/-!
Specification and correctness of the zero-depth closure.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

@[simp]
theorem step2c_apply
    (stepper : State → State) (closure : ClosureFun)
    (ctu ctr : CTree) (gtu : GTree) :
    step2c stepper closure ctu ctr gtu =
      stepper (stepper (closure ctu ctr gtu)) := rfl

@[simp]
theorem doStep2c_apply
    (h : Nat) (closure : ClosureFun)
    (ctu ctr : CTree) (gtu : GTree) :
    doStep2c h closure ctu ctr gtu =
      step h closure (step h closure (closure ctu ctr gtu)) := rfl

@[simp]
theorem closure_zero (h : Nat) (ctu ctr : CTree) (gtu : GTree) :
    closure h 0 ctu ctr gtu =
      ⟨ctu, GTree.restrict gtu (baseGRestriction ctr)⟩ := rfl

@[simp]
theorem closure_succ
    (h d : Nat) (ctu ctr : CTree) (gtu : GTree) :
    closure h (d + 1) ctu ctr gtu =
      step h (closure h d)
        (step h (closure h d) (closure h d ctu ctr gtu)) := rfl

@[simp]
theorem closure_zero_ctu (h : Nat) (ctu ctr : CTree) (gtu : GTree) :
    (closure h 0 ctu ctr gtu).ctu = ctu := rfl

@[simp]
theorem closure_zero_gtp (h : Nat) (ctu ctr : CTree) (gtu : GTree) :
    (closure h 0 ctu ctr gtu).gtp =
      GTree.restrict gtu (baseGRestriction ctr) := rfl

theorem closure_zero_gtp_left_mem
    (h : Nat) (ctu ctr : CTree) (gtu : GTree) (w : Chromogram) :
    GTree.mem (closure h 0 ctu ctr gtu).gtp.left w =
      (GTree.mem gtu w &&
        GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w) := by
  exact restrict_baseG_left_mem gtu ctr w

theorem closure_zero_gtp_right_mem
    (h : Nat) (ctu ctr : CTree) (gtu : GTree) (w : Chromogram) :
    GTree.mem (closure h 0 ctu ctr gtu).gtp.right w =
      (GTree.mem gtu w &&
        !(GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w)) := by
  exact restrict_baseG_right_mem gtu ctr w

theorem closure_zero_gtp_partition
    (h : Nat) (ctu ctr : CTree) (gtu : GTree) :
    GTree.Partition gtu (closure h 0 ctu ctr gtu).gtp := by
  exact GTree.restrict_partition_exact gtu (baseGRestriction ctr)

theorem closure_zero_gtp_sub_add
    (h : Nat) (ctu ctr : CTree) (gtu : GTree)
    (bs : Chromogram.BitStack) (et : ColSeq) :
    GTree.sub gtu bs et =
      GTree.sub (closure h 0 ctu ctr gtu).gtp.left bs et +
        GTree.sub (closure h 0 ctu ctr gtu).gtp.right bs et := by
  exact restrict_baseG_sub_add gtu ctr bs et

theorem closure_zero_gtp_empty_sub_add
    (h : Nat) (ctu ctr : CTree) (gtu : GTree) (et : ColSeq) :
    GTree.sub gtu Chromogram.BitStack.empty et =
      GTree.sub (closure h 0 ctu ctr gtu).gtp.left
          Chromogram.BitStack.empty et +
        GTree.sub (closure h 0 ctu ctr gtu).gtp.right
          Chromogram.BitStack.empty et :=
  closure_zero_gtp_sub_add h ctu ctr gtu Chromogram.BitStack.empty et

theorem closure_zero_ctu_proper_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) :
    CTree.Proper (h + 1) (closure h 0 ctu ctr gtu).ctu :=
  Valid.ctu_proper hvalid

theorem closure_zero_ctu_sub_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) (et : ColSeq) :
    CTree.sub (closure h 0 ctu ctr gtu).ctu et =
      if ColSeq.evenTrace et then
        GTree.sub (closure h 0 ctu ctr gtu).gtp.left
            Chromogram.BitStack.empty et +
          GTree.sub (closure h 0 ctu ctr gtu).gtp.right
            Chromogram.BitStack.empty et
      else 0 := by
  rw [closure_zero_ctu, Valid.ctu_sub hvalid et]
  cases heven : ColSeq.evenTrace et
  · simp
  · simp [GTree.sub_empty,
      closure_zero_gtp_empty_sub_add h ctu ctr gtu et]

private theorem closure_zero_valid_with_ctr
    {h : Nat} {P : ColSeq → Prop} {ctu ctr ctr' : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu)
    (hctr :
      ∀ et : ColSeq, CTree.mem ctr' et = true →
        Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
          et.length = h + 1) :
    Valid h P (closure h 0 ctu ctr gtu).ctu ctr'
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right := by
  constructor
  · exact closure_zero_ctu_proper_of_valid hvalid
  constructor
  · exact closure_zero_ctu_sub_of_valid hvalid
  constructor
  · exact hctr
  constructor
  · intro w hleft
    have hleft' :
        GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).left w =
          true := by
      simpa using hleft
    have hgtu := (restrict_baseG_left_mem_true hleft').1
    have hright := (closure_zero_gtp_partition h ctu ctr gtu).2 w hleft
    exact ⟨hright, Valid.gtu_mem hvalid hgtu⟩
  constructor
  · intro w hright
    have hright' :
        GTree.mem (GTree.restrict gtu (baseGRestriction ctr)).right w =
          true := by
      simpa using hright
    exact Valid.gtu_mem hvalid
      (restrict_baseG_right_mem_true hright').1
  · intro w hright hspec
    cases hgtu : GTree.mem gtu w with
    | false => exact Valid.gtu_nonmem_complete hvalid hgtu hspec
    | true =>
        cases hmatch :
            GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w with
        | false =>
            have hcontr : (closure h 0 ctu ctr gtu).gtp.right.mem w = true := by
              rw [closure_zero_gtp_right_mem, hgtu, hmatch]
              rfl
            rw [hright] at hcontr
            contradiction
        | true =>
            rcases (GTree.hasMatch_eq_true_iff
                Chromogram.BitStack.empty (CTree.mem ctr) w).mp hmatch with
              ⟨et, hct, hmatchOpen⟩
            exact ⟨et, (Valid.ctr_mem hvalid hct).1, hmatchOpen⟩

theorem closure_zero_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) :
    Valid h P (closure h 0 ctu ctr gtu).ctu ctr
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right :=
  closure_zero_valid_with_ctr hvalid
    (fun _et hmem => Valid.ctr_mem hvalid hmem)

theorem closure_zero_valid_empty_ctr
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) :
    Valid h P (closure h 0 ctu ctr gtu).ctu CTree.empty
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right :=
  closure_zero_valid_with_ctr hvalid (by simp)
private theorem closure_zero_complete_with_ctr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr ctr' : CTree} {gtu : GTree}
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu)
    (hempty : ctr = CTree.empty → ctr' = CTree.empty)
    (hquery :
      ∀ et : ColSeq, CTree.mem ctr (ColSeq.etrace et) = true →
        CTree.mem ctr' (ColSeq.etrace et) = true ∨
          GTree.sub (closure h 0 ctu ctr gtu).gtp.right
            Chromogram.BitStack.empty et = 0) :
    Complete sz P (closure h 0 ctu ctr gtu).ctu ctr'
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right := by
  constructor
  · rcases Complete.progress_or_empty hcomplete with hprogress | hemptyInput
    · exact Or.inl (by simpa using hprogress)
    · right
      rcases hemptyInput with ⟨hctr, _⟩
      refine ⟨hempty hctr, ?_⟩
      intro w
      have hctfalse : ∀ et, CTree.mem ctr et = false := by
        intro et
        rw [hctr]
        simp
      have hhas :
          GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w = false :=
        GTree.hasMatch_eq_false_of_false hctfalse Chromogram.BitStack.empty w
      rw [closure_zero_gtp_left_mem]
      simp [hhas]
  · intro et hprem
    have hprem' :
        P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem ctu
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false) := by
      simpa using hprem
    rcases Complete.query hcomplete et hprem' with hctr | hzero
    · exact hquery et hctr
    · right
      have hsplit := closure_zero_gtp_empty_sub_add h ctu ctr gtu et
      rw [hzero] at hsplit
      omega

theorem closure_zero_complete
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Complete sz P (closure h 0 ctu ctr gtu).ctu ctr
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right :=
  closure_zero_complete_with_ctr hcomplete id
    (fun _et hmem => Or.inl hmem)

theorem closure_zero_complete_empty_ctr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Complete sz P (closure h 0 ctu ctr gtu).ctu CTree.empty
      (closure h 0 ctu ctr gtu).gtp.left
      (closure h 0 ctu ctr gtu).gtp.right :=
  closure_zero_complete_with_ctr hcomplete (fun _ => rfl) (fun et hctr =>
    Or.inr (by
      unfold GTree.sub
      exact GTree.matchCount_eq_zero_of_no_match
        (st := GTree.mem (closure h 0 ctu ctr gtu).gtp.right)
        (bs := Chromogram.BitStack.empty) (et := et)
        (by
          intro w hmatch
          rw [closure_zero_gtp_right_mem]
          have hmatchE :
              GTree.matchOpen Chromogram.BitStack.empty
                  (ColSeq.etrace et) w = true := by
            rw [GTree.matchOpen_empty_etrace et w]
            exact hmatch
          have hhas :
              GTree.hasMatch Chromogram.BitStack.empty (CTree.mem ctr) w =
                true :=
            (GTree.hasMatch_eq_true_iff
              Chromogram.BitStack.empty (CTree.mem ctr) w).mpr
              ⟨ColSeq.etrace et, hctr, hmatchE⟩
          cases hgtu : GTree.mem gtu w <;> simp [hhas])))
theorem closure_zero_correct
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu)
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Valid h P (closure h 0 ctu ctr gtu).ctu ctr
        (closure h 0 ctu ctr gtu).gtp.left
        (closure h 0 ctu ctr gtu).gtp.right ∧
      Complete sz P (closure h 0 ctu ctr gtu).ctu ctr
        (closure h 0 ctu ctr gtu).gtp.left
        (closure h 0 ctu ctr gtu).gtp.right :=
  ⟨closure_zero_valid hvalid, closure_zero_complete hcomplete⟩

theorem closure_zero_correct_empty_ctr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu)
    (hcomplete : Complete sz P ctu ctr GTree.empty gtu) :
    Valid h P (closure h 0 ctu ctr gtu).ctu CTree.empty
        (closure h 0 ctu ctr gtu).gtp.left
        (closure h 0 ctu ctr gtu).gtp.right ∧
      Complete sz P (closure h 0 ctu ctr gtu).ctu CTree.empty
        (closure h 0 ctu ctr gtu).gtp.left
        (closure h 0 ctu ctr gtu).gtp.right :=
  ⟨closure_zero_valid_empty_ctr hvalid,
    closure_zero_complete_empty_ctr hcomplete⟩

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
