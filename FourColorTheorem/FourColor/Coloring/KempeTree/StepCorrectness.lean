import FourColorTheorem.FourColor.Coloring.KempeTree.DegenerateSteps

/-!
Validity, completeness, and correctness of an active or general closure step.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

theorem step_active_eq
    (h : Nat) (closure : ClosureFun) (ctu : CTree) (gtr gtu : GTree)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false) :
    step h closure ⟨ctu, ⟨gtr, gtu⟩⟩ =
      let ctp := CTree.restrict h ctu (baseCRestriction gtr)
      closure ctp.left (CTree.rotLR ctp.right) gtu := by
  simp [step, hctu, hleft, hright]

theorem stepCtr_active_eq
    (h : Nat) (ctr ctu : CTree) (gtr gtu : GTree)
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false) :
    stepCtr h ctr ⟨ctu, ⟨gtr, gtu⟩⟩ =
      CTree.rotLR
        (CTree.restrict h ctu (baseCRestriction gtr)).right := by
  simp [stepCtr, hctu, hleft, hright]

theorem step_active_valid_of_closure
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false)
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
  exact hclosure (active_restrict_valid_of_ctr_mem hvalid hctr)

theorem step_valid_of_closure
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (stepCtr h ctr ⟨ctu, ⟨gtr, gtu⟩⟩)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    simpa using step_empty_ctu_valid h closure hvalid
  · intro _hctu hleftEq
    subst gtr
    simpa [stepCtr_empty_gtp_left] using
      step_empty_gtp_left_valid h closure hvalid
  · intro hctu hleft hrightEq
    subst gtu
    simpa [stepCtr_empty_gtp_right_of_active h ctr ctu gtr hctu hleft]
      using step_empty_gtp_right_valid_of_active h closure hctu hleft hvalid
  · intro hctu hleft hright
    simpa [stepCtr_active_eq h ctr ctu gtr gtu hctu hleft hright] using
      step_active_valid_of_closure h closure hctu hleft hright hvalid hctr
        hclosure

theorem step_active_complete_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false)
    (hcompleteInput :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
  exact hclosure hcompleteInput

theorem step_active_complete_of_closure_empty_ctr
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right :=
  step_active_complete_of_closure h sz closure hctu hleft hright
    (active_restrict_complete_of_complete_empty_ctr hvalid hcomplete hsize)
    hclosure

theorem step_active_complete_of_closure_empty_ctr_no_size
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right :=
  step_active_complete_of_closure h sz closure hctu hleft hright
    (active_restrict_complete_of_complete_empty_ctr_no_size
      hvalid hcomplete)
    hclosure

theorem step_complete_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hcompleteInput :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (stepCtr h ctr ⟨ctu, ⟨gtr, gtu⟩⟩)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    simpa using step_empty_ctu_complete h sz closure hcomplete
  · intro _hctu hleftEq
    subst gtr
    simpa [stepCtr_empty_gtp_left] using
      step_empty_gtp_left_complete h sz closure hcomplete
  · intro hctu hleft hrightEq
    subst gtu
    simpa [stepCtr_empty_gtp_right_of_active h ctr ctu gtr hctu hleft] using
      step_empty_gtp_right_complete_of_active h sz closure hsz hctu hleft
  · intro hctu hleft hright
    simpa [stepCtr_active_eq h ctr ctu gtr gtu hctu hleft hright] using
      step_active_complete_of_closure h sz closure hctu hleft hright
        hcompleteInput hclosure

theorem step_complete_empty_ctr_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    simpa using
      step_empty_ctu_complete_of_pos h sz (sz + 1) closure hsz hcomplete
  · intro _hctu hleftEq
    subst gtr
    simpa [stepCtr_empty_gtp_left] using
      step_empty_gtp_left_complete_empty_ctr h sz (sz + 1) closure hcomplete
  · intro hctu hleft hrightEq
    subst gtu
    simpa [stepCtr_empty_gtp_right_of_active h CTree.empty ctu gtr hctu
        hleft] using
      step_empty_gtp_right_complete_of_active h sz closure hsz hctu hleft
  · intro hctu hleft hright
    simpa [stepCtr_active_eq h CTree.empty ctu gtr gtu hctu hleft hright]
      using step_active_complete_of_closure_empty_ctr h sz closure hctu hleft
        hright hvalid hcomplete hsize hclosure

theorem step_complete_empty_ctr_of_closure_no_size
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hclosure :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).ctu
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    simpa using
      step_empty_ctu_complete_of_pos h sz (sz + 1) closure hsz hcomplete
  · intro _hctu hleftEq
    subst gtr
    simpa [stepCtr_empty_gtp_left] using
      step_empty_gtp_left_complete_empty_ctr h sz (sz + 1) closure hcomplete
  · intro hctu hleft hrightEq
    subst gtu
    simpa [stepCtr_empty_gtp_right_of_active h CTree.empty ctu gtr hctu
        hleft] using
      step_empty_gtp_right_complete_of_active h sz closure hsz hctu hleft
  · intro hctu hleft hright
    simpa [stepCtr_active_eq h CTree.empty ctu gtr gtu hctu hleft hright]
      using step_active_complete_of_closure_empty_ctr_no_size h sz closure
        hctu hleft hright hvalid hcomplete hclosure

theorem step_active_correct_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hctu : CTree.isEmpty ctu = false)
    (hleft : GTree.isEmpty gtr = false)
    (hright : GTree.isEmpty gtu = false)
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hcompleteInput :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right ∧
          Complete sz P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
  exact hclosure (active_restrict_valid_of_ctr_mem hvalid hctr)
    hcompleteInput

theorem step_correct_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hcompleteInput :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right ∧
          Complete sz P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h ctr ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h ctr ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  let activeValid :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
        (CTree.rotLR
          (CTree.restrict h ctu (baseCRestriction gtr)).right)
        GTree.empty gtu :=
    active_restrict_valid_of_ctr_mem hvalid hctr
  constructor
  · exact step_valid_of_closure h closure hvalid hctr
      (fun hv => (hclosure hv hcompleteInput).1)
  · exact step_complete_of_closure h sz closure hsz hcomplete hcompleteInput
      (fun hc => (hclosure activeValid hc).2)

theorem step_correct_empty_ctr_of_closure
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right ∧
          Complete sz P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  let activeValid :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
        (CTree.rotLR
          (CTree.restrict h ctu (baseCRestriction gtr)).right)
        GTree.empty gtu :=
    active_restrict_valid_of_ctr_mem hvalid hctr
  constructor
  · exact step_valid_of_closure h closure hvalid hctr
      (fun hv =>
        (hclosure hv
          (active_restrict_complete_of_complete_empty_ctr
            hvalid hcomplete hsize)).1)
  · exact step_complete_empty_ctr_of_closure h sz closure hsz hvalid
      hcomplete hsize (fun hc => (hclosure activeValid hc).2)

theorem step_correct_empty_ctr_of_closure_no_size
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right ∧
          Complete sz P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        (stepCtr h CTree.empty ⟨ctu, ⟨gtr, gtu⟩⟩)
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  let activeValid :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
        (CTree.rotLR
          (CTree.restrict h ctu (baseCRestriction gtr)).right)
        GTree.empty gtu :=
    active_restrict_valid_of_ctr_mem hvalid hctr
  let activeComplete :
      Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
        (CTree.rotLR
          (CTree.restrict h ctu (baseCRestriction gtr)).right)
        GTree.empty gtu :=
    active_restrict_complete_of_complete_empty_ctr_no_size
      hvalid hcomplete
  constructor
  · exact step_valid_of_closure h closure hvalid hctr
      (fun hv => (hclosure hv activeComplete).1)
  · exact step_complete_empty_ctr_of_closure_no_size h sz closure hsz
      hvalid hcomplete (fun hc => (hclosure activeValid hc).2)

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
