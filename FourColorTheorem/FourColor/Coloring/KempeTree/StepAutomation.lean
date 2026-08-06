import FourColorTheorem.FourColor.Coloring.KempeTree.StepCorrectness

/-!
Derived step-correctness interfaces used by closure induction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

theorem step_correct_of_closure_auto
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
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
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right :=
  step_correct_of_closure h sz closure hsz hvalid hcomplete
    (fun _et hmem => active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem)
    hcompleteInput hclosure

theorem step_correct_empty_ctr_of_closure_auto
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
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
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right :=
  step_correct_empty_ctr_of_closure h sz closure hsz hvalid hcomplete hsize
    (fun _et hmem => active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem)
    hclosure

theorem step_correct_empty_ctr_of_closure_auto_no_size
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
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
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right :=
  step_correct_empty_ctr_of_closure_no_size h sz closure hsz hvalid hcomplete
    (fun _et hmem => active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem)
    hclosure

theorem step_correct_empty_ctr_of_closure_empty_output
    (h sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hsz : 0 < sz)
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
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
            CTree.empty
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
            CTree.empty
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        CTree.empty
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete sz P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        CTree.empty
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    exact ⟨by simpa using step_empty_ctu_valid h closure hvalid,
      by simpa using
        step_empty_ctu_complete_of_pos h sz (sz + 1) closure hsz hcomplete⟩
  · intro _hctu hleftEq
    subst gtr
    exact ⟨by simpa using step_empty_gtp_left_valid h closure hvalid,
      by simpa using
        step_empty_gtp_left_complete_empty_ctr h sz (sz + 1) closure hcomplete⟩
  · intro hctu hleft hrightEq
    subst gtu
    exact
      ⟨by simpa using
          step_empty_gtp_right_valid_of_active h closure hctu hleft hvalid,
        by simpa using
          step_empty_gtp_right_complete_of_active h sz closure hsz hctu hleft⟩
  · intro hctu hleft hright
    rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
    exact hclosure
      (active_restrict_valid_of_ctr_mem hvalid
        (fun _et hmem =>
          active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem))
      (active_restrict_complete_of_complete_empty_ctr_no_size hvalid hcomplete)

theorem step_valid_empty_ctr_of_closure_empty_output
    (h : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
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
          CTree.empty
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.left
          (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
      CTree.empty
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
      (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    simpa using step_empty_ctu_valid h closure hvalid
  · intro _hctu hleftEq
    subst gtr
    simpa using step_empty_gtp_left_valid h closure hvalid
  · intro hctu hleft hrightEq
    subst gtu
    simpa using
      step_empty_gtp_right_valid_of_active h closure hctu hleft hvalid
  · intro hctu hleft hright
    rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
    exact hclosure
      (active_restrict_valid_of_ctr_mem hvalid
        (fun _et hmem =>
          active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem))

theorem step_correct_empty_ctr_of_closure_empty_output_shift
    (h extra sz : Nat) (closure : ClosureFun) {P : ColSeq → Prop}
    {ctu : CTree} {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete :
      Complete (extra + (sz + 1)) P ctu CTree.empty gtr gtu)
    (hclosure :
      Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Complete (extra + sz) P
          (CTree.restrict h ctu (baseCRestriction gtr)).left
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right)
          GTree.empty gtu →
        Valid h P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            CTree.empty
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right ∧
          Complete (sz + 1) P
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).ctu
            CTree.empty
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.left
            (closure (CTree.restrict h ctu (baseCRestriction gtr)).left
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              gtu).gtp.right) :
    Valid h P (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        CTree.empty
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right ∧
      Complete (sz + 1) P
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).ctu
        CTree.empty
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.left
        (step h closure ⟨ctu, ⟨gtr, gtu⟩⟩).gtp.right := by
  apply closureState_cases ctu gtr gtu
  · intro hctuEq
    subst ctu
    exact ⟨by simpa using step_empty_ctu_valid h closure hvalid,
      by simpa using (step_empty_ctu_complete_of_pos h (sz + 1)
        (extra + (sz + 1)) closure (Nat.succ_pos sz) hcomplete)⟩
  · intro _hctu hleftEq
    subst gtr
    exact ⟨by simpa using step_empty_gtp_left_valid h closure hvalid,
      by simpa using (step_empty_gtp_left_complete_empty_ctr h (sz + 1)
        (extra + (sz + 1)) closure hcomplete)⟩
  · intro hctu hleft hrightEq
    subst gtu
    exact
      ⟨by simpa using
          step_empty_gtp_right_valid_of_active h closure hctu hleft hvalid,
        by simpa using (step_empty_gtp_right_complete_of_active h (sz + 1)
          closure (Nat.succ_pos sz) hctu hleft)⟩
  · intro hctu hleft hright
    rw [step_active_eq h closure ctu gtr gtu hctu hleft hright]
    have hcomplete' :
        Complete ((extra + sz) + 1) P ctu CTree.empty gtr gtu := by
      simpa [Nat.add_assoc] using hcomplete
    exact hclosure
      (active_restrict_valid_of_ctr_mem hvalid
        (fun _et hmem =>
          active_restrict_rotLR_right_mem_ctr_of_valid hvalid hmem))
      (active_restrict_complete_of_complete_empty_ctr_no_size
        hvalid hcomplete')

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
