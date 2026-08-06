import FourColorTheorem.FourColor.Coloring.KempeTree.TraceSemantics

/-!
Validity and completeness under an active restriction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

theorem active_restrict_valid_of_ctr_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hctr :
      ∀ et : ColSeq,
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
          true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1) :
    Valid h P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  constructor
  · exact active_restrict_ctu_proper_of_valid hvalid
  constructor
  · exact active_restrict_ctu_sub_of_valid hvalid
  constructor
  · exact hctr
  constructor
  · intro w hmem
    have hfalse : False := by
      change GTree.mem GTree.empty w = true at hmem
      simp at hmem
    exact False.elim hfalse
  constructor
  · intro w hmem
    exact Valid.gtu_mem hvalid hmem
  · intro w hmem hspec
    exact Valid.gtu_nonmem_complete hvalid hmem hspec

theorem active_restrict_complete_of_progress_and_query
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hsize : CTree.size ctu < sz)
    (hquery :
      ∀ et : ColSeq,
        (P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false)) →
          CTree.mem
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              (ColSeq.etrace et) =
            true ∨
            GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  constructor
  · left
    exact active_restrict_ctu_size_lt_of_valid hvalid hsize
  · exact hquery

theorem active_restrict_complete_of_progress_succ_right_pos_and_query
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hright :
      0 < CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right)
    (hquery :
      ∀ et : ColSeq,
        (P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false)) →
          CTree.mem
              (CTree.rotLR
                (CTree.restrict h ctu (baseCRestriction gtr)).right)
              (ColSeq.etrace et) =
            true ∨
            GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  constructor
  · left
    exact active_restrict_ctu_size_lt_of_valid_right_pos hvalid hsize hright
  · exact hquery

theorem active_restrict_query_of_complete_empty_ctr
    {h sz : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete sz P ctu CTree.empty gtr gtu) :
    ∀ et : ColSeq,
      (P (ColSeq.ctrace et) ∨
        (∃ e : Color,
          CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left
            (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
              false)) →
        CTree.mem
            (CTree.rotLR
              (CTree.restrict h ctu (baseCRestriction gtr)).right)
            (ColSeq.etrace et) =
          true ∨
          GTree.sub gtu Chromogram.BitStack.empty et = 0 := by
  intro et hprem
  rcases hprem with hP | ⟨e, hleftNorm⟩
  · rcases hcomplete.2 et (Or.inl hP) with hctr | hzero
    · simp at hctr
    · exact Or.inr hzero
  · let et0 := ColSeq.etrace et
    cases hleftEt :
        CTree.mem (CTree.restrict h ctu (baseCRestriction gtr)).left et0 with
    | false =>
        right
        have hmemEq := active_restrict_ctu_mem_of_valid hvalid et0
        have hzeroEt0 :
            GTree.sub gtu Chromogram.BitStack.empty et0 = 0 := by
          rw [hleftEt, ColSeq.even_etrace] at hmemEq
          simpa using hmemEq
        simpa [et0, GTree.sub_empty_etrace] using hzeroEt0
    | true =>
        cases hctuNorm :
            CTree.mem ctu
              (ColSeq.perm (EdgePerm.edgeRot e) et0) with
        | false =>
            rcases hcomplete.2 et
                (Or.inr ⟨e, by simpa [et0] using hctuNorm⟩) with
              hctr | hzero
            · simp at hctr
            · exact Or.inr hzero
        | true =>
            left
            exact
              restrict_baseC_rotLR_right_mem_of_edgeRot_left_false h
                (Valid.ctu_proper hvalid) hleftEt hctuNorm
                (by simpa [et0] using hleftNorm)

theorem active_restrict_complete_of_complete_empty_ctr_right_pos
    {h sz : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1)
    (hright :
      0 < CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu :=
  active_restrict_complete_of_progress_succ_right_pos_and_query
    hvalid hsize hright
    (active_restrict_query_of_complete_empty_ctr hvalid hcomplete)

theorem active_restrict_complete_of_complete_empty_ctr_right_zero
    {h sz sz' : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete sz' P ctu CTree.empty gtr gtu)
    (hright :
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right = 0) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  have hright_empty :=
    active_restrict_right_eq_empty_of_size_zero hvalid hright
  have hctr :
      CTree.rotLR
          (CTree.restrict h ctu (baseCRestriction gtr)).right =
        CTree.empty := by
    rw [hright_empty]
    exact CTree.rotLR_empty
  constructor
  · right
    constructor
    · exact hctr
    · intro w
      simp
  · exact active_restrict_query_of_complete_empty_ctr hvalid hcomplete

theorem active_restrict_complete_of_complete_empty_ctr
    {h sz : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu)
    (hsize : CTree.size ctu < sz + 1) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  by_cases hzero :
      CTree.size (CTree.restrict h ctu (baseCRestriction gtr)).right = 0
  · exact active_restrict_complete_of_complete_empty_ctr_right_zero
      hvalid hcomplete hzero
  · exact active_restrict_complete_of_complete_empty_ctr_right_pos
      hvalid hcomplete hsize (Nat.pos_of_ne_zero hzero)

theorem active_restrict_right_eq_empty_of_gtr_semantic_empty
    {h : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false) :
    (CTree.restrict h ctu (baseCRestriction gtr)).right = CTree.empty := by
  apply CTree.eq_empty_of_proper_no_mem
    (restrict_baseC_right_proper_of_proper h gtr
      (Valid.ctu_proper hvalid))
  intro et
  have hgtrZero :
      GTree.sub gtr Chromogram.BitStack.empty et = 0 :=
    GTree.matchCount_eq_zero_of_false
      (st := GTree.mem gtr) hgtr Chromogram.BitStack.empty et
  rw [restrict_baseC_right_mem_of_proper h gtr
    (Valid.ctu_proper hvalid) et]
  cases hctu : CTree.mem ctu et with
  | false =>
      simp
  | true =>
      have hctuSubNe : CTree.sub ctu et ≠ 0 := by
        unfold CTree.mem at hctu
        simpa using hctu
      have hnotLe : ¬ CTree.sub ctu et ≤
          GTree.sub gtr Chromogram.BitStack.empty et := by
        rw [hgtrZero]
        omega
      simp [hnotLe]

theorem active_restrict_complete_of_complete_empty_ctr_no_size
    {h sz : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu CTree.empty gtr gtu)
    (hcomplete : Complete (sz + 1) P ctu CTree.empty gtr gtu) :
    Complete sz P (CTree.restrict h ctu (baseCRestriction gtr)).left
      (CTree.rotLR (CTree.restrict h ctu (baseCRestriction gtr)).right)
      GTree.empty gtu := by
  rcases hcomplete.1 with hsize | hempty
  · exact active_restrict_complete_of_complete_empty_ctr
      hvalid hcomplete hsize
  · have hright :
        (CTree.restrict h ctu (baseCRestriction gtr)).right =
          CTree.empty :=
      active_restrict_right_eq_empty_of_gtr_semantic_empty
        hvalid hempty.2
    exact active_restrict_complete_of_complete_empty_ctr_right_zero
      hvalid hcomplete (by rw [hright, CTree.size_empty])

theorem valid_with_ctr
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hctr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
            et.length = h + 1)
    (hvalid : Valid h P ctu CTree.empty gtr gtu) :
    Valid h P ctu ctr gtr gtu := by
  constructor
  · exact Valid.ctu_proper hvalid
  constructor
  · exact Valid.ctu_sub hvalid
  constructor
  · exact hctr
  constructor
  · intro w hmem
    exact Valid.gtr_mem hvalid hmem
  constructor
  · intro w hmem
    exact Valid.gtu_mem hvalid hmem
  · intro w hmem hspec
    exact Valid.gtu_nonmem_complete hvalid hmem hspec

theorem valid_with_ctr_of_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hctr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hvalid : Valid h P ctu CTree.empty gtr gtu) :
    Valid h P ctu ctr gtr gtu :=
  valid_with_ctr
    (fun et hmem =>
      let h := hctr et hmem
      ⟨Chromogram.KempeCoclosure.of_mem h.1, h.2⟩)
    hvalid

namespace Complete

theorem intro_of_progress
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hsize : CTree.size ctu < sz)
    (hquery :
      ∀ et : ColSeq,
        (P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem ctu
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false)) →
          CTree.mem ctr (ColSeq.etrace et) = true ∨
            GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    Complete sz P ctu ctr gtr gtu :=
  ⟨Or.inl hsize, hquery⟩

theorem intro_of_empty
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    (hquery :
      ∀ et : ColSeq,
        (P (ColSeq.ctrace et) ∨
          (∃ e : Color,
            CTree.mem ctu
              (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
                false)) →
          CTree.mem ctr (ColSeq.etrace et) = true ∨
            GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    Complete sz P ctu ctr gtr gtu :=
  ⟨Or.inr ⟨hctr, hgtr⟩, hquery⟩

theorem mono_size
    {sz sz' : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hle : sz ≤ sz')
    (hcomplete : Complete sz P ctu ctr gtr gtu) :
    Complete sz' P ctu ctr gtr gtu := by
  constructor
  · rcases hcomplete.1 with hprogress | hempty
    · left
      omega
    · right
      exact hempty
  · exact hcomplete.2

theorem mono_of_empty_ctr_gtr
    {sz sz' : Nat} {P : ColSeq → Prop} {ctu : CTree}
    {gtu : GTree}
    (hcomplete : Complete sz' P ctu CTree.empty GTree.empty gtu) :
    Complete sz P ctu CTree.empty GTree.empty gtu := by
  constructor
  · right
    constructor
    · rfl
    · intro w
      simp
  · exact hcomplete.2

theorem progress_or_empty
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hcomplete : Complete sz P ctu ctr gtr gtu) :
    CTree.size ctu < sz ∨
      (ctr = CTree.empty ∧ ∀ w : Chromogram, GTree.mem gtr w = false) :=
  hcomplete.1

theorem query
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (et : ColSeq)
    (h :
      P (ColSeq.ctrace et) ∨
        (∃ e : Color,
          CTree.mem ctu
            (ColSeq.perm (EdgePerm.edgeRot e) (ColSeq.etrace et)) =
              false)) :
    CTree.mem ctr (ColSeq.etrace et) = true ∨
      GTree.sub gtu Chromogram.BitStack.empty et = 0 :=
  hcomplete.2 et h

theorem empty_ctr_of_not_progress
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hnot : ¬ CTree.size ctu < sz) :
    ctr = CTree.empty :=
  Or.resolve_left hcomplete.1 hnot |>.1

theorem gtr_empty_of_not_progress
    {sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hnot : ¬ CTree.size ctu < sz)
    (w : Chromogram) :
    GTree.mem gtr w = false :=
  Or.resolve_left hcomplete.1 hnot |>.2 w

theorem ctu_empty_or_empty_ctr_gtr_of_one
    {height : Nat}
    {P : ColSeq → Prop} {ctu ctr : CTree} {gtr gtu : GTree}
    (hproper : CTree.Proper height ctu)
    (hcomplete : Complete 1 P ctu ctr gtr gtu) :
    ctu = CTree.empty ∨
      (ctr = CTree.empty ∧ ∀ w : Chromogram, GTree.mem gtr w = false) := by
  rcases Complete.progress_or_empty hcomplete with hprogress | hempty
  · left
    have hsize : CTree.size ctu = 0 := by omega
    exact CTree.eq_empty_of_proper_size_zero hproper hsize
  · exact Or.inr hempty

end Complete

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
