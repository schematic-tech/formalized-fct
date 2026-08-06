import FourColorTheorem.FourColor.Coloring.KempeTree.ClosureState

/-!
Trace, coclosure, and completeness semantics for closure states.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

theorem kempeClosed_openPrefix_of_ctrace
    {P' : ColSeq → Prop} (hclosed : Chromogram.KempeClosed P')
    {et : ColSeq} (hmem : P' (ColSeq.ctrace et)) :
    ∃ w : Chromogram,
      Chromogram.matchg [] (ColSeq.ctrace et) w = true ∧
        GTree.matchOpen Chromogram.BitStack.empty et w.dropLast = true ∧
        ∀ et' : ColSeq,
          Chromogram.matchg [] et' w = true → P' et' := by
  rcases Chromogram.KempeClosed.chromogram hclosed hmem with
    ⟨w, hmatch, hforall⟩
  exact ⟨w, hmatch,
    GTree.matchOpen_dropLast_of_matchg_ctrace hmatch, hforall⟩

theorem kempeClosed_openPrefix_of_ctrace_perm
    {P' : ColSeq → Prop} (hclosed : Chromogram.KempeClosed P')
    {et : ColSeq} (hmem : P' (ColSeq.ctrace et)) (g : EdgePerm) :
    ∃ w : Chromogram,
      Chromogram.matchg []
          (ColSeq.ctrace (ColSeq.perm g et)) w =
        true ∧
        GTree.matchOpen Chromogram.BitStack.empty
            (ColSeq.perm g et) w.dropLast =
          true ∧
        ∀ et' : ColSeq,
          Chromogram.matchg [] et' w = true → P' et' := by
  have hmem' : P' (ColSeq.ctrace (ColSeq.perm g et)) := by
    rw [ColSeq.perm_ctrace]
    exact Chromogram.KempeClosed.perm hclosed hmem g
  exact kempeClosed_openPrefix_of_ctrace hclosed hmem'

theorem initSpec_dropLast_of_matchg_ctrace
    {h : Nat} {et : ColSeq} {w : Chromogram}
    (hmatch : Chromogram.matchg [] (ColSeq.ctrace et) w = true)
    (hlen : et.length = h) :
    GTree.initSpec h w.dropLast = true := by
  have hmatchLen := Chromogram.matchg_length hmatch
  have hdropLen : w.dropLast.length = h := by
    rw [List.length_dropLast, hmatchLen, ColSeq.length_ctrace, hlen]
    omega
  have hcomplete := Chromogram.matchg_complete_of_ctrace hmatch
  have hbalancedFull : Chromogram.balanced 0 false w = true := by
    have hb := (Chromogram.matchg_balanced hmatch).2
    rw [ColSeq.sum_ctrace] at hb
    simpa [Color.bit0] using hb
  have hbalanced :
      Chromogram.balanced 0 false
          (Chromogram.complete 0 false w.dropLast) =
        true := by
    rw [hcomplete]
    exact hbalancedFull
  simp [GTree.initSpec, hdropLen, hbalanced]

theorem kempeClosed_openPrefix_initSpec_of_ctrace_perm
    {P' : ColSeq → Prop} (hclosed : Chromogram.KempeClosed P')
    {h : Nat} {et : ColSeq}
    (hmem : P' (ColSeq.ctrace et)) (hlen : et.length = h)
    (g : EdgePerm) :
    ∃ w : Chromogram,
      Chromogram.matchg []
          (ColSeq.ctrace (ColSeq.perm g et)) w =
        true ∧
        GTree.matchOpen Chromogram.BitStack.empty
            (ColSeq.perm g et) w.dropLast =
          true ∧
        GTree.initSpec h w.dropLast = true ∧
        ∀ et' : ColSeq,
          Chromogram.matchg [] et' w = true → P' et' := by
  rcases kempeClosed_openPrefix_of_ctrace_perm hclosed hmem g with
    ⟨w, hmatch, hopen, hforall⟩
  have hlenPerm : (ColSeq.perm g et).length = h := by
    simpa [ColSeq.length_perm] using hlen
  exact ⟨w, hmatch, hopen,
    initSpec_dropLast_of_matchg_ctrace hmatch hlenPerm, hforall⟩

theorem valid_closed_meets_of_zero_count
    {h : Nat} {P P' : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hclosed : Chromogram.KempeClosed P')
    {et : ColSeq} (hmem : P' (ColSeq.ctrace et))
    (hlen : et.length = h + 1) (g : EdgePerm)
    (hzero :
      GTree.sub gtu Chromogram.BitStack.empty (ColSeq.perm g et) = 0) :
    ∃ et' : ColSeq, P et' ∧ P' et' := by
  rcases kempeClosed_openPrefix_initSpec_of_ctrace_perm
      (h := h + 1) hclosed hmem hlen g with
    ⟨wFull, hmatchFull, hmatchOpen, hspec, hforall⟩
  have hnotMem :
      GTree.mem gtu wFull.dropLast = false :=
    GTree.mem_eq_false_of_sub_eq_zero_of_match hzero hmatchOpen
  rcases Valid.gtu_nonmem_complete hvalid hnotMem hspec with
    ⟨et₁, hclose, hmatch₁⟩
  have hmatchFull₁ :
      Chromogram.matchg [] (ColSeq.ctrace et₁) wFull = true := by
    have hcomplete := Chromogram.matchg_complete_of_ctrace hmatchFull
    rw [← hcomplete]
    exact GTree.matchg_ctrace_complete_of_matchOpen_initSpec hspec hmatch₁
  exact hclose P' hclosed (hforall (ColSeq.ctrace et₁) hmatchFull₁)

theorem active_restrict_rotLR_right_mem_length_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    et.length = h + 1 :=
  CTree.length_of_mem_of_proper
    (restrict_baseC_rotLR_right_proper_of_proper h gtr
      (Valid.ctu_proper hvalid))
    hmem

theorem active_restrict_rotLR_right_mem_coclosure_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro P' hclosed hP'
  have hlen := active_restrict_rotLR_right_mem_length_of_valid hvalid hmem
  rcases active_restrict_rotLR_right_mem_subs_of_valid hvalid hmem with
    h312 | h231
  · exact valid_closed_meets_of_zero_count hvalid hclosed hP' hlen
      EdgePerm.p312 h312.2
  · exact valid_closed_meets_of_zero_count hvalid hclosed hP' hlen
      EdgePerm.p231 h231.2

theorem active_restrict_rotLR_right_mem_ctr_of_valid
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu) {et : ColSeq}
    (hmem :
      CTree.mem
          (CTree.rotLR
            (CTree.restrict h ctu (baseCRestriction gtr)).right) et =
        true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) ∧
      et.length = h + 1 :=
  ⟨active_restrict_rotLR_right_mem_coclosure_of_valid hvalid hmem,
    active_restrict_rotLR_right_mem_length_of_valid hvalid hmem⟩

private theorem gtu_sub_zero_of_valid_even_nonmem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree} (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq} (heven : ColSeq.evenTrace et = true)
    (hmem : CTree.mem ctu et = false) :
    GTree.sub gtu Chromogram.BitStack.empty et = 0 := by
  have hctuSub : CTree.sub ctu et = 0 := by
    unfold CTree.mem at hmem
    simpa using hmem
  have hsub := Valid.ctu_sub hvalid et
  rw [heven, hctuSub] at hsub
  simp at hsub
  omega

theorem valid_coclosure_of_ctu_etrace_nonmem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq} (hlen : et.length = h + 1)
    (hmem : CTree.mem ctu (ColSeq.etrace et) = false) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro P' hclosed hP'
  have hgtuZero :
      GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et) = 0 :=
    gtu_sub_zero_of_valid_even_nonmem hvalid (ColSeq.even_etrace et) hmem
  exact valid_closed_meets_of_zero_count hvalid hclosed hP' hlen
    (ColSeq.etracePerm et) (by simpa [ColSeq.etrace] using hgtuZero)

theorem valid_ctu_etrace_mem_of_not_coclosure
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq} (hlen : et.length = h + 1)
    (hnot : ¬ Chromogram.KempeCoclosure P (ColSeq.ctrace et)) :
    CTree.mem ctu (ColSeq.etrace et) = true := by
  cases hmem : CTree.mem ctu (ColSeq.etrace et)
  · exact False.elim
      (hnot (valid_coclosure_of_ctu_etrace_nonmem hvalid hlen hmem))
  · rfl

theorem valid_coclosure_of_ctu_even_nonmem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq} (hlen : et.length = h + 1)
    (heven : ColSeq.evenTrace et = true)
    (hmem : CTree.mem ctu et = false) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro P' hclosed hP'
  have hgtuZero :
      GTree.sub gtu Chromogram.BitStack.empty et = 0 :=
    gtu_sub_zero_of_valid_even_nonmem hvalid heven hmem
  exact valid_closed_meets_of_zero_count hvalid hclosed hP' hlen
    EdgePerm.p123 (by simpa [ColSeq.perm_id] using hgtuZero)

theorem valid_gtu_sub_zero_of_ctu_even_nonmem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    {et : ColSeq} (heven : ColSeq.evenTrace et = true)
    (hmem : CTree.mem ctu et = false) :
    GTree.sub gtu Chromogram.BitStack.empty et = 0 :=
  gtu_sub_zero_of_valid_even_nonmem hvalid heven hmem

theorem gtree_sub_zero_perm132_of_sub_zero
    {gtu : GTree} {et : ColSeq}
    (hzero : GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    GTree.sub gtu Chromogram.BitStack.empty
        (ColSeq.perm EdgePerm.p132 et) =
      0 := by
  rw [show
      GTree.sub gtu Chromogram.BitStack.empty
          (ColSeq.perm EdgePerm.p132 et) =
        GTree.sub gtu Chromogram.BitStack.empty et by
        simpa [GTree.sub] using
          GTree.matchCount_empty_perm132 (GTree.mem gtu) et]
  exact hzero

theorem valid_ctu_mem_false_of_gtu_sub_zero_of_gtr_empty
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {et : ColSeq}
    (hzero : GTree.sub gtu Chromogram.BitStack.empty et = 0) :
    CTree.mem ctu et = false := by
  have hgtrZero :
      GTree.sub gtr Chromogram.BitStack.empty et = 0 :=
    GTree.matchCount_eq_zero_of_false
      (st := GTree.mem gtr) hgtr Chromogram.BitStack.empty et
  have hsub := Valid.ctu_sub hvalid et
  cases heven : ColSeq.evenTrace et with
  | false =>
      rw [heven] at hsub
      simp [CTree.mem, hsub]
  | true =>
      rw [heven, hgtrZero, hzero] at hsub
      simp [CTree.mem, hsub]

theorem valid_ctu_perm132_etrace_mem_imp_ctu_etrace_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {et : ColSeq}
    (hmem :
      CTree.mem ctu
          (ColSeq.perm EdgePerm.p132 (ColSeq.etrace et)) =
        true) :
    CTree.mem ctu (ColSeq.etrace et) = true := by
  cases hctu : CTree.mem ctu (ColSeq.etrace et) with
  | false =>
      have hzero :
          GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et) = 0 :=
        valid_gtu_sub_zero_of_ctu_even_nonmem hvalid
          (ColSeq.even_etrace et) hctu
      have hzero132 :
          GTree.sub gtu Chromogram.BitStack.empty
              (ColSeq.perm EdgePerm.p132 (ColSeq.etrace et)) =
            0 :=
        gtree_sub_zero_perm132_of_sub_zero hzero
      have hfalse :
          CTree.mem ctu
              (ColSeq.perm EdgePerm.p132 (ColSeq.etrace et)) =
            false :=
        valid_ctu_mem_false_of_gtu_sub_zero_of_gtr_empty
          hvalid hgtr hzero132
      rw [hfalse] at hmem
      contradiction
  | true => rfl

theorem valid_ctu_etrace_mem_eq_or_perm132_mem
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    (et : ColSeq) :
    CTree.mem ctu (ColSeq.etrace et) =
      (CTree.mem ctu et ||
        CTree.mem ctu (ColSeq.perm EdgePerm.p132 et)) := by
  by_cases heven : ColSeq.evenTrace et = true
  · have hetrace : ColSeq.etrace et = et :=
      ColSeq.etrace_of_even heven
    have himp :
        CTree.mem ctu (ColSeq.perm EdgePerm.p132 et) = true →
          CTree.mem ctu et = true := by
      intro hmem
      have h :=
        valid_ctu_perm132_etrace_mem_imp_ctu_etrace_mem
          hvalid hgtr (et := et) (by simpa [hetrace] using hmem)
      simpa [hetrace] using h
    rw [hetrace]
    cases hmem : CTree.mem ctu et <;>
      cases hmem132 : CTree.mem ctu (ColSeq.perm EdgePerm.p132 et) <;>
      simp
    have hbad := himp hmem132
    rw [hmem] at hbad
    contradiction
  · have hfalse : ColSeq.evenTrace et = false := by
      cases h : ColSeq.evenTrace et with
      | false => rfl
      | true => exact False.elim (heven h)
    have hetrace : ColSeq.etrace et = ColSeq.perm EdgePerm.p132 et :=
      ColSeq.etrace_of_not_even hfalse
    have himp :
        CTree.mem ctu et = true →
          CTree.mem ctu (ColSeq.perm EdgePerm.p132 et) = true := by
      intro hmem
      have hmem132 :
          CTree.mem ctu
              (ColSeq.perm EdgePerm.p132
                (ColSeq.etrace (ColSeq.perm EdgePerm.p132 et))) =
            true := by
        rw [ColSeq.etrace_perm132_of_not_even hfalse,
          ColSeq.etrace_involutive_p132]
        exact hmem
      have h :=
        valid_ctu_perm132_etrace_mem_imp_ctu_etrace_mem
          hvalid hgtr (et := ColSeq.perm EdgePerm.p132 et) hmem132
      simpa [ColSeq.etrace_perm132_of_not_even hfalse] using h
    rw [hetrace]
    cases hmem : CTree.mem ctu et <;>
      cases hmem132 : CTree.mem ctu (ColSeq.perm EdgePerm.p132 et) <;>
      simp
    have hbad := himp hmem
    rw [hmem132] at hbad
    contradiction

/-- Trace-level predicate represented by the even-normalised members of a
`CTree`.  This is the Lean counterpart of the local `tr_ctu` predicate in Coq
`Kempe_completeP`. -/
def CtuTracePred (ctu : CTree) (cet : ColSeq) : Prop :=
  ∃ et : ColSeq,
    cet = ColSeq.ctrace et ∧
      CTree.mem ctu (ColSeq.etrace et) = true

theorem ctuTracePred_of_etrace_mem
    {ctu : CTree} {et : ColSeq}
    (hmem : CTree.mem ctu (ColSeq.etrace et) = true) :
    CtuTracePred ctu (ColSeq.ctrace et) :=
  ⟨et, rfl, hmem⟩

theorem complete_no_P_ctuTracePred_of_empty_ctr_gtr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {cet : ColSeq}
    (hP : P cet)
    (htrace : CtuTracePred ctu cet) :
    False := by
  rcases htrace with ⟨et, rfl, hmem⟩
  rcases hcomplete.2 et (Or.inl hP) with hctrMem | hzero
  · rw [hctr] at hctrMem
    simp at hctrMem
  · have hzeroE :
        GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et) = 0 := by
      rw [GTree.sub_empty_etrace]
      exact hzero
    have hfalse :
        CTree.mem ctu (ColSeq.etrace et) = false :=
      valid_ctu_mem_false_of_gtu_sub_zero_of_gtr_empty
        hvalid hgtr hzeroE
    rw [hfalse] at hmem
    contradiction

theorem coclosure_not_ctuTracePred_of_complete_empty_ctr_gtr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    (hclosed : Chromogram.KempeClosed (CtuTracePred ctu))
    {cet : ColSeq}
    (hcoclosure : Chromogram.KempeCoclosure P cet) :
    ¬ CtuTracePred ctu cet := by
  intro htrace
  rcases hcoclosure (CtuTracePred ctu) hclosed htrace with
    ⟨cet', hP, htrace'⟩
  exact complete_no_P_ctuTracePred_of_empty_ctr_gtr
    hvalid hcomplete hctr hgtr hP htrace'

theorem complete_empty_ctr_gtr_ctu_etrace_nonmem_of_coclosure
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    (hclosed : Chromogram.KempeClosed (CtuTracePred ctu))
    {et : ColSeq}
    (hcoclosure : Chromogram.KempeCoclosure P (ColSeq.ctrace et)) :
    CTree.mem ctu (ColSeq.etrace et) = false := by
  cases hmem : CTree.mem ctu (ColSeq.etrace et) with
  | false => rfl
  | true =>
      have hnot :=
        coclosure_not_ctuTracePred_of_complete_empty_ctr_gtr
          hvalid hcomplete hctr hgtr hclosed hcoclosure
      exact False.elim (hnot (ctuTracePred_of_etrace_mem hmem))

theorem complete_one_ctu_etrace_nonmem_of_coclosure_of_closed
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete 1 P ctu ctr gtr gtu)
    (hclosed : Chromogram.KempeClosed (CtuTracePred ctu))
    {et : ColSeq}
    (hcoclosure : Chromogram.KempeCoclosure P (ColSeq.ctrace et)) :
    CTree.mem ctu (ColSeq.etrace et) = false := by
  rcases hcomplete.1 with hprogress | hempty
  · have hsize : CTree.size ctu = 0 := by omega
    have hctu : ctu = CTree.empty :=
      CTree.eq_empty_of_proper_size_zero hvalid.1 hsize
    rw [hctu]
    simp
  · exact complete_empty_ctr_gtr_ctu_etrace_nonmem_of_coclosure
      hvalid hcomplete hempty.1 hempty.2 hclosed hcoclosure

theorem ctuTracePred_chromogram_witness_of_valid_gtr_empty
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {cet : ColSeq}
    (htrace : CtuTracePred ctu cet) :
    ∃ w : Chromogram,
      Chromogram.matchg [] cet w = true ∧
        ∀ cet' : ColSeq,
          Chromogram.matchg [] cet' w = true →
            CtuTracePred ctu cet' := by
  rcases htrace with ⟨et, rfl, hmem⟩
  have hctuNe :
      CTree.sub ctu (ColSeq.etrace et) ≠ 0 := by
    intro hzero
    unfold CTree.mem at hmem
    simp [hzero] at hmem
  have hgtrZero :
      GTree.sub gtr Chromogram.BitStack.empty (ColSeq.etrace et) = 0 :=
    GTree.matchCount_eq_zero_of_false
      (st := GTree.mem gtr) hgtr Chromogram.BitStack.empty
      (ColSeq.etrace et)
  have hsub := Valid.ctu_sub hvalid (ColSeq.etrace et)
  have hgtuNe :
      GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et) ≠ 0 := by
    rw [ColSeq.even_etrace, hgtrZero] at hsub
    intro hzero
    rw [hzero] at hsub
    simp at hsub
    exact hctuNe hsub
  rcases GTree.exists_mem_match_of_sub_ne_zero hgtuNe with
    ⟨w, hgtuMem, hmatchE⟩
  have hspec : GTree.initSpec (h + 1) w = true :=
    Valid.gtu_mem hvalid hgtuMem
  have hmatch :
      GTree.matchOpen Chromogram.BitStack.empty et w = true := by
    rw [← GTree.matchOpen_empty_etrace et w]
    exact hmatchE
  refine
    ⟨Chromogram.complete 0 false w,
      GTree.matchg_ctrace_complete_of_matchOpen_initSpec hspec hmatch,
      ?_⟩
  intro cet' hmatchCet'
  have hbal :
      Chromogram.balanced 0 false
          (Chromogram.complete 0 false w) =
        true :=
    GTree.initSpec_balanced_of_true hspec
  have hsum : ColSeq.sum cet' = Color.zero :=
    Chromogram.balanced_sum_zero hbal hmatchCet'
  have hne : cet' ≠ [] := by
    intro hnil
    have hnilMatch :
        Chromogram.matchg [] []
            (Chromogram.complete 0 false w) =
          false :=
      Chromogram.matchg_nil_complete [] 0 false w
    rw [hnil, hnilMatch] at hmatchCet'
    contradiction
  let et' : ColSeq := cet'.dropLast
  have hctrace : ColSeq.ctrace et' = cet' :=
    ColSeq.ctrace_dropLast_of_sum_zero hne hsum
  have hmatchOpen :
      GTree.matchOpen Chromogram.BitStack.empty et' w = true := by
    rw [← hctrace] at hmatchCet'
    rw [GTree.matchg_ctrace_complete_eq_matchOpen et' w hbal] at hmatchCet'
    exact hmatchCet'
  have hgtuNe' :
      GTree.sub gtu Chromogram.BitStack.empty et' ≠ 0 :=
    GTree.sub_ne_zero_of_mem_match hgtuMem hmatchOpen
  have hgtuNeE' :
      GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et') ≠ 0 := by
    rw [GTree.sub_empty_etrace]
    exact hgtuNe'
  have hsubEq' :
      CTree.sub ctu (ColSeq.etrace et') =
        GTree.sub gtr Chromogram.BitStack.empty (ColSeq.etrace et') +
          GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et') := by
    simpa [ColSeq.even_etrace] using
      Valid.ctu_sub hvalid (ColSeq.etrace et')
  have hctuNe' :
      CTree.sub ctu (ColSeq.etrace et') ≠ 0 := by
    intro hzero
    have hsumZero :
        GTree.sub gtr Chromogram.BitStack.empty (ColSeq.etrace et') +
            GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et') =
          0 := by
      rw [← hsubEq', hzero]
    have hgtuZero' :
        GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et') = 0 := by
      omega
    exact hgtuNeE' hgtuZero'
  refine ⟨et', hctrace.symm, ?_⟩
  unfold CTree.mem
  simp [hctuNe']

theorem exists_edgeRot_mem_false_of_perm_or_perm132_false
    {ctu : CTree} {et etg : ColSeq} {g : EdgePerm}
    (hg : ColSeq.perm g et = etg)
    (hmem : CTree.mem ctu etg = false)
    (hmem132 :
      CTree.mem ctu (ColSeq.perm EdgePerm.p132 etg) = false) :
    ∃ e : Color,
      CTree.mem ctu (ColSeq.perm (EdgePerm.edgeRot e) et) =
        false := by
  cases g with
  | p123 =>
      refine ⟨Color.one, ?_⟩
      rw [← hg] at hmem
      simpa [EdgePerm.edgeRot, ColSeq.perm_id] using hmem
  | p132 =>
      refine ⟨Color.one, ?_⟩
      rw [← hg] at hmem132
      simpa [EdgePerm.edgeRot, ColSeq.perm_id,
        ColSeq.etrace_involutive_p132] using hmem132
  | p213 =>
      refine ⟨Color.two, ?_⟩
      rw [← hg] at hmem132
      rw [← ColSeq.perm_comp EdgePerm.p132 EdgePerm.p213 et] at hmem132
      simpa [EdgePerm.edgeRot, EdgePerm.comp] using hmem132
  | p231 =>
      refine ⟨Color.three, ?_⟩
      rw [← hg] at hmem
      simpa [EdgePerm.edgeRot] using hmem
  | p312 =>
      refine ⟨Color.two, ?_⟩
      rw [← hg] at hmem
      simpa [EdgePerm.edgeRot] using hmem
  | p321 =>
      refine ⟨Color.three, ?_⟩
      rw [← hg] at hmem132
      rw [← ColSeq.perm_comp EdgePerm.p132 EdgePerm.p321 et] at hmem132
      simpa [EdgePerm.edgeRot, EdgePerm.comp] using hmem132

theorem ctuTracePred_perm_of_complete_empty_ctr_gtr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {cet : ColSeq}
    (htrace : CtuTracePred ctu cet)
    (g : EdgePerm) :
    CtuTracePred ctu (ColSeq.perm g cet) := by
  rcases htrace with ⟨et, rfl, hmem⟩
  refine ⟨ColSeq.perm g et, (ColSeq.perm_ctrace g et).symm, ?_⟩
  cases htarget :
      CTree.mem ctu (ColSeq.etrace (ColSeq.perm g et)) with
  | true => rfl
  | false =>
      have horFalse :
          (CTree.mem ctu (ColSeq.perm g et) ||
              CTree.mem ctu
                (ColSeq.perm EdgePerm.p132 (ColSeq.perm g et))) =
            false := by
        rw [← valid_ctu_etrace_mem_eq_or_perm132_mem
          hvalid hgtr (ColSeq.perm g et), htarget]
      have hmemPerm :
          CTree.mem ctu (ColSeq.perm g et) = false := by
        cases hmemPerm : CTree.mem ctu (ColSeq.perm g et) <;>
          simp [hmemPerm] at horFalse ⊢
      have hmem132 :
          CTree.mem ctu
              (ColSeq.perm EdgePerm.p132 (ColSeq.perm g et)) =
            false := by
        cases hmem132 :
            CTree.mem ctu
              (ColSeq.perm EdgePerm.p132 (ColSeq.perm g et)) <;>
          simp [hmem132] at horFalse ⊢
      rcases ColSeq.exists_perm_from_etrace g et with ⟨g2, hg2⟩
      rcases exists_edgeRot_mem_false_of_perm_or_perm132_false
          (ctu := ctu) (et := ColSeq.etrace et)
          (etg := ColSeq.perm g et) hg2 hmemPerm hmem132 with
        ⟨e, hedge⟩
      rcases hcomplete.2 et (Or.inr ⟨e, hedge⟩) with hctrMem | hzero
      · rw [hctr] at hctrMem
        simp at hctrMem
      · have hzeroE :
            GTree.sub gtu Chromogram.BitStack.empty (ColSeq.etrace et) = 0 := by
          rw [GTree.sub_empty_etrace]
          exact hzero
        have hfalse :
            CTree.mem ctu (ColSeq.etrace et) = false :=
          valid_ctu_mem_false_of_gtu_sub_zero_of_gtr_empty
            hvalid hgtr hzeroE
        rw [hfalse] at hmem
        contradiction

theorem ctuTracePred_closed_of_complete_empty_ctr_gtr
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false) :
    Chromogram.KempeClosed (CtuTracePred ctu) := by
  intro cet htrace
  exact
    ⟨fun g =>
        ctuTracePred_perm_of_complete_empty_ctr_gtr
          hvalid hcomplete hctr hgtr htrace g,
      ctuTracePred_chromogram_witness_of_valid_gtr_empty
        hvalid hgtr htrace⟩

theorem complete_empty_ctr_gtr_ctu_etrace_nonmem_of_coclosure_auto
    {h sz : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete sz P ctu ctr gtr gtu)
    (hctr : ctr = CTree.empty)
    (hgtr : ∀ w : Chromogram, GTree.mem gtr w = false)
    {et : ColSeq}
    (hcoclosure : Chromogram.KempeCoclosure P (ColSeq.ctrace et)) :
    CTree.mem ctu (ColSeq.etrace et) = false :=
  complete_empty_ctr_gtr_ctu_etrace_nonmem_of_coclosure
    hvalid hcomplete hctr hgtr
    (ctuTracePred_closed_of_complete_empty_ctr_gtr
      hvalid hcomplete hctr hgtr)
    hcoclosure

theorem complete_one_ctu_etrace_nonmem_of_coclosure
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete 1 P ctu ctr gtr gtu)
    {et : ColSeq}
    (hcoclosure : Chromogram.KempeCoclosure P (ColSeq.ctrace et)) :
    CTree.mem ctu (ColSeq.etrace et) = false := by
  rcases hcomplete.1 with hprogress | hempty
  · have hsize : CTree.size ctu = 0 := by omega
    have hctu : ctu = CTree.empty :=
      CTree.eq_empty_of_proper_size_zero hvalid.1 hsize
    rw [hctu]
    simp
  · exact complete_empty_ctr_gtr_ctu_etrace_nonmem_of_coclosure_auto
      hvalid hcomplete hempty.1 hempty.2 hcoclosure

theorem complete_one_ctu_etrace_nonmem_iff_coclosure
    {h : Nat} {P : ColSeq → Prop} {ctu ctr : CTree}
    {gtr gtu : GTree}
    (hvalid : Valid h P ctu ctr gtr gtu)
    (hcomplete : Complete 1 P ctu ctr gtr gtu)
    {et : ColSeq} (hlen : et.length = h + 1) :
    CTree.mem ctu (ColSeq.etrace et) = false ↔
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  constructor
  · exact valid_coclosure_of_ctu_etrace_nonmem hvalid hlen
  · exact complete_one_ctu_etrace_nonmem_of_coclosure hvalid hcomplete


end KempeTree

end FourColor

end Schematic.Math.GraphTheory
