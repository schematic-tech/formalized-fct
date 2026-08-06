import FourColorTheorem.FourColor.Coloring.KempeTree.StepAutomation

/-!
Correctness of iterated closure and the final Kempe trees.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KempeTree

theorem closure_correct
    (h d : Nat) {P : ColSeq → Prop}
    {ctu ctr : CTree} {gtu : GTree}
    (hvalid : Valid h P ctu ctr GTree.empty gtu) :
    Valid h P (closure h d ctu ctr gtu).ctu CTree.empty
        (closure h d ctu ctr gtu).gtp.left
        (closure h d ctu ctr gtu).gtp.right ∧
      ∀ sz : Nat,
        Complete (3 ^ d + sz) P ctu ctr GTree.empty gtu →
          Complete (sz + 1) P (closure h d ctu ctr gtu).ctu
            CTree.empty
            (closure h d ctu ctr gtu).gtp.left
            (closure h d ctu ctr gtu).gtp.right := by
  induction d generalizing ctu ctr gtu with
  | zero =>
      constructor
      · simpa using closure_zero_valid_empty_ctr hvalid
      · intro sz hcomplete
        simpa [Nat.add_comm] using
          (closure_zero_complete_empty_ctr (h := h) (P := P)
            (ctu := ctu) (ctr := ctr) (gtu := gtu) hcomplete)
  | succ d ih =>
      let st0 : State := closure h d ctu ctr gtu
      have ih0 := ih (ctu := ctu) (ctr := ctr) (gtu := gtu) hvalid
      have hvalid0 :
          Valid h P st0.ctu CTree.empty st0.gtp.left st0.gtp.right := by
        simpa [st0] using ih0.1
      let st1 : State := step h (closure h d) st0
      have hvalid1 :
          Valid h P st1.ctu CTree.empty st1.gtp.left st1.gtp.right := by
        simpa [st1, st0] using
          (step_valid_empty_ctr_of_closure_empty_output
            h (closure h d)
            (ctu := st0.ctu) (gtr := st0.gtp.left)
            (gtu := st0.gtp.right) hvalid0
            (fun hv => (ih hv).1))
      have hvalid2 :
          Valid h P
            (step h (closure h d) st1).ctu CTree.empty
            (step h (closure h d) st1).gtp.left
            (step h (closure h d) st1).gtp.right := by
        simpa [st1] using
          (step_valid_empty_ctr_of_closure_empty_output
            h (closure h d)
            (ctu := st1.ctu) (gtr := st1.gtp.left)
            (gtu := st1.gtp.right) hvalid1
            (fun hv => (ih hv).1))
      constructor
      · simpa [closure_succ, st0, st1] using hvalid2
      · intro sz hcomplete
        have hcomplete0Input :
            Complete (3 ^ d + (2 * 3 ^ d + sz)) P ctu ctr
              GTree.empty gtu := by
          have heq :
              3 ^ d + (2 * 3 ^ d + sz) =
                3 ^ (d + 1) + sz := by
            rw [Nat.pow_succ]
            omega
          rwa [heq]
        have hcomplete0 :
            Complete ((2 * 3 ^ d + sz) + 1) P st0.ctu CTree.empty
              st0.gtp.left st0.gtp.right := by
          simpa [st0] using ih0.2 (2 * 3 ^ d + sz) hcomplete0Input
        have hcomplete0Shift :
            Complete (3 ^ d + ((3 ^ d + sz) + 1)) P st0.ctu
              CTree.empty st0.gtp.left st0.gtp.right := by
          have heq :
              3 ^ d + ((3 ^ d + sz) + 1) =
                (2 * 3 ^ d + sz) + 1 := by
            omega
          rwa [heq]
        have step1Correct :=
          step_correct_empty_ctr_of_closure_empty_output_shift
            h (3 ^ d) (3 ^ d + sz) (closure h d)
            (ctu := st0.ctu) (gtr := st0.gtp.left)
            (gtu := st0.gtp.right) hvalid0 hcomplete0Shift
            (fun hv hc =>
              let ihv := ih hv
              ⟨ihv.1, ihv.2 (3 ^ d + sz) hc⟩)
        have hcomplete1 :
            Complete (3 ^ d + (sz + 1)) P st1.ctu CTree.empty
              st1.gtp.left st1.gtp.right := by
          have heq :
              3 ^ d + (sz + 1) = (3 ^ d + sz) + 1 := by
            omega
          rw [heq]
          simpa [st1, st0] using step1Correct.2
        have step2Correct :=
          step_correct_empty_ctr_of_closure_empty_output_shift
            h (3 ^ d) sz (closure h d)
            (ctu := st1.ctu) (gtr := st1.gtp.left)
            (gtu := st1.gtp.right) hvalid1 hcomplete1
            (fun hv hc =>
              let ihv := ih hv
              ⟨ihv.1, ihv.2 sz hc⟩)
        simpa [closure_succ, st0, st1] using step2Correct.2

theorem treeOfHeight_closure_correct_of_ctr_mem
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree}
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem ctr (ColSeq.etrace et) = true) :
    Valid h P (closure h (h + 2) (initialCTree h) ctr
        (initialGTree h)).ctu CTree.empty
        (closure h (h + 2) (initialCTree h) ctr
          (initialGTree h)).gtp.left
        (closure h (h + 2) (initialCTree h) ctr
          (initialGTree h)).gtp.right ∧
      Complete 1 P (closure h (h + 2) (initialCTree h) ctr
        (initialGTree h)).ctu CTree.empty
        (closure h (h + 2) (initialCTree h) ctr
          (initialGTree h)).gtp.left
        (closure h (h + 2) (initialCTree h) ctr
          (initialGTree h)).gtp.right := by
  rcases initial_valid_complete_of_ctr_mem h hvalidCtr hcompleteCtr with
    ⟨hvalid, hcomplete⟩
  have hcorrect :=
    closure_correct h (h + 2) (P := P) hvalid
  constructor
  · exact hcorrect.1
  · have hcompleteInput :
        Complete (3 ^ (h + 2) + 0) P (initialCTree h) ctr
          GTree.empty (initialGTree h) := by
      simpa using hcomplete
    simpa using hcorrect.2 0 hcompleteInput

theorem treeOfHeight_etrace_nonmem_iff_coclosure_of_ctr_mem
    (h : Nat) {P : ColSeq → Prop} {ctr : CTree}
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem ctr et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem ctr (ColSeq.etrace et) = true)
    {et : ColSeq} (hlen : et.length = h + 1) :
    CTree.mem (treeOfHeight h ctr) (ColSeq.etrace et) = false ↔
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hcorrect :=
    treeOfHeight_closure_correct_of_ctr_mem h hvalidCtr hcompleteCtr
  simpa [treeOfHeight] using
    (complete_one_ctu_etrace_nonmem_iff_coclosure
      hcorrect.1 hcorrect.2 hlen)

private theorem treeWith_ring_zero
    (colorTree : CProg → CTree) (cp : CProg)
    (hsize : CProg.ringSize cp = 0) :
    treeWith colorTree cp = CTree.empty := by
  simp [treeWith, hsize]

private theorem treeWith_ring_one
    (colorTree : CProg → CTree) (cp : CProg)
    (hsize : CProg.ringSize cp = 1) :
    treeWith colorTree cp = CTree.empty := by
  simp [treeWith, hsize]

private theorem treeWith_succ_succ
    (colorTree : CProg → CTree) (cp : CProg) (h : Nat)
    (hsize : CProg.ringSize cp = Nat.succ (Nat.succ h)) :
    treeWith colorTree cp = treeOfHeight h (colorTree cp) := by
  simp [treeWith, hsize]

@[simp]
theorem tree_ring_zero (cp : CProg)
    (hsize : CProg.ringSize cp = 0) :
    tree cp = CTree.empty :=
  treeWith_ring_zero CProg.cpColor cp hsize

@[simp]
theorem tree_ring_one (cp : CProg)
    (hsize : CProg.ringSize cp = 1) :
    tree cp = CTree.empty :=
  treeWith_ring_one CProg.cpColor cp hsize

theorem tree_succ_succ
    (cp : CProg) (h : Nat)
    (hsize : CProg.ringSize cp = Nat.succ (Nat.succ h)) :
    tree cp = treeOfHeight h (CProg.cpColor cp) :=
  treeWith_succ_succ CProg.cpColor cp h hsize

theorem tree_etrace_nonmem_iff_coclosure_of_cpColor_spec
    (cp : CProg) {h : Nat} {P : ColSeq → Prop}
    (hring : CProg.ringSize cp = Nat.succ (Nat.succ h))
    (hvalidCtr :
      ∀ et : ColSeq,
        CTree.mem (CProg.cpColor cp) et = true →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteCtr :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CTree.mem (CProg.cpColor cp) (ColSeq.etrace et) = true)
    {et : ColSeq} (hlen : et.length = h + 1) :
    CTree.mem (tree cp) (ColSeq.etrace et) = false ↔
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  rw [tree_succ_succ cp h hring]
  exact treeOfHeight_etrace_nonmem_iff_coclosure_of_ctr_mem
    h hvalidCtr hcompleteCtr hlen

theorem tree_etrace_nonmem_iff_coclosure_of_cpColorSpec
    (cp : CProg) {h branchHeight : Nat} {P : ColSeq → Prop}
    (hring : CProg.ringSize cp = Nat.succ (Nat.succ h))
    (hbranch : ∀ et, CTree.Proper branchHeight (CProg.cpBranch et))
    (hvalidSpec :
      ∀ et : ColSeq,
        CProg.cpColorSpec cp et →
          P (ColSeq.ctrace et) ∧ et.length = h + 1)
    (hcompleteSpec :
      ∀ et : ColSeq,
        P (ColSeq.ctrace et) →
          CProg.cpColorSpec cp (ColSeq.etrace et))
    {et : ColSeq} (hlen : et.length = h + 1) :
    CTree.mem (tree cp) (ColSeq.etrace et) = false ↔
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  exact tree_etrace_nonmem_iff_coclosure_of_cpColor_spec
    cp hring
    (fun et hmem =>
      hvalidSpec et
        ((CProg.cpColor_mem_iff_of_branch_proper hbranch cp et).1 hmem))
    (fun et hP =>
      (CProg.cpColor_mem_iff_of_branch_proper
        hbranch cp (ColSeq.etrace et)).2 (hcompleteSpec et hP))
    hlen

@[simp]
theorem treeFast_ring_zero (cp : CProg)
    (hsize : CProg.ringSize cp = 0) :
    treeFast cp = CTree.empty :=
  treeWith_ring_zero CProg.cpColorFast cp hsize

@[simp]
theorem treeFast_ring_one (cp : CProg)
    (hsize : CProg.ringSize cp = 1) :
    treeFast cp = CTree.empty :=
  treeWith_ring_one CProg.cpColorFast cp hsize

theorem treeFast_succ_succ
    (cp : CProg) (h : Nat)
    (hsize : CProg.ringSize cp = Nat.succ (Nat.succ h)) :
    treeFast cp = treeOfHeight h (CProg.cpColorFast cp) :=
  treeWith_succ_succ CProg.cpColorFast cp h hsize

theorem treeFast_spec (cp : CProg) :
    treeFast cp = tree cp := by
  unfold treeFast tree treeWith
  cases CProg.ringSize cp with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ h =>
          simp [treeOfHeight, CProg.cpColorFast_spec]

end KempeTree

end FourColor

end Schematic.Math.GraphTheory
