import FourColorTheorem.FourColor.Reducibility.CFContract.Foundations

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

namespace CFContract.Internal

def yNilResult (b1 b2 b3 : Bool) : CProg :=
  if b1 || (b2 || b3) then [] else [CpStep.y]

def yResult (b1 b2 b3 : Bool) (cpc : CProg) : CProg :=
  if b1 || b2 then cpc
  else (if b3 then CpStep.u else CpStep.y) :: cpc

def hResult (b1 b2 b3 b4 b5 : Bool) (cpc : CProg) : CProg :=
  if b3 then cpc
  else if b1 then
    if b2 then CpStep.a :: cpc
    else if b5 then cpc else CpStep.k :: cpc
  else if b2 then
    if b4 then cpc else CpStep.k :: cpc
  else if b4 then
    if b5 then CpStep.u :: cpc else CpStep.y :: cpc
  else if b5 then CpStep.y :: cpc else CpStep.h :: cpc

/-- A single induction principle for successful contraction-program runs.
It isolates the parser and recursive control flow shared by the semantic
correctness and rooted-sparsity proofs. -/
theorem contractProgram_induction
    (P : List Bool → List Bool → CProg → CProg → Prop)
    (rotateCase : ∀ n mr mc cp cpc,
      mr.length = CProg.ringSize (CpStep.rotate n :: cp) →
      mc.length = CProg.contractEdgeSize (CpStep.rotate n :: cp) →
      CProg.contractProgram (CProg.rotateRight n mr) mc cp = some cpc →
      P (CProg.rotateRight n mr) mc cp cpc →
      P mr mc (CpStep.rotate n :: cp)
        (CpStep.rotate
          (CProg.countFalse ((CProg.rotateRight n mr).take n)) :: cpc))
    (yNilCase : ∀ b1 b2 b3,
      CProg.nonSparse b1 b2 b3 = false →
      P [b1, b2, b3] [] [CpStep.y] (yNilResult b1 b2 b3))
    (yCase : ∀ b1 b2 b3 mr mc step cp cpc,
      (b1 :: b2 :: mr).length =
        CProg.ringSize (CpStep.y :: step :: cp) →
      (b3 :: mc).length =
        CProg.contractEdgeSize (CpStep.y :: step :: cp) →
      CProg.nonSparse b1 b2 b3 = false →
      CProg.contractProgram (b3 :: mr) mc (step :: cp) = some cpc →
      P (b3 :: mr) mc (step :: cp) cpc →
      P (b1 :: b2 :: mr) (b3 :: mc) (CpStep.y :: step :: cp)
        (yResult b1 b2 b3 cpc))
    (hCase : ∀ b1 b2 b3 b4 b5 mr mc cp cpc,
      (b1 :: b2 :: mr).length = CProg.ringSize (CpStep.h :: cp) →
      (b3 :: b4 :: b5 :: mc).length =
        CProg.contractEdgeSize (CpStep.h :: cp) →
      CProg.nonSparse b3 b1 b4 = false →
      CProg.nonSparse b3 b2 b5 = false →
      ¬ (b1 && b2 && mr.all (fun b => b)) →
      CProg.contractProgram (b4 :: b5 :: mr) mc cp = some cpc →
      P (b4 :: b5 :: mr) mc cp cpc →
      P (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc) (CpStep.h :: cp)
        (hResult b1 b2 b3 b4 b5 cpc)) :
    ∀ {mr mc cp cpc},
      mr.length = CProg.ringSize cp →
      mc.length = CProg.contractEdgeSize cp →
      CProg.contractProgram mr mc cp = some cpc →
      P mr mc cp cpc := by
  intro mr mc cp
  induction cp generalizing mr mc with
  | nil =>
      intro cpc _ _ hrun
      simp [CProg.contractProgram] at hrun
  | cons step cp ih =>
      intro cpc hmr hmc hrun
      cases step with
      | rotate n =>
          simp only [CProg.contractProgram] at hrun
          cases hcp : CProg.contractProgram (CProg.rotateRight n mr) mc cp with
          | none => simp [hcp] at hrun
          | some cp' =>
              have hmr' : (CProg.rotateRight n mr).length =
                  CProg.ringSize cp := by
                rw [CProg.length_rotateRight]
                simpa [CProg.ringSize] using hmr
              have hmc' : mc.length = CProg.contractEdgeSize cp := by
                simpa [CProg.contractEdgeSize] using hmc
              simp [hcp] at hrun
              subst cpc
              exact rotateCase n mr mc cp cp' hmr hmc hcp
                (ih hmr' hmc' hcp)
      | reverseRotate =>
          simp [CProg.contractProgram] at hrun
      | y =>
          cases cp with
          | nil =>
              have hmr3 : mr.length = 3 := by
                simpa [CProg.ringSize] using hmr
              rcases List.length_eq_three.mp hmr3 with ⟨b1, b2, b3, rfl⟩
              have hmc0 : mc.length = 0 := by
                simpa [CProg.contractEdgeSize] using hmc
              have hmcnil := List.eq_nil_of_length_eq_zero hmc0
              subst mc
              cases b1 <;> cases b2 <;> cases b3 <;>
                simp [CProg.contractProgram, CProg.nonSparse] at hrun ⊢
              all_goals subst cpc
              all_goals exact yNilCase _ _ _ (by decide)
          | cons step cp =>
              cases mr with
              | nil => simp [CProg.contractProgram] at hrun
              | cons b1 mr1 =>
                  cases mr1 with
                  | nil => simp [CProg.contractProgram] at hrun
                  | cons b2 mr =>
                      cases mc with
                      | nil => simp [CProg.contractProgram] at hrun
                      | cons b3 mc =>
                          by_cases hnsp : CProg.nonSparse b1 b2 b3
                          · simp [CProg.contractProgram, hnsp] at hrun
                          · have hnsp' :
                                CProg.nonSparse b1 b2 b3 = false := by
                              simpa using hnsp
                            simp only [CProg.contractProgram] at hrun
                            rw [if_neg hnsp] at hrun
                            cases hcp : CProg.contractProgram (b3 :: mr) mc
                                (step :: cp) with
                            | none => simp [hcp] at hrun
                            | some cp' =>
                                have hmr' : (b3 :: mr).length =
                                    CProg.ringSize (step :: cp) := by
                                  simp [CProg.ringSize] at hmr ⊢
                                  omega
                                have hmc' : mc.length =
                                    CProg.contractEdgeSize (step :: cp) := by
                                  simp [CProg.contractEdgeSize] at hmc ⊢
                                  omega
                                simp [hcp] at hrun
                                subst cpc
                                simpa [yResult] using
                                  yCase b1 b2 b3 mr mc step cp cp'
                                    hmr hmc hnsp' hcp (ih hmr' hmc' hcp)
      | h =>
          cases mr with
          | nil => simp [CProg.contractProgram] at hrun
          | cons b1 mr1 =>
              cases mr1 with
              | nil => simp [CProg.contractProgram] at hrun
              | cons b2 mr =>
                  cases mc with
                  | nil => simp [CProg.contractProgram] at hrun
                  | cons b3 mc1 =>
                      cases mc1 with
                      | nil => simp [CProg.contractProgram] at hrun
                      | cons b4 mc2 =>
                          cases mc2 with
                          | nil => simp [CProg.contractProgram] at hrun
                          | cons b5 mc =>
                              let guard := CProg.nonSparse b3 b1 b4 ||
                                CProg.nonSparse b3 b2 b5
                              by_cases hguard : guard
                              · simp [CProg.contractProgram, guard, hguard] at hrun
                              · have hguard' : guard = false := by
                                  simpa using hguard
                                have hnsps :
                                    CProg.nonSparse b3 b1 b4 = false ∧
                                      CProg.nonSparse b3 b2 b5 = false := by
                                  simpa [guard] using hguard'
                                simp only [CProg.contractProgram] at hrun
                                rw [if_neg hguard] at hrun
                                by_cases hall :
                                    b1 && b2 && mr.all (fun b => b)
                                · simp [hall] at hrun
                                · rw [if_neg hall] at hrun
                                  cases hcp : CProg.contractProgram
                                      (b4 :: b5 :: mr) mc cp with
                                  | none => simp [hcp] at hrun
                                  | some cp' =>
                                      have hmr' : (b4 :: b5 :: mr).length =
                                          CProg.ringSize cp := by
                                        simpa [CProg.ringSize] using hmr
                                      have hmc' : mc.length =
                                          CProg.contractEdgeSize cp := by
                                        simp [CProg.contractEdgeSize] at hmc ⊢
                                        omega
                                      simp [hcp] at hrun
                                      subst cpc
                                      simpa [hResult] using
                                        hCase b1 b2 b3 b4 b5 mr mc cp cp'
                                          hmr hmc hnsps.1 hnsps.2 hall hcp
                                          (ih hmr' hmc' hcp)
      | u => simp [CProg.contractProgram] at hrun
      | k => simp [CProg.contractProgram] at hrun
      | a => simp [CProg.contractProgram] at hrun

end CFContract.Internal

end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
