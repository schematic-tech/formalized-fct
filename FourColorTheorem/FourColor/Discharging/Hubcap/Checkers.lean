import FourColorTheorem.FourColor.Discharging.Hubcap.Rotation

/-! Executable source, target, and hubcap-fit checkers. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open Part PartRel

namespace Discharge

namespace Hubcap

/-- Interpret a nonnegative integer as a natural number. -/
def intAsNat? (z : Int) : Option Nat :=
  if z < 0 then none else some z.toNat

theorem intAsNat?_eq_some {z : Int} {n : Nat}
    (h : intAsNat? z = some n) :
    0 ≤ z ∧ z = n := by
  unfold intAsNat? at h
  by_cases hz : z < 0
  · simp [hz] at h
  · simp [hz] at h
    have hznon : 0 ≤ z := le_of_not_gt hz
    exact ⟨hznon, by
      rw [← Int.toNat_of_nonneg hznon, h]⟩

theorem intAsNat?_eq_some_of_nonneg {z : Int}
    (hz : 0 ≤ z) :
    intAsNat? z = some z.toNat := by
  unfold intAsNat?
  have hnlt : ¬ z < 0 := by omega
  simp [hnlt]

theorem intAsNat?_eq_none_iff {z : Int} :
    intAsNat? z = none ↔ z < 0 := by
  unfold intAsNat?
  by_cases hz : z < 0 <;> simp [hz]

/-- Source-bound recursion from Coq `check_dbound1_rec`. -/
def checkDbound1Rec (redp : Part → Bool) (p : Part) (rs : Drules)
    (ns : Nat) : Nat → Bool
  | 0 => false
  | m + 1 =>
      match rs with
      | [] => true
      | r :: rs' =>
          if rs'.length < ns then
            true
          else
            let p' := Part.meet p r
            let sorted := sortDrules p' rs'
            let first :=
              match ns - sorted.nbForcedDrules with
              | 0 => redp p'
              | ns' + 1 => checkDbound1Rec redp p' sorted.straddlingDrules ns' m
            first && checkDbound1Rec redp p rs' ns m

def checkDbound1 (redp : Part → Bool) {nhub : Nat}
    (rf : DruleFork nhub) (p : Part) (ns : Nat) : Bool :=
  checkDbound1Rec redp p rf.sourceDrules ns (rf.sourceDrules.length + 1)

/-- Whether `p` implies one of the excluded rules. -/
def checkUnfit (p : Part) : Drules → Bool
  | [] => false
  | r :: rs =>
      match Part.cmp p r with
      | Psubset => true
      | _ => checkUnfit p rs

theorem checkUnfit_eq_true_exists_subset {p : Part} :
    ∀ {rs : Drules},
      checkUnfit p rs = true →
        ∃ r ∈ rs, Part.cmp p r = PartRel.Psubset := by
  intro rs
  induction rs with
  | nil =>
      intro h
      simp [checkUnfit] at h
  | cons r rs ih =>
      intro h
      simp [checkUnfit] at h
      cases hcmp : Part.cmp p r
      · simp [hcmp] at h
        rcases ih h with ⟨r', hr', hcmp'⟩
        exact ⟨r', by simp [hr'], hcmp'⟩
      · simp [hcmp] at h
        rcases ih h with ⟨r', hr', hcmp'⟩
        exact ⟨r', by simp [hr'], hcmp'⟩
      · exact ⟨r, by simp, hcmp⟩

/-- Single target-bound recursion from Coq `check_dbound2_rec`. -/
def checkDbound2Rec (redp : Part → Bool) (p : Part)
    (rt rs ru : Drules) (nt : Nat) : Nat → Bool
  | 0 => false
  | m + 1 =>
      match rt with
      | [] => true
      | r :: rt' =>
          if rt'.length < nt then
            true
          else
            let p' := Part.meet p r
            let first :=
              if checkUnfit p' ru then
                true
              else
                let srt := sortDrules p' rt'
                let srs := sortDrules p' rs
                match srs.nbForcedDrules + nt - srt.nbForcedDrules with
                | 0 => redp p'
                | nt' + 1 =>
                    checkDbound2Rec redp p' srt.straddlingDrules
                      srs.straddlingDrules ru nt' m
            first && checkDbound2Rec redp p rt' rs (r :: ru) nt m

def checkDbound2 (redp : Part → Bool) {nhub : Nat}
    (rf : DruleFork nhub) (p : Part) (b : Int) : Bool :=
  let srt := sortDrules p rf.targetDrules
  let srs := sortDrules p rf.sourceDrules
  match intAsNat? (Int.ofNat srs.nbForcedDrules -
      Int.ofNat srt.nbForcedDrules + b) with
  | none => false
  | some nt =>
      checkDbound2Rec redp p srt.straddlingDrules srs.straddlingDrules
        [] nt (srt.straddlingDrules.length + 2)

/-- Dual target-bound recursion from Coq `check_2dbound2_rec`. -/
def check2Dbound2Rec (nhub : Nat) (redp : Part → Bool)
    (p1 p2 : Part)
    (rt1 rs1 ru1 rt2 rs2 ru2 : Drules)
    (i nt : Nat) : Nat → Bool
  | 0 => false
  | m + 1 =>
      match rt1 with
      | [] =>
          match rt2 with
          | [] => true
          | _ =>
              check2Dbound2Rec nhub redp p2 p1
                rt2 rs2 ru2 rt1 rs1 ru1 (nhub - i) nt m
      | r :: rt1' =>
          if rt1'.length + rt2.length < nt then
            true
          else
            let p1' := Part.meet p1 r
            let p2' := Part.rotate i p1'
            let first :=
              if checkUnfit p1' ru1 || checkUnfit p2' ru2 then
                true
              else
                let srt1 := sortDrules p1' rt1'
                let srs1 := sortDrules p1' rs1
                let srt2 := sortDrules p2' rt2
                let srs2 := sortDrules p2' rs2
                match srs1.nbForcedDrules + (srs2.nbForcedDrules + nt) -
                    (srt1.nbForcedDrules + srt2.nbForcedDrules) with
                | 0 => redp p1'
                | nt' + 1 =>
                    check2Dbound2Rec nhub redp p1' p2'
                      srt1.straddlingDrules srs1.straddlingDrules ru1
                      srt2.straddlingDrules srs2.straddlingDrules ru2
                      i nt' m
            first && check2Dbound2Rec nhub redp p1 p2
              rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt m

def check2Dbound2 (redp : Part → Bool) {nhub : Nat}
    (rf : DruleFork nhub) (p1 : Part) (i : Nat) (b : Int) : Bool :=
  let p2 := Part.rotate i p1
  let srt1 := sortDrules p1 rf.targetDrules
  let srs1 := sortDrules p1 rf.sourceDrules
  let srt2 := sortDrules p2 rf.targetDrules
  let srs2 := sortDrules p2 rf.sourceDrules
  match intAsNat? (Int.ofNat (srs1.nbForcedDrules + srs2.nbForcedDrules) -
      Int.ofNat (srt1.nbForcedDrules + srt2.nbForcedDrules) + b) with
  | none => false
  | some nt =>
      let m := srt1.straddlingDrules.length +
        (srt2.straddlingDrules.length + 3)
      check2Dbound2Rec nhub redp p1 p2
        srt1.straddlingDrules srs1.straddlingDrules []
        srt2.straddlingDrules srs2.straddlingDrules []
        i nt m

/-- Hubcap fit checker for a fixed part. -/
def fit (nhub : Nat) (redp : Part → Bool) (rf : DruleFork nhub)
    (p : Part) : Hubcap → Bool
  | Hubcap0 => true
  | Hubcap1 j b hc =>
      checkDbound2 redp rf (rot nhub j p) b && fit nhub redp rf p hc
  | Hubcap2 j1 j2 b hc =>
      check2Dbound2 redp rf (rot nhub j1 p) (hubSubn nhub j2 j1) b &&
        fit nhub redp rf p hc

end Hubcap

end Discharge

end FourColor

end Schematic.Math.GraphTheory
