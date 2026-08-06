import Mathlib.Data.List.Rotate
import FourColorTheorem.FourColor.Coloring.CTree
import FourColorTheorem.FourColor.Configuration.Encoding

/-!
Executable configuration-colouring branch trees and their branch semantics.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CProg

/-- Second-stage optimized branch builder from Coq's `cfcbr2`: push every
remaining colour through a supplied one-branch constructor. -/
def cfBranch2 (h : Color → CTree → CTree) : ColSeq → CTree
  | [] => CTree.simpleLeaf
  | e :: et => h e (cfBranch2 h et)

/-- One-branch constructor after applying an arbitrary colour map. -/
def ctreeConsMap (g : Color → Color) (c : Color) : CTree → CTree :=
  CTree.consE (g c)

/-- First-stage optimized branch builder from Coq's `cfcbr1`: scan until the
normalised tail is known to be even, then switch to the straight builder. -/
def cfBranch1 (g : Color → Color) : ColSeq → CTree
  | [] => CTree.simpleLeaf
  | e :: et =>
      match g e with
      | Color.zero => CTree.empty
      | Color.one => CTree.cons1 (cfBranch1 g et)
      | Color.two => CTree.cons2 (cfBranch2 (ctreeConsMap g) et)
      | Color.three =>
          CTree.cons2 (cfBranch2 (ctreeConsMap (fun c => EdgePerm.p132 (g c))) et)

/-- Optimized executable branch builder corresponding to Coq's `cpbranch`. -/
def cpBranchFast : ColSeq → CTree
  | _ :: e :: et =>
      if e = Color.zero then CTree.empty
      else cfBranch1 (EdgePerm.edgeRot e) et
  | _ => CTree.empty

/-- Tree branch for a full edge trace: it stores the normalised even tail of
the trace after dropping the first edge colour.  This is the specification form
of Coq's optimised `cpbranch`. -/
def cpBranch (et : ColSeq) : CTree :=
  CTree.ofTtail (ColSeq.etail (et.drop 1))

theorem cpBranch_spec (et : ColSeq) :
    cpBranch et = CTree.ofTtail (ColSeq.etail (et.drop 1)) := rfl

theorem cpBranch_proper (et : ColSeq) :
    CTree.Proper (ColSeq.etail (et.drop 1)).length (cpBranch et) := by
  simp [cpBranch, CTree.proper_ofTtail]

theorem cpBranch_mem_iff_of_not_mem_zero_etail
    {et et' : ColSeq}
    (hzero : Color.zero ∉ ColSeq.etail (et.drop 1)) :
    CTree.mem (cpBranch et) et' = true ↔
      et' = ColSeq.etail (et.drop 1) := by
  simpa [cpBranch] using
    (CTree.mem_ofTtail_iff
      (et := ColSeq.etail (et.drop 1)) (et' := et') hzero)

theorem cpBranch_mem_self_of_not_mem_zero_etail
    {et : ColSeq}
    (hzero : Color.zero ∉ ColSeq.etail (et.drop 1)) :
    CTree.mem (cpBranch et) (ColSeq.etail (et.drop 1)) = true :=
  (cpBranch_mem_iff_of_not_mem_zero_etail
    (et := et) (et' := ColSeq.etail (et.drop 1)) hzero).2 rfl

theorem cpBranch_mem_iff_of_proper_no_zero_drop
    {et et' : ColSeq}
    (hproper : ColSeq.ProperTrace (et.drop 1))
    (hzeroDrop : Color.zero ∉ et.drop 1) :
    CTree.mem (cpBranch et) et' = true ↔
      et' = ColSeq.etail (et.drop 1) := by
  exact cpBranch_mem_iff_of_not_mem_zero_etail
    ((ColSeq.not_mem_zero_etail_iff (et.drop 1)).2
      ⟨hproper, hzeroDrop⟩)

theorem cfBranch2_eq_ofTtail_map
    (h : Color → Color) :
    ∀ et : ColSeq,
      cfBranch2 (ctreeConsMap h) et = CTree.ofTtail (et.map h)
  | [] => rfl
  | e :: et => by
      simp [cfBranch2, ctreeConsMap, CTree.ofTtail,
        cfBranch2_eq_ofTtail_map h et]

theorem cfBranch1_eq_ofTtail_evenMap
    (g : Color → Color) :
    ∀ et : ColSeq,
      cfBranch1 g et =
        CTree.ofTtail
          (if ColSeq.evenTail (et.map g) then
            et.map g
          else
            et.map (fun c => EdgePerm.p132 (g c)))
  | [] => rfl
  | e :: et => by
      have ih := cfBranch1_eq_ofTtail_evenMap g et
      cases hg : g e with
      | zero =>
          cases heven : ColSeq.evenTail (et.map g) <;>
            simp [cfBranch1, hg, heven]
      | one =>
          cases heven : ColSeq.evenTail (et.map g) <;>
            simp [cfBranch1, hg, heven, ih,
              CTree.cons1, EdgePerm.apply]
      | two =>
          simp [cfBranch1, hg, ColSeq.evenTail, CTree.cons2,
            cfBranch2_eq_ofTtail_map]
      | three =>
          simp [cfBranch1, hg, ColSeq.evenTail, CTree.cons2,
            cfBranch2_eq_ofTtail_map, EdgePerm.apply]

theorem cfBranch1_eq_ofTtail_evenPerm
    (g : EdgePerm) (et : ColSeq) :
    cfBranch1 (fun c => g c) et =
      CTree.ofTtail
        (if ColSeq.evenTail (ColSeq.perm g et) then
          ColSeq.perm g et
        else
          ColSeq.perm EdgePerm.p132 (ColSeq.perm g et)) := by
  simpa [ColSeq.perm] using
    cfBranch1_eq_ofTtail_evenMap (fun c => g c) et

theorem cpBranchFast_spec (et : ColSeq) :
    cpBranchFast et = cpBranch et := by
  cases et with
  | nil =>
      rfl
  | cons e0 et =>
      cases et with
      | nil =>
          rfl
      | cons e et =>
          cases e with
          | zero =>
              simp [cpBranchFast, cpBranch, ColSeq.etail, ColSeq.ttail,
                ColSeq.etracePerm, ColSeq.evenTrace, ColSeq.evenTail,
                ColSeq.ProperTrace, ColSeq.headColor]
          | one =>
              change cfBranch1 (fun c => EdgePerm.p123 c) et =
                CTree.ofTtail (ColSeq.etail (Color.one :: et))
              rw [cfBranch1_eq_ofTtail_evenPerm EdgePerm.p123 et]
              cases heven : ColSeq.evenTail (ColSeq.perm EdgePerm.p123 et) with
              | false =>
                  have hplain : ColSeq.evenTail et = false := by
                    simpa [ColSeq.perm_id] using heven
                  simp [ColSeq.etail, ColSeq.ttail, ColSeq.etracePerm,
                    ColSeq.evenTrace, hplain, ColSeq.ProperTrace,
                    ColSeq.headColor, EdgePerm.edgeRot]
              | true =>
                  have hplain : ColSeq.evenTail et = true := by
                    simpa [ColSeq.perm_id] using heven
                  simp [ColSeq.etail, ColSeq.ttail, ColSeq.etracePerm,
                    ColSeq.evenTrace, hplain, ColSeq.ProperTrace,
                    ColSeq.headColor, EdgePerm.edgeRot]
          | two =>
              change cfBranch1 (fun c => EdgePerm.p312 c) et =
                CTree.ofTtail (ColSeq.etail (Color.two :: et))
              rw [cfBranch1_eq_ofTtail_evenPerm EdgePerm.p312 et]
              cases heven : ColSeq.evenTail (ColSeq.perm EdgePerm.p312 et) <;>
                simp [ColSeq.etail, ColSeq.ttail, ColSeq.etracePerm,
                  ColSeq.evenTrace, heven, ColSeq.ProperTrace,
                  ColSeq.headColor, EdgePerm.edgeRot, ColSeq.perm_comp_apply]
          | three =>
              change cfBranch1 (fun c => EdgePerm.p231 c) et =
                CTree.ofTtail (ColSeq.etail (Color.three :: et))
              rw [cfBranch1_eq_ofTtail_evenPerm EdgePerm.p231 et]
              cases heven : ColSeq.evenTail (ColSeq.perm EdgePerm.p231 et) <;>
                simp [ColSeq.etail, ColSeq.ttail, ColSeq.etracePerm,
                  ColSeq.evenTrace, heven, ColSeq.ProperTrace,
                  ColSeq.headColor, EdgePerm.edgeRot, ColSeq.perm_comp_apply]

theorem cpBranchFast_proper (et : ColSeq) :
    CTree.Proper (ColSeq.etail (et.drop 1)).length (cpBranchFast et) := by
  rw [cpBranchFast_spec]
  exact cpBranch_proper et


end CProg

end FourColor

end Schematic.Math.GraphTheory
