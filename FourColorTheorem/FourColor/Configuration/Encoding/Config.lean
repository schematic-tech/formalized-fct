import FourColorTheorem.FourColor.Configuration.Encoding.CProg

/-! Configuration descriptors and program parsing. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- A configuration descriptor: symmetry flag, reducibility contract reference
indices, and the construction program. -/
structure Config where
  symmetric : Bool
  contractRef : List Nat
  program : CProg
  deriving DecidableEq, Repr

namespace Config

/-- Parse the concrete Coq syntax convention: initial rotations before the
first non-rotation step are contract references, not construction steps. -/
def parse (symmetric : Bool) (contractAcc : List Nat) : CProg → Config
  | CpStep.rotate i :: cp => parse symmetric (i :: contractAcc) cp
  | cp => {
      symmetric := symmetric
      contractRef := contractAcc.reverse
      program := cp
    }

/-- Leading rotations in Coq's concrete configuration syntax are contract
references rather than construction steps. -/
def leadingContractRefs : CProg → List Nat
  | CpStep.rotate i :: cp => i :: leadingContractRefs cp
  | _ => []

/-- The construction program left after stripping leading contract-reference
rotations from Coq's concrete configuration syntax. -/
def dropLeadingContractRefs : CProg → CProg
  | CpStep.rotate _ :: cp => dropLeadingContractRefs cp
  | cp => cp

/-- Configuration-program well-formedness for a descriptor. -/
def WellFormed (cf : Config) : Prop :=
  CProg.config cf.program = true

/-- Cubic-program well-formedness for a descriptor. -/
def CubicProgram (cf : Config) : Prop :=
  CProg.cubic cf.program = true

theorem wellFormed_cubicProgram
    {cf : Config}
    (hcf : cf.WellFormed) :
    cf.CubicProgram :=
  CProg.config_implies_cubic hcf

@[simp]
theorem parse_program_of_nonrotate
    (sym : Bool) (cc : List Nat) :
    (parse sym cc []).program = [] := rfl

@[simp]
theorem parse_contract_of_nonrotate
    (sym : Bool) (cc : List Nat) :
    (parse sym cc []).contractRef = cc.reverse := rfl

theorem parse_rotate_contract
    (sym : Bool) (cc : List Nat) (i : Nat) (cp : CProg) :
    parse sym cc (CpStep.rotate i :: cp) = parse sym (i :: cc) cp := rfl

theorem parse_symmetric
    (sym : Bool) (cc : List Nat) (cp : CProg) :
    (parse sym cc cp).symmetric = sym := by
  induction cp generalizing cc with
  | nil => rfl
  | cons step cp ih =>
      cases step <;> simp [parse, ih]

theorem parse_contractRef
    (sym : Bool) (cc : List Nat) :
    ∀ cp : CProg,
      (parse sym cc cp).contractRef =
        cc.reverse ++ leadingContractRefs cp
  | [] => by
      simp [parse, leadingContractRefs]
  | CpStep.rotate i :: cp => by
      calc
        (parse sym cc (CpStep.rotate i :: cp)).contractRef
            = (parse sym (i :: cc) cp).contractRef := rfl
        _ = (i :: cc).reverse ++ leadingContractRefs cp :=
            parse_contractRef sym (i :: cc) cp
        _ = cc.reverse ++ leadingContractRefs (CpStep.rotate i :: cp) := by
            simp [leadingContractRefs, List.append_assoc]
  | CpStep.reverseRotate :: cp => by
      simp [parse, leadingContractRefs]
  | CpStep.y :: cp => by
      simp [parse, leadingContractRefs]
  | CpStep.h :: cp => by
      simp [parse, leadingContractRefs]
  | CpStep.u :: cp => by
      simp [parse, leadingContractRefs]
  | CpStep.k :: cp => by
      simp [parse, leadingContractRefs]
  | CpStep.a :: cp => by
      simp [parse, leadingContractRefs]

theorem parse_program
    (sym : Bool) (cc : List Nat) :
    ∀ cp : CProg,
      (parse sym cc cp).program = dropLeadingContractRefs cp
  | [] => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.rotate i :: cp => by
      calc
        (parse sym cc (CpStep.rotate i :: cp)).program
            = (parse sym (i :: cc) cp).program := rfl
        _ = dropLeadingContractRefs cp := parse_program sym (i :: cc) cp
        _ = dropLeadingContractRefs (CpStep.rotate i :: cp) := by
            simp [dropLeadingContractRefs]
  | CpStep.reverseRotate :: cp => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.y :: cp => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.h :: cp => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.u :: cp => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.k :: cp => by
      simp [parse, dropLeadingContractRefs]
  | CpStep.a :: cp => by
      simp [parse, dropLeadingContractRefs]

theorem parse_contractRef_nil
    (sym : Bool) (cp : CProg) :
    (parse sym [] cp).contractRef = leadingContractRefs cp := by
  simpa using parse_contractRef sym [] cp

theorem parse_program_nil
    (sym : Bool) (cp : CProg) :
    (parse sym [] cp).program = dropLeadingContractRefs cp :=
  parse_program sym [] cp

/-- Contract mask carried by a parsed configuration descriptor. -/
def contractMask (cf : Config) : List Bool :=
  CProg.contractMask cf.program cf.contractRef

/-- In-range contract-edge candidate indices selected by a configuration. -/
def selectedContractIndices (cf : Config) : List Nat :=
  CProg.selectedContractIndices cf.program cf.contractRef

theorem length_contractMask (cf : Config) :
    cf.contractMask.length = CProg.contractEdgeSize cf.program := by
  simp [contractMask, CProg.length_contractMask]

theorem length_selectedContractIndices_le (cf : Config) :
    cf.selectedContractIndices.length ≤ CProg.contractEdgeSize cf.program :=
  CProg.length_selectedContractIndices_le cf.program cf.contractRef

theorem mem_selectedContractIndices_iff (cf : Config) (k : Nat) :
    k ∈ cf.selectedContractIndices ↔
      k < CProg.contractEdgeSize cf.program ∧ k ∈ cf.contractRef := by
  simpa [selectedContractIndices] using
    CProg.mem_selectedContractIndices_iff cf.program cf.contractRef k

theorem mem_selectedContractIndices_lt
    {cf : Config} {k : Nat}
    (h : k ∈ cf.selectedContractIndices) :
    k < CProg.contractEdgeSize cf.program :=
  ((mem_selectedContractIndices_iff cf k).1 h).1

theorem mem_selectedContractIndices_ref
    {cf : Config} {k : Nat}
    (h : k ∈ cf.selectedContractIndices) :
    k ∈ cf.contractRef :=
  ((mem_selectedContractIndices_iff cf k).1 h).2

theorem nodup_selectedContractIndices (cf : Config) :
    cf.selectedContractIndices.Nodup :=
  CProg.nodup_selectedContractIndices cf.program cf.contractRef

theorem pairwise_lt_selectedContractIndices (cf : Config) :
    cf.selectedContractIndices.Pairwise (fun a b => a < b) :=
  CProg.pairwise_lt_selectedContractIndices cf.program cf.contractRef

/-- Finset view of the selected in-range contract-edge indices. -/
def selectedContractIndexFinset (cf : Config) : Finset Nat :=
  cf.selectedContractIndices.toFinset

theorem mem_selectedContractIndexFinset_iff (cf : Config) (k : Nat) :
    k ∈ cf.selectedContractIndexFinset ↔
      k < CProg.contractEdgeSize cf.program ∧ k ∈ cf.contractRef := by
  simp [selectedContractIndexFinset, mem_selectedContractIndices_iff]

theorem selectedContractIndexFinset_subset_contractRef
    (cf : Config) :
    ∀ ⦃k : Nat⦄, k ∈ cf.selectedContractIndexFinset → k ∈ cf.contractRef := by
  intro k hk
  exact ((mem_selectedContractIndexFinset_iff cf k).1 hk).2

theorem mem_selectedContractIndexFinset_lt
    {cf : Config} {k : Nat}
    (h : k ∈ cf.selectedContractIndexFinset) :
    k < CProg.contractEdgeSize cf.program :=
  ((mem_selectedContractIndexFinset_iff cf k).1 h).1

theorem card_selectedContractIndexFinset_eq_length
    (cf : Config) :
    cf.selectedContractIndexFinset.card = cf.selectedContractIndices.length :=
  List.toFinset_card_of_nodup cf.nodup_selectedContractIndices

theorem contractMask_parse
    (sym : Bool) (cc : List Nat) (cp : CProg) :
    (parse sym cc cp).contractMask =
      CProg.contractMask (dropLeadingContractRefs cp)
        (cc.reverse ++ leadingContractRefs cp) := by
  simp [contractMask, parse_program, parse_contractRef]

theorem contractMask_parse_nil
    (sym : Bool) (cp : CProg) :
    (parse sym [] cp).contractMask =
      CProg.contractMask (dropLeadingContractRefs cp)
        (leadingContractRefs cp) := by
  simpa using contractMask_parse sym [] cp

theorem selectedContractIndices_parse
    (sym : Bool) (cc : List Nat) (cp : CProg) :
    (parse sym cc cp).selectedContractIndices =
      CProg.selectedContractIndices (dropLeadingContractRefs cp)
        (cc.reverse ++ leadingContractRefs cp) := by
  simp [selectedContractIndices, parse_program, parse_contractRef]

theorem selectedContractIndices_parse_nil
    (sym : Bool) (cp : CProg) :
    (parse sym [] cp).selectedContractIndices =
      CProg.selectedContractIndices (dropLeadingContractRefs cp)
        (leadingContractRefs cp) := by
  simpa using selectedContractIndices_parse sym [] cp

theorem wellFormed_parse_iff
    (sym : Bool) (cc : List Nat) (cp : CProg) :
    (parse sym cc cp).WellFormed ↔
      CProg.config (dropLeadingContractRefs cp) = true := by
  simp [WellFormed, parse_program]

theorem cubicProgram_parse_iff
    (sym : Bool) (cc : List Nat) (cp : CProg) :
    (parse sym cc cp).CubicProgram ↔
      CProg.cubic (dropLeadingContractRefs cp) = true := by
  simp [CubicProgram, parse_program]

end Config

end FourColor

end Schematic.Math.GraphTheory
