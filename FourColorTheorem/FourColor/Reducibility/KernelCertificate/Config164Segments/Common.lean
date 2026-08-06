import FourColorTheorem.FourColor.Configuration.Database
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.BaseWitness
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.ConfigBridge
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.Source
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.ProgramReplay

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KernelCertificate

def config164Height : Nat := CProg.ringSize Config.cf164.program - 1

abbrev config164Boundary (et : ColSeq) : Prop :=
  Config.cf164.map.map.RingTrace
    (CProg.rotateLeft 1 Config.cf164.ringDarts) et

abbrev Config164SourceSound (limit : Nat) : Prop :=
  SourceSound config164Height config164Boundary config164Source limit

theorem config164_program_config :
    CProg.config Config.cf164.program = true := by
  decide

theorem config164_base_accepted
    {et : ColSeq} (hspec : CProg.cpColorSpec Config.cf164.program et) :
    Chromogram.KempeCoclosure config164Boundary (ColSeq.ctrace et) :=
  configColorSpec_coclosure config164_program_config hspec

theorem config164_sourceSound_zero : Config164SourceSound 0 :=
  sourceSound_zero config164Height config164Boundary config164Source

def config164ContractProgram : CProg := [
  CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.h,
  CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 3,
  CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
  CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 2,
  CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
  CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
  CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.u, CpStep.y
]

/-- The program left after `cpColor0Spec` consumes the initial reversed `Y`. -/
def config164ReplayProgram : CProg := [
  CpStep.u, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
  CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 8, CpStep.h,
  CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 2,
  CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 3, CpStep.y,
  CpStep.rotate 1, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 3,
  CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.h,
  CpStep.rotate 11, CpStep.h, CpStep.rotate 3, CpStep.h
]

theorem config164_contractProgram_reverse :
    config164ContractProgram.reverse = CpStep.y :: config164ReplayProgram := by
  decide

theorem config164_contractProgram :
    CProg.contractProgram Config.cf164.initialRingMask
      Config.cf164.contractMask Config.cf164.program =
        some config164ContractProgram := by
  decide

theorem config164_validContractMask :
    CfMask.validContractMask Config.cf164.contractMask
      Config.cf164.program = true := by
  decide

theorem config164_contractTree :
    Config.cf164.contractTree =
      some (CProg.cpColor config164ContractProgram) :=
  (Config.contractTree_eq_some_iff _ _).2
    ⟨config164ContractProgram, config164_contractProgram,
      config164_validContractMask, rfl⟩

theorem config164Height_eq : config164Height = 12 := by
  decide

/-- Declare one independently checked owner-trie certificate.  The owner data
generator emits hundreds of these certificates; keeping the resource bounds
and proposition template here prevents the generated check modules from
repeating them. -/
syntax (name := ownerTrieCertificate)
  "owner_trie_certificate " ident " for " term " using " term : command

macro_rules
  | `(owner_trie_certificate $certificate:ident for $pfx:term
        using $trie:term) =>
      `(set_option maxHeartbeats 0 in
        set_option maxRecDepth 100000 in
        theorem $certificate :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyOwnerTrie)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Height)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Source)
              $pfx $trie = true := by
          decide)

/-- Declare one base-witness check and its source-soundness step. -/
syntax (name := config164BaseCertificate)
  "config164_base_certificate " ident " and " ident " using " ident
    " from " term:max " to " term:max : command

macro_rules
  | `(config164_base_certificate $verified:ident and $sound:ident
        using $witnesses:ident from $start:term to $finish:term) =>
      `(section
        set_option maxHeartbeats 0 in
        set_option maxRecDepth 100000 in
        theorem $verified :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyBaseWitnesses)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Height)
              ($(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.Config.program)
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.Config.cf164))
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Source)
              $start $witnesses = true := by
          decide

        set_option maxRecDepth 100000 in
        theorem $sound
            (hsound :
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
                $start) :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
              $finish := by
          change
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
              ($start + List.length $witnesses)
          exact
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyBaseWitnesses_sound)
              (h :=
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Height))
              (P :=
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Boundary))
              (cp :=
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.Config.program)
                  $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.Config.cf164))
              (source :=
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Source))
              (fun et hspec =>
                $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164_base_accepted)
                  (et := et) hspec)
              hsound $verified
        end)

/-- Declare one independently checked owner-entry segment and its soundness
step. -/
syntax (name := config164OwnerSegmentCertificate)
  "config164_owner_segment_certificate " ident " and " ident " using " ident
    " from " term:max " to " term:max : command

macro_rules
  | `(config164_owner_segment_certificate $verified:ident and $sound:ident
        using $entries:ident from $start:term to $finish:term) =>
      `(section
        set_option maxHeartbeats 0 in
        set_option maxRecDepth 100000 in
        theorem $verified :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyOwnerEntries)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Height)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Source)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164OwnerTrie)
              $start $finish $entries = true := by
          decide

        theorem $sound
            (hsound :
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
                $start) :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
              $finish :=
          $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyOwnerEntries_sound)
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164OwnerTrie_sound)
            hsound $verified
        end)

/-- Declare one independently checked program-transition range together with
its semantic soundness theorem. -/
syntax (name := config164TransitionCertificate)
  "config164_transition_certificate " ident " and " ident " using " "("
    term "," term "," term "," term "," term "," term "," term
    "," term "," term ")" : command

macro_rules
  | `(config164_transition_certificate $verified:ident and $sound:ident
        using ($currentLength:term, $currentSource:term,
          $nextLength:term, $nextSource:term, $nextCount:term,
          $nextRefs:term, $programStep:term, $start:term, $count:term)) =>
      `(section
        set_option maxHeartbeats 0 in
        set_option maxRecDepth 100000 in
        theorem $verified :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyTransitionRange)
              $currentLength $currentSource $nextLength $nextSource
              $nextCount $nextRefs $programStep $start $count = true := by
          decide

        theorem $sound :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.TransitionRangeSound)
              $currentLength $currentSource $nextLength $nextSource
              $nextCount $programStep $start $count :=
          $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyTransitionRange_sound)
            $verified
        end)

/-- Declare one independently checked final program range and its soundness
theorem. -/
syntax (name := config164FinalCertificate)
  "config164_final_certificate " ident " and " ident " using " "("
    term "," term "," term ")" : command

macro_rules
  | `(config164_final_certificate $verified:ident and $sound:ident
        using ($sourceCount:term, $start:term, $count:term)) =>
      `(section
        set_option maxHeartbeats 0 in
        set_option maxRecDepth 100000 in
        theorem $verified :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyFinalRange)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Stage034Length)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Stage034Source)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Height)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Source)
              $sourceCount
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164TargetRefs)
              $start $count = true := by
          decide

        theorem $sound
            (hsound :
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.Config164SourceSound)
                $sourceCount) :
            $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.FinalRangeSound)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Boundary)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Stage034Length)
              $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.config164Stage034Source)
              $start $count :=
          $(Lean.mkIdent `Schematic.Math.GraphTheory.FourColor.KernelCertificate.verifyFinalRange_sound)
            hsound $verified
        end)

end KernelCertificate

end FourColor

end Schematic.Math.GraphTheory
