import FourColorTheorem.FourColor.Configuration.Encoding.Config

/-! Configuration masks, selection, and Boolean counting. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

/-- A pair of masks selecting ring and kernel faces of a configuration
program. -/
structure CfMask where
  ring : List Bool
  kernel : List Bool
  deriving DecidableEq, Repr

namespace CfMask

/-- A mask has the lengths required by a program. -/
def Proper (cp : CProg) (m : CfMask) : Prop :=
  m.ring.length = CProg.ringSize cp ∧
    m.kernel.length = CProg.kernelSize cp

/-- Empty mask used as the failure/default value for syntax-only mask
algorithms. -/
def empty : CfMask where
  ring := []
  kernel := []

/-- Rotate the ring component of a mask. -/
def rotateRing (n : Nat) (m : CfMask) : CfMask where
  ring := CProg.rotateLeft n m.ring
  kernel := m.kernel

theorem proper_rotateRing
    {cp : CProg} {m : CfMask} (n : Nat)
    (hm : Proper cp m) :
    Proper cp (rotateRing n m) := by
  constructor
  · simpa [rotateRing, Proper, CProg.length_rotateLeft] using hm.1
  · simpa [rotateRing, Proper] using hm.2

/-- The mask selecting the `i`th kernel entry and no ring entries. -/
def kernelSingleton (cp : CProg) (i : Nat) : CfMask where
  ring := List.replicate (CProg.ringSize cp) false
  kernel := (List.range (CProg.kernelSize cp)).map (fun j => j == i)

theorem proper_kernelSingleton (cp : CProg) (i : Nat) :
    Proper cp (kernelSingleton cp i) := by
  constructor
  · simp [kernelSingleton]
  · simp [kernelSingleton]

/-- Coq-name alias for the singleton kernel mask `cfmask1`. -/
abbrev cfmask1 : CProg → Nat → CfMask := kernelSingleton

/-- Coq `proper_cpmask1`. -/
theorem proper_cpmask1 (cp : CProg) (i : Nat) :
    Proper cp (cfmask1 cp i) :=
  proper_kernelSingleton cp i

end CfMask

end FourColor

end Schematic.Math.GraphTheory
