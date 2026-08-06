import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Semantics

/-!
Kernel-replayable compact Kempe certificates.

Each entry names a fixed-length trace and a colour permutation.  Replay checks
that the trace was already known or that the permuted trace satisfies the
local coverage condition against all earlier entries, then inserts it into the
known-trace trie.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KernelCertificate

/-- Decode one base-three digit as a non-zero edge colour. -/
def digitColor (n : Nat) : Color :=
  match n % 3 with
  | 0 => Color.one
  | 1 => Color.two
  | _ => Color.three

theorem digitColor_ne_zero (n : Nat) :
    digitColor n ≠ Color.zero := by
  simp [digitColor]
  split <;> simp

/-- Decode a compact base-three trace code at a fixed height. -/
def decodeTrace : Nat → Nat → ColSeq
  | 0, _ => []
  | h + 1, code => digitColor code :: decodeTrace h (code / 3)

@[simp]
theorem length_decodeTrace (h code : Nat) :
    (decodeTrace h code).length = h := by
  induction h generalizing code with
  | zero => rfl
  | succ h ih => simp [decodeTrace, ih]

theorem zero_not_mem_decodeTrace (h code : Nat) :
    Color.zero ∉ decodeTrace h code := by
  induction h generalizing code with
  | zero => simp [decodeTrace]
  | succ h ih =>
      simp only [decodeTrace, List.mem_cons, not_or]
      exact ⟨Ne.symm (digitColor_ne_zero code), ih (code / 3)⟩

/-- Decode the six edge-colour permutations from compact natural tags. -/
def decodePerm (tag : Nat) : EdgePerm :=
  match tag % 6 with
  | 0 => EdgePerm.p123
  | 1 => EdgePerm.p132
  | 2 => EdgePerm.p213
  | 3 => EdgePerm.p231
  | 4 => EdgePerm.p312
  | _ => EdgePerm.p321

/-- One topologically ordered certificate entry. -/
structure Entry where
  traceCode : Nat
  permTag : Nat
  deriving DecidableEq, Repr

namespace Entry

def trace (h : Nat) (entry : Entry) : ColSeq :=
  decodeTrace h entry.traceCode

def perm (entry : Entry) : EdgePerm :=
  decodePerm entry.permTag

/-- Check one entry against the trie containing all earlier entries. -/
def accepted (h : Nat) (known : TraceTrie) (entry : Entry) : Bool :=
  known.mem (entry.trace h) ||
    covered h known (ColSeq.perm entry.perm (entry.trace h))

end Entry

/-- Replay a topologically ordered certificate. -/
def replay (h : Nat) : List Entry → TraceTrie → Option TraceTrie
  | [], known => some known
  | entry :: entries, known =>
      if entry.accepted h known then
        replay h entries (known.insert (entry.trace h))
      else
        none

theorem replay_sound
    {h : Nat} {P : ColSeq → Prop} {entries : List Entry}
    {known final : TraceTrie}
    (hknown : ∀ et, known.mem et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hreplay : replay h entries known = some final) :
    ∀ et, final.mem et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  induction entries generalizing known with
  | nil =>
      simp [replay] at hreplay
      subst final
      exact hknown
  | cons entry entries ih =>
      unfold replay at hreplay
      cases haccept : entry.accepted h known with
      | false => simp [haccept] at hreplay
      | true =>
          rw [haccept] at hreplay
          apply ih (known := known.insert (entry.trace h))
          · intro et hmem
            rcases TraceTrie.mem_of_mem_insert hmem with hEq | hOld
            · subst et
              unfold Entry.accepted at haccept
              cases hAlready : known.mem (entry.trace h) with
              | true => exact hknown _ hAlready
              | false =>
                  simp [hAlready] at haccept
                  exact kempeCoclosure_of_covered_perm hknown
                    (length_decodeTrace h entry.traceCode)
                    entry.perm haccept
            · exact hknown et hOld
          · exact hreplay

/-- Check a Boolean property at every represented trace leaf. -/
def allTreeMem : CTree → (ColSeq → Bool) → Bool
  | .empty, _ => true
  | .leaf _, p => p []
  | .node t1 t2 t3, p =>
      allTreeMem t1 (fun et => p (Color.one :: et)) &&
        allTreeMem t2 (fun et => p (Color.two :: et)) &&
          allTreeMem t3 (fun et => p (Color.three :: et))

theorem allTreeMem_sound :
    ∀ (t : CTree) (p : ColSeq → Bool),
      allTreeMem t p = true →
        ∀ et, CTree.mem t et = true → p et = true
  | .empty, p, hall, et, hmem => by simp at hmem
  | .leaf lf, p, hall, et, hmem => by
      cases et with
      | nil => simpa [allTreeMem] using hall
      | cons e et => simp [CTree.mem, CTree.sub] at hmem
  | .node t1 t2 t3, p, hall, et, hmem => by
      simp [allTreeMem] at hall
      cases et with
      | nil => simp [CTree.mem, CTree.sub] at hmem
      | cons e et =>
          cases e with
          | zero => simp [CTree.mem, CTree.sub] at hmem
          | one =>
              exact allTreeMem_sound t1 (fun et => p (Color.one :: et))
                hall.1.1 et (by simpa [CTree.mem, CTree.sub] using hmem)
          | two =>
              exact allTreeMem_sound t2 (fun et => p (Color.two :: et))
                hall.1.2 et (by simpa [CTree.mem, CTree.sub] using hmem)
          | three =>
              exact allTreeMem_sound t3 (fun et => p (Color.three :: et))
                hall.2 et (by simpa [CTree.mem, CTree.sub] using hmem)

/-- A compact certificate is a topologically ordered list of trace entries. -/
structure Certificate where
  entries : List Entry
  deriving DecidableEq, Repr

/-- Replay a certificate and check that its final trie covers every trace in
the supplied target tree. -/
def verifyAgainst
    (h : Nat) (base : TraceTrie) (target : CTree)
    (certificate : Certificate) : Bool :=
  match replay h certificate.entries base with
  | none => false
  | some known => allTreeMem target known.mem

theorem verifyAgainst_sound
    {h : Nat} {P : ColSeq → Prop} {base : TraceTrie}
    {target : CTree} {certificate : Certificate}
    (hbase : ∀ et, base.mem et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hverify : verifyAgainst h base target certificate = true) :
    ∀ et, CTree.mem target et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  unfold verifyAgainst at hverify
  cases hreplay : replay h certificate.entries base with
  | none => simp [hreplay] at hverify
  | some known =>
      rw [hreplay] at hverify
      have hknown := replay_sound hbase hreplay
      intro et hmem
      exact hknown et (allTreeMem_sound target known.mem hverify et hmem)

end KernelCertificate

end FourColor

end Schematic.Math.GraphTheory
