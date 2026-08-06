import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

/-! Static chromogram owners for compact indexed closure replay. -/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

/-- A four-way trie assigning an earlier source reference to a chromogram. -/
inductive OwnerTrie
  | empty
  | node (owner : Option Nat)
      (push skip pop0 pop1 : OwnerTrie)
  deriving DecidableEq, Repr

namespace OwnerTrie

def get : OwnerTrie → Chromogram → Option Nat
  | .empty, _ => none
  | .node owner _ _ _ _, [] => owner
  | .node _ push _ _ _, GramSymbol.push :: word => push.get word
  | .node _ _ skip _ _, GramSymbol.skip :: word => skip.get word
  | .node _ _ _ pop0 _, GramSymbol.pop0 :: word => pop0.get word
  | .node _ _ _ _ pop1, GramSymbol.pop1 :: word => pop1.get word

/-- Select one grammar-symbol child, treating an absent trie as all absent. -/
def child : OwnerTrie → GramSymbol → OwnerTrie
  | .empty, _ => .empty
  | .node _ push _ _ _, .push => push
  | .node _ _ skip _ _, .skip => skip
  | .node _ _ _ pop0 _, .pop0 => pop0
  | .node _ _ _ _ pop1, .pop1 => pop1

@[simp]
theorem child_get (owners : OwnerTrie) (symbol : GramSymbol)
    (word : Chromogram) :
    (owners.child symbol).get word = owners.get (symbol :: word) := by
  cases owners <;> cases symbol <;> rfl

/-- Whether completion accepts a grammar prefix with this balance state. -/
def completionAccepts : Nat → Bool → Bool
  | 0, parity => parity
  | 1, _ => true
  | _ + 2, _ => false

def rootBelow (limit : Nat) : OwnerTrie → Bool
  | .empty => false
  | .node owner _ _ _ _ =>
      match owner with
      | none => false
      | some ref => decide (ref < limit)

theorem rootBelow_get
    {limit : Nat} {owners : OwnerTrie}
    (hbelow : rootBelow limit owners = true) :
    ∃ ref, ref < limit ∧ owners.get [] = some ref := by
  cases owners with
  | empty => simp [rootBelow] at hbelow
  | node owner push skip pop0 pop1 =>
      cases owner with
      | none => simp [rootBelow] at hbelow
      | some ref =>
          simp only [rootBelow, decide_eq_true_eq] at hbelow
          exact ⟨ref, hbelow, rfl⟩

/-- Direct owner coverage checker with the balance state threaded through the
open grammar traversal. Invalid partial chromograms are pruned immediately. -/
def coversState (limit : Nat) :
    Nat → Bool → Chromogram.BitStack → ColSeq → OwnerTrie → Bool
  | depth, parity, _, [], owners =>
      if completionAccepts depth parity then rootBelow limit owners else true
  | _, _, _, Color.zero :: _, _ => true
  | depth, parity, bs, Color.one :: et, owners =>
      coversState limit depth (!parity) bs et (owners.child .skip)
  | depth, parity, bs, Color.two :: et, owners =>
      coversState limit (depth + 1) parity (.push0 bs) et
          (owners.child .push) &&
        match bs, depth with
        | .empty, _ => true
        | _, 0 => true
        | .push0 bs', depth' + 1 =>
            coversState limit depth' parity bs' et (owners.child .pop0)
        | .push1 bs', depth' + 1 =>
            coversState limit depth' (!parity) bs' et (owners.child .pop1)
  | depth, parity, bs, Color.three :: et, owners =>
      coversState limit (depth + 1) parity (.push1 bs) et
          (owners.child .push) &&
        match bs, depth with
        | .empty, _ => true
        | _, 0 => true
        | .push0 bs', depth' + 1 =>
            coversState limit depth' (!parity) bs' et (owners.child .pop1)
        | .push1 bs', depth' + 1 =>
            coversState limit depth' parity bs' et (owners.child .pop0)

theorem completionAccepts_of_balanced_complete_nil
    {depth : Nat} {parity : Bool}
    (hbalanced : Chromogram.balanced depth parity
      (Chromogram.complete depth parity []) = true) :
    completionAccepts depth parity = true := by
  cases depth with
  | zero =>
      cases parity <;>
        simp [completionAccepts, Chromogram.complete,
          Chromogram.balanced] at hbalanced ⊢
  | succ depth =>
      cases depth with
      | zero => simp [completionAccepts]
      | succ depth =>
          cases parity <;>
            simp [completionAccepts, Chromogram.complete,
              Chromogram.balanced] at hbalanced

theorem coversState_get
    {limit : Nat} :
    ∀ {depth : Nat} {parity : Bool} {bs : Chromogram.BitStack}
        {et : ColSeq} {owners : OwnerTrie},
      coversState limit depth parity bs et owners = true →
        ∀ {word : Chromogram},
          Chromogram.balanced depth parity
            (Chromogram.complete depth parity word) = true →
          GTree.matchOpen bs et word = true →
            ∃ ref, ref < limit ∧ owners.get word = some ref := by
  intro depth parity bs et
  induction et generalizing depth parity bs with
  | nil =>
      intro owners hcovered word hbalanced hmatch
      cases word with
      | cons symbol word => simp [GTree.matchOpen] at hmatch
      | nil =>
          have haccept := completionAccepts_of_balanced_complete_nil hbalanced
          simp only [coversState, haccept, if_true] at hcovered
          exact rootBelow_get hcovered
  | cons color et ih =>
      intro owners hcovered word hbalanced hmatch
      cases color with
      | zero => cases word <;> simp [GTree.matchOpen] at hmatch
      | one =>
          cases word with
          | nil => simp [GTree.matchOpen] at hmatch
          | cons symbol word =>
              cases symbol with
              | skip =>
                  simp only [coversState] at hcovered
                  simpa only [child_get] using ih hcovered
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced] using
                        hbalanced)
                    hmatch
              | push | pop0 | pop1 => simp [GTree.matchOpen] at hmatch
      | two =>
          simp only [coversState, Bool.and_eq_true] at hcovered
          cases word with
          | nil => simp [GTree.matchOpen] at hmatch
          | cons symbol word =>
              cases symbol with
              | skip => simp [GTree.matchOpen] at hmatch
              | push =>
                  simpa only [child_get] using ih hcovered.1
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced] using
                        hbalanced)
                    hmatch
              | pop0 =>
                  cases bs with
                  | empty => simp [GTree.matchOpen] at hmatch
                  | push0 bs' =>
                      cases depth with
                      | zero =>
                          simp [Chromogram.complete, Chromogram.balanced] at hbalanced
                      | succ depth =>
                          simpa only [child_get] using ih hcovered.2
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced] using
                                hbalanced)
                            hmatch
                  | push1 bs' => simp [GTree.matchOpen] at hmatch
              | pop1 =>
                  cases bs with
                  | empty => simp [GTree.matchOpen] at hmatch
                  | push0 bs' => simp [GTree.matchOpen] at hmatch
                  | push1 bs' =>
                      cases depth with
                      | zero =>
                          simp [Chromogram.complete, Chromogram.balanced] at hbalanced
                      | succ depth =>
                          simpa only [child_get] using ih hcovered.2
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced] using
                                hbalanced)
                            hmatch
      | three =>
          simp only [coversState, Bool.and_eq_true] at hcovered
          cases word with
          | nil => simp [GTree.matchOpen] at hmatch
          | cons symbol word =>
              cases symbol with
              | skip => simp [GTree.matchOpen] at hmatch
              | push =>
                  simpa only [child_get] using ih hcovered.1
                    (by
                      simpa [Chromogram.complete, Chromogram.balanced] using
                        hbalanced)
                    hmatch
              | pop0 =>
                  cases bs with
                  | empty => simp [GTree.matchOpen] at hmatch
                  | push0 bs' => simp [GTree.matchOpen] at hmatch
                  | push1 bs' =>
                      cases depth with
                      | zero =>
                          simp [Chromogram.complete, Chromogram.balanced] at hbalanced
                      | succ depth =>
                          simpa only [child_get] using ih hcovered.2
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced] using
                                hbalanced)
                            hmatch
              | pop1 =>
                  cases bs with
                  | empty => simp [GTree.matchOpen] at hmatch
                  | push0 bs' =>
                      cases depth with
                      | zero =>
                          simp [Chromogram.complete, Chromogram.balanced] at hbalanced
                      | succ depth =>
                          simpa only [child_get] using ih hcovered.2
                            (by
                              simpa [Chromogram.complete, Chromogram.balanced] using
                                hbalanced)
                            hmatch
                  | push1 bs' => simp [GTree.matchOpen] at hmatch

/-- Check precisely the `initSpec` open matches of a fixed-height trace. -/
def coversOpen (h limit : Nat) (et : ColSeq) (owners : OwnerTrie) : Bool :=
  if decide (et.length = h) then
    coversState limit 0 false .empty et owners
  else
    true

theorem coversOpen_get
    {h limit : Nat} {et : ColSeq} {owners : OwnerTrie}
    (hcovered : coversOpen h limit et owners = true)
    {word : Chromogram} (hspec : GTree.initSpec h word = true)
    (hmatch : GTree.matchOpen .empty et word = true) :
    ∃ ref, ref < limit ∧ owners.get word = some ref := by
  have hlength : et.length = h := by
    rw [← GTree.matchOpen_length hmatch]
    exact GTree.initSpec_length_of_true hspec
  have hstate : coversState limit 0 false .empty et owners = true := by
    simpa [coversOpen, hlength] using hcovered
  exact coversState_get hstate
    (GTree.initSpec_balanced_of_true hspec) hmatch

end OwnerTrie

/-- Every owner stored below a reversed prefix names a source trace matching
the corresponding complete chromogram. -/
def OwnerSoundPrefix
    (h : Nat) (source : SourceTable) : List GramSymbol → OwnerTrie → Prop
  | _, .empty => True
  | reversePrefix, .node owner push skip pop0 pop1 =>
      (∀ ref, owner = some ref → ∃ code,
        source ref = some code ∧
          GTree.matchOpen Chromogram.BitStack.empty (decodeTrace h code)
            reversePrefix.reverse = true) ∧
      OwnerSoundPrefix h source (GramSymbol.push :: reversePrefix) push ∧
      OwnerSoundPrefix h source (GramSymbol.skip :: reversePrefix) skip ∧
      OwnerSoundPrefix h source (GramSymbol.pop0 :: reversePrefix) pop0 ∧
      OwnerSoundPrefix h source (GramSymbol.pop1 :: reversePrefix) pop1

def OwnerSound (h : Nat) (source : SourceTable) (owners : OwnerTrie) : Prop :=
  OwnerSoundPrefix h source [] owners

theorem OwnerSoundPrefix.empty
    {h : Nat} {source : SourceTable} {reversePrefix : List GramSymbol} :
    OwnerSoundPrefix h source reversePrefix .empty := by
  trivial

def verifyOwner
    (h : Nat) (source : SourceTable) (reversePrefix : List GramSymbol) :
    Option Nat → Bool
  | none => true
  | some ref =>
      match source ref with
      | none => false
      | some code =>
          GTree.matchOpen Chromogram.BitStack.empty (decodeTrace h code)
            reversePrefix.reverse

def verifyOwnerTrie
    (h : Nat) (source : SourceTable) : List GramSymbol → OwnerTrie → Bool
  | _, .empty => true
  | reversePrefix, .node owner push skip pop0 pop1 =>
      verifyOwner h source reversePrefix owner &&
        (verifyOwnerTrie h source (GramSymbol.push :: reversePrefix) push &&
          (verifyOwnerTrie h source (GramSymbol.skip :: reversePrefix) skip &&
            (verifyOwnerTrie h source (GramSymbol.pop0 :: reversePrefix) pop0 &&
              verifyOwnerTrie h source
                (GramSymbol.pop1 :: reversePrefix) pop1)))

theorem verifyOwner_sound
    {h : Nat} {source : SourceTable} {reversePrefix : List GramSymbol}
    {owner : Option Nat}
    (hverify : verifyOwner h source reversePrefix owner = true) :
    ∀ ref, owner = some ref → ∃ code,
      source ref = some code ∧
        GTree.matchOpen Chromogram.BitStack.empty (decodeTrace h code)
          reversePrefix.reverse = true := by
  intro ref howner
  cases owner with
  | none => contradiction
  | some actual =>
      injection howner with heq
      subst actual
      unfold verifyOwner at hverify
      cases hsource : source ref with
      | none => simp [hsource] at hverify
      | some code =>
          simp only [hsource] at hverify
          exact ⟨code, rfl, hverify⟩

theorem verifyOwnerTrie_sound
    {h : Nat} {source : SourceTable}
    {reversePrefix : List GramSymbol} {owners : OwnerTrie}
    (hverify : verifyOwnerTrie h source reversePrefix owners = true) :
    OwnerSoundPrefix h source reversePrefix owners := by
  induction owners generalizing reversePrefix with
  | empty => trivial
  | node owner push skip pop0 pop1 ihPush ihSkip ihPop0 ihPop1 =>
      simp only [verifyOwnerTrie, Bool.and_eq_true] at hverify
      exact ⟨verifyOwner_sound hverify.1,
        ihPush hverify.2.1,
        ihSkip hverify.2.2.1,
        ihPop0 hverify.2.2.2.1,
        ihPop1 hverify.2.2.2.2⟩

theorem OwnerSoundPrefix.node_none
    {h : Nat} {source : SourceTable} {reversePrefix : List GramSymbol}
    {push skip pop0 pop1 : OwnerTrie}
    (hpush : OwnerSoundPrefix h source
      (GramSymbol.push :: reversePrefix) push)
    (hskip : OwnerSoundPrefix h source
      (GramSymbol.skip :: reversePrefix) skip)
    (hpop0 : OwnerSoundPrefix h source
      (GramSymbol.pop0 :: reversePrefix) pop0)
    (hpop1 : OwnerSoundPrefix h source
      (GramSymbol.pop1 :: reversePrefix) pop1) :
    OwnerSoundPrefix h source reversePrefix
      (.node none push skip pop0 pop1) := by
  exact ⟨by intro ref h; contradiction, hpush, hskip, hpop0, hpop1⟩

theorem OwnerSoundPrefix.get
    {h : Nat} {source : SourceTable} {reversePrefix : List GramSymbol}
    {owners : OwnerTrie}
    (hsound : OwnerSoundPrefix h source reversePrefix owners)
    {word : Chromogram} {ref : Nat}
    (hget : owners.get word = some ref) :
    ∃ code, source ref = some code ∧
      GTree.matchOpen Chromogram.BitStack.empty (decodeTrace h code)
        (reversePrefix.reverse ++ word) = true := by
  induction owners generalizing reversePrefix word with
  | empty => simp [OwnerTrie.get] at hget
  | node owner push skip pop0 pop1 ihPush ihSkip ihPop0 ihPop1 =>
      cases word with
      | nil =>
          rcases hsound.1 ref hget with ⟨code, hsource, hmatch⟩
          exact ⟨code, hsource, by simpa using hmatch⟩
      | cons symbol word =>
          cases symbol with
          | push =>
              simpa [List.reverse_cons, List.append_assoc] using
                ihPush hsound.2.1 hget
          | skip =>
              simpa [List.reverse_cons, List.append_assoc] using
                ihSkip hsound.2.2.1 hget
          | pop0 =>
              simpa [List.reverse_cons, List.append_assoc] using
                ihPop0 hsound.2.2.2.1 hget
          | pop1 =>
              simpa [List.reverse_cons, List.append_assoc] using
                ihPop1 hsound.2.2.2.2 hget

theorem OwnerSound.get
    {h : Nat} {source : SourceTable} {owners : OwnerTrie}
    (hsound : OwnerSound h source owners)
    {word : Chromogram} {ref : Nat}
    (hget : owners.get word = some ref) :
    ∃ code, source ref = some code ∧
      GTree.matchOpen Chromogram.BitStack.empty (decodeTrace h code)
        word = true := by
  simpa [OwnerSound] using OwnerSoundPrefix.get hsound hget

/-- A derived trace and colour permutation; chromogram owners are shared
globally instead of repeated as selectors in every entry. -/
structure OwnerEntry where
  packed : Nat
  deriving DecidableEq, Repr

namespace OwnerEntry

def entry (ownerEntry : OwnerEntry) : Entry :=
  ⟨ownerEntry.packed / 6, ownerEntry.packed % 6⟩

def coveredBy
    (h : Nat) (owners : OwnerTrie)
    (limit : Nat) (et : ColSeq) : Bool :=
  OwnerTrie.coversOpen h limit et owners

theorem coveredBy_sourceMatches
    {h : Nat} {source : SourceTable} {owners : OwnerTrie}
    {limit : Nat} {et : ColSeq}
    (howners : OwnerSound h source owners)
    (hcovered : coveredBy h owners limit et = true) :
    SourceMatches h source limit et := by
  intro word hspec hmatch
  rcases OwnerTrie.coversOpen_get hcovered hspec hmatch with
    ⟨ref, href, hget⟩
  rcases howners.get hget with ⟨code, hsource, hsourceMatch⟩
  exact ⟨ref, code, href, hsource, hsourceMatch⟩

def accepted
    (h : Nat) (source : SourceTable) (owners : OwnerTrie)
    (limit : Nat) (ownerEntry : OwnerEntry) : Bool :=
  match source limit with
  | none => false
  | some code =>
      decide (code = ownerEntry.entry.traceCode) &&
        coveredBy h owners limit
          (ColSeq.perm ownerEntry.entry.perm (ownerEntry.entry.trace h))

theorem accepted_source
    {h : Nat} {source : SourceTable} {owners : OwnerTrie}
    {limit : Nat} {ownerEntry : OwnerEntry}
    (haccept : ownerEntry.accepted h source owners limit = true) :
    source limit = some ownerEntry.entry.traceCode := by
  unfold accepted at haccept
  cases hsource : source limit with
  | none => simp [hsource] at haccept
  | some code =>
      simp only [hsource, Bool.and_eq_true, decide_eq_true_eq] at haccept
      exact congrArg some haccept.1

theorem accepted_coclosure
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {owners : OwnerTrie}
    {limit : Nat} {ownerEntry : OwnerEntry}
    (howners : OwnerSound h source owners)
    (hsound : SourceSound h P source limit)
    (haccept : ownerEntry.accepted h source owners limit = true) :
    Chromogram.KempeCoclosure P
      (ColSeq.ctrace (ownerEntry.entry.trace h)) := by
  unfold accepted at haccept
  cases hsource : source limit with
  | none => simp [hsource] at haccept
  | some code =>
      simp only [hsource, Bool.and_eq_true, decide_eq_true_eq] at haccept
      exact kempeCoclosure_of_sourceMatches_perm hsound
        (length_decodeTrace h ownerEntry.entry.traceCode)
        ownerEntry.entry.perm
        (coveredBy_sourceMatches howners haccept.2)

end OwnerEntry

def replayOwners
    (h : Nat) (source : SourceTable) (owners : OwnerTrie) :
    List OwnerEntry → Nat → Option Nat
  | [], limit => some limit
  | entry :: entries, limit =>
      if entry.accepted h source owners limit then
        replayOwners h source owners entries (limit + 1)
      else
        none

theorem replayOwners_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {owners : OwnerTrie}
    (howners : OwnerSound h source owners)
    {entries : List OwnerEntry} {start finish : Nat}
    (hsound : SourceSound h P source start)
    (hreplay : replayOwners h source owners entries start = some finish) :
    SourceSound h P source finish := by
  induction entries generalizing start with
  | nil =>
      simp [replayOwners] at hreplay
      subst finish
      exact hsound
  | cons entry entries ih =>
      unfold replayOwners at hreplay
      cases haccept : entry.accepted h source owners start with
      | false => simp [haccept] at hreplay
      | true =>
          rw [haccept] at hreplay
          exact ih
            (hsound.succ (entry.accepted_source haccept)
              (entry.accepted_coclosure howners hsound haccept))
            hreplay

def verifyOwnerEntries
    (h : Nat) (source : SourceTable) (owners : OwnerTrie)
    (start finish : Nat) (entries : List OwnerEntry) : Bool :=
  match replayOwners h source owners entries start with
  | none => false
  | some actual => decide (actual = finish)

theorem verifyOwnerEntries_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {owners : OwnerTrie}
    (howners : OwnerSound h source owners)
    {start finish : Nat} {entries : List OwnerEntry}
    (hsound : SourceSound h P source start)
    (hverify : verifyOwnerEntries h source owners
      start finish entries = true) :
    SourceSound h P source finish := by
  unfold verifyOwnerEntries at hverify
  cases hreplay : replayOwners h source owners entries start with
  | none => simp [hreplay] at hverify
  | some actual =>
      simp only [hreplay, decide_eq_true_eq] at hverify
      subst actual
      exact replayOwners_sound howners hsound hreplay

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
