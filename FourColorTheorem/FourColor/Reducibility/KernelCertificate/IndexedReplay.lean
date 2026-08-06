import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Checker

/-!
Kernel replay using immutable, indexed trace sources.

The source table is a generated balanced tree.  A certificate entry may use
only indices below its own position, so checking availability needs neither a
transient closure nor a dynamically rebuilt trace trie.
-/

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

/-- A balanced, immutable table used for constant-depth source lookup. -/
inductive NatTree
  | empty
  | leaf (value : Nat)
  | node (leftSize : Nat) (left right : NatTree)
  deriving DecidableEq, Repr

namespace NatTree

def get : NatTree → Nat → Option Nat
  | .empty, _ => none
  | .leaf value, 0 => some value
  | .leaf _, _ + 1 => none
  | .node leftSize left right, index =>
      if index < leftSize then left.get index
      else right.get (index - leftSize)

end NatTree

/-- A sparse trace-indexed table. -/
inductive RefTrie
  | empty
  | node (terminal : Option Nat) (one two three : RefTrie)
  deriving DecidableEq, Repr

namespace RefTrie

def get : RefTrie → ColSeq → Option Nat
  | .empty, _ => none
  | .node terminal _ _ _, [] => terminal
  | .node _ _ _ _, Color.zero :: _ => none
  | .node _ one _ _, Color.one :: et => one.get et
  | .node _ _ two _, Color.two :: et => two.get et
  | .node _ _ _ three, Color.three :: et => three.get et

def subtree : RefTrie → ColSeq → RefTrie
  | trie, [] => trie
  | .node _ one _ _, Color.one :: path => one.subtree path
  | .node _ _ two _, Color.two :: path => two.subtree path
  | .node _ _ _ three, Color.three :: path => three.subtree path
  | _, _ => .empty

end RefTrie

abbrev SourceTable := Nat → Option Nat

/-- Every source below `limit` has the required semantic interpretation. -/
def SourceSound
    (h : Nat) (P : ColSeq → Prop) (source : SourceTable) (limit : Nat) : Prop :=
  ∀ ref code, ref < limit → source ref = some code →
    Chromogram.KempeCoclosure P (ColSeq.ctrace (decodeTrace h code))

theorem sourceSound_zero
    (h : Nat) (P : ColSeq → Prop) (source : SourceTable) :
    SourceSound h P source 0 := by
  intro ref code href
  omega

theorem SourceSound.succ
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {limit code : Nat}
    (hsound : SourceSound h P source limit)
    (hget : source limit = some code)
    (hnew : Chromogram.KempeCoclosure P
      (ColSeq.ctrace (decodeTrace h code))) :
    SourceSound h P source (limit + 1) := by
  intro ref code' href hsource
  by_cases hlt : ref < limit
  · exact hsound ref code' hlt hsource
  · have heq : ref = limit := by omega
    subst ref
    rw [hget] at hsource
    injection hsource with heq
    subst code'
    exact hnew

/-- Check a consecutive source range against a per-code predicate. -/
def verifySourceRange
    (source : SourceTable) (accepted : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
      match source start with
      | none => false
      | some code =>
          accepted code && verifySourceRange source accepted (start + 1) count

theorem verifySourceRange_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {accepted : Nat → Bool} {start count : Nat}
    (haccepted : ∀ code, accepted code = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace (decodeTrace h code)))
    (hsound : SourceSound h P source start)
    (hverify : verifySourceRange source accepted start count = true) :
    SourceSound h P source (start + count) := by
  induction count generalizing start with
  | zero => simpa using hsound
  | succ count ih =>
      unfold verifySourceRange at hverify
      cases hsource : source start with
      | none => simp [hsource] at hverify
      | some code =>
          simp only [hsource, Bool.and_eq_true] at hverify
          have hnext := hsound.succ hsource (haccepted code hverify.1)
          have hresult := ih hnext hverify.2
          have heq : start + (count + 1) = start + 1 + count := by omega
          rw [heq]
          exact hresult

/-- One indexed derivation.  `support` contains source-table references and
`selectors` chooses one support reference for each matching chromogram. -/
structure IndexedEntry where
  packed : Nat
  support : List Nat
  selectors : List Nat
  deriving DecidableEq, Repr

namespace IndexedEntry

def entry (wentry : IndexedEntry) : Entry :=
  ⟨wentry.packed / 6, wentry.packed % 6⟩

end IndexedEntry

/-- Check one earlier source reference per matching chromogram. -/
def selectedIndexed
    (h : Nat) (source : SourceTable) (limit : Nat) (support : List Nat) :
    List Chromogram → List Nat → Bool
  | [], [] => true
  | w :: ws, selector :: selectors =>
      match support[selector]? with
      | none => false
      | some ref =>
          decide (ref < limit) &&
            match source ref with
            | none => false
            | some code =>
                GTree.matchOpen Chromogram.BitStack.empty
                    (decodeTrace h code) w &&
                  selectedIndexed h source limit support ws selectors
  | _, _ => false

theorem selectedIndexed_sound
    {h : Nat} {source : SourceTable} {limit : Nat} {support : List Nat} :
    ∀ {ws : List Chromogram} {selectors : List Nat},
      selectedIndexed h source limit support ws selectors = true →
        ∀ w ∈ ws, ∃ ref code,
          ref < limit ∧ source ref = some code ∧
            GTree.matchOpen Chromogram.BitStack.empty
              (decodeTrace h code) w = true
  | [], selectors, haccept, w, hw => by simp at hw
  | _ :: _, [], haccept, w, hw => by
      simp [selectedIndexed] at haccept
  | w' :: ws, selector :: selectors, haccept, w, hw => by
      unfold selectedIndexed at haccept
      cases hsupport : support[selector]? with
      | none => simp [hsupport] at haccept
      | some ref =>
          simp only [hsupport, Bool.and_eq_true, decide_eq_true_eq] at haccept
          cases hsource : source ref with
          | none => simp [hsource] at haccept
          | some code =>
              simp only [hsource, Bool.and_eq_true] at haccept
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact ⟨ref, code, haccept.1, hsource, haccept.2.1⟩
              · exact selectedIndexed_sound haccept.2.2 w hw

/-- The semantic progress condition expressed directly through indexed
sources. -/
def SourceMatches
    (h : Nat) (source : SourceTable) (limit : Nat) (et : ColSeq) : Prop :=
  ∀ w, GTree.initSpec h w = true →
    GTree.matchOpen Chromogram.BitStack.empty et w = true →
      ∃ ref code, ref < limit ∧ source ref = some code ∧
        GTree.matchOpen Chromogram.BitStack.empty
          (decodeTrace h code) w = true

theorem kempeCoclosure_of_sourceMatches
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {limit : Nat} {et : ColSeq}
    (hsound : SourceSound h P source limit)
    (hlen : et.length = h)
    (hmatches : SourceMatches h source limit et) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro P' hclosed hP'et
  rcases KempeTree.kempeClosed_openPrefix_initSpec_of_ctrace_perm
      (h := h) hclosed hP'et hlen EdgePerm.p123 with
    ⟨wFull, hmatchFull, hmatchOpen, hspec, hforall⟩
  have hmatchOpen' :
      GTree.matchOpen Chromogram.BitStack.empty et wFull.dropLast = true := by
    simpa [ColSeq.perm_id] using hmatchOpen
  rcases hmatches wFull.dropLast hspec hmatchOpen' with
    ⟨ref, code, href, hsource, hsourceMatch⟩
  have hmatchFull' :
      Chromogram.matchg [] (ColSeq.ctrace (decodeTrace h code)) wFull = true := by
    have hcomplete := Chromogram.matchg_complete_of_ctrace hmatchFull
    rw [← hcomplete]
    exact GTree.matchg_ctrace_complete_of_matchOpen_initSpec
      hspec hsourceMatch
  exact hsound ref code href hsource P' hclosed
    (hforall (ColSeq.ctrace (decodeTrace h code)) hmatchFull')

theorem kempeCoclosure_of_sourceMatches_perm
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {limit : Nat} {et : ColSeq}
    (hsound : SourceSound h P source limit)
    (hlen : et.length = h) (g : EdgePerm)
    (hmatches : SourceMatches h source limit (ColSeq.perm g et)) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hlenPerm : (ColSeq.perm g et).length = h := by
    simpa [ColSeq.length_perm] using hlen
  have hclose := kempeCoclosure_of_sourceMatches hsound hlenPerm hmatches
  have hback := Chromogram.KempeCoclosure.perm hclose (EdgePerm.inv g)
  simpa [ColSeq.perm_ctrace, ColSeq.perm_inv] using hback

namespace IndexedEntry

def accepted
    (h : Nat) (source : SourceTable) (limit : Nat)
    (wentry : IndexedEntry) : Bool :=
  match source limit with
  | none => false
  | some code =>
      decide (code = wentry.entry.traceCode) &&
        selectedIndexed h source limit wentry.support
          ((matchingOpen Chromogram.BitStack.empty
              (ColSeq.perm wentry.entry.perm (wentry.entry.trace h))).filter
            (GTree.initSpec h))
          wentry.selectors

theorem accepted_source
    {h : Nat} {source : SourceTable} {limit : Nat} {wentry : IndexedEntry}
    (haccept : wentry.accepted h source limit = true) :
    source limit = some wentry.entry.traceCode := by
  unfold accepted at haccept
  cases hsource : source limit with
  | none => simp [hsource] at haccept
  | some code =>
      simp only [hsource, Bool.and_eq_true, decide_eq_true_eq] at haccept
      exact congrArg some haccept.1

theorem accepted_matches
    {h : Nat} {source : SourceTable} {limit : Nat} {wentry : IndexedEntry}
    (haccept : wentry.accepted h source limit = true) :
    SourceMatches h source limit
      (ColSeq.perm wentry.entry.perm (wentry.entry.trace h)) := by
  unfold accepted at haccept
  cases hsource : source limit with
  | none => simp [hsource] at haccept
  | some code =>
      simp only [hsource, Bool.and_eq_true, decide_eq_true_eq] at haccept
      intro w hspec hmatch
      have hw : w ∈ matchingOpen Chromogram.BitStack.empty
          (ColSeq.perm wentry.entry.perm (wentry.entry.trace h)) :=
        (mem_matchingOpen_iff _ _ _).2 hmatch
      have hwValid : w ∈
          (matchingOpen Chromogram.BitStack.empty
            (ColSeq.perm wentry.entry.perm (wentry.entry.trace h))).filter
              (GTree.initSpec h) := by
        simp [hw, hspec]
      exact selectedIndexed_sound haccept.2 w hwValid

theorem accepted_coclosure
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {limit : Nat} {wentry : IndexedEntry}
    (hsound : SourceSound h P source limit)
    (haccept : wentry.accepted h source limit = true) :
    Chromogram.KempeCoclosure P
      (ColSeq.ctrace (wentry.entry.trace h)) :=
  kempeCoclosure_of_sourceMatches_perm hsound
    (length_decodeTrace h wentry.entry.traceCode) wentry.entry.perm
    (accepted_matches haccept)

end IndexedEntry

/-- Replay a topologically indexed list. -/
def replayIndexed (h : Nat) (source : SourceTable) :
    List IndexedEntry → Nat → Option Nat
  | [], limit => some limit
  | wentry :: entries, limit =>
      if wentry.accepted h source limit then
        replayIndexed h source entries (limit + 1)
      else
        none

/-- Check a typed indexed segment and its exact source-index endpoint. -/
def verifyIndexedEntries
    (h : Nat) (source : SourceTable) (start finish : Nat)
    (entries : List IndexedEntry) : Bool :=
  match replayIndexed h source entries start with
  | none => false
  | some actual => decide (actual = finish)

theorem replayIndexed_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {entries : List IndexedEntry} {start finish : Nat}
    (hsound : SourceSound h P source start)
    (hreplay : replayIndexed h source entries start = some finish) :
    SourceSound h P source finish := by
  induction entries generalizing start with
  | nil =>
      simp [replayIndexed] at hreplay
      subst finish
      exact hsound
  | cons wentry entries ih =>
      unfold replayIndexed at hreplay
      cases haccept : wentry.accepted h source start with
      | false => simp [haccept] at hreplay
      | true =>
          rw [haccept] at hreplay
          exact ih
            (hsound.succ (wentry.accepted_source haccept)
              (wentry.accepted_coclosure hsound haccept))
            hreplay

theorem verifyIndexedEntries_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {start finish : Nat} {entries : List IndexedEntry}
    (hsound : SourceSound h P source start)
    (hverify : verifyIndexedEntries h source start finish entries = true) :
    SourceSound h P source finish := by
  unfold verifyIndexedEntries at hverify
  cases hreplay : replayIndexed h source entries start with
  | none => simp [hreplay] at hverify
  | some actual =>
      simp only [hreplay, decide_eq_true_eq] at hverify
      subst actual
      exact replayIndexed_sound hsound hreplay

/-- Check a consecutive range of source codes against the ordinary colouring
tree. -/
def verifyBaseRange
    (h : Nat) (source : SourceTable) (base : CTree) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
      match source start with
      | none => false
      | some code =>
          CTree.mem base (decodeTrace h code) &&
            verifyBaseRange h source base (start + 1) count

theorem verifyBaseRange_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {base : CTree}
    {start count : Nat}
    (hbase : ∀ et, CTree.mem base et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hsound : SourceSound h P source start)
    (hverify : verifyBaseRange h source base start count = true) :
    SourceSound h P source (start + count) := by
  induction count generalizing start with
  | zero => simpa using hsound
  | succ count ih =>
      unfold verifyBaseRange at hverify
      cases hsource : source start with
      | none => simp [hsource] at hverify
      | some code =>
          simp only [hsource, Bool.and_eq_true] at hverify
          have hnext := hsound.succ hsource
            (hbase (decodeTrace h code) hverify.1)
          have hresult := ih hnext hverify.2
          have heq : start + (count + 1) = start + 1 + count := by omega
          rw [heq]
          exact hresult

/-- Select the branch below a trace prefix. -/
def baseSubtree : CTree → ColSeq → CTree
  | tree, [] => tree
  | .node one _ _, Color.one :: path => baseSubtree one path
  | .node _ two _, Color.two :: path => baseSubtree two path
  | .node _ _ three, Color.three :: path => baseSubtree three path
  | _, _ => .empty

@[simp]
theorem mem_baseSubtree (tree : CTree) (path et : ColSeq) :
    CTree.mem (baseSubtree tree path) et = CTree.mem tree (path ++ et) := by
  induction path generalizing tree with
  | nil => simp [baseSubtree]
  | cons color path ih =>
      cases tree with
      | empty => cases color <;> simp [baseSubtree, CTree.mem, CTree.sub]
      | leaf leaf => cases color <;> simp [baseSubtree, CTree.mem, CTree.sub]
      | node one two three =>
          cases color with
          | zero => simp [baseSubtree, CTree.mem, CTree.sub]
          | one =>
              simpa only [baseSubtree, List.cons_append, CTree.mem, CTree.sub]
                using ih one
          | two =>
              simpa only [baseSubtree, List.cons_append, CTree.mem, CTree.sub]
                using ih two
          | three =>
              simpa only [baseSubtree, List.cons_append, CTree.mem, CTree.sub]
                using ih three

/-- Traverse an ordinary colouring tree once, checking that consecutive
source-table entries are exactly its represented traces. -/
def verifyBaseTree
    (h : Nat) (source : SourceTable) : CTree → ColSeq → Nat → Option Nat
  | .empty, _, start => some start
  | .leaf _, path, start =>
      match source start with
      | none => none
      | some code =>
          if decodeTrace h code = path then some (start + 1) else none
  | .node one two three, path, start =>
      match verifyBaseTree h source one (path ++ [Color.one]) start with
      | none => none
      | some afterOne =>
          match verifyBaseTree h source two (path ++ [Color.two]) afterOne with
          | none => none
          | some afterTwo =>
              verifyBaseTree h source three
                (path ++ [Color.three]) afterTwo

theorem verifyBaseTree_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {tree : CTree} {path : ColSeq} {start finish : Nat}
    (htree : ∀ et, CTree.mem tree et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace (path ++ et)))
    (hsound : SourceSound h P source start)
    (hverify : verifyBaseTree h source tree path start = some finish) :
    SourceSound h P source finish := by
  induction tree generalizing path start finish with
  | empty =>
      simp [verifyBaseTree] at hverify
      subst finish
      exact hsound
  | leaf multiplicity =>
      unfold verifyBaseTree at hverify
      cases hsource : source start with
      | none => simp [hsource] at hverify
      | some code =>
          simp only [hsource] at hverify
          split at hverify
          next heq =>
            injection hverify with hfinish
            subst finish
            apply hsound.succ hsource
            rw [heq]
            simpa using htree [] (by simp [CTree.mem, CTree.sub])
          next => simp at hverify
  | node one two three ihOne ihTwo ihThree =>
      unfold verifyBaseTree at hverify
      cases hone : verifyBaseTree h source one
          (path ++ [Color.one]) start with
      | none => simp [hone] at hverify
      | some afterOne =>
          simp only [hone] at hverify
          cases htwo : verifyBaseTree h source two
              (path ++ [Color.two]) afterOne with
          | none => simp [htwo] at hverify
          | some afterTwo =>
              simp only [htwo] at hverify
              have htreeOne : ∀ et, CTree.mem one et = true →
                  Chromogram.KempeCoclosure P
                    (ColSeq.ctrace ((path ++ [Color.one]) ++ et)) := by
                intro et hmem
                have hparent := htree (Color.one :: et)
                  (by simpa [CTree.mem, CTree.sub] using hmem)
                simpa [List.append_assoc] using hparent
              have htreeTwo : ∀ et, CTree.mem two et = true →
                  Chromogram.KempeCoclosure P
                    (ColSeq.ctrace ((path ++ [Color.two]) ++ et)) := by
                intro et hmem
                have hparent := htree (Color.two :: et)
                  (by simpa [CTree.mem, CTree.sub] using hmem)
                simpa [List.append_assoc] using hparent
              have htreeThree : ∀ et, CTree.mem three et = true →
                  Chromogram.KempeCoclosure P
                    (ColSeq.ctrace ((path ++ [Color.three]) ++ et)) := by
                intro et hmem
                have hparent := htree (Color.three :: et)
                  (by simpa [CTree.mem, CTree.sub] using hmem)
                simpa [List.append_assoc] using hparent
              exact ihThree htreeThree
                (ihTwo htreeTwo (ihOne htreeOne hsound hone) htwo) hverify

theorem verifyBaseSubtree_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {base : CTree} {path : ColSeq} {start finish : Nat}
    (hbase : ∀ et, CTree.mem base et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hsound : SourceSound h P source start)
    (hverify : verifyBaseTree h source (baseSubtree base path)
      path start = some finish) :
    SourceSound h P source finish := by
  exact verifyBaseTree_sound
    (fun et hmem => hbase (path ++ et) (by simpa using hmem))
    hsound hverify

def verifyIndexedBase
    (h : Nat) (source : SourceTable) (base : CTree) (finish : Nat) : Bool :=
  match verifyBaseTree h source base [] 0 with
  | none => false
  | some actual => decide (actual = finish)

theorem verifyIndexedBase_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable}
    {base : CTree} {finish : Nat}
    (hbase : ∀ et, CTree.mem base et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et))
    (hverify : verifyIndexedBase h source base finish = true) :
    SourceSound h P source finish := by
  unfold verifyIndexedBase at hverify
  cases htree : verifyBaseTree h source base [] 0 with
  | none => simp [htree] at hverify
  | some actual =>
      simp only [htree, decide_eq_true_eq] at hverify
      subst actual
      exact verifyBaseTree_sound
        (fun et hmem => by simpa using hbase et hmem)
        (sourceSound_zero h P source) htree

/-- Check that every target trace resolves to an available source. -/
def targetKnown
    (h : Nat) (source : SourceTable) (limit : Nat)
    (refs : RefTrie) (et : ColSeq) : Bool :=
  match refs.get et with
  | none => false
  | some ref =>
      decide (ref < limit) &&
        match source ref with
        | none => false
        | some code => decide (decodeTrace h code = et)

theorem targetKnown_coclosure
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {limit : Nat}
    {refs : RefTrie} {et : ColSeq}
    (hsound : SourceSound h P source limit)
    (hknown : targetKnown h source limit refs et = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  unfold targetKnown at hknown
  cases href : refs.get et with
  | none => simp [href] at hknown
  | some ref =>
      simp only [href, Bool.and_eq_true, decide_eq_true_eq] at hknown
      cases hsource : source ref with
      | none => simp [hsource] at hknown
      | some code =>
          simp only [hsource, decide_eq_true_eq] at hknown
          rw [← hknown.2]
          exact hsound ref code hknown.1 hsource

def verifyIndexedTarget
    (h : Nat) (source : SourceTable) (limit : Nat)
    (target : CTree) (refs : RefTrie) : Bool :=
  allTreeMem target (targetKnown h source limit refs)

theorem verifyIndexedTarget_sound
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {limit : Nat}
    {target : CTree} {refs : RefTrie}
    (hsound : SourceSound h P source limit)
    (hverify : verifyIndexedTarget h source limit target refs = true) :
    ∀ et, CTree.mem target et = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro et hmem
  have hknown := allTreeMem_sound target
    (targetKnown h source limit refs) hverify et hmem
  unfold targetKnown at hknown
  cases href : refs.get et with
  | none => simp [href] at hknown
  | some ref =>
      simp only [href, Bool.and_eq_true, decide_eq_true_eq] at hknown
      cases hsource : source ref with
      | none => simp [hsource] at hknown
      | some code =>
          simp only [hsource, decide_eq_true_eq] at hknown
          rw [← hknown.2]
          exact hsound ref code hknown.1 hsource

/-- Check a target suffix against a reference trie indexed below a fixed
trace path. -/
def targetKnownBelow
    (h : Nat) (source : SourceTable) (limit : Nat)
    (path : ColSeq) (refs : RefTrie) (suffix : ColSeq) : Bool :=
  match refs.get suffix with
  | none => false
  | some ref =>
      decide (ref < limit) &&
        match source ref with
        | none => false
        | some code => decide (decodeTrace h code = path ++ suffix)

theorem targetKnownBelow_coclosure
    {h : Nat} {P : ColSeq → Prop} {source : SourceTable} {limit : Nat}
    {path suffix : ColSeq} {refs : RefTrie}
    (hsound : SourceSound h P source limit)
    (hknown : targetKnownBelow h source limit path refs suffix = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace (path ++ suffix)) := by
  unfold targetKnownBelow at hknown
  cases href : refs.get suffix with
  | none => simp [href] at hknown
  | some ref =>
      simp only [href, Bool.and_eq_true, decide_eq_true_eq] at hknown
      cases hsource : source ref with
      | none => simp [hsource] at hknown
      | some code =>
          simp only [hsource, decide_eq_true_eq] at hknown
          rw [← hknown.2]
          exact hsound ref code hknown.1 hsource

/-- Check a Boolean property on every nonzero colour word of a fixed length. -/
def allColorWords : Nat → (ColSeq → Bool) → Bool
  | 0, p => p []
  | n + 1, p =>
      allColorWords n (fun suffix => p (Color.one :: suffix)) &&
        (allColorWords n (fun suffix => p (Color.two :: suffix)) &&
          allColorWords n (fun suffix => p (Color.three :: suffix)))

theorem allColorWords_sound :
    ∀ {n : Nat} {p : ColSeq → Bool},
      allColorWords n p = true →
        ∀ et, et.length = n → Color.zero ∉ et → p et = true
  | 0, p, hall, et, hlength, _ => by
      have het : et = [] := List.eq_nil_of_length_eq_zero hlength
      subst et
      exact hall
  | n + 1, p, hall, et, hlength, hnonzero => by
      simp only [allColorWords, Bool.and_eq_true] at hall
      cases et with
      | nil => simp at hlength
      | cons color et =>
          have htailLength : et.length = n := by
            simp only [List.length_cons] at hlength
            omega
          have hhead : color ≠ Color.zero := by
            intro hzero
            subst color
            exact hnonzero (by simp)
          have htail : Color.zero ∉ et := by
            intro hzero
            exact hnonzero (by simp [hzero])
          cases color with
          | zero => contradiction
          | one => exact allColorWords_sound hall.1 et htailLength htail
          | two => exact allColorWords_sound hall.2.1 et htailLength htail
          | three => exact allColorWords_sound hall.2.2 et htailLength htail

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
