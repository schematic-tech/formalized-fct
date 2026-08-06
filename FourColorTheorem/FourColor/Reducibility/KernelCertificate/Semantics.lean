import FourColorTheorem.FourColor.Coloring.KempeTree

/-!
A compact semantic certificate for Kempe co-closure.

The executable Kempe-tree construction materializes large intermediate trees.
For certificate checking we only need its logical progress rule: a trace is
Kempe-coclosed when every partial chromogram matching it also matches an
already coclosed trace.  The definitions below package that rule around a
small finite trie of previously certified traces.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace KernelCertificate

/-- A finite set of colour traces.  Unlike `CTree`, this stores no leaf
multiplicities and permits terminals at arbitrary depths. -/
inductive TraceTrie
  | empty
  | node (terminal : Bool)
      (zero one two three : TraceTrie)
  deriving DecidableEq, Repr

namespace TraceTrie

/-- Membership in a finite trace trie. -/
def mem : TraceTrie → ColSeq → Bool
  | empty, _ => false
  | node terminal _ _ _ _, [] => terminal
  | node _ zero _ _ _, Color.zero :: et => zero.mem et
  | node _ _ one _ _, Color.one :: et => one.mem et
  | node _ _ _ two _, Color.two :: et => two.mem et
  | node _ _ _ _ three, Color.three :: et => three.mem et

/-- Insert one trace into a trie. -/
def insert : ColSeq → TraceTrie → TraceTrie
  | [], empty => node true empty empty empty empty
  | [], node _ zero one two three => node true zero one two three
  | Color.zero :: et, empty =>
      node false (insert et empty) empty empty empty
  | Color.zero :: et, node terminal zero one two three =>
      node terminal (insert et zero) one two three
  | Color.one :: et, empty =>
      node false empty (insert et empty) empty empty
  | Color.one :: et, node terminal zero one two three =>
      node terminal zero (insert et one) two three
  | Color.two :: et, empty =>
      node false empty empty (insert et empty) empty
  | Color.two :: et, node terminal zero one two three =>
      node terminal zero one (insert et two) three
  | Color.three :: et, empty =>
      node false empty empty empty (insert et empty)
  | Color.three :: et, node terminal zero one two three =>
      node terminal zero one two (insert et three)

@[simp]
theorem mem_empty (et : ColSeq) :
    TraceTrie.empty.mem et = false := rfl

theorem mem_insert (trie : TraceTrie) (et et' : ColSeq) :
    (trie.insert et).mem et' = (decide (et' = et) || trie.mem et') := by
  induction et generalizing trie et' with
  | nil =>
      cases trie <;> cases et' with
      | nil => simp [insert, mem]
      | cons e et' => cases e <;> simp [insert, mem]
  | cons e et ih =>
      cases trie <;> cases et' with
      | nil =>
          cases e <;> simp [insert, mem]
      | cons e' et' =>
          cases e <;> cases e' <;>
            simp [insert, mem, ih]

theorem mem_insert_self (trie : TraceTrie) (et : ColSeq) :
    (trie.insert et).mem et = true := by
  simp [mem_insert]

theorem mem_of_mem_insert
    {trie : TraceTrie} {et et' : ColSeq}
    (hmem : (trie.insert et).mem et' = true) :
    et' = et ∨ trie.mem et' = true := by
  simpa [mem_insert] using hmem

/-- Forget multiplicities in a colouring tree. -/
def ofCTree : CTree → TraceTrie
  | .empty => empty
  | .leaf _ => node true empty empty empty empty
  | .node t1 t2 t3 =>
      node false empty (ofCTree t1) (ofCTree t2) (ofCTree t3)

theorem mem_ofCTree :
    ∀ (t : CTree) (et : ColSeq),
      (ofCTree t).mem et = CTree.mem t et
  | .empty, et => by simp [ofCTree]
  | .leaf lf, et => by
      cases et with
      | nil => simp [ofCTree, mem, CTree.mem, CTree.sub]
      | cons e et => cases e <;> simp [ofCTree, mem, CTree.mem, CTree.sub]
  | .node t1 t2 t3, et => by
      cases et with
      | nil => simp [ofCTree, mem, CTree.mem, CTree.sub]
      | cons e et =>
          cases e <;>
            simp [ofCTree, mem, CTree.mem, CTree.sub,
              mem_ofCTree]

end TraceTrie

/-- Enumerate exactly the partial chromograms matched by a trace and an open
parity stack. -/
def matchingOpen : Chromogram.BitStack → ColSeq → List Chromogram
  | _, [] => [[]]
  | _, Color.zero :: _ => []
  | bs, Color.one :: et =>
      (matchingOpen bs et).map (GramSymbol.skip :: .)
  | bs, Color.two :: et =>
      (matchingOpen (Chromogram.BitStack.push0 bs) et).map
          (GramSymbol.push :: .) ++
        match bs with
        | .empty => []
        | .push0 bs' =>
            (matchingOpen bs' et).map (GramSymbol.pop0 :: .)
        | .push1 bs' =>
            (matchingOpen bs' et).map (GramSymbol.pop1 :: .)
  | bs, Color.three :: et =>
      (matchingOpen (Chromogram.BitStack.push1 bs) et).map
          (GramSymbol.push :: .) ++
        match bs with
        | .empty => []
        | .push0 bs' =>
            (matchingOpen bs' et).map (GramSymbol.pop1 :: .)
        | .push1 bs' =>
            (matchingOpen bs' et).map (GramSymbol.pop0 :: .)

theorem mem_matchingOpen_iff :
    ∀ (bs : Chromogram.BitStack) (et : ColSeq) (w : Chromogram),
      w ∈ matchingOpen bs et ↔
        GTree.matchOpen bs et w = true
  | bs, [], w => by
      cases w <;> simp [matchingOpen, GTree.matchOpen]
  | bs, Color.zero :: et, w => by
      cases w <;> simp [matchingOpen, GTree.matchOpen]
  | bs, Color.one :: et, w => by
      cases w with
      | nil => simp [matchingOpen, GTree.matchOpen]
      | cons s w =>
          cases s <;>
            simp [matchingOpen, GTree.matchOpen,
              mem_matchingOpen_iff]
  | bs, Color.two :: et, w => by
      cases w with
      | nil => cases bs <;> simp [matchingOpen, GTree.matchOpen]
      | cons s w =>
          cases bs <;> cases s <;>
            simp [matchingOpen, GTree.matchOpen,
              mem_matchingOpen_iff]
  | bs, Color.three :: et, w => by
      cases w with
      | nil => cases bs <;> simp [matchingOpen, GTree.matchOpen]
      | cons s w =>
          cases bs <;> cases s <;>
            simp [matchingOpen, GTree.matchOpen,
              mem_matchingOpen_iff]

/-- Every initial partial chromogram matching `et` also matches a trace in
`known`.  This is the local progress condition checked by a certificate
entry. -/
def covered (h : Nat) (known : TraceTrie) (et : ColSeq) : Bool :=
  (matchingOpen Chromogram.BitStack.empty et).all fun w =>
    !GTree.initSpec h w ||
      GTree.hasMatch Chromogram.BitStack.empty known.mem w

theorem covered_hasMatch
    {h : Nat} {known : TraceTrie} {et : ColSeq}
    (hcovered : covered h known et = true)
    {w : Chromogram}
    (hspec : GTree.initSpec h w = true)
    (hmatch : GTree.matchOpen Chromogram.BitStack.empty et w = true) :
    GTree.hasMatch Chromogram.BitStack.empty known.mem w = true := by
  have hw : w ∈ matchingOpen Chromogram.BitStack.empty et :=
    (mem_matchingOpen_iff _ _ _).2 hmatch
  have hall := List.all_eq_true.mp hcovered w hw
  simp [hspec] at hall
  exact hall

/-- The semantic progress rule behind compact certificate replay. -/
theorem kempeCoclosure_of_covered
    {h : Nat} {P : ColSeq → Prop} {known : TraceTrie} {et : ColSeq}
    (hknown : ∀ et', known.mem et' = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et'))
    (hlen : et.length = h)
    (hcovered : covered h known et = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  intro P' hclosed hP'et
  rcases KempeTree.kempeClosed_openPrefix_initSpec_of_ctrace_perm
      (h := h) hclosed hP'et hlen EdgePerm.p123 with
    ⟨wFull, hmatchFull, hmatchOpen, hspec, hforall⟩
  have hmatchOpen' :
      GTree.matchOpen Chromogram.BitStack.empty et wFull.dropLast = true := by
    simpa [ColSeq.perm_id] using hmatchOpen
  have hhas := covered_hasMatch hcovered hspec hmatchOpen'
  rcases (GTree.hasMatch_eq_true_iff
      Chromogram.BitStack.empty known.mem wFull.dropLast).1 hhas with
    ⟨et', hmem, hmatchOpen'⟩
  have hmatchFull' :
      Chromogram.matchg [] (ColSeq.ctrace et') wFull = true := by
    have hcomplete := Chromogram.matchg_complete_of_ctrace hmatchFull
    rw [← hcomplete]
    exact GTree.matchg_ctrace_complete_of_matchOpen_initSpec
      hspec hmatchOpen'
  exact hknown et' hmem P' hclosed
    (hforall (ColSeq.ctrace et') hmatchFull')

/-- The same progress rule after a non-zero colour permutation. -/
theorem kempeCoclosure_of_covered_perm
    {h : Nat} {P : ColSeq → Prop} {known : TraceTrie} {et : ColSeq}
    (hknown : ∀ et', known.mem et' = true →
      Chromogram.KempeCoclosure P (ColSeq.ctrace et'))
    (hlen : et.length = h) (g : EdgePerm)
    (hcovered : covered h known (ColSeq.perm g et) = true) :
    Chromogram.KempeCoclosure P (ColSeq.ctrace et) := by
  have hlenPerm : (ColSeq.perm g et).length = h := by
    simpa [ColSeq.length_perm] using hlen
  have hclose := kempeCoclosure_of_covered hknown hlenPerm hcovered
  have hback := Chromogram.KempeCoclosure.perm hclose (EdgePerm.inv g)
  simpa [ColSeq.perm_ctrace, ColSeq.perm_inv] using hback

end KernelCertificate

end FourColor

end Schematic.Math.GraphTheory
