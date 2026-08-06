import FourColorTheorem.FourColor.Coloring.KempeTree
import FourColorTheorem.FourColor.Reducibility.ProgramMap

/-!
Executable Birkhoff ring checks.

This is a direct port of the computational section of Gonthier's
`birkhoff.v`: `cpcard`, `ctree_pick_rev`, the symmetric recursive
Kempe-closure check, and the four bases used for rings of lengths two through
five.  Semantic soundness is proved in the Birkhoff layer built on
`Patch`/`Snip`/`Sew`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

open PointedHypermap

namespace Birkhoff

/-- Number of darts in the hypermap represented by a construction program.
This is Coq `cpcard`. -/
def cpCard : CProg → Nat
  | [] => 2
  | CpStep.rotate _ :: cp => cpCard cp
  | CpStep.reverseRotate :: cp => cpCard cp
  | CpStep.a :: cp => cpCard cp
  | CpStep.u :: cp => cpCard cp + 2
  | CpStep.k :: cp => cpCard cp + 2
  | CpStep.y :: cp => cpCard cp + 4
  | CpStep.h :: cp => cpCard cp + 6

/-- Cardinality of the two-dart extension, phrased with intrinsic cardinality
so it is independent of the `Fintype` instance stored in a hypermap. -/
theorem natCard_extDart (α : Type) [Finite α] :
    Nat.card (ExtDart α) = Nat.card α + 2 := by
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ExtDart.card

/-- Intrinsic-cardinality form of Coq `card_cpmap`. -/
theorem natCard_cpmap (cp : CProg) :
    Nat.card (cpmap cp).map.Dart = cpCard cp := by
  induction cp with
  | nil =>
      simp only [cpmap_nil, base_map, cpCard]
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_bool
  | cons s cp ih =>
      cases s with
      | rotate n =>
          simpa only [cpmap_cons, step_rotate, rotate_map, cpCard] using ih
      | reverseRotate =>
          simpa only [cpmap_cons, step_reverseRotate, reverseRotate_map,
            cpCard] using ih
      | u =>
          simpa only [cpmap_cons, step_u, u_map, Hypermap.extensionU, cpCard,
            ih] using natCard_extDart (cpmap cp).map.Dart
      | k =>
          simpa only [cpmap_cons, step_k, k_map, Hypermap.extensionN, cpCard,
            ih] using natCard_extDart (cpmap cp).map.Dart
      | y =>
          simp only [cpmap_cons, step_y, y_map, Hypermap.extensionY,
            Hypermap.extensionN, Hypermap.extensionU, cpCard]
          calc
            Nat.card (ExtDart (ExtDart (cpmap cp).map.Dart)) =
                Nat.card (ExtDart (cpmap cp).map.Dart) + 2 :=
              natCard_extDart _
            _ = (Nat.card (cpmap cp).map.Dart + 2) + 2 := by
              rw [natCard_extDart]
            _ = cpCard cp + 4 := by omega
      | h =>
          simp only [cpmap_cons, step_h, h_map, Hypermap.extensionH,
            Hypermap.extensionY, Hypermap.extensionN, Hypermap.extensionU,
            cpCard]
          calc
            Nat.card (ExtDart (ExtDart (ExtDart (cpmap cp).map.Dart))) =
                Nat.card (ExtDart (ExtDart (cpmap cp).map.Dart)) + 2 :=
              natCard_extDart _
            _ = (Nat.card (ExtDart (cpmap cp).map.Dart) + 2) + 2 := by
              rw [natCard_extDart]
            _ = ((Nat.card (cpmap cp).map.Dart + 2) + 2) + 2 := by
              rw [natCard_extDart]
            _ = cpCard cp + 6 := by omega
      | a =>
          simpa only [cpmap_cons, step_a, a_map, Hypermap.extensionA,
            cpCard] using ih

/-- Coq `card_cpmap`: `cpCard` is the exact dart cardinality of the semantic
construction map. -/
theorem card_cpmap (cp : CProg) :
    Fintype.card (cpmap cp).map.Dart = cpCard cp := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_cpmap cp

/-- Coq `Birkhoff_check1`: one small cubic basis program has the required
ring size and dart bound. -/
def checkBasisProgram (h m : Nat) (cp : CProg) : Bool :=
  CProg.cubic cp &&
    decide (cpCard cp + 1 < 6 * m + 4 * h) &&
      decide (CProg.ringSize cp = h + 1)

/-- Semantic package extracted from one successful Coq `Birkhoff_check1`. -/
theorem checkBasisProgram_spec
    {h m : Nat} {cp : CProg}
    (hcheck : checkBasisProgram h m cp = true) :
    CProg.cubic cp = true ∧
      Fintype.card (cpmap cp).map.Dart + 1 < 6 * m + 4 * h ∧
        (cpRing cp).length = h + 1 := by
  have hraw :
      (CProg.cubic cp = true ∧
        cpCard cp + 1 < 6 * m + 4 * h) ∧
          CProg.ringSize cp = h + 1 := by
    simpa [checkBasisProgram] using hcheck
  refine ⟨hraw.1.1, ?_, ?_⟩
  · simpa [card_cpmap] using hraw.1.2
  · simpa [length_cpRing] using hraw.2

/-- Structural recursion underlying Coq `ctree_pick_rev_rec`. -/
def pickReverseRec
    (et : ColSeq) (e : Color) (t' : CTree) : CTree → ColSeq
  | CTree.leaf _ =>
      if CTree.mem t' (ColSeq.etrace (ColSeq.prevs e et)) then
        e :: et
      else
        []
  | CTree.node t1 t2 t3 =>
      match pickReverseRec (Color.one :: et) (e + Color.one) t' t1 with
      | e' :: et' => e' :: et'
      | [] =>
          match pickReverseRec (Color.two :: et) (e + Color.two) t' t2 with
          | e' :: et' => e' :: et'
          | [] =>
              pickReverseRec (Color.three :: et) (e + Color.three) t' t3
  | CTree.empty => []

/-- Pick a complete trace represented by `t` whose reversed even trace is
represented by `t'`. -/
def pickReverse (t' t : CTree) : ColSeq :=
  pickReverseRec [] Color.zero t' t

/-- Accumulator invariant behind Coq `sumt_ctree_pick_rev`: every successful
search path preserves the xor of its leading colour and accumulated suffix. -/
theorem sum_pickReverseRec
    (et : ColSeq) (e : Color) (t' t : CTree)
    (hsum : e + ColSeq.sum et = Color.zero) :
    ColSeq.sum (pickReverseRec et e t' t) = Color.zero := by
  induction t generalizing et e with
  | empty =>
      rfl
  | leaf lf ih =>
      by_cases hmem : CTree.mem t' (ColSeq.etrace (ColSeq.prevs e et))
      · simpa [pickReverseRec, hmem] using hsum
      · simp [pickReverseRec, hmem]
  | node t1 t2 t3 ih1 ih2 ih3 =>
      have hsum1 :
          (e + Color.one) + ColSeq.sum (Color.one :: et) = Color.zero := by
        simpa [Color.add_assoc] using hsum
      have hsum2 :
          (e + Color.two) + ColSeq.sum (Color.two :: et) = Color.zero := by
        simpa [Color.add_assoc] using hsum
      have hsum3 :
          (e + Color.three) + ColSeq.sum (Color.three :: et) = Color.zero := by
        simpa [Color.add_assoc] using hsum
      cases h1 : pickReverseRec (Color.one :: et) (e + Color.one) t' t1 with
      | cons e1 et1 =>
          simpa only [pickReverseRec, h1] using
            ih1 (Color.one :: et) (e + Color.one) hsum1
      | nil =>
          cases h2 : pickReverseRec (Color.two :: et) (e + Color.two) t' t2 with
          | cons e2 et2 =>
              simpa only [pickReverseRec, h1, h2] using
                ih2 (Color.two :: et) (e + Color.two) hsum2
          | nil =>
              simpa only [pickReverseRec, h1, h2] using
                ih3 (Color.three :: et) (e + Color.three) hsum3

/-- Generalized accumulator invariant behind Coq `size_ctree_pick_rev`.
Starting at height `h` with an accumulator whose length completes it to `H`,
a successful search returns exactly `H + 1` colours. -/
theorem length_pickReverseRec
    {h H : Nat} (et : ColSeq) (e : Color) (t' t : CTree)
    (hlen : et.length + h = H) (hproper : CTree.Proper h t) :
    (pickReverseRec et e t' t).length = 0 ∨
      (pickReverseRec et e t' t).length = H + 1 := by
  induction h generalizing et e t with
  | zero =>
      cases t with
      | empty => simp [pickReverseRec]
      | node t1 t2 t3 => simp [CTree.Proper] at hproper
      | leaf lf =>
          by_cases hmem : CTree.mem t' (ColSeq.etrace (ColSeq.prevs e et))
          · right
            simp only [pickReverseRec, hmem, if_true, List.length_cons]
            omega
          · left
            simp [pickReverseRec, hmem]
  | succ h ih =>
      cases t with
      | empty => simp [pickReverseRec]
      | leaf lf => simp [CTree.Proper] at hproper
      | node t1 t2 t3 =>
          rcases hproper with ⟨hnode, ht1, ht2, ht3⟩
          have hlen1 : (Color.one :: et).length + h = H := by
            simp only [List.length_cons]
            omega
          have hlen2 : (Color.two :: et).length + h = H := by
            simp only [List.length_cons]
            omega
          have hlen3 : (Color.three :: et).length + h = H := by
            simp only [List.length_cons]
            omega
          cases h1 : pickReverseRec (Color.one :: et) (e + Color.one) t' t1 with
          | cons e1 et1 =>
              simpa only [pickReverseRec, h1] using
                ih (Color.one :: et) (e + Color.one) t1 hlen1 ht1
          | nil =>
              cases h2 : pickReverseRec (Color.two :: et) (e + Color.two) t' t2 with
              | cons e2 et2 =>
                  simpa only [pickReverseRec, h1, h2] using
                    ih (Color.two :: et) (e + Color.two) t2 hlen2 ht2
              | nil =>
                  simpa only [pickReverseRec, h1, h2] using
                    ih (Color.three :: et) (e + Color.three) t3 hlen3 ht3

/-- Coq `sumt_ctree_pick_rev`. -/
theorem sum_pickReverse (t' t : CTree) :
    ColSeq.sum (pickReverse t' t) = Color.zero := by
  exact sum_pickReverseRec [] Color.zero t' t (by simp)

/-- Coq `size_ctree_pick_rev`. -/
theorem length_pickReverse {h : Nat} (t' : CTree) {t : CTree}
    (hproper : CTree.Proper h t) :
    (pickReverse t' t).length = 0 ∨
      (pickReverse t' t).length = h + 1 := by
  exact length_pickReverseRec [] Color.zero t' t (by simp) hproper

/-- One side of Coq `Birkhoff_check2`. -/
def doCheck2
    (h : Nat) (checkBasis : CTree → Bool)
    (et : ColSeq) (ctu : CTree) (gtu : GTree)
    (next : CTree → GTree → Bool) : Bool :=
  let ctr := CTree.ofTtail (ColSeq.etrace et)
  if Color.zero ∈ et then
    false
  else
    let kr := KempeTree.closure (h - 1) h ctu ctr gtu
    GTree.isEmpty kr.gtp.left &&
      (checkBasis kr.ctu || next kr.ctu kr.gtp.right)

/-- A successful one-sided Birkhoff check has passed all three executable
guards: the proposed trace contains no zero colour, closure has discharged
its left chromogram tree, and either a basis tree or the continuation
succeeds.  This is the Boolean decomposition used at lines 303--319 and
322--340 of Coq `birkhoff.v`. -/
theorem doCheck2_spec
    {h : Nat} {checkBasis : CTree → Bool}
    {et : ColSeq} {ctu : CTree} {gtu : GTree}
    {next : CTree → GTree → Bool}
    (hcheck : doCheck2 h checkBasis et ctu gtu next = true) :
    Color.zero ∉ et ∧
      GTree.isEmpty
          (KempeTree.closure (h - 1) h ctu
            (CTree.ofTtail (ColSeq.etrace et)) gtu).gtp.left = true ∧
        (checkBasis
              (KempeTree.closure (h - 1) h ctu
                (CTree.ofTtail (ColSeq.etrace et)) gtu).ctu = true ∨
          next
              (KempeTree.closure (h - 1) h ctu
                (CTree.ofTtail (ColSeq.etrace et)) gtu).ctu
              (KempeTree.closure (h - 1) h ctu
                (CTree.ofTtail (ColSeq.etrace et)) gtu).gtp.right = true) := by
  by_cases hzero : Color.zero ∈ et
  · simp [doCheck2, hzero] at hcheck
  · simpa [doCheck2, hzero, Bool.and_eq_true, Bool.or_eq_true] using
      And.intro hzero hcheck

/-- Semantic preservation through one side of Coq `Birkhoff_check2`.

The caller supplies the map-specific fact that the selected trace belongs to
the coclosure predicate.  The singleton `ctr` is then a valid restriction;
`Kempe_tree_closure_correct` supplies the new state, and the successful
`gtree_empty` guard turns its discharged side into the literal empty tree. -/
theorem doCheck2_valid
    {h : Nat} {P : ColSeq → Prop} {checkBasis : CTree → Bool}
    {et : ColSeq} {ctu : CTree} {gtu : GTree}
    {next : CTree → GTree → Bool}
    (hvalid :
      KempeTree.Valid (h - 1) P ctu CTree.empty GTree.empty gtu)
    (htrace :
      P (ColSeq.ctrace (ColSeq.etrace et)) ∧
        (ColSeq.etrace et).length = (h - 1) + 1)
    (hcheck : doCheck2 h checkBasis et ctu gtu next = true) :
    KempeTree.Valid (h - 1) P
        (KempeTree.closure (h - 1) h ctu
          (CTree.ofTtail (ColSeq.etrace et)) gtu).ctu
        CTree.empty GTree.empty
        (KempeTree.closure (h - 1) h ctu
          (CTree.ofTtail (ColSeq.etrace et)) gtu).gtp.right ∧
      (checkBasis
            (KempeTree.closure (h - 1) h ctu
              (CTree.ofTtail (ColSeq.etrace et)) gtu).ctu = true ∨
        next
            (KempeTree.closure (h - 1) h ctu
              (CTree.ofTtail (ColSeq.etrace et)) gtu).ctu
            (KempeTree.closure (h - 1) h ctu
              (CTree.ofTtail (ColSeq.etrace et)) gtu).gtp.right = true) := by
  have hspec := doCheck2_spec hcheck
  have hrestricted :
      KempeTree.Valid (h - 1) P ctu
        (CTree.ofTtail (ColSeq.etrace et)) GTree.empty gtu :=
    KempeTree.valid_with_ctr_of_mem
      (fun et' hmem => by
        have het' :=
          (CTree.mem_ofTtail_iff_total (ColSeq.etrace et) et').1 hmem
        rw [het'.2]
        exact htrace)
      hvalid
  have hclosed :=
    (KempeTree.closure_correct (h - 1) h hrestricted).1
  have hleft :
      (KempeTree.closure (h - 1) h ctu
        (CTree.ofTtail (ColSeq.etrace et)) gtu).gtp.left = GTree.empty :=
    GTree.isEmpty_eq hspec.2.1
  rw [hleft] at hclosed
  exact ⟨hclosed, hspec.2.2⟩

/-- Coq `Birkhoff_check2`: remove a common reversed trace on either side and
recurse symmetrically. -/
def check2
    (h : Nat) (checkBasis : CTree → Bool) :
    CTree → GTree → Nat → CTree → GTree → Bool
  | _, _, 0, _, _ => false
  | ctu1, gtu1, n + 1, ctu2, gtu2 =>
      match pickReverse ctu1 ctu2 with
      | [] => false
      | e :: et =>
          doCheck2 h checkBasis (ColSeq.prevs e et) ctu1 gtu1
              (check2 h checkBasis ctu2 gtu2 n) &&
            doCheck2 h checkBasis et.reverse ctu2 gtu2
              (check2 h checkBasis ctu1 gtu1 n)

@[simp]
theorem check2_zero
    (h : Nat) (checkBasis : CTree → Bool)
    (ctu1 : CTree) (gtu1 : GTree) (ctu2 : CTree) (gtu2 : GTree) :
    check2 h checkBasis ctu1 gtu1 0 ctu2 gtu2 = false :=
  rfl

/-- Exact successor decomposition of the symmetric bounded recursion.  It is
the Lean form of the two `case`/`andP` eliminations at Coq `birkhoff.v`
lines 288--300. -/
theorem check2_succ_iff
    (h : Nat) (checkBasis : CTree → Bool)
    (ctu1 : CTree) (gtu1 : GTree) (n : Nat)
    (ctu2 : CTree) (gtu2 : GTree) :
    check2 h checkBasis ctu1 gtu1 (n + 1) ctu2 gtu2 = true ↔
      ∃ e : Color, ∃ et : ColSeq,
        pickReverse ctu1 ctu2 = e :: et ∧
          doCheck2 h checkBasis (ColSeq.prevs e et) ctu1 gtu1
              (check2 h checkBasis ctu2 gtu2 n) = true ∧
            doCheck2 h checkBasis et.reverse ctu2 gtu2
              (check2 h checkBasis ctu1 gtu1 n) = true := by
  cases hpick : pickReverse ctu1 ctu2 with
  | nil => simp [check2, hpick]
  | cons e et =>
      simp only [check2, hpick, Bool.and_eq_true]
      constructor
      · rintro ⟨hleft, hright⟩
        exact ⟨e, et, rfl, hleft, hright⟩
      · rintro ⟨e', et', heq, hleft, hright⟩
        cases List.cons.inj heq with
        | intro he het =>
            subst e'
            subst et'
            exact ⟨hleft, hright⟩

/-- Semantic output of one side of the symmetric checker. -/
def SideSemantics
    (h : Nat) (P : ColSeq → Prop) (checkBasis : CTree → Bool)
    (et : ColSeq) (ctu : CTree) (gtu : GTree)
    (next : CTree → GTree → Bool) : Prop :=
  let kr := KempeTree.closure (h - 1) h ctu
    (CTree.ofTtail (ColSeq.etrace et)) gtu
  KempeTree.Valid (h - 1) P kr.ctu CTree.empty GTree.empty kr.gtp.right ∧
    (checkBasis kr.ctu = true ∨ next kr.ctu kr.gtp.right = true)

/-- Two-sided semantic successor rule for `check2`.

The only map-dependent inputs are the two selected-trace admissibility facts.
Everything else, including preservation of both `KempeTree.Valid` states and
the orientation swap in the recursive continuations, follows from the checked
program and `closure_correct`.  Reapplying this theorem to either continuation
is the bounded recursion used in Coq `Birkhoff_valid`. -/
theorem check2_succ_valid
    {h : Nat} {checkBasis : CTree → Bool}
    {P1 P2 : ColSeq → Prop}
    {ctu1 : CTree} {gtu1 : GTree} {n : Nat}
    {ctu2 : CTree} {gtu2 : GTree}
    (hvalid1 :
      KempeTree.Valid (h - 1) P1 ctu1 CTree.empty GTree.empty gtu1)
    (hvalid2 :
      KempeTree.Valid (h - 1) P2 ctu2 CTree.empty GTree.empty gtu2)
    (htrace1 :
      ∀ e et, pickReverse ctu1 ctu2 = e :: et →
        Color.zero ∉ ColSeq.prevs e et →
          P1 (ColSeq.ctrace (ColSeq.etrace (ColSeq.prevs e et))) ∧
            (ColSeq.etrace (ColSeq.prevs e et)).length = (h - 1) + 1)
    (htrace2 :
      ∀ e et, pickReverse ctu1 ctu2 = e :: et →
        Color.zero ∉ et.reverse →
          P2 (ColSeq.ctrace (ColSeq.etrace et.reverse)) ∧
            (ColSeq.etrace et.reverse).length = (h - 1) + 1)
    (hcheck :
      check2 h checkBasis ctu1 gtu1 (n + 1) ctu2 gtu2 = true) :
    ∃ e : Color, ∃ et : ColSeq,
      pickReverse ctu1 ctu2 = e :: et ∧
        SideSemantics h P1 checkBasis (ColSeq.prevs e et) ctu1 gtu1
          (check2 h checkBasis ctu2 gtu2 n) ∧
        SideSemantics h P2 checkBasis et.reverse ctu2 gtu2
          (check2 h checkBasis ctu1 gtu1 n) := by
  rcases (check2_succ_iff h checkBasis ctu1 gtu1 n ctu2 gtu2).1 hcheck with
    ⟨e, et, hpick, hleft, hright⟩
  have hleftSpec := doCheck2_spec hleft
  have hrightSpec := doCheck2_spec hright
  refine ⟨e, et, hpick, ?_, ?_⟩
  · unfold SideSemantics
    exact doCheck2_valid hvalid1
      (htrace1 e et hpick hleftSpec.1) hleft
  · unfold SideSemantics
    exact doCheck2_valid hvalid2
      (htrace2 e et hpick hrightSpec.1) hright

/-- Semantic soundness of the complete symmetric recursion in Coq
`Birkhoff_valid`.

The two predicates describe colorable boundary traces on the current left and
right disks.  A failed trace is fed through Kempe closure; a successful basis
branch is contradictory, while a continuation either keeps the orientation or
swaps the two states.  If both selected traces exist, `hglue` finishes the
ambient goal. -/
theorem check2_valid_glue
    {h niter : Nat} {checkBasis : CTree → Bool}
    {Q1 Q2 : ColSeq → Prop} {R : Prop}
    {ctu1 ctu2 : CTree} {gtu1 gtu2 : GTree}
    (hpos : 0 < h)
    (hvalid1 : KempeTree.Valid (h - 1) (fun cet => ¬ Q1 cet)
      ctu1 CTree.empty GTree.empty gtu1)
    (hvalid2 : KempeTree.Valid (h - 1) (fun cet => ¬ Q2 cet)
      ctu2 CTree.empty GTree.empty gtu2)
    (hnormalize1 : ∀ et : ColSeq,
      Q1 (ColSeq.ctrace (ColSeq.etrace et)) → Q1 (ColSeq.ctrace et))
    (hnormalize2 : ∀ et : ColSeq,
      Q2 (ColSeq.ctrace (ColSeq.etrace et)) → Q2 (ColSeq.ctrace et))
    (hbasis1 : ∀ {ctu : CTree} {gtu : GTree},
      KempeTree.Valid (h - 1) (fun cet => ¬ Q1 cet)
          ctu CTree.empty GTree.empty gtu →
        checkBasis ctu = true → False)
    (hbasis2 : ∀ {ctu : CTree} {gtu : GTree},
      KempeTree.Valid (h - 1) (fun cet => ¬ Q2 cet)
          ctu CTree.empty GTree.empty gtu →
        checkBasis ctu = true → False)
    (hglue : ∀ cet : ColSeq, Q1 cet → Q2 cet.reverse → R)
    (hcheck : check2 h checkBasis ctu1 gtu1 niter ctu2 gtu2 = true) :
    R := by
  induction niter generalizing Q1 Q2 ctu1 gtu1 ctu2 gtu2 with
  | zero =>
      simp at hcheck
  | succ n ih =>
      rcases (check2_succ_iff h checkBasis ctu1 gtu1 n ctu2 gtu2).1
          hcheck with
        ⟨e, et, hpick, hleft, hright⟩
      have hsum : ColSeq.sum (e :: et) = Color.zero := by
        rw [← hpick]
        exact sum_pickReverse ctu1 ctu2
      have hpickLen := length_pickReverse ctu1
        (KempeTree.Valid.ctu_proper hvalid2)
      rw [hpick] at hpickLen
      have hfullLen : (e :: et).length = h + 1 := by
        rcases hpickLen with hzero | hlen
        · simp at hzero
        · omega
      have hetLen : et.length = h := by
        simp only [List.length_cons] at hfullLen
        omega
      have hleftLen :
          (ColSeq.etrace (ColSeq.prevs e et)).length = (h - 1) + 1 := by
        rw [ColSeq.length_etrace, ColSeq.length_prevs]
        omega
      have hrightLen :
          (ColSeq.etrace et.reverse).length = (h - 1) + 1 := by
        rw [ColSeq.length_etrace, List.length_reverse]
        omega
      by_cases hq1 : Q1 (e :: et)
      · by_cases hq2 : Q2 (e :: et).reverse
        · exact hglue (e :: et) hq1 hq2
        · have hnot2 :
              ¬ Q2 (ColSeq.ctrace (ColSeq.etrace et.reverse)) := by
            intro htrace
            apply hq2
            have htrace' := hnormalize2 et.reverse htrace
            rwa [ColSeq.ctrace_reverse_tail_eq_of_sum_zero hsum] at htrace'
          rcases doCheck2_valid hvalid2 ⟨hnot2, hrightLen⟩ hright with
            ⟨hvalid2', hbasis | hnext⟩
          · exact False.elim (hbasis2 hvalid2' hbasis)
          · exact ih hvalid1 hvalid2' hnormalize1 hnormalize2
              hbasis1 hbasis2 hglue hnext
      · have hnot1 :
            ¬ Q1
              (ColSeq.ctrace
                (ColSeq.etrace (ColSeq.prevs e et))) := by
          intro htrace
          apply hq1
          have htrace' := hnormalize1 (ColSeq.prevs e et) htrace
          rwa [ColSeq.ctrace_prevs_eq_of_sum_zero hsum] at htrace'
        rcases doCheck2_valid hvalid1 ⟨hnot1, hleftLen⟩ hleft with
          ⟨hvalid1', hbasis | hnext⟩
        · exact False.elim (hbasis1 hvalid1' hbasis)
        · have hglueSwap :
              ∀ cet : ColSeq, Q2 cet → Q1 cet.reverse → R := by
            intro cet hq2 hq1rev
            apply hglue cet.reverse hq1rev
            simpa using hq2
          exact ih hvalid2 hvalid1' hnormalize2 hnormalize1
            hbasis2 hbasis1 hglueSwap hnext

/-- Full executable form of Coq's inductive `Birkhoff_check` witness. -/
def check (h m niter : Nat) (cps : List CProg) : Bool :=
  let ctu := KempeTree.initialCTree (h - 1)
  let gtu := KempeTree.initialGTree (h - 1)
  let basis := cps.map CProg.cpColor
  let checkBasis := fun t => basis.any (CTree.disjoint t)
  cps.all (checkBasisProgram h m) &&
    check2 h checkBasis ctu gtu niter ctu gtu

theorem check_spec
    {h m niter : Nat} {cps : List CProg}
    (hcheck : check h m niter cps = true) :
    (∀ cp : CProg, cp ∈ cps → checkBasisProgram h m cp = true) ∧
      check2 h
        (fun t => (cps.map CProg.cpColor).any (CTree.disjoint t))
        (KempeTree.initialCTree (h - 1))
        (KempeTree.initialGTree (h - 1)) niter
        (KempeTree.initialCTree (h - 1))
        (KempeTree.initialGTree (h - 1)) = true := by
  have hraw :
      cps.all (checkBasisProgram h m) = true ∧
        check2 h
          (fun t => (cps.map CProg.cpColor).any (CTree.disjoint t))
          (KempeTree.initialCTree (h - 1))
          (KempeTree.initialGTree (h - 1)) niter
          (KempeTree.initialCTree (h - 1))
          (KempeTree.initialGTree (h - 1)) = true := by
    simpa [check, Bool.and_eq_true] using hcheck
  exact ⟨List.all_eq_true.mp hraw.1, hraw.2⟩

theorem check_basis_witness
    {h m niter : Nat} {cps : List CProg}
    (hcheck : check h m niter cps = true)
    {ctu : CTree}
    (hbasis :
      (cps.map CProg.cpColor).any (CTree.disjoint ctu) = true) :
    ∃ cp : CProg, cp ∈ cps ∧
      checkBasisProgram h m cp = true ∧
        CTree.disjoint ctu (CProg.cpColor cp) = true := by
  rcases List.any_eq_true.mp hbasis with ⟨ct, hct, hdisjoint⟩
  rcases List.mem_map.mp hct with ⟨cp, hcp, rfl⟩
  exact ⟨cp, hcp, (check_spec hcheck).1 cp hcp, hdisjoint⟩

def basis2 : List CProg :=
  [[]]

def basis3 : List CProg :=
  [[CpStep.y]]

def basis4 : List CProg :=
  [[CpStep.u], [CpStep.rotate 1, CpStep.u]]

def basis5 : List CProg :=
  [ [CpStep.u, CpStep.y],
    [CpStep.rotate 1, CpStep.u, CpStep.y],
    [CpStep.rotate 2, CpStep.u, CpStep.y],
    [CpStep.rotate 3, CpStep.u, CpStep.y],
    [CpStep.rotate 4, CpStep.u, CpStep.y],
    [CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y] ]

private theorem check_small_basis_cert :
    check 1 0 1 basis2 = true ∧
      check 2 0 1 basis3 = true ∧
        check 3 0 4 basis4 = true ∧
          check 4 1 10 basis5 = true := by
  fct_decide

theorem check2_cert : check 1 0 1 basis2 = true :=
  check_small_basis_cert.1

theorem check3_cert : check 2 0 1 basis3 = true :=
  check_small_basis_cert.2.1

theorem check4_cert : check 3 0 4 basis4 = true :=
  check_small_basis_cert.2.2.1

theorem check5_cert : check 4 1 10 basis5 = true :=
  check_small_basis_cert.2.2.2

end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
