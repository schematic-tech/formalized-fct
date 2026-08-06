import FourColorTheorem.FourColor.Coloring.Birkhoff.CertificateTrace

/-! Soundness of executable Birkhoff ring certificates. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- The recursive core of Coq `Birkhoff_valid`, after the two elementary ring
geometry facts (`nontrivial_ring_proper` and `nontrivial_rev_ring`) have been
supplied. -/
theorem check_excludes_nontrivial_ring_of_reverse
    {G : Hypermap.{u}} {r : List G.Dart} {h m niter : Nat}
    {cps : List CProg}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1) (hnt : G.NontrivialRing m r)
    (hshort : ∀ r' : List G.Dart,
      G.SimpleRLinkCycle r' → r'.length ≤ h →
        ¬ G.NontrivialRing 0 r')
    (hpos : 0 < h) (hproper : G.ProperRing r)
    (hntRev : G.NontrivialRing m (G.RevRing r))
    (hcheck : check h m niter cps = true) :
    False := by
  let rr : List G.Dart := G.RevRing r
  let hrRev : G.SimpleRLinkCycle rr :=
    Hypermap.SimpleRLinkCycle.revRing_of_plain (G := G) hG.plain hr
  have hrrlen : rr.length = h + 1 := by
    simpa [rr] using hrlen
  have hproperRev : G.ProperRing rr := by
    exact (Hypermap.properRing_revRing_iff_of_plain
      (G := G) hG.plain r).2 hproper
  let Q1 : ColSeq → Prop := fun cet =>
    (G.snipDisk r hG.planar hr).RingTrace
      (Hypermap.snipdRing hG.planar hr) cet
  let Q2 : ColSeq → Prop := fun cet =>
    (Hypermap.revSnipDisk G r hG.planar hG.plain hr).RingTrace
      (Hypermap.revSnipdRing hG.planar hG.plain hr) cet
  let checkBasis : CTree → Bool := fun ctu =>
    (cps.map CProg.cpColor).any (CTree.disjoint ctu)
  have hvalid1 : KempeTree.Valid (h - 1) (fun cet => ¬ Q1 cet)
      (KempeTree.initialCTree (h - 1)) CTree.empty GTree.empty
      (KempeTree.initialGTree (h - 1)) :=
    KempeTree.initial_valid (h - 1) (fun cet => ¬ Q1 cet)
  have hvalid2 : KempeTree.Valid (h - 1) (fun cet => ¬ Q2 cet)
      (KempeTree.initialCTree (h - 1)) CTree.empty GTree.empty
      (KempeTree.initialGTree (h - 1)) :=
    KempeTree.initial_valid (h - 1) (fun cet => ¬ Q2 cet)
  have hclosed1 : Chromogram.KempeClosed Q1 := by
    simpa [Q1] using Hypermap.ring_disk_closed hG.planar hconnected
      hG.plain hcubic hr hproper
  have hclosed2 : Chromogram.KempeClosed Q2 := by
    simpa [Q2, rr, hrRev, Hypermap.revSnipDisk,
      Hypermap.revSnipdRing] using
      Hypermap.ring_disk_closed hG.planar hconnected hG.plain hcubic
        hrRev hproperRev
  have hnormalize1 : ∀ et : ColSeq,
      Q1 (ColSeq.ctrace (ColSeq.etrace et)) →
        Q1 (ColSeq.ctrace et) := by
    intro et htrace
    exact ringTrace_ctrace_of_etrace htrace
  have hnormalize2 : ∀ et : ColSeq,
      Q2 (ColSeq.ctrace (ColSeq.etrace et)) →
        Q2 (ColSeq.ctrace et) := by
    intro et htrace
    exact ringTrace_ctrace_of_etrace htrace
  have hbasis1 : ∀ {ctu : CTree} {gtu : GTree},
      KempeTree.Valid (h - 1) (fun cet => ¬ Q1 cet)
          ctu CTree.empty GTree.empty gtu →
        checkBasis ctu = true → False := by
    intro ctu gtu hvalid hbasis
    rcases check_basis_witness hcheck (by simpa [checkBasis] using hbasis) with
      ⟨cp, _hcpMem, hcpCheck, hdisjoint⟩
    exact basisTree_trace_contradiction hG hconnected hcubic hr hrlen hnt
      hshort hpos hcpCheck (by simpa [Q1] using hvalid) hclosed1 hdisjoint
  have hbasis2 : ∀ {ctu : CTree} {gtu : GTree},
      KempeTree.Valid (h - 1) (fun cet => ¬ Q2 cet)
          ctu CTree.empty GTree.empty gtu →
        checkBasis ctu = true → False := by
    intro ctu gtu hvalid hbasis
    rcases check_basis_witness hcheck (by simpa [checkBasis] using hbasis) with
      ⟨cp, _hcpMem, hcpCheck, hdisjoint⟩
    exact basisTree_trace_contradiction hG hconnected hcubic hrRev hrrlen
      (by simpa [rr] using hntRev) hshort hpos hcpCheck
      (by simpa [Q2, rr, hrRev, Hypermap.revSnipDisk,
        Hypermap.revSnipdRing] using hvalid) hclosed2 hdisjoint
  have hglue : ∀ cet : ColSeq, Q1 cet → Q2 cet.reverse → False := by
    intro cet htrace1 htrace2
    apply hG.false_of_fourColorable
    exact Hypermap.colorable_from_ring hG.planar hconnected hG.plain hr
      hproper cet (by simpa [Q1] using htrace1)
      (by simpa [Q2] using htrace2)
  have hcheck2 := (check_spec hcheck).2
  exact check2_valid_glue hpos hvalid1 hvalid2 hnormalize1 hnormalize2
    hbasis1 hbasis2 hglue (by simpa [checkBasis] using hcheck2)

/-- Coq `Birkhoff_valid`: every successful executable certificate excludes a
nontrivial ring of its certified length and order. -/
theorem check_excludes_nontrivial_ring
    {G : Hypermap.{u}} {r : List G.Dart} {h m niter : Nat}
    {cps : List CProg}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (hr : G.SimpleRLinkCycle r)
    (hrlen : r.length = h + 1)
    (hshort : ∀ r' : List G.Dart,
      G.SimpleRLinkCycle r' → r'.length ≤ h →
        ¬ G.NontrivialRing 0 r')
    (hpos : 0 < h)
    (hcheck : check h m niter cps = true) :
    ¬ G.NontrivialRing m r := by
  intro hnt
  have hproper := Hypermap.nontrivial_ring_proper hG.planar hconnected
    hG.bridgeless hG.plain hr hnt
  have hntRev := Hypermap.nontrivial_rev_ring hG.planar hconnected
    hG.bridgeless hG.plain hr hnt
  exact check_excludes_nontrivial_ring_of_reverse hG hconnected hcubic hr
    hrlen hnt hshort hpos hproper hntRev hcheck

set_option linter.dupNamespace false in
/-- Coq `Birkhoff`: rings of length at most five in a minimal counterexample
cannot have the certified number of face orbits on both sides.  Lengths below
five exclude order zero; length five excludes order one. -/
theorem Birkhoff
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (r : List G.Dart)
    (hlen : r.length ≤ 5) (hr : G.SimpleRLinkCycle r) :
    ¬ G.NontrivialRing (if r.length = 5 then 1 else 0) r := by
  let P : Nat → Prop := fun n =>
    ∀ r : List G.Dart, r.length = n → r.length ≤ 5 →
      G.SimpleRLinkCycle r →
        ¬ G.NontrivialRing (if r.length = 5 then 1 else 0) r
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro r hrlen hn5 hr hnt
        have hproper := Hypermap.nontrivial_ring_proper hG.planar hconnected
          hG.bridgeless hG.plain hr hnt
        have htwo : 2 ≤ r.length := by
          cases r with
          | nil => simp [Hypermap.ProperRing] at hproper
          | cons x xs =>
              cases xs with
              | nil => simp [Hypermap.ProperRing, Hypermap.EdgePath] at hproper
              | cons y ys => simp
        have hshortCurrent : ∀ r' : List G.Dart,
            G.SimpleRLinkCycle r' → r'.length < n →
              ¬ G.NontrivialRing 0 r' := by
          intro r' hr' hlt hnt'
          have hlen5 : r'.length ≤ 5 := by omega
          have hne5 : r'.length ≠ 5 := by omega
          have hnot := ih r'.length hlt r' rfl hlen5 hr'
          have hnot0 : ¬ G.NontrivialRing 0 r' := by
            simpa [P, hne5] using hnot
          exact hnot0 hnt'
        have hnCases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
          omega
        rcases hnCases with rfl | rfl | rfl | rfl
        · exact (check_excludes_nontrivial_ring hG hconnected hcubic hr
            (by omega)
            (fun r' hr' hle => hshortCurrent r' hr' (by omega))
            (by omega) check2_cert) (by simpa [hrlen] using hnt)
        · exact (check_excludes_nontrivial_ring hG hconnected hcubic hr
            (by omega)
            (fun r' hr' hle => hshortCurrent r' hr' (by omega))
            (by omega) check3_cert) (by simpa [hrlen] using hnt)
        · exact (check_excludes_nontrivial_ring hG hconnected hcubic hr
            (by omega)
            (fun r' hr' hle => hshortCurrent r' hr' (by omega))
            (by omega) check4_cert) (by simpa [hrlen] using hnt)
        · exact (check_excludes_nontrivial_ring hG hconnected hcubic hr
            (by omega)
            (fun r' hr' hle => hshortCurrent r' hr' (by omega))
            (by omega) check5_cert) (by simpa [hrlen] using hnt)
  exact hP r.length r rfl hlen hr


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
