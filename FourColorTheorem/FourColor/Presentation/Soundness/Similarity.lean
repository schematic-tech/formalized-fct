import FourColorTheorem.FourColor.Presentation.Soundness.ForcedParts

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Presentation

noncomputable section

universe u

theorem similarityCheck_eq_true
    {ps p : Part} {j : Nat} {mir : Bool}
    (h : similarityCheck ps p j mir = true) :
    let p1 := if mir then Part.mirror p else p
    let p2 := Part.rotate j p1
    ps.size = p2.size ∧ Part.cmp p2 ps = PartRel.Psubset := by
  dsimp [similarityCheck]
  dsimp [similarityCheck] at h
  rw [Bool.and_eq_true] at h
  constructor
  · exact beq_iff_eq.mp h.1
  · generalize hc :
      Part.cmp (Part.rotate j (if mir then Part.mirror p else p)) ps = c at h
    cases c <;> simp at h ⊢

theorem forcedPart_of_similarityCheck_transformed
    {ps p : Part} {j : Nat} {mir : Bool}
    (h : similarityCheck ps p j mir = true) :
    let p1 := if mir then Part.mirror p else p
    let p2 := Part.rotate j p1
    ForcedPart.{u} p2 ps := by
  dsimp
  intro G x _ hfit
  rcases similarityCheck_eq_true h with ⟨hsize, hcmp⟩
  exact Part.exactFitp_of_cmp_eq_subset_of_size_eq hcmp hsize.symm hfit

theorem forcedPart_of_similarityCheck_zero
    {ps p : Part}
    (h : similarityCheck ps p 0 false = true) :
    ForcedPart.{u} p ps := by
  have hf := forcedPart_of_similarityCheck_transformed h
  dsimp at hf
  simpa using (hf : ForcedPart.{u} (Part.rotate 0 p) ps)

theorem succeedsIn_of_similarityCheck_zero_successful
    {p0 ps p : Part}
    (h : similarityCheck ps p 0 false = true)
    (hps : Successful.{u} ps) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_forced_successful
    (forcedPart_of_similarityCheck_zero h) hps

theorem successful_of_similarityCheck_rotate
    {ps p : Part} {j : Nat}
    (h : similarityCheck ps p j false = true)
    (hps : Successful.{u} ps) :
    Successful.{u} p := by
  intro G x hx
  cases hfit : Part.exactFitp G x p
  · rfl
  · have hforce := forcedPart_of_similarityCheck_transformed h
    dsimp at hforce
    by_cases hle : j ≤ p.size
    · have hxj : ValidHub G ((G.face : G.Dart → G.Dart)^[j] x) :=
        validHub_face_iter (G := G) j hx
      have hrot :
          Part.exactFitp G ((G.face : G.Dart → G.Dart)^[j] x)
            (Part.rotate j p) = true :=
        Part.exactFitp_rotate_of_le (G := G) hle hfit
      have hpsfit :
          Part.exactFitp G ((G.face : G.Dart → G.Dart)^[j] x) ps = true :=
        hforce ((G.face : G.Dart → G.Dart)^[j] x) hxj hrot
      have hfail := hps ((G.face : G.Dart → G.Dart)^[j] x) hxj
      rw [hpsfit] at hfail
      cases hfail
    · have hsizele : p.size ≤ j := le_of_not_ge hle
      have hrot :
          Part.exactFitp G x (Part.rotate j p) = true := by
        simpa [Part.rotate_eq_self_of_size_le j p hsizele] using hfit
      have hpsfit : Part.exactFitp G x ps = true :=
        hforce x hx hrot
      have hfail := hps x hx
      rw [hpsfit] at hfail
      cases hfail

theorem successful_rotate_of_successful
    {p : Part} (n : Nat)
    (hp : Successful.{u} p) :
    Successful.{u} (Part.rotate n p) := by
  intro G x hx
  cases hfit : Part.exactFitp G x (Part.rotate n p)
  · rfl
  · have hx' : ValidHub G
        ((G.face : G.Dart → G.Dart)^[p.size - n] x) :=
      validHub_face_iter (G := G) (p.size - n) hx
    have hback :
        Part.exactFitp G
          ((G.face : G.Dart → G.Dart)^[p.size - n] x)
          (Part.rotate (p.size - n) (Part.rotate n p)) = true :=
      Part.exactFitp_rotate_of_le (G := G)
        (n := p.size - n) (p := Part.rotate n p)
        (by simp) hfit
    have hpfit :
        Part.exactFitp G
          ((G.face : G.Dart → G.Dart)^[p.size - n] x) p = true := by
      simpa [Part.rotate_size_sub_rotate] using hback
    have hfail := hp
      ((G.face : G.Dart → G.Dart)^[p.size - n] x) hx'
    rw [hpfit] at hfail
    cases hfail

theorem successful_of_rotate_successful
    {p : Part} (n : Nat)
    (hrot : Successful.{u} (Part.rotate n p)) :
    Successful.{u} p := by
  intro G x hx
  cases hfit : Part.exactFitp G x p
  · rfl
  · by_cases hle : n ≤ p.size
    · have hx' :
          ValidHub G ((G.face : G.Dart → G.Dart)^[n] x) :=
        validHub_face_iter (G := G) n hx
      have hrotfit :
          Part.exactFitp G ((G.face : G.Dart → G.Dart)^[n] x)
            (Part.rotate n p) = true :=
        Part.exactFitp_rotate_of_le (G := G) hle hfit
      have hfail := hrot
        ((G.face : G.Dart → G.Dart)^[n] x) hx'
      rw [hrotfit] at hfail
      cases hfail
    · have hsizele : p.size ≤ n := le_of_not_ge hle
      have hrotEq : Part.rotate n p = p :=
        Part.rotate_eq_self_of_size_le n p hsizele
      have hfail := hrot x hx
      rw [hrotEq] at hfail
      rw [hfit] at hfail
      cases hfail

theorem successful_rotate_iff
    {p : Part} (n : Nat) :
    Successful.{u} (Part.rotate n p) ↔ Successful.{u} p := by
  constructor
  · exact successful_of_rotate_successful n
  · exact successful_rotate_of_successful n

theorem forcedPart_rotate_of_forcedPart
    {p0 p : Part} (n : Nat)
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u} (Part.rotate n p0) (Part.rotate n p) := by
  intro G x hx hfit
  by_cases hle : n ≤ p0.size
  · have hfit0s := hfit
    simp [Part.exactFitp] at hfit0s
    have hxArity : G.arity x = p0.size := by
      simpa using hfit0s.1
    have hxShift : ValidHub G
        ((G.face : G.Dart → G.Dart)^[p0.size - n] x) :=
      validHub_face_iter (G := G) (p0.size - n) hx
    have hback0 :
        Part.exactFitp G
          ((G.face : G.Dart → G.Dart)^[p0.size - n] x) p0 = true := by
      have hrotback :
          Part.exactFitp G
            ((G.face : G.Dart → G.Dart)^[p0.size - n] x)
            (Part.rotate (p0.size - n) (Part.rotate n p0)) = true :=
        Part.exactFitp_rotate_of_le (G := G)
          (n := p0.size - n) (p := Part.rotate n p0)
          (by simp) hfit
      simpa [Part.rotate_size_sub_rotate] using hrotback
    have hpfit :
        Part.exactFitp G
          ((G.face : G.Dart → G.Dart)^[p0.size - n] x) p = true :=
      hforce
        ((G.face : G.Dart → G.Dart)^[p0.size - n] x) hxShift hback0
    have hrev := Part.exactFitp_face_iter_reverse_rotate_of_arity_eq
      (G := G) (n := p0.size - n) (nhub := p0.size)
      (p := p) (x := x) (by omega) hxArity hpfit
    simpa [show p0.size - (p0.size - n) = n by omega] using hrev
  · have hsizele0 : p0.size ≤ n := le_of_not_ge hle
    have hfit0 : Part.exactFitp G x p0 = true := by
      simpa [Part.rotate_eq_self_of_size_le n p0 hsizele0] using hfit
    have hpfit : Part.exactFitp G x p = true := hforce x hx hfit0
    have hfit0s := hfit0
    have hpfits := hpfit
    simp [Part.exactFitp] at hfit0s hpfits
    have hsizep : p.size = p0.size := hpfits.1.symm.trans hfit0s.1
    have hsizelep : p.size ≤ n := by omega
    simpa [Part.rotate_eq_self_of_size_le n p hsizelep] using hpfit

theorem forcedPart_of_rotate_forcedPart
    {p0 p : Part} (n : Nat)
    (hforce : ForcedPart.{u} (Part.rotate n p0) (Part.rotate n p)) :
    ForcedPart.{u} p0 p := by
  intro G x hx hfit0
  by_cases hle : n ≤ p0.size
  · have hfit0s := hfit0
    simp [Part.exactFitp] at hfit0s
    have hxArity : G.arity x = p0.size := hfit0s.1
    have hxShift :
        ValidHub G ((G.face : G.Dart → G.Dart)^[n] x) :=
      validHub_face_iter (G := G) n hx
    have hrot0 :
        Part.exactFitp G ((G.face : G.Dart → G.Dart)^[n] x)
          (Part.rotate n p0) = true :=
      Part.exactFitp_rotate_of_le (G := G) hle hfit0
    have hrotp :
        Part.exactFitp G ((G.face : G.Dart → G.Dart)^[n] x)
          (Part.rotate n p) = true :=
      hforce ((G.face : G.Dart → G.Dart)^[n] x) hxShift hrot0
    have hrot0s := hrot0
    have hrotps := hrotp
    simp [Part.exactFitp] at hrot0s hrotps
    have hsizep : p.size = p0.size := hrotps.1.symm.trans hrot0s.1
    have hrev := Part.exactFitp_face_iter_reverse_rotate_of_arity_eq
      (G := G) (n := n) (nhub := p0.size)
      (p := Part.rotate n p) (x := x) hle hxArity hrotp
    have htarget :
        Part.exactFitp G x
          (Part.rotate (p0.size - n) (Part.rotate n p)) = true := hrev
    simpa [← hsizep, Part.rotate_size_sub_rotate] using htarget
  · have hsizele0 : p0.size ≤ n := le_of_not_ge hle
    have hrot0 : Part.exactFitp G x (Part.rotate n p0) = true := by
      simpa [Part.rotate_eq_self_of_size_le n p0 hsizele0] using hfit0
    have hrotp : Part.exactFitp G x (Part.rotate n p) = true :=
      hforce x hx hrot0
    have hfit0s := hfit0
    have hrotps := hrotp
    simp [Part.exactFitp] at hfit0s hrotps
    have hsizep : p.size = p0.size := hrotps.1.symm.trans hfit0s.1
    have hsizelep : p.size ≤ n := by omega
    simpa [Part.rotate_eq_self_of_size_le n p hsizelep] using hrotp

theorem succeedsIn_of_rotate
    {p0 p : Part} (n : Nat)
    (h : SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p)) :
    SucceedsIn.{u} p0 p := by
  intro hforce
  exact successful_of_rotate_successful n
    (h (forcedPart_rotate_of_forcedPart n hforce))

theorem succeedsIn_rotate
    {p0 p : Part} (n : Nat)
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p) := by
  intro hforce
  exact successful_rotate_of_successful n
    (h (forcedPart_of_rotate_forcedPart n hforce))

theorem succeedsIn_rotate_iff
    {p0 p : Part} (n : Nat) :
    SucceedsIn.{u} (Part.rotate n p0) (Part.rotate n p) ↔
      SucceedsIn.{u} p0 p := by
  constructor
  · exact succeedsIn_of_rotate n
  · exact succeedsIn_rotate n

theorem succeedsIn_of_similarityCheck_rotate_successful
    {p0 ps p : Part} {j : Nat}
    (h : similarityCheck ps p j false = true)
    (hps : Successful.{u} ps) :
    SucceedsIn.{u} p0 p := by
  exact succeedsIn_of_successful
    (successful_of_similarityCheck_rotate h hps)

/-- Transport success through a mirror-side exact-fit equivalence. -/
theorem successful_of_mirror_fit_iff
    (hvalid : MirrorValidHubTransport.{u})
    {p q : Part}
    (hfit : ∀ (G : Hypermap.{u}) (x : G.Dart),
      G.MinimalCounterexample →
        (Part.exactFitp G.mirror x q = true ↔
          Part.exactFitp G x p = true))
    (hq : Successful.{u} q) :
    Successful.{u} p := by
  intro G x hx
  cases hp : Part.exactFitp G x p
  · rfl
  · have hqfit : Part.exactFitp G.mirror x q = true :=
      (hfit G x hx.1).2 hp
    have hqfail := hq (G := G.mirror) x (hvalid G x hx)
    rw [hqfit] at hqfail
    cases hqfail

/-- Transport forcedness through mirror-side exact-fit equivalences. -/
theorem forcedPart_of_mirror_fit_iff
    (hvalid : MirrorValidHubTransport.{u})
    {p0 p q0 q : Part}
    (hfit0 : ∀ (G : Hypermap.{u}) (x : G.Dart),
      G.MinimalCounterexample →
        (Part.exactFitp G.mirror x q0 = true ↔
          Part.exactFitp G x p0 = true))
    (hfit : ∀ (G : Hypermap.{u}) (x : G.Dart),
      G.MinimalCounterexample →
        (Part.exactFitp G.mirror x q = true ↔
          Part.exactFitp G x p = true))
    (hforce : ForcedPart.{u} q0 q) :
    ForcedPart.{u} p0 p := by
  intro G x hx hp0
  have hq0 : Part.exactFitp G.mirror x q0 = true :=
    (hfit0 G x hx.1).2 hp0
  have hq : Part.exactFitp G.mirror x q = true :=
    hforce (G := G.mirror) x (hvalid G x hx) hq0
  exact (hfit G x hx.1).1 hq

theorem successful_of_mirror_successful
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p : Part}
    (hm : Successful.{u} (Part.mirror p)) :
    Successful.{u} p := by
  exact successful_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransport_true_iff hfitMirror G x p hG)
    hm

theorem successful_mirror_of_successful
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p : Part}
    (hp : Successful.{u} p) :
    Successful.{u} (Part.mirror p) := by
  exact successful_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransport_symm_true_iff hfitMirror G x p hG)
    hp

theorem successful_mirror_iff
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p : Part} :
    Successful.{u} (Part.mirror p) ↔ Successful.{u} p := by
  constructor
  · exact successful_of_mirror_successful hvalid hfitMirror
  · exact successful_mirror_of_successful hvalid hfitMirror

theorem forcedPart_mirror_of_forcedPart
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u} (Part.mirror p0) (Part.mirror p) := by
  exact forcedPart_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransport_symm_true_iff hfitMirror G x p0 hG)
    (fun G x hG =>
      mirrorExactFitTransport_symm_true_iff hfitMirror G x p hG)
    hforce

theorem forcedPart_of_mirror_forcedPart
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} (Part.mirror p0) (Part.mirror p)) :
    ForcedPart.{u} p0 p := by
  have h := forcedPart_mirror_of_forcedPart hvalid hfitMirror hforce
  simpa [Part.mirror_mirror] using h

theorem succeedsIn_mirror
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) := by
  intro hforce
  exact successful_mirror_of_successful hvalid hfitMirror
    (h (forcedPart_of_mirror_forcedPart hvalid hfitMirror hforce))

theorem succeedsIn_of_mirror
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (h : SucceedsIn.{u} (Part.mirror p0) (Part.mirror p)) :
    SucceedsIn.{u} p0 p := by
  intro hforce
  exact successful_of_mirror_successful hvalid hfitMirror
    (h (forcedPart_mirror_of_forcedPart hvalid hfitMirror hforce))

theorem succeedsIn_mirror_iff
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part} :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p := by
  constructor
  · exact succeedsIn_of_mirror hvalid hfitMirror
  · exact succeedsIn_mirror hvalid hfitMirror

theorem successful_of_mirror_successful_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p : Part}
    (hsize : p.size ≤ n)
    (hm : Successful.{u} (Part.mirror p)) :
    Successful.{u} p := by
  exact successful_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransportUpTo_true_iff
        hfitMirror G x p hsize hG)
    hm

theorem successful_mirror_of_successful_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p : Part}
    (hsize : p.size ≤ n)
    (hp : Successful.{u} p) :
    Successful.{u} (Part.mirror p) := by
  exact successful_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransportUpTo_symm_true_iff
        hfitMirror G x p hsize hG)
    hp

theorem successful_mirror_iff_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p : Part}
    (hsize : p.size ≤ n) :
    Successful.{u} (Part.mirror p) ↔ Successful.{u} p := by
  constructor
  · exact successful_of_mirror_successful_upTo
      hvalid hfitMirror hsize
  · exact successful_mirror_of_successful_upTo
      hvalid hfitMirror hsize

theorem forcedPart_mirror_of_forcedPart_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u} (Part.mirror p0) (Part.mirror p) := by
  exact forcedPart_of_mirror_fit_iff hvalid
    (fun G x hG =>
      mirrorExactFitTransportUpTo_symm_true_iff
        hfitMirror G x p0 hsize0 hG)
    (fun G x hG =>
      mirrorExactFitTransportUpTo_symm_true_iff
        hfitMirror G x p hsize hG)
    hforce

theorem forcedPart_of_mirror_forcedPart_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (hforce : ForcedPart.{u} (Part.mirror p0) (Part.mirror p)) :
    ForcedPart.{u} p0 p := by
  have h := forcedPart_mirror_of_forcedPart_upTo
    hvalid hfitMirror
    (p0 := Part.mirror p0) (p := Part.mirror p)
    (by simpa [Part.size_mirror] using hsize0)
    (by simpa [Part.size_mirror] using hsize)
    hforce
  simpa [Part.mirror_mirror] using h

theorem succeedsIn_mirror_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (h : SucceedsIn.{u} p0 p) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) := by
  intro hforce
  exact successful_mirror_of_successful_upTo hvalid hfitMirror hsize
    (h (forcedPart_of_mirror_forcedPart_upTo
      hvalid hfitMirror hsize0 hsize hforce))

theorem succeedsIn_of_mirror_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n)
    (h : SucceedsIn.{u} (Part.mirror p0) (Part.mirror p)) :
    SucceedsIn.{u} p0 p := by
  intro hforce
  exact successful_of_mirror_successful_upTo hvalid hfitMirror hsize
    (h (forcedPart_mirror_of_forcedPart_upTo
      hvalid hfitMirror hsize0 hsize hforce))

theorem succeedsIn_mirror_iff_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 p : Part}
    (hsize0 : p0.size ≤ n)
    (hsize : p.size ≤ n) :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p := by
  constructor
  · exact succeedsIn_of_mirror_upTo
      hvalid hfitMirror hsize0 hsize
  · exact succeedsIn_mirror_upTo
      hvalid hfitMirror hsize0 hsize

theorem successful_mirror_iff_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p : Part} :
    Successful.{u} (Part.mirror p) ↔ Successful.{u} p :=
  successful_mirror_iff
    (mirrorValidHubTransport_of_dscore_mirror hscore) hfitMirror

theorem forcedPart_mirror_of_forcedPart_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u} (Part.mirror p0) (Part.mirror p) :=
  forcedPart_mirror_of_forcedPart
    (mirrorValidHubTransport_of_dscore_mirror hscore) hfitMirror hforce

theorem forcedPart_of_mirror_forcedPart_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} (Part.mirror p0) (Part.mirror p)) :
    ForcedPart.{u} p0 p :=
  forcedPart_of_mirror_forcedPart
    (mirrorValidHubTransport_of_dscore_mirror hscore) hfitMirror hforce

theorem succeedsIn_mirror_iff_of_dscore_mirror
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part} :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_mirror_iff
    (mirrorValidHubTransport_of_dscore_mirror hscore) hfitMirror

theorem successful_mirror_iff_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p : Part} :
    Successful.{u} (Part.mirror p) ↔ Successful.{u} p :=
  successful_mirror_iff
    (mirrorValidHubTransport_of_dscore2_mirror h2) hfitMirror

theorem forcedPart_mirror_of_forcedPart_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} p0 p) :
    ForcedPart.{u} (Part.mirror p0) (Part.mirror p) :=
  forcedPart_mirror_of_forcedPart
    (mirrorValidHubTransport_of_dscore2_mirror h2) hfitMirror hforce

theorem forcedPart_of_mirror_forcedPart_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part}
    (hforce : ForcedPart.{u} (Part.mirror p0) (Part.mirror p)) :
    ForcedPart.{u} p0 p :=
  forcedPart_of_mirror_forcedPart
    (mirrorValidHubTransport_of_dscore2_mirror h2) hfitMirror hforce

theorem succeedsIn_mirror_iff_of_dscore2_mirror
    (h2 : MirrorDscore2Transport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 p : Part} :
    SucceedsIn.{u} (Part.mirror p0) (Part.mirror p) ↔
      SucceedsIn.{u} p0 p :=
  succeedsIn_mirror_iff
    (mirrorValidHubTransport_of_dscore2_mirror h2) hfitMirror

theorem successful_of_similarityCheck_mirror
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {ps p : Part} {j : Nat}
    (h : similarityCheck ps p j true = true)
    (hps : Successful.{u} ps) :
    Successful.{u} p := by
  have hmirror :
      similarityCheck ps (Part.mirror p) j false = true := by
    simpa [similarityCheck] using h
  exact successful_of_mirror_successful
    (mirrorValidHubTransport_of_dscore_mirror hscore) hfitMirror
    (successful_of_similarityCheck_rotate hmirror hps)

theorem successful_of_similarityCheck_mirror_of_validHubTransport
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {ps p : Part} {j : Nat}
    (h : similarityCheck ps p j true = true)
    (hps : Successful.{u} ps) :
    Successful.{u} p := by
  have hmirror :
      similarityCheck ps (Part.mirror p) j false = true := by
    simpa [similarityCheck] using h
  exact successful_of_mirror_successful hvalid hfitMirror
    (successful_of_similarityCheck_rotate hmirror hps)

theorem successful_of_similarityCheck_mirror_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {ps p : Part} {j : Nat}
    (hsize : p.size ≤ n)
    (h : similarityCheck ps p j true = true)
    (hps : Successful.{u} ps) :
    Successful.{u} p := by
  have hmirror :
      similarityCheck ps (Part.mirror p) j false = true := by
    simpa [similarityCheck] using h
  exact successful_of_mirror_successful_upTo
    hvalid hfitMirror hsize
    (successful_of_similarityCheck_rotate hmirror hps)

theorem succeedsIn_of_similarityCheck_successful
    (hscore : MirrorDscoreTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (h : similarityCheck ps p j mir = true)
    (hps : Successful.{u} ps) :
    SucceedsIn.{u} p0 p := by
  cases mir
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_rotate h hps)
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_mirror hscore hfitMirror h hps)

theorem succeedsIn_of_similarityCheck_successful_of_validHubTransport
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransport.{u})
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (h : similarityCheck ps p j mir = true)
    (hps : Successful.{u} ps) :
    SucceedsIn.{u} p0 p := by
  cases mir
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_rotate h hps)
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_mirror_of_validHubTransport
        hvalid hfitMirror h hps)

theorem succeedsIn_of_similarityCheck_successful_upTo
    {n : Nat}
    (hvalid : MirrorValidHubTransport.{u})
    (hfitMirror : MirrorExactFitTransportUpTo.{u} n)
    {p0 ps p : Part} {j : Nat} {mir : Bool}
    (hsize : p.size ≤ n)
    (h : similarityCheck ps p j mir = true)
    (hps : Successful.{u} ps) :
    SucceedsIn.{u} p0 p := by
  cases mir
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_rotate h hps)
  · exact succeedsIn_of_successful
      (successful_of_similarityCheck_mirror_upTo
        hvalid hfitMirror hsize h hps)


end

end Presentation

end FourColor

end Schematic.Math.GraphTheory
