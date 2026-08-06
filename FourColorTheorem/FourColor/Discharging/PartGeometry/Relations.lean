import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorSpecializations
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem fitp_meet (p q : Part) (x : G.Dart) :
    fitp G x p = true →
      fitp G x q = true →
        fitp G x (meet p q) = true := by
  induction p generalizing q x with
  | Pnil =>
      intro _ _
      cases q <;> simp [meet, fitp]
  | Pcons sp hp p ih =>
      intro hfitp hfitq
      cases q <;> simp [fitp, meet] at hfitp hfitq ⊢
      · exact hfitp
      · rcases hfitp with ⟨⟨hsp, hhp⟩, htp⟩
        rcases hfitq with ⟨⟨hsq, hhq⟩, htq⟩
        exact ⟨⟨PRange.contains_meetRange_of_contains _ _ hsp hsq,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          ih _ _ htp htq⟩
      · rcases hfitp with ⟨⟨_, hhp⟩, htp⟩
        rcases hfitq with ⟨⟨⟨h66q, hhq⟩, hf1q⟩, htq⟩
        exact ⟨⟨⟨h66q,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩, hf1q⟩,
          ih _ _ htp htq⟩
      · rcases hfitp with ⟨⟨_, hhp⟩, htp⟩
        rcases hfitq with ⟨⟨⟨⟨h77q, hhq⟩, hf1q⟩, hf2q⟩, htq⟩
        exact ⟨⟨⟨⟨h77q,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          hf1q⟩, hf2q⟩, ih _ _ htp htq⟩
      · rcases hfitp with ⟨⟨_, hhp⟩, htp⟩
        rcases hfitq with
          ⟨⟨⟨⟨⟨h88q, hhq⟩, hf1q⟩, hf2q⟩, hf3q⟩, htq⟩
        exact ⟨⟨⟨⟨⟨h88q,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          hf1q⟩, hf2q⟩, hf3q⟩, ih _ _ htp htq⟩
  | Pcons6 hp f1 p ih =>
      intro hfitp hfitq
      cases q <;> simp [fitp, meet] at hfitp hfitq ⊢
      · exact hfitp
      · rcases hfitp with ⟨⟨⟨h66p, hhp⟩, hf1p⟩, htp⟩
        rcases hfitq with ⟨⟨_, hhq⟩, htq⟩
        exact ⟨⟨⟨h66p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩, hf1p⟩,
          ih _ _ htp htq⟩
      · rcases hfitp with ⟨⟨⟨h66p, hhp⟩, hf1p⟩, htp⟩
        rcases hfitq with ⟨⟨⟨_, hhq⟩, hf1q⟩, htq⟩
        exact ⟨⟨⟨h66p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          PRange.contains_meetRange_of_contains _ _ hf1p hf1q⟩,
          ih _ _ htp htq⟩
      · exact hfitp
      · exact hfitp
  | Pcons7 hp f1 f2 p ih =>
      intro hfitp hfitq
      cases q <;> simp [fitp, meet] at hfitp hfitq ⊢
      · exact hfitp
      · rcases hfitp with ⟨⟨⟨⟨h77p, hhp⟩, hf1p⟩, hf2p⟩, htp⟩
        rcases hfitq with ⟨⟨_, hhq⟩, htq⟩
        exact ⟨⟨⟨⟨h77p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩, hf1p⟩,
          hf2p⟩, ih _ _ htp htq⟩
      · exact hfitp
      · rcases hfitp with ⟨⟨⟨⟨h77p, hhp⟩, hf1p⟩, hf2p⟩, htp⟩
        rcases hfitq with ⟨⟨⟨⟨_, hhq⟩, hf1q⟩, hf2q⟩, htq⟩
        exact ⟨⟨⟨⟨h77p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          PRange.contains_meetRange_of_contains _ _ hf1p hf1q⟩,
          PRange.contains_meetRange_of_contains _ _ hf2p hf2q⟩,
          ih _ _ htp htq⟩
      · exact hfitp
  | Pcons8 hp f1 f2 f3 p ih =>
      intro hfitp hfitq
      cases q <;> simp [fitp, meet] at hfitp hfitq ⊢
      · exact hfitp
      · rcases hfitp with
          ⟨⟨⟨⟨⟨h88p, hhp⟩, hf1p⟩, hf2p⟩, hf3p⟩, htp⟩
        rcases hfitq with ⟨⟨_, hhq⟩, htq⟩
        exact ⟨⟨⟨⟨⟨h88p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩, hf1p⟩,
          hf2p⟩, hf3p⟩, ih _ _ htp htq⟩
      · exact hfitp
      · exact hfitp
      · rcases hfitp with
          ⟨⟨⟨⟨⟨h88p, hhp⟩, hf1p⟩, hf2p⟩, hf3p⟩, htp⟩
        rcases hfitq with
          ⟨⟨⟨⟨⟨_, hhq⟩, hf1q⟩, hf2q⟩, hf3q⟩, htq⟩
        exact ⟨⟨⟨⟨⟨h88p,
          PRange.contains_meetRange_of_contains _ _ hhp hhq⟩,
          PRange.contains_meetRange_of_contains _ _ hf1p hf1q⟩,
          PRange.contains_meetRange_of_contains _ _ hf2p hf2q⟩,
          PRange.contains_meetRange_of_contains _ _ hf3p hf3q⟩,
          ih _ _ htp htq⟩

theorem exactFitp_meet_of_fitp
    {p q : Part} {x : G.Dart}
    (hp : exactFitp G x p = true)
    (hq : fitp G x q = true) :
    exactFitp G x (meet p q) = true := by
  simp [exactFitp] at hp ⊢
  exact ⟨by simpa using hp.1,
    fitp_meet (G := G) p q x hp.2 hq⟩

theorem exactFitp_meet_of_exactFitp
    {p q : Part} {x : G.Dart}
    (hp : exactFitp G x p = true)
    (hq : exactFitp G x q = true) :
    exactFitp G x (meet p q) = true := by
  have hqs := hq
  simp [exactFitp] at hqs
  exact exactFitp_meet_of_fitp (G := G) hp hqs.2

theorem fitp_of_cmp_eq_subset (p q : Part) (x : G.Dart)
    (hcmp : cmp p q = PartRel.Psubset) :
    fitp G x p = true → fitp G x q = true := by
  induction p generalizing q x with
  | Pnil =>
      intro _
      cases q <;> simp [cmp] at hcmp ⊢
      rfl
  | Pcons sp hp p ih =>
      intro hfitp
      cases q with
      | Pnil =>
          simp [fitp]
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hspcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hhcmp, htcmp⟩
          exact ⟨⟨
            PRange.contains_of_cmpRange_eq_subset _ _ hspcmp hfitp.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp hfitp.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons6 _ _ _ =>
          simp only [cmp] at hcmp
          rcases PartRel.meetPRel_eq_subset hcmp with ⟨hbad, _⟩
          exact False.elim (PartRel.notPsubset_ne_subset _ hbad)
      | Pcons7 _ _ _ _ =>
          simp only [cmp] at hcmp
          rcases PartRel.meetPRel_eq_subset hcmp with ⟨hbad, _⟩
          exact False.elim (PartRel.notPsubset_ne_subset _ hbad)
      | Pcons8 _ _ _ _ _ =>
          simp only [cmp] at hcmp
          rcases PartRel.meetPRel_eq_subset hcmp with ⟨hbad, _⟩
          exact False.elim (PartRel.notPsubset_ne_subset _ hbad)
  | Pcons6 hp f1 p ih =>
      intro hfitp
      cases q with
      | Pnil =>
          simp [fitp]
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hspcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hhcmp, htcmp⟩
          exact ⟨⟨
            PRange.contains_of_cmpRange_eq_subset _ _ hspcmp hfitp.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp hfitp.1.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons6 hq f1q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hhcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hf1cmp, htcmp⟩
          exact ⟨⟨⟨hfitp.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp hfitp.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf1cmp hfitp.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons7 _ _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
      | Pcons8 _ _ _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
  | Pcons7 hp f1 f2 p ih =>
      intro hfitp
      cases q with
      | Pnil =>
          simp [fitp]
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hspcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hhcmp, htcmp⟩
          exact ⟨⟨
            PRange.contains_of_cmpRange_eq_subset _ _ hspcmp
              hfitp.1.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp
              hfitp.1.1.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons6 _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
      | Pcons7 hq f1q f2q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hhcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hf1cmp, hrestcmp'⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp' with
            ⟨hf2cmp, htcmp⟩
          exact ⟨⟨⟨⟨hfitp.1.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp
              hfitp.1.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf1cmp hfitp.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf2cmp hfitp.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons8 _ _ _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
  | Pcons8 hp f1 f2 f3 p ih =>
      intro hfitp
      cases q with
      | Pnil =>
          simp [fitp]
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hspcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hhcmp, htcmp⟩
          exact ⟨⟨
            PRange.contains_of_cmpRange_eq_subset _ _ hspcmp
              hfitp.1.1.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp
              hfitp.1.1.1.1.2⟩,
            ih _ _ htcmp hfitp.2⟩
      | Pcons6 _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
      | Pcons7 _ _ _ _ =>
          simp only [cmp] at hcmp
          cases hcmp
      | Pcons8 hq f1q f2q f3q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hfitp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hfitp
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true]
          rcases PartRel.meetPRel_eq_subset hcmp with
            ⟨hhcmp, hrestcmp⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp with
            ⟨hf1cmp, hrestcmp'⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp' with
            ⟨hf2cmp, hrestcmp''⟩
          rcases PartRel.meetPRel_eq_subset hrestcmp'' with
            ⟨hf3cmp, htcmp⟩
          exact ⟨⟨⟨⟨⟨hfitp.1.1.1.1.1,
            PRange.contains_of_cmpRange_eq_subset _ _ hhcmp
              hfitp.1.1.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf1cmp
              hfitp.1.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf2cmp hfitp.1.1.2⟩,
            PRange.contains_of_cmpRange_eq_subset _ _ hf3cmp hfitp.1.2⟩,
            ih _ _ htcmp hfitp.2⟩

theorem exactFitp_of_cmp_eq_subset_of_size_eq
    {p q : Part} {x : G.Dart}
    (hcmp : cmp p q = PartRel.Psubset)
    (hsize : p.size = q.size)
    (hp : exactFitp G x p = true) :
    exactFitp G x q = true := by
  have hps := hp
  simp [exactFitp] at hps ⊢
  exact ⟨by simpa [← hsize] using hps.1,
    fitp_of_cmp_eq_subset (G := G) p q x hcmp hps.2⟩

theorem fitp_false_of_cmp_eq_disjoint
    {p q : Part} {x : G.Dart}
    (hcmp : cmp p q = PartRel.Pdisjoint)
    (hp : fitp G x p = true) :
    fitp G x q = false := by
  induction p generalizing q x with
  | Pnil =>
      cases q <;> simp [cmp] at hcmp
  | Pcons sp hpR p ih =>
      cases q with
      | Pnil =>
          simp [cmp] at hcmp
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint sp sq
                hsp hp.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons6 hq f1q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hsp' : cmpRange sp PRange.Pr66 = PartRel.Pdisjoint := by
              cases h : cmpRange sp PRange.Pr66 <;>
                simp [h, notPsubset] at hsp ⊢
            have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint sp PRange.Pr66
                hsp' hp.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons7 hq f1q f2q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hsp' : cmpRange sp PRange.Pr77 = PartRel.Pdisjoint := by
              cases h : cmpRange sp PRange.Pr77 <;>
                simp [h, notPsubset] at hsp ⊢
            have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint sp PRange.Pr77
                hsp' hp.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons8 hq f1q f2q f3q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hsp' : cmpRange sp PRange.Pr88 = PartRel.Pdisjoint := by
              cases h : cmpRange sp PRange.Pr88 <;>
                simp [h, notPsubset] at hsp ⊢
            have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint sp PRange.Pr88
                hsp' hp.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
  | Pcons6 hpR f1p p ih =>
      cases q with
      | Pnil =>
          simp [cmp] at hcmp
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint PRange.Pr66 sq
                hsp hp.1.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons6 hq f1q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hh | hrest
          · have hhfalse :=
              PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                hh hp.1.1.2
            simp [hhfalse]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hf1 | ht
            · have hf1false :=
                PRange.contains_false_of_cmpRange_eq_disjoint f1p f1q
                  hf1 hp.1.2
              simp [hf1false]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons7 hq f1q f2q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
          have h77 :=
            PRange.contains_Pr77_false_of_Pr66 hp.1.1.1
          simp [h77]
      | Pcons8 hq f1q f2q f3q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
          have h88 :=
            PRange.contains_Pr88_false_of_Pr66 hp.1.1.1
          simp [h88]
  | Pcons7 hpR f1p f2p p ih =>
      cases q with
      | Pnil =>
          simp [cmp] at hcmp
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint PRange.Pr77 sq
                hsp hp.1.1.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.1.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons6 hq f1q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hp
          have h66 :=
            PRange.contains_Pr66_false_of_Pr77 hp.1.1.1.1
          simp [h66]
      | Pcons7 hq f1q f2q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hh | hrest
          · have hhfalse :=
              PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                hh hp.1.1.1.2
            simp [hhfalse]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hf1 | hrest'
            · have hf1false :=
                PRange.contains_false_of_cmpRange_eq_disjoint f1p f1q
                  hf1 hp.1.1.2
              simp [hf1false]
            · rcases PartRel.meetPRel_eq_disjoint hrest' with hf2 | ht
              · have hf2false :=
                  PRange.contains_false_of_cmpRange_eq_disjoint f2p f2q
                    hf2 hp.1.2
                simp [hf2false]
              · have htfalse := ih (q := q) (x := G.face x) ht hp.2
                simp [htfalse]
      | Pcons8 hq f1q f2q f3q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hp
          have h88 :=
            PRange.contains_Pr88_false_of_Pr77 hp.1.1.1.1
          simp [h88]
  | Pcons8 hpR f1p f2p f3p p ih =>
      cases q with
      | Pnil =>
          simp [cmp] at hcmp
      | Pcons sq hq q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hsp | hrest
          · have hs :=
              PRange.contains_false_of_cmpRange_eq_disjoint PRange.Pr88 sq
                hsp hp.1.1.1.1.1
            simp [hs]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hh | ht
            · have hhfalse :=
                PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                  hh hp.1.1.1.1.2
              simp [hhfalse]
            · have htfalse := ih (q := q) (x := G.face x) ht hp.2
              simp [htfalse]
      | Pcons6 hq f1q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hp
          have h66 :=
            PRange.contains_Pr66_false_of_Pr88 hp.1.1.1.1.1
          simp [h66]
      | Pcons7 hq f1q f2q q =>
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hp
          have h77 :=
            PRange.contains_Pr77_false_of_Pr88 hp.1.1.1.1.1
          simp [h77]
      | Pcons8 hq f1q f2q f3q q =>
          simp only [cmp] at hcmp
          simp only [fitp] at hp ⊢
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true] at hp
          rcases PartRel.meetPRel_eq_disjoint hcmp with hh | hrest
          · have hhfalse :=
              PRange.contains_false_of_cmpRange_eq_disjoint hpR hq
                hh hp.1.1.1.1.2
            simp [hhfalse]
          · rcases PartRel.meetPRel_eq_disjoint hrest with hf1 | hrest'
            · have hf1false :=
                PRange.contains_false_of_cmpRange_eq_disjoint f1p f1q
                  hf1 hp.1.1.1.2
              simp [hf1false]
            · rcases PartRel.meetPRel_eq_disjoint hrest' with hf2 | hrest''
              · have hf2false :=
                  PRange.contains_false_of_cmpRange_eq_disjoint f2p f2q
                    hf2 hp.1.1.2
                simp [hf2false]
              · rcases PartRel.meetPRel_eq_disjoint hrest'' with hf3 | ht
                · have hf3false :=
                    PRange.contains_false_of_cmpRange_eq_disjoint f3p f3q
                      hf3 hp.1.2
                  simp [hf3false]
                · have htfalse := ih (q := q) (x := G.face x) ht hp.2
                  simp [htfalse]


end

end Part

end FourColor

end Schematic.Math.GraphTheory
