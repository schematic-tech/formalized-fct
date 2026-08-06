import FourColorTheorem.FourColor.Discharging.Part.Mirror

/-! Converse, range splitting, comparison, and intersection of parts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PRange PartRel SubpartLoc

namespace Part

/-- First helper for Coq's over-approximating converse operation. -/
def convPart12 : Part → PRange × (Part → Part)
  | Pcons s2 s1 (Pcons h23 f2 _) =>
      match f2, s2 with
      | Pr59, _ => (h23, fun q => pconsS s1 (pconsS s2 q))
      | _, Pr55 => (h23, fun q => pconsS s1 (Pcons Pr55 f2 q))
      | _, Pr66 => (h23, fun q => pconsS s1 (Pcons6 Pr59 f2 q))
      | _, Pr77 => (h23, fun q => pconsS s1 (Pcons7 Pr59 Pr59 f2 q))
      | _, _ => (Pr59, fun _ => Pnil)
  | Pcons6 s1 h12 (Pcons h23 f21 _) =>
      (h23, fun q => pconsS s1 (Pcons6 h12 f21 q))
  | Pcons7 s1 h12 f21 (Pcons h23 f22 _) =>
      (h23, fun q => pconsS s1 (Pcons7 h12 f21 f22 q))
  | _ => (Pr59, fun _ => Pnil)

/-- Third-spoke helper for Coq's over-approximating converse operation. -/
def convPart3 (h23 : PRange) : Part → Part → Part
  | Pnil => fun q => Pcons Pr55 h23 q
  | Pcons _ _ Pnil => fun q => Pcons Pr66 h23 q
  | Pcons f31 _ (Pcons f32 _ Pnil) =>
      match f31, f32 with
      | Pr59, Pr59 => fun q => Pcons Pr77 h23 q
      | _, _ => fun q => Pcons7 h23 f31 f32 q
  | Pcons f31 _ (Pcons f32 _ (Pcons f33 _ Pnil)) =>
      fun q => Pcons8 h23 f31 f32 f33 q
  | _ => fun _ => Pnil

/-- Fourth-spoke helper for Coq's over-approximating converse operation. -/
def convPart4 : Part → PRange × (Part → Part)
  | Pcons h34 _ (Pcons s4 f41 _) =>
      match f41, s4 with
      | Pr59, _ => (Pr59, fun q => Pcons s4 h34 q)
      | _, Pr55 => (f41, fun q => Pcons Pr55 h34 q)
      | _, Pr66 => (Pr59, fun q => Pcons6 h34 f41 q)
      | _, Pr77 => (Pr59, fun q => Pcons7 h34 f41 Pr59 q)
      | _, _ => (Pr59, fun _ => Pnil)
  | Pcons h34 _ (Pcons6 f41 h45 _) =>
      (h45, fun q => Pcons6 h34 f41 q)
  | Pcons h34 _ (Pcons7 f41 f42 h45 _) =>
      (h45, fun q => Pcons7 h34 f41 f42 q)
  | _ => (Pr59, fun _ => Pnil)

/-- Fifth-spoke helper for Coq's over-approximating converse operation. -/
def convPart5 (h45 : PRange) : Part → PRange × Part
  | Pcons u s5 _ => (u, Pcons s5 h45 Pnil)
  | Pcons7 s5 s6 s7 _ => (Pr77, Pcons s5 h45 (pconsS s6 (pconsS s7 Pnil)))
  | _ => (Pr59, Pnil)

/-- Converse part: reflection along the third spoke.  This is intentionally
over-approximating, exactly as in Coq `part.v`. -/
def converse (p : Part) : PRange × Part :=
  let (h45, q4) := convPart4 p
  let (u, q5) := convPart5 h45 (drop 2 p)
  let (h23, q12) := convPart12 (drop 3 p)
  let q3 := convPart3 h23 (drop 5 p)
  (u, q12 (q3 (q4 q5)))

/-- Range `[5,k]`, with out-of-table values mapped to the free range. -/
def rangeLo : Nat → PRange
  | 5 => Pr55
  | 6 => Pr56
  | 7 => Pr57
  | 8 => Pr58
  | _ => Pr59

/-- Range `[k+1,∞)`, with out-of-table values mapped to the free range. -/
def rangeHi : Nat → PRange
  | 5 => Pr69
  | 6 => Pr79
  | 7 => Pr89
  | 8 => Pr99
  | _ => Pr59

/-- A range can be split at `k` exactly when it straddles `[5,k]`. -/
def goodRSplit (k : Nat) (r : PRange) : Bool :=
  match cmpRange r (rangeLo k) with
  | Pstraddle => true
  | _ => false

/-- Restrict a range to the low or high side of a split. -/
def splitRange (k : Nat) (lo : Bool) (r : PRange) : PRange :=
  meetRange (if lo then rangeLo k else rangeHi k) r

/-- Whether the range at a location can be split. -/
def goodSplit (i : SubpartLoc) (j k : Nat) (p : Part) : Bool :=
  match i, drop j p with
  | Pspoke, Pcons s _ _ => goodRSplit k s
  | Phat, Pcons _ h _ => goodRSplit k h
  | Phat, Pcons6 h _ _ => goodRSplit k h
  | Phat, Pcons7 h _ _ _ => goodRSplit k h
  | Phat, Pcons8 h _ _ _ _ => goodRSplit k h
  | Pfan1, Pcons6 _ f1 _ => goodRSplit k f1
  | Pfan1, Pcons Pr66 _ _ => goodRSplit k Pr59
  | Pfan1, Pcons7 _ f1 _ _ => goodRSplit k f1
  | Pfan1, Pcons Pr77 _ _ => goodRSplit k Pr59
  | Pfan1, Pcons8 _ f1 _ _ _ => goodRSplit k f1
  | Pfan1, Pcons Pr88 _ _ => goodRSplit k Pr59
  | Pfan2, Pcons7 _ _ f2 _ => goodRSplit k f2
  | Pfan2, Pcons Pr77 _ _ => goodRSplit k Pr59
  | Pfan2, Pcons8 _ _ f2 _ _ => goodRSplit k f2
  | Pfan2, Pcons Pr88 _ _ => goodRSplit k Pr59
  | Pfan3, Pcons8 _ _ _ f3 _ => goodRSplit k f3
  | Pfan3, Pcons Pr88 _ _ => goodRSplit k Pr59
  | _, _ => false

/-- Split the range at a location, selecting either the low or high side. -/
def split (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) : Part :=
  let p1 := take j p
  let p2 := drop j p
  let mkp (df : PRange → Part → Part) (r : PRange) (p' : Part) :=
    append p1 (df (splitRange k lo r) p')
  match i, p2 with
  | Pspoke, Pcons s h p' => mkp (fun r => Pcons r h) s p'
  | Phat, Pcons s h p' => mkp (fun r => Pcons s r) h p'
  | Phat, Pcons6 h f1 p' => mkp (fun r => Pcons6 r f1) h p'
  | Phat, Pcons7 h f1 f2 p' => mkp (fun r => Pcons7 r f1 f2) h p'
  | Phat, Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 r f1 f2 f3) h p'
  | Pfan1, Pcons6 h f1 p' => mkp (fun r => Pcons6 h r) f1 p'
  | Pfan1, Pcons Pr66 h p' => mkp (fun r => Pcons6 h r) Pr59 p'
  | Pfan1, Pcons7 h f1 f2 p' => mkp (fun r => Pcons7 h r f2) f1 p'
  | Pfan1, Pcons Pr77 h p' => mkp (fun r => Pcons7 h r Pr59) Pr59 p'
  | Pfan1, Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h r f2 f3) f1 p'
  | Pfan1, Pcons Pr88 h p' => mkp (fun r => Pcons8 h r Pr59 Pr59) Pr59 p'
  | Pfan2, Pcons7 h f1 f2 p' => mkp (fun r => Pcons7 h f1 r) f2 p'
  | Pfan2, Pcons Pr77 h p' => mkp (fun r => Pcons7 h Pr59 r) Pr59 p'
  | Pfan2, Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 r f3) f2 p'
  | Pfan2, Pcons Pr88 h p' => mkp (fun r => Pcons8 h Pr59 r Pr59) Pr59 p'
  | Pfan3, Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 f2 r) f3 p'
  | Pfan3, Pcons Pr88 h p' => mkp (fun r => Pcons8 h Pr59 Pr59 r) Pr59 p'
  | _, _ => p

/-- Compare two parts as sets of pointed maps. -/
def cmp : Part → Part → PartRel
  | Pcons sp hp p, Pcons sq hq q =>
      meetPRel (cmpRange sp sq) (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons6 hp _ p, Pcons sq hq q =>
      meetPRel (cmpRange Pr66 sq) (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons7 hp _ _ p, Pcons sq hq q =>
      meetPRel (cmpRange Pr77 sq) (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons8 hp _ _ _ p, Pcons sq hq q =>
      meetPRel (cmpRange Pr88 sq) (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons sp hp p, Pcons6 hq _ q =>
      meetPRel (notPsubset (cmpRange sp Pr66))
        (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons sp hp p, Pcons7 hq _ _ q =>
      meetPRel (notPsubset (cmpRange sp Pr77))
        (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons sp hp p, Pcons8 hq _ _ _ q =>
      meetPRel (notPsubset (cmpRange sp Pr88))
        (meetPRel (cmpRange hp hq) (cmp p q))
  | Pcons6 hp f1p p, Pcons6 hq f1q q =>
      meetPRel (cmpRange hp hq)
        (meetPRel (cmpRange f1p f1q) (cmp p q))
  | Pcons7 hp f1p f2p p, Pcons7 hq f1q f2q q =>
      meetPRel (cmpRange hp hq)
        (meetPRel (cmpRange f1p f1q)
          (meetPRel (cmpRange f2p f2q) (cmp p q)))
  | Pcons8 hp f1p f2p f3p p, Pcons8 hq f1q f2q f3q q =>
      meetPRel (cmpRange hp hq)
        (meetPRel (cmpRange f1p f1q)
          (meetPRel (cmpRange f2p f2q)
            (meetPRel (cmpRange f3p f3q) (cmp p q))))
  | _, Pnil => Psubset
  | Pnil, _ => Pstraddle
  | _, _ => Pdisjoint

/-- Intersection of a part with a sector part.  This truncates the second
argument in the same asymmetric way as Coq `meet_part`. -/
def meet : Part → Part → Part
  | Pcons sp hp p, Pcons sq hq q =>
      Pcons (meetRange sp sq) (meetRange hp hq) (meet p q)
  | Pcons6 hp f1 p, Pcons _ hq q =>
      Pcons6 (meetRange hp hq) f1 (meet p q)
  | Pcons7 hp f1 f2 p, Pcons _ hq q =>
      Pcons7 (meetRange hp hq) f1 f2 (meet p q)
  | Pcons8 hp f1 f2 f3 p, Pcons _ hq q =>
      Pcons8 (meetRange hp hq) f1 f2 f3 (meet p q)
  | Pcons _ hp p, Pcons6 hq f1 q =>
      Pcons6 (meetRange hp hq) f1 (meet p q)
  | Pcons _ hp p, Pcons7 hq f1 f2 q =>
      Pcons7 (meetRange hp hq) f1 f2 (meet p q)
  | Pcons _ hp p, Pcons8 hq f1 f2 f3 q =>
      Pcons8 (meetRange hp hq) f1 f2 f3 (meet p q)
  | Pcons6 hp f1p p, Pcons6 hq f1q q =>
      Pcons6 (meetRange hp hq) (meetRange f1p f1q) (meet p q)
  | Pcons7 hp f1p f2p p, Pcons7 hq f1q f2q q =>
      Pcons7 (meetRange hp hq) (meetRange f1p f1q)
        (meetRange f2p f2q) (meet p q)
  | Pcons8 hp f1p f2p f3p p, Pcons8 hq f1q f2q f3q q =>
      Pcons8 (meetRange hp hq) (meetRange f1p f1q)
        (meetRange f2p f2q) (meetRange f3p f3q) (meet p q)
  | p, _ => p

@[simp]
theorem size_meet (p q : Part) :
    size (meet p q) = size p := by
  induction q generalizing p with
  | Pnil =>
      cases p <;> rfl
  | Pcons _ _ q ih =>
      cases p <;> simp [meet, size, ih]
  | Pcons6 _ _ q ih =>
      cases p <;> simp [meet, size, ih]
  | Pcons7 _ _ _ q ih =>
      cases p <;> simp [meet, size, ih]
  | Pcons8 _ _ _ _ q ih =>
      cases p <;> simp [meet, size, ih]

end Part

end FourColor

end Schematic.Math.GraphTheory
