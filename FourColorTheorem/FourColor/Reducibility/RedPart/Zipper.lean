import FourColorTheorem.FourColor.Configuration.QuizTree.Foundations

/-!
Part reducibility search.

This ports the executable core of Coq `redpart.v`: zipper locations for parts,
range-to-question matching, recursive range popping, and the bounded redpart
search over a quiz tree.  The semantic soundness theorem (`no_fit_redpart` in
Coq) belongs to the later embedding/presentation layer.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

open Part
open PRange
open Question
open QArity

namespace RedPart

/-- Zipper locations used while searching a part for a reducible configuration. -/
inductive ZPartLoc
  | Znil
  | Zhub | Zhubl | Zhubr
  | Zhat | Zhatl | Zhatr
  | Zfan0l | Zfan1l | Zfan2l | Zfan3l
  | Zfan0r | Zfan1r | Zfan2r | Zfan3r
  deriving DecidableEq, Repr, Inhabited

open ZPartLoc

/-- A zipped part: left sector, right sector, and the represented local dart. -/
structure ZPart where
  loc : ZPartLoc
  left : Part
  right : Part
  deriving DecidableEq, Repr, Inhabited

namespace ZPart

def proper (zp : ZPart) : Bool :=
  match zp.loc with
  | Znil => false
  | _ => true

end ZPart

/-- Runtime context for one redpart search. -/
structure Context where
  qt : QuizTree
  ahub : QArity
  redRec : Part → Bool
  p0l : Part
  p0r : Part

namespace Context

def nhub (ctx : Context) : Nat :=
  ctx.ahub.toNat

end Context

def NoRedRec (G : Hypermap) (ctx : Context) : Prop :=
  ∀ (x : G.Dart) (p : Part),
    G.arity x = ctx.nhub →
      Part.exactFitp G x p = true →
        ctx.redRec p = false

/-- The left sector is stored in reverse order; validity says that left+right
sectors cover the doubled reference part, matching Coq `zvalid`. -/
def zvalid (ctx : Context) (pl pr : Part) : Prop :=
  Part.reverseAppend pl pr = Part.append ctx.p0r ctx.p0r

def zpvalid (ctx : Context) (zp : ZPart) : Prop :=
  zvalid ctx zp.left zp.right

theorem zvalid_init
    (ctx : Context)
    (hleft : ctx.p0l = Part.reverse ctx.p0r) :
    zvalid ctx ctx.p0l ctx.p0r := by
  rw [zvalid, hleft, Part.reverseAppend_reverse]

theorem zvalid_size
    {ctx : Context} {pl pr : Part}
    (hvalid : zvalid ctx pl pr) :
    Part.size pl + Part.size pr = 2 * Part.size ctx.p0r := by
  have hsize := congrArg Part.size hvalid
  simpa [zvalid, Part.size_append, Part.size_reverseAppend,
    Nat.two_mul] using hsize

noncomputable def zmove (G : Hypermap) : ZPartLoc → G.Dart → G.Dart
  | Znil, x => x
  | Zhub, x => x
  | Zhubl, x => G.node x
  | Zhubr, x => G.node (G.node x)
  | Zhat, x => G.node (G.edge (G.node (G.node x)))
  | Zhatl, x => G.edge (G.node (G.node x))
  | Zhatr, x => G.face (G.node (G.node x))
  | Zfan0l, x =>
      G.face (G.edge (((fun y : G.Dart => G.edge (G.node y))^[2])
        (G.node x)))
  | Zfan1l, x =>
      G.face (G.edge (((fun y : G.Dart => G.edge (G.node y))^[3])
        (G.node x)))
  | Zfan2l, x =>
      G.face (G.edge (((fun y : G.Dart => G.edge (G.node y))^[4])
        (G.node x)))
  | Zfan3l, x =>
      G.face (G.edge (((fun y : G.Dart => G.edge (G.node y))^[5])
        (G.node x)))
  | Zfan0r, x => G.edge (((G.face : G.Dart → G.Dart)^[2]) (G.node x))
  | Zfan1r, x => G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.node x))
  | Zfan2r, x => G.edge (((G.face : G.Dart → G.Dart)^[4]) (G.node x))
  | Zfan3r, x => G.edge (((G.face : G.Dart → G.Dart)^[5]) (G.node x))

@[simp]
theorem zmove_zfan0r (G : Hypermap) (x : G.Dart) :
    zmove G Zfan0r x =
      G.edge (((G.face : G.Dart → G.Dart)^[2]) (G.node x)) := by
  simp [zmove]

@[simp]
theorem zmove_zfan1r (G : Hypermap) (x : G.Dart) :
    zmove G Zfan1r x =
      G.edge (((G.face : G.Dart → G.Dart)^[3]) (G.node x)) := by
  simp [zmove]

@[simp]
theorem zmove_zfan2r (G : Hypermap) (x : G.Dart) :
    zmove G Zfan2r x =
      G.edge (((G.face : G.Dart → G.Dart)^[4]) (G.node x)) := by
  simp [zmove]

@[simp]
theorem zmove_zfan3r (G : Hypermap) (x : G.Dart) :
    zmove G Zfan3r x =
      G.edge (((G.face : G.Dart → G.Dart)^[5]) (G.node x)) := by
  simp [zmove]

noncomputable def zorg (G : Hypermap) (x0 : G.Dart) (pl : Part) : G.Dart :=
  ((G.face : G.Dart → G.Dart)^[Part.size pl]) x0

noncomputable def zporg (G : Hypermap) (x0 : G.Dart) (zp : ZPart) : G.Dart :=
  zorg G x0 zp.left

noncomputable def zdart (G : Hypermap) (x0 : G.Dart) (zp : ZPart) : G.Dart :=
  zmove G zp.loc (zporg G x0 zp)

noncomputable def zpfit
    (G : Hypermap) (x0 : G.Dart) (x : G.Dart) (zp : ZPart) : Prop :=
  zp.proper = true → zdart G x0 zp = x

def shiftPart (p1 p2 : Part) : Part :=
  Part.append (Part.take 1 p1) p2

private theorem reverseAppend_take_one
    (p q : Part) :
    Part.reverseAppend (Part.take 1 p) q =
      Part.append (Part.take 1 p) q := by
  cases p <;> rfl

theorem zvalid_wrapL
    (ctx : Context)
    (hleft : ctx.p0l = Part.reverse ctx.p0r) :
    zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r) := by
  rw [zvalid, shiftPart]
  calc
    Part.reverseAppend (Part.drop 1 ctx.p0l)
        (Part.append (Part.take 1 ctx.p0l) ctx.p0r)
        =
      Part.reverseAppend
        (Part.append (Part.take 1 ctx.p0l) (Part.drop 1 ctx.p0l))
        ctx.p0r := by
          rw [Part.reverseAppend_append]
          rw [reverseAppend_take_one]
    _ = Part.reverseAppend ctx.p0l ctx.p0r := by
          rw [Part.append_take_drop]
    _ = Part.append ctx.p0r ctx.p0r := by
          rw [hleft, Part.reverseAppend_reverse]

theorem zvalid_wrapR
    (ctx : Context)
    (hleft : ctx.p0l = Part.reverse ctx.p0r) :
    zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r) := by
  rw [zvalid, shiftPart]
  calc
    Part.reverseAppend (Part.append (Part.take 1 ctx.p0r) ctx.p0l)
        (Part.drop 1 ctx.p0r)
        =
      Part.reverseAppend ctx.p0l
        (Part.reverseAppend (Part.take 1 ctx.p0r) (Part.drop 1 ctx.p0r)) := by
          rw [Part.reverseAppend_append]
    _ =
      Part.reverseAppend ctx.p0l
        (Part.append (Part.take 1 ctx.p0r) (Part.drop 1 ctx.p0r)) := by
          rw [reverseAppend_take_one]
    _ = Part.reverseAppend ctx.p0l ctx.p0r := by
          rw [Part.append_take_drop]
    _ = Part.append ctx.p0r ctx.p0r := by
          rw [hleft, Part.reverseAppend_reverse]

def mkZ (loc : ZPartLoc) (left right : Part) : ZPart :=
  ⟨loc, left, right⟩

/-- Zipper validity depends only on its two sectors, not on the selected
local dart. -/
theorem zpvalid_mkZ_loc
    {ctx : Context} {loc loc' : ZPartLoc} {left right : Part}
    (hvalid : zpvalid ctx (mkZ loc left right)) :
    zpvalid ctx (mkZ loc' left right) :=
  hvalid

def locProper : ZPartLoc → Bool
  | Znil => false
  | _ => true

@[simp]
theorem mkZ_proper (loc : ZPartLoc) (pl pr : Part) :
    (mkZ loc pl pr).proper = locProper loc := by
  cases loc <;> rfl

def hubRange : QArity → PRange
  | Qa5 => Pr55
  | Qa6 => Pr66
  | Qa7 => Pr77
  | Qa8 => Pr88
  | _ => Pr99

def zrange (ctx : Context) (zp : ZPart) : PRange :=
  match zp.loc with
  | Znil => Pr59
  | Zhub => hubRange ctx.ahub
  | Zhubl => Part.getSpoke zp.left
  | Zhubr => Part.getSpoke zp.right
  | Zhatl => Part.getSpoke zp.left
  | Zhat => Part.getHat zp.right
  | Zhatr => Part.getSpoke zp.right
  | Zfan0l => Part.getHat zp.right
  | Zfan1l => Part.getFan1l zp.left
  | Zfan2l => Part.getFan2l zp.left
  | Zfan3l => Part.getFan3l zp.left
  | Zfan0r => Part.getHat zp.left
  | Zfan1r => Part.getFan1r zp.left
  | Zfan2r => Part.getFan2r zp.left
  | Zfan3r => Part.getFan3r zp.left

def zshiftL (ctx : Context) (loc : ZPartLoc) (zp : ZPart) : ZPart :=
  match zp.left with
  | Pcons _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons6 _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons7 _ _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons8 _ _ _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons s h pl => mkZ loc pl (Pcons s h zp.right)
  | Pcons6 h f1 pl => mkZ loc pl (Pcons6 h f1 zp.right)
  | Pcons7 h f1 f2 pl => mkZ loc pl (Pcons7 h f1 f2 zp.right)
  | Pcons8 h f1 f2 f3 pl => mkZ loc pl (Pcons8 h f1 f2 f3 zp.right)
  | Pnil => mkZ loc (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r)

def zshiftR (ctx : Context) (loc : ZPartLoc) (zp : ZPart) : ZPart :=
  match zp.right with
  | Pcons _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons6 _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons7 _ _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons8 _ _ _ _ Pnil => mkZ loc ctx.p0l ctx.p0r
  | Pcons s h pr => mkZ loc (Pcons s h zp.left) pr
  | Pcons6 h f1 pr => mkZ loc (Pcons6 h f1 zp.left) pr
  | Pcons7 h f1 f2 pr => mkZ loc (Pcons7 h f1 f2 zp.left) pr
  | Pcons8 h f1 f2 f3 pr => mkZ loc (Pcons8 h f1 f2 f3 zp.left) pr
  | Pnil => mkZ loc (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r)

def zfanL : Part → ZPartLoc
  | Pcons Pr55 _ _ => Zfan0l
  | Pcons6 _ _ _ => Zfan1l
  | Pcons7 _ _ _ _ => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _ => Znil

def zfanR : Part → ZPartLoc
  | Pcons Pr55 _ _ => Zfan0r
  | Pcons6 _ _ _ => Zfan1r
  | Pcons7 _ _ _ _ => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _ => Znil

def zfanLt : Part → ZPartLoc
  | Pcons Pr55 _ _ => Zfan0l
  | Pcons Pr56 _ _ => Zfan1l
  | Pcons Pr66 _ _ => Zfan1l
  | Pcons6 _ _ _ => Zfan1l
  | Pcons7 _ _ _ _ => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _ => Znil

def zfanRt : Part → ZPartLoc
  | Pcons Pr55 _ _ => Zfan0r
  | Pcons Pr56 _ _ => Zfan1r
  | Pcons Pr66 _ _ => Zfan1r
  | Pcons6 _ _ _ => Zfan1r
  | Pcons7 _ _ _ _ => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _ => Znil

def zstepL (ctx : Context) (zp : ZPart) : ZPart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftL ctx Zhubl zp
  | ⟨Zhubl, pl, pr⟩ => mkZ Zhat pl pr
  | ⟨Zhubr, _, _⟩ => zshiftR ctx Zhubr zp
  | ⟨Zhat, _, pr⟩ => zshiftR ctx (zfanL pr) zp
  | ⟨Zhatl, pl, pr⟩ => mkZ (zfanR pl) pl pr
  | ⟨Zhatr, pl, pr⟩ => mkZ Zhub pl pr
  | ⟨Zfan0l, pl, pr⟩ => mkZ Zhatr pl pr
  | ⟨Zfan1l, pl, pr⟩ => mkZ Zfan0l pl pr
  | ⟨Zfan2l, pl, pr⟩ => mkZ Zfan1l pl pr
  | ⟨Zfan3l, pl, pr⟩ => mkZ Zfan2l pl pr
  | ⟨_, pl, pr⟩ => mkZ Znil pl pr

def zstepR (ctx : Context) (zp : ZPart) : ZPart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftR ctx Zhubr zp
  | ⟨Zhubl, _, _⟩ => zshiftL ctx Zhubl zp
  | ⟨Zhubr, pl, pr⟩ => mkZ Zhat pl pr
  | ⟨Zhat, pl, pr⟩ => mkZ (zfanR pl) pl pr
  | ⟨Zhatl, pl, pr⟩ => mkZ Zhub pl pr
  | ⟨Zhatr, _, pr⟩ => zshiftR ctx (zfanL pr) zp
  | ⟨Zfan0r, _, _⟩ => zshiftL ctx Zhatl zp
  | ⟨Zfan1r, pl, pr⟩ => mkZ Zfan0r pl pr
  | ⟨Zfan2r, pl, pr⟩ => mkZ Zfan1r pl pr
  | ⟨Zfan3r, pl, pr⟩ => mkZ Zfan2r pl pr
  | ⟨_, pl, pr⟩ => mkZ Znil pl pr

def zstepLt (ctx : Context) (zp : ZPart) : ZPart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftL ctx Zhubl zp
  | ⟨Zhubl, pl, pr⟩ => mkZ Zhat pl pr
  | ⟨Zhubr, _, _⟩ => zshiftR ctx Zhubr zp
  | ⟨Zhat, _, pr⟩ => zshiftR ctx (zfanL pr) zp
  | ⟨Zhatl, pl, pr⟩ => mkZ (zfanRt pl) pl pr
  | ⟨Zhatr, pl, pr⟩ => mkZ Zhub pl pr
  | ⟨Zfan0l, pl, pr⟩ => mkZ Zhatr pl pr
  | ⟨Zfan1l, pl, pr⟩ => mkZ Zfan0l pl pr
  | ⟨Zfan2l, pl, pr⟩ => mkZ Zfan1l pl pr
  | ⟨Zfan3l, pl, pr⟩ => mkZ Zfan2l pl pr
  | ⟨_, pl, pr⟩ => mkZ Znil pl pr

def zstepRt (ctx : Context) (zp : ZPart) : ZPart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftR ctx Zhubr zp
  | ⟨Zhubl, _, _⟩ => zshiftL ctx Zhubl zp
  | ⟨Zhubr, pl, pr⟩ => mkZ Zhat pl pr
  | ⟨Zhat, pl, pr⟩ => mkZ (zfanR pl) pl pr
  | ⟨Zhatl, pl, pr⟩ => mkZ Zhub pl pr
  | ⟨Zhatr, _, pr⟩ => zshiftR ctx (zfanLt pr) zp
  | ⟨Zfan0r, _, _⟩ => zshiftL ctx Zhatl zp
  | ⟨Zfan1r, pl, pr⟩ => mkZ Zfan0r pl pr
  | ⟨Zfan2r, pl, pr⟩ => mkZ Zfan1r pl pr
  | ⟨Zfan3r, pl, pr⟩ => mkZ Zfan2r pl pr
  | ⟨_, pl, pr⟩ => mkZ Znil pl pr

theorem zpvalid_zshiftL
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrap : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (loc : ZPartLoc) {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zshiftL ctx loc zp) := by
  rcases zp with ⟨loc', pl, pr⟩
  cases pl with
  | Pnil =>
      simpa [zpvalid, zshiftL, zvalid] using hwrap
  | Pcons s h tail =>
      cases tail <;> simp [zpvalid, zshiftL, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons6 h f1 tail =>
      cases tail <;> simp [zpvalid, zshiftL, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons7 h f1 f2 tail =>
      cases tail <;> simp [zpvalid, zshiftL, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;> simp [zpvalid, zshiftL, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid

theorem zpvalid_zshiftR
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrap : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r))
    (loc : ZPartLoc) {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zshiftR ctx loc zp) := by
  rcases zp with ⟨loc', pl, pr⟩
  cases pr with
  | Pnil =>
      simpa [zpvalid, zshiftR, zvalid] using hwrap
  | Pcons s h tail =>
      cases tail <;> simp [zpvalid, zshiftR, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons6 h f1 tail =>
      cases tail <;> simp [zpvalid, zshiftR, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons7 h f1 f2 tail =>
      cases tail <;> simp [zpvalid, zshiftR, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;> simp [zpvalid, zshiftR, zvalid, mkZ] at hvalid ⊢
      · exact hinit
      · exact hvalid
      · exact hvalid
      · exact hvalid
      · exact hvalid

theorem zpvalid_stepL
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrapL : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (hwrapR : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r))
    {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zstepL ctx zp) := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc
  · simpa [zstepL, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhubl hvalid
  · simpa [zstepL, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR Zhubr hvalid
  · exact zpvalid_zshiftR hinit hwrapR (zfanL pr) hvalid
  · simpa [zstepL, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepL, zpvalid, zvalid, mkZ] using hvalid
  all_goals simpa [zstepL, zpvalid, zvalid, mkZ] using hvalid

theorem zpvalid_stepR
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrapL : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (hwrapR : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r))
    {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zstepR ctx zp) := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR Zhubr hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhubl hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR (zfanL pr) hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhatl hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepR, zpvalid, zvalid, mkZ] using hvalid

theorem zpvalid_stepLt
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrapL : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (hwrapR : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r))
    {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zstepLt ctx zp) := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc
  · simpa [zstepLt, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhubl hvalid
  · simpa [zstepLt, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR Zhubr hvalid
  · exact zpvalid_zshiftR hinit hwrapR (zfanL pr) hvalid
  · simpa [zstepLt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepLt, zpvalid, zvalid, mkZ] using hvalid
  all_goals simpa [zstepLt, zpvalid, zvalid, mkZ] using hvalid

theorem zpvalid_stepRt
    {ctx : Context}
    (hinit : zvalid ctx ctx.p0l ctx.p0r)
    (hwrapL : zvalid ctx (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (hwrapR : zvalid ctx (shiftPart ctx.p0r ctx.p0l) (Part.drop 1 ctx.p0r))
    {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    zpvalid ctx (zstepRt ctx zp) := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR Zhubr hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhubl hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftR hinit hwrapR (zfanLt pr) hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · exact zpvalid_zshiftL hinit hwrapL Zhatl hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid
  · simpa [zstepRt, zpvalid, zvalid, mkZ] using hvalid

theorem zshiftL_proper (ctx : Context) (loc : ZPartLoc) (zp : ZPart) :
    (zshiftL ctx loc zp).proper = locProper loc := by
  rcases zp with ⟨loc', pl, pr⟩
  cases pl with
  | Pnil =>
      cases loc <;> rfl
  | Pcons s h tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons6 h f1 tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons7 h f1 f2 tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;> cases loc <;> rfl

theorem zshiftR_proper (ctx : Context) (loc : ZPartLoc) (zp : ZPart) :
    (zshiftR ctx loc zp).proper = locProper loc := by
  rcases zp with ⟨loc', pl, pr⟩
  cases pr with
  | Pnil =>
      cases loc <;> rfl
  | Pcons s h tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons6 h f1 tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons7 h f1 f2 tail =>
      cases tail <;> cases loc <;> rfl
  | Pcons8 h f1 f2 f3 tail =>
      cases tail <;> cases loc <;> rfl

theorem zproper_stepL
    {ctx : Context} {zp : ZPart}
    (hproper : (zstepL ctx zp).proper = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;>
    simp [zstepL, ZPart.proper, mkZ] at hproper ⊢

theorem zproper_stepR
    {ctx : Context} {zp : ZPart}
    (hproper : (zstepR ctx zp).proper = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;>
    simp [zstepR, ZPart.proper, mkZ] at hproper ⊢

theorem zproper_stepLt
    {ctx : Context} {zp : ZPart}
    (hproper : (zstepLt ctx zp).proper = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;>
    simp [zstepLt, ZPart.proper, mkZ] at hproper ⊢

theorem zproper_stepRt
    {ctx : Context} {zp : ZPart}
    (hproper : (zstepRt ctx zp).proper = true) :
    zp.proper = true := by
  rcases zp with ⟨loc, pl, pr⟩
  cases loc <;>
    simp [zstepRt, ZPart.proper, mkZ] at hproper ⊢


end RedPart

end FourColor

end Schematic.Math.GraphTheory
