import FourColorTheorem.FourColor.Reducibility.RedPartSoundness.Branches.Hub

namespace Schematic.Math.GraphTheory.FourColor.RedPart

open Part
open ZPartLoc

universe u

open SoundnessInternal
/-- One-step semantic contradiction for the executable redpart zipper step.
This is the branch-heavy target corresponding to Coq's `red_partP`; the
loop-level theorems below show that this is enough for the bounded search. -/
def RedZPartStepSound
    (_G : Hypermap.{u}) (ctx : Context) : Prop :=
  ∀ (zp : ZPart),
    zpvalid ctx zp →
      redZPartStep ctx zp = true →
        False

theorem zpvalid_iterate_zshiftR_zhub
    {ctx : Context}
    (hshift : ∀ ⦃zp : ZPart⦄,
      zpvalid ctx zp → zpvalid ctx (zshiftR ctx Zhub zp))
    {zp : ZPart}
    (hvalid : zpvalid ctx zp) :
    ∀ i : Nat,
      zpvalid ctx (((fun z : ZPart => zshiftR ctx Zhub z)^[i]) zp)
  | 0 => hvalid
  | i + 1 => by
      simpa [Function.iterate_succ_apply'] using
        hshift (zpvalid_iterate_zshiftR_zhub hshift hvalid i)

theorem false_of_redZPartRec_of_stepSound
    {G : Hypermap.{u}} {ctx : Context}
    {zp : ZPart} {d : Nat}
    (hshift : ∀ ⦃zp : ZPart⦄,
      zpvalid ctx zp → zpvalid ctx (zshiftR ctx Zhub zp))
    (hstep : RedZPartStepSound G ctx)
    (hvalid : zpvalid ctx zp)
    (hred : redZPartRec ctx zp d = true) :
    False := by
  rcases redZPartRec_exists_step ctx hred with ⟨i, _hi, hstepi⟩
  exact hstep
    (((fun z : ZPart => zshiftR ctx Zhub z)^[i]) zp)
    (zpvalid_iterate_zshiftR_zhub hshift hvalid i) hstepi

theorem false_of_redZPart_of_stepSound_reverse
    {G : Hypermap.{u}} {ctx : Context}
    (hleft : ctx.p0l = Part.reverse ctx.p0r)
    (hstep : RedZPartStepSound G ctx)
    (hred : redZPart ctx = true) :
    False := by
  exact false_of_redZPartRec_of_stepSound
    (G := G) (ctx := ctx)
    (zp := mkZ Zhub (Part.drop 1 ctx.p0l) (shiftPart ctx.p0l ctx.p0r))
    (d := ctx.nhub)
    (fun {zp} hvalid =>
      zpvalid_zshiftR
        (zvalid_init ctx hleft)
        (zvalid_wrapR ctx hleft)
        Zhub hvalid)
    hstep
    (by simpa [zpvalid, mkZ] using zvalid_wrapL ctx hleft)
    hred

theorem redpartLoopSound_succ_of_stepSound
    {G : Hypermap.{u}} {qt : QuizTree} {ahub : QArity} {d : Nat}
    (hstep :
      ∀ (x : G.Dart) (p : Part),
        G.arity x = ahub.toNat →
          Part.exactFitp G x p = true →
            RedZPartStepSound G
              { qt := qt
                ahub := ahub
                redRec := fun q => redpartLoop qt ahub d q
                p0l := Part.reverse p
                p0r := p }) :
    RedpartLoopSound G qt ahub (d + 1) := by
  intro x p hx hred
  cases hfit : Part.exactFitp G x p
  · rfl
  · have hctxRed :
        redZPart
          { qt := qt
            ahub := ahub
            redRec := fun q => redpartLoop qt ahub d q
            p0l := Part.reverse p
            p0r := p } = true := by
      simpa [redpartLoop] using hred
    exact False.elim
      (false_of_redZPart_of_stepSound_reverse
        (G := G)
        (ctx :=
          { qt := qt
            ahub := ahub
            redRec := fun q => redpartLoop qt ahub d q
            p0l := Part.reverse p
            p0r := p })
        rfl (hstep x p hx hfit) hctxRed)

theorem redpartLoopSound_succ_of_noQuizTreeFit
    {G : Hypermap.{u}} {qt : QuizTree} {ahub : QArity} {d : Nat}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hnofit : NoQuizTreeFit G qt)
    (hloopSound : RedpartLoopSound G qt ahub d) :
    RedpartLoopSound G qt ahub (d + 1) := by
  intro x p hx hred
  by_cases hfit : Part.exactFitp G x p = true
  · have hctxRed :
        redZPart
          { qt := qt
            ahub := ahub
            redRec := fun q => redpartLoop qt ahub d q
            p0l := Part.reverse p
            p0r := p } = true := by
      simpa [redpartLoop] using hred
    exact False.elim
      (false_of_redZPart_of_reverse_exact_and_noFit
        (G := G)
        (ctx :=
          { qt := qt
            ahub := ahub
            redRec := fun q => redpartLoop qt ahub d q
            p0l := Part.reverse p
            p0r := p })
        (x0 := x)
        hPlain hCubic
        (noRedRec_of_redpartLoopSound
          (G := G) (qt := qt) (ahub := ahub) (d := d)
          (p0l := Part.reverse p) (p0r := p) hloopSound)
        rfl hfit
        (by simpa [Context.nhub] using hx)
        hnofit hctxRed)
  · cases h : Part.exactFitp G x p
    · rfl
    · exact False.elim (hfit h)

theorem redpartLoopSound_of_noQuizTreeFit
    {G : Hypermap.{u}} {qt : QuizTree} {ahub : QArity}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hnofit : NoQuizTreeFit G qt) :
    ∀ d : Nat, RedpartLoopSound G qt ahub d
  | 0 => redpartLoopSound_zero G qt ahub
  | d + 1 =>
      redpartLoopSound_succ_of_noQuizTreeFit
        (G := G) (qt := qt) (ahub := ahub) (d := d)
        hPlain hCubic hnofit
        (redpartLoopSound_of_noQuizTreeFit
          (G := G) (qt := qt) (ahub := ahub)
          hPlain hCubic hnofit d)

theorem exactFitp_eq_false_of_redpart_of_noQuizTreeFit
    {G : Hypermap.{u}} {qt : QuizTree} {p : Part} {x : G.Dart}
    (hPlain : G.Plain)
    (hCubic : G.Cubic)
    (hnofit : NoQuizTreeFit G qt)
    (hred : redpart qt p = true)
    (hx : G.arity x = Part.size p) :
    Part.exactFitp G x p = false := by
  have hredParts := redpart_true_size_and_loop (qt := qt) (p := p) hred
  have hbounds := QArity.bounds_of_sizeCheck hredParts.1
  have hqa :
      (QArity.ofNatCode (Part.size p)).toNat = Part.size p :=
    QArity.toNat_ofNatCode_eq_of_le hbounds.1 hbounds.2
  exact
    redpartLoopSound_of_noQuizTreeFit
      (G := G) (qt := qt) (ahub := QArity.ofNatCode (Part.size p))
      hPlain hCubic hnofit (Part.size p * 12)
      x p
      (by rw [hqa]; exact hx)
      hredParts.2


end Schematic.Math.GraphTheory.FourColor.RedPart
