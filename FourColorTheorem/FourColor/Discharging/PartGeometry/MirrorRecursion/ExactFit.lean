import FourColorTheorem.FourColor.Discharging.PartGeometry.MirrorRecursion.MirrorFit
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem exactFitp_mirror_true_of_exactFitp_mirror_true
    (hPlain : G.Plain) (hCubic : G.Cubic)
    {p : Part} {x : G.Dart}
    (hfit : exactFitp G.mirror x p = true) :
    exactFitp G x (mirror p) = true := by
  by_cases hp : p = Pnil
  · subst p
    have hfits := hfit
    simp [exactFitp, fitp, mirror, mirrorRec, size] at hfits ⊢
    simpa [G.arity_mirror x] using hfits
  · have hfits := hfit
    simp [exactFitp] at hfits
    rcases hfits with ⟨hsizeMirror, hfitp⟩
    have hsizeG : G.arity x = p.size := by
      simpa [G.arity_mirror x] using hsizeMirror
    have hboundary :
        getHat p (G.arity (SubpartLoc.move SubpartLoc.Phat G x)) = true := by
      rcases fitp_nextHat_or_pnil (G := G.mirror) (getHat p) hfitp with
        hnil | hhat
      · exact (hp hnil).elim
      · simpa [SubpartLoc.arity_mirror_hat (G := G) hPlain hCubic x] using hhat
    have hfitMirror :=
      fitp_mirrorRec_true_of_fitp_mirror_true
        (G := G) hPlain hCubic (getHat p) (p := p) (q := Pnil) (x := x)
        (by simpa [size] using hsizeG)
        (by simpa [nextHat] using (nextHat_getHat p).symm)
        (by simpa [size] using hboundary)
        (by simp [fitp])
        hfitp
    have hfitMirror' : fitp G x (mirror p) = true := by
      simpa [mirror, size] using hfitMirror
    simp [exactFitp, hsizeG, hfitMirror']

theorem exactFitp_mirror
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (p : Part) (x : G.Dart) :
    exactFitp G x (mirror p) = exactFitp G.mirror x p := by
  cases hleft : exactFitp G x (mirror p) <;>
    cases hright : exactFitp G.mirror x p
  · rfl
  · have hleftTrue := exactFitp_mirror_true_of_exactFitp_mirror_true
      (G := G) hPlain hCubic (p := p) (x := x) hright
    simp [hleft] at hleftTrue
  · have hinput :
        exactFitp G.mirror.mirror x (mirror p) = true := by
      convert hleft using 2
      exact Hypermap.mirror_mirror (G := G)
    have hrightTrue := exactFitp_mirror_true_of_exactFitp_mirror_true
      (G := G.mirror) hPlain.mirror hCubic.mirror
      (p := mirror p) (x := x) hinput
    simp [hright, mirror_mirror] at hrightTrue
  · rfl

end

end Part

end FourColor

end Schematic.Math.GraphTheory
