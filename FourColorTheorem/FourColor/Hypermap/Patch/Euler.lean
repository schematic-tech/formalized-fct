import FourColorTheorem.FourColor.Hypermap.Patch.Coloring
import FourColorTheorem.FourColor.Hypermap.Patch.EdgeNodeCounts
import FourColorTheorem.FourColor.Hypermap.Patch.FaceCounts
import FourColorTheorem.FourColor.Hypermap.Patch.ComponentCounts

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

theorem eulerLeft_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.eulerLeft + Gr.eulerLeft =
      G.eulerLeft + 2 * (if bGd = [] then 0 else 1) + bGd.length := by
  have hcomp := P.componentCount_patch
  have hcard := P.card_patch
  simp only [Hypermap.eulerLeft]
  omega

theorem eulerRight_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.eulerRight + Gr.eulerRight =
      G.eulerRight + 2 * (if bGd = [] then 0 else 1) + bGd.length := by
  have hedge := P.edgeOrbitCount_patch
  have hnode := P.nodeOrbitCount_patch
  have hface := P.faceOrbitCount_patch
  simp only [Hypermap.eulerRight]
  omega

/-- Coq `genus_patch`: gluing a disk and remainder along a patch boundary
adds their genera. -/
theorem genus_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.genus = Gd.genus + Gr.genus := by
  have hleft := P.eulerLeft_patch
  have hright := P.eulerRight_patch
  have hG := Hypermap.evenGenus G
  have hGd := Hypermap.evenGenus Gd
  have hGr := Hypermap.evenGenus Gr
  change G.eulerLeft = 2 * G.genus + G.eulerRight at hG
  change Gd.eulerLeft = 2 * Gd.genus + Gd.eulerRight at hGd
  change Gr.eulerLeft = 2 * Gr.genus + Gr.eulerRight at hGr
  omega

/-- Coq `planar_patch`. -/
theorem eulerPlanar_iff
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.EulerPlanar ↔ Gd.EulerPlanar ∧ Gr.EulerPlanar := by
  simp [Hypermap.EulerPlanar, P.genus_patch]

theorem compatible_of_boundary_colors
    (P : Patch G Gd Gr hd hr bGd bGr)
    {kd : Gd.Dart → Color} {kr : Gr.Dart → Color}
    (hcolors :
      (Gd.colorsOn kd bGd).reverse = Gr.colorsOn kr bGr) :
    ∀ xd xr, hd xd = hr xr → kd xd = kr xr := by
  have hDartMaps :
      List.Forall₂ (fun xr xd => hr xr = hd xd) bGr bGd.reverse := by
    have hMapEq : bGr.map hr = bGd.reverse.map hd := by
      rw [List.map_reverse]
      exact P.map_boundaryR
    have hEq : List.Forall₂ Eq (bGr.map hr) (bGd.reverse.map hd) := by
      rw [List.forall₂_eq_eq_eq]
      exact hMapEq
    simpa only [List.forall₂_map_left_iff,
      List.forall₂_map_right_iff] using hEq
  have hColorMaps :
      List.Forall₂ (fun xr xd => kr xr = kd xd) bGr bGd.reverse := by
    have hMapEq : bGr.map kr = bGd.reverse.map kd := by
      rw [List.map_reverse]
      simpa [Hypermap.colorsOn] using hcolors.symm
    have hEq : List.Forall₂ Eq (bGr.map kr) (bGd.reverse.map kd) := by
      rw [List.forall₂_eq_eq_eq]
      exact hMapEq
    simpa only [List.forall₂_map_left_iff,
      List.forall₂_map_right_iff] using hEq
  intro xd xr hmap
  have hxrBoundary : xr ∈ bGr :=
    (P.remainder_boundary_iff_disk_overlap xr).2 ⟨xd, hmap⟩
  obtain ⟨i, hi, hixr⟩ := List.getElem_of_mem hxrBoundary
  have hiD : i < bGd.reverse.length := by
    rw [← hDartMaps.length_eq]
    exact hi
  have hDart := hDartMaps.get hi hiD
  have hColor := hColorMaps.get hi hiD
  have hixr' : bGr.get ⟨i, hi⟩ = xr := hixr
  rw [hixr'] at hDart hColor
  have hxd : xd = bGd.reverse.get ⟨i, hiD⟩ :=
    P.injd (hmap.trans hDart)
  rw [hxd]
  exact hColor.symm

/-- Exact Coq `colorable_patch`, including the reversed and one-step-rotated
boundary trace. -/
theorem colorable_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.FourColorable ↔
      ∃ et : ColSeq,
        Gd.RingTrace bGd et ∧
          Gr.RingTrace bGr (ColSeq.rot1 et.reverse) := by
  constructor
  · rintro ⟨k, hk⟩
    let kd : Gd.Dart → Color := k ∘ hd
    let kr : Gr.Dart → Color := k ∘ hr
    have hkd : Gd.Coloring kd := by
      constructor
      · intro xd hsame
        apply hk.1 (hd xd)
        calc
          k (G.edge (hd xd)) = k (hd (Gd.edge xd)) :=
            Coloring.eq_of_face_reachable (G := G) hk
              (P.map_edgeD_face_reachable_host_edge xd)
          _ = k (hd xd) := hsame
      · intro xd
        exact Coloring.eq_of_face_reachable (G := G) hk
          (P.map_faceD_reachable xd)
    have hkr : Gr.Coloring kr := by
      constructor
      · intro xr hsame
        apply hk.1 (hr xr)
        calc
          k (G.edge (hr xr)) = k (hr (Gr.edge xr)) := by
            rw [P.map_edgeR]
          _ = k (hr xr) := hsame
      · intro xr
        exact Coloring.eq_of_face_reachable (G := G) hk
          (P.map_faceR_reachable xr)
    let et := ColSeq.trace (Gd.colorsOn kd bGd)
    refine ⟨et, ⟨kd, hkd, rfl⟩, kr, hkr, ?_⟩
    have hBoundaryColors :
        Gr.colorsOn kr bGr = (Gd.colorsOn kd bGd).reverse := by
      have h := congrArg (List.map k) P.map_boundaryR
      simpa [Hypermap.colorsOn, kd, kr, List.map_map,
        Function.comp_def] using h
    calc
      ColSeq.rot1 et.reverse =
          ColSeq.trace (Gd.colorsOn kd bGd).reverse := by
        rw [ColSeq.trace_reverse]
      _ = ColSeq.trace (Gr.colorsOn kr bGr) := by
        rw [hBoundaryColors]
  · rintro ⟨et, ⟨kd, hkd, hEtD⟩, ⟨kr, hkr, hEtR⟩⟩
    let diskColors := Gd.colorsOn kd bGd
    let revDiskColors := diskColors.reverse
    let remColors := Gr.colorsOn kr bGr
    have htrace : ColSeq.trace revDiskColors =
        ColSeq.trace remColors := by
      calc
        ColSeq.trace revDiskColors =
            ColSeq.rot1 (ColSeq.trace diskColors).reverse := by
          exact ColSeq.trace_reverse diskColors
        _ = ColSeq.rot1 et.reverse := by rw [hEtD]
        _ = ColSeq.trace remColors := hEtR
    let shift := ColSeq.headColor revDiskColors +
      ColSeq.headColor remColors
    let kd' : Gd.Dart → Color := (fun c => shift + c) ∘ kd
    have hshiftInjective : Function.Injective (fun c : Color => shift + c) := by
      intro c d h
      exact Color.add_left_cancel h
    have hkd' : Gd.Coloring kd' := by
      exact Gd.coloring_of_injective_color_map hshiftInjective hkd
    have hBoundaryColors :
        (Gd.colorsOn kd' bGd).reverse = Gr.colorsOn kr bGr := by
      calc
        (Gd.colorsOn kd' bGd).reverse =
            revDiskColors.map (fun c => shift + c) := by
          simp [Hypermap.colorsOn, kd', revDiskColors, diskColors,
            List.map_map, Function.comp_def]
        _ = remColors := by
          simpa [shift] using
            ColSeq.map_headShift_eq_of_trace_eq
              revDiskColors remColors htrace
        _ = Gr.colorsOn kr bGr := rfl
    apply (P.fourColorable_iff_compatibleColorings).2
    exact ⟨kd', kr, hkd', hkr,
      P.compatible_of_boundary_colors hBoundaryColors⟩

end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
