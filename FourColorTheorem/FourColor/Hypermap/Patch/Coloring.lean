import FourColorTheorem.FourColor.Hypermap.Patch.Topology

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

set_option linter.unusedVariables false in
/-- The semantic core beneath Coq `colorable_patch`: colorings of the two
parts agree at every dart of their common boundary image. -/
def CompatibleColorings
    (P : Patch G Gd Gr hd hr bGd bGr) : Prop :=
  ∃ kd : Gd.Dart → Color, ∃ kr : Gr.Dart → Color,
    Gd.Coloring kd ∧ Gr.Coloring kr ∧
      ∀ xd xr, hd xd = hr xr → kd xd = kr xr

theorem fourColorable_iff_compatibleColorings
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.FourColorable ↔ P.CompatibleColorings := by
  constructor
  · rintro ⟨k, hk⟩
    let kd : Gd.Dart → Color := k ∘ hd
    let kr : Gr.Dart → Color := k ∘ hr
    have hkd : Gd.Coloring kd := by
      constructor
      · intro xd hsame
        apply hk.1 (hd xd)
        have hedgeColor :
            k (G.edge (hd xd)) = k (hd (Gd.edge xd)) :=
          Coloring.eq_of_face_reachable (G := G) hk
            (P.map_edgeD_face_reachable_host_edge xd)
        exact hedgeColor.trans hsame
      · intro xd
        exact Coloring.eq_of_face_reachable (G := G) hk
          (P.map_faceD_reachable xd)
    have hkr : Gr.Coloring kr := by
      constructor
      · intro xr hsame
        apply hk.1 (hr xr)
        rw [← P.map_edgeR xr]
        exact hsame
      · intro xr
        exact Coloring.eq_of_face_reachable (G := G) hk
          (P.map_faceR_reachable xr)
    exact ⟨kd, kr, hkd, hkr, fun xd xr hmap => congrArg k hmap⟩
  · rintro ⟨kd, kr, hkd, hkr, hcompat⟩
    classical
    let k : G.Dart → Color := fun x =>
      if hxR : P.InRemainderImage x then
        kr (Classical.choose hxR)
      else
        kd (Classical.choose (Or.resolve_right (P.cover x) hxR))
    have hkR (xr : Gr.Dart) : k (hr xr) = kr xr := by
      have hxR : P.InRemainderImage (hr xr) := ⟨xr, rfl⟩
      rw [show k (hr xr) = kr (Classical.choose hxR) by simp [k, hxR]]
      apply congrArg kr
      apply P.injr
      exact Classical.choose_spec hxR
    have hkD (xd : Gd.Dart) : k (hd xd) = kd xd := by
      by_cases hxR : P.InRemainderImage (hd xd)
      · let xr := Classical.choose hxR
        have hxrMap : hr xr = hd xd := Classical.choose_spec hxR
        calc
          k (hd xd) = kr xr := by simp [k, hxR, xr]
          _ = kd xd := (hcompat xd xr hxrMap.symm).symm
      · let hxD : P.InDiskImage (hd xd) :=
          Or.resolve_right (P.cover (hd xd)) hxR
        let yd := Classical.choose hxD
        have hydMap : hd yd = hd xd := Classical.choose_spec hxD
        calc
          k (hd xd) = kd yd := by simp [k, hxR, yd]
          _ = kd xd := congrArg kd (P.injd hydMap)
    refine ⟨k, ?_, ?_⟩
    · intro x hsame
      by_cases hxR : P.InRemainderImage x
      · rcases hxR with ⟨xr, rfl⟩
        apply hkr.1 xr
        calc
          kr (Gr.edge xr) = k (hr (Gr.edge xr)) := (hkR _).symm
          _ = k (G.edge (hr xr)) := by rw [P.map_edgeR]
          _ = k (hr xr) := hsame
          _ = kr xr := hkR xr
      · rcases P.cover x with ⟨xd, hxdMap⟩ | hxR'
        · have hxRD : ¬ P.InRemainderImage (hd xd) := by
            intro h
            exact hxR (by simpa [hxdMap] using h)
          have hsameD : k (G.edge (hd xd)) = k (hd xd) := by
            simpa [hxdMap] using hsame
          have hxdOff : xd ∉ bGd := by
            intro hxdBoundary
            exact hxRD
              ((P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary)
          apply hkd.1 xd
          calc
            kd (Gd.edge xd) = k (hd (Gd.edge xd)) := (hkD _).symm
            _ = k (G.edge (hd xd)) := by rw [P.map_edgeD xd hxdOff]
            _ = k (hd xd) := hsameD
            _ = kd xd := hkD xd
        · exact False.elim (hxR hxR')
    · intro x
      by_cases hxR : P.InRemainderImage x
      · rcases hxR with ⟨xr, rfl⟩
        by_cases hfaceR : P.InRemainderImage (G.face (hr xr))
        · rcases hfaceR with ⟨yr, hyrMap⟩
          have hreachHost :
              PermReachable G.face (hr xr) (hr yr) := by
            rw [hyrMap]
            exact PermReachable.forward G.face (hr xr)
          have hreachR : PermReachable Gr.face xr yr :=
            (P.map_faceR_reachable_iff xr yr).2 hreachHost
          calc
            k (G.face (hr xr)) = k (hr yr) := congrArg k hyrMap.symm
            _ = kr yr := hkR yr
            _ = kr xr :=
              Coloring.eq_of_face_reachable (G := Gr) hkr hreachR
            _ = k (hr xr) := (hkR xr).symm
        · rcases P.cover (G.face (hr xr)) with
            ⟨yd, hydMap⟩ | hfaceR'
          · let zd : Gd.Dart := Gd.face.symm yd
            have hcross : hd zd = hr (Gr.face xr) := by
              apply
                (P.map_faceD_eq_face_mapR_iff_mapD_eq_map_faceR zd xr).1
              simpa [zd] using hydMap
            have hkdFace : kd yd = kd zd := by
              simpa [zd] using hkd.2 zd
            calc
              k (G.face (hr xr)) = k (hd yd) := congrArg k hydMap.symm
              _ = kd yd := hkD yd
              _ = kd zd := hkdFace
              _ = kr (Gr.face xr) := hcompat zd (Gr.face xr) hcross
              _ = kr xr := hkr.2 xr
              _ = k (hr xr) := (hkR xr).symm
          · exact False.elim (hfaceR hfaceR')
      · rcases P.cover x with ⟨xd, hxdMap⟩ | hxR'
        · have hxRD : ¬ P.InRemainderImage (hd xd) := by
            intro h
            exact hxR (by simpa [hxdMap] using h)
          have hxdOff : xd ∉ bGd := by
            intro hxdBoundary
            exact hxRD
              ((P.disk_boundary_iff_remainder_overlap xd).1 hxdBoundary)
          calc
            k (G.face x) = k (G.face (hd xd)) := by rw [hxdMap]
            _ = k (hd (Gd.face xd)) := by
              rw [P.map_faceD_of_not_boundary xd hxdOff]
            _ = kd (Gd.face xd) := hkD (Gd.face xd)
            _ = kd xd := hkd.2 xd
            _ = k (hd xd) := (hkD xd).symm
            _ = k x := congrArg k hxdMap
        · exact False.elim (hxR hxR')
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
