import FourColorTheorem.FourColor.Hypermap.OrbitRestriction
import FourColorTheorem.FourColor.Hypermap.EulerInequality
import Schematic.Math.GraphTheory.Embedding.Geometry
import FourColorTheorem.FourColor.Coloring.RingTrace

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

/-- Coq `patch hd hr bGd bGr`: `G` is obtained by gluing the disk `Gd` to
the remainder `Gr` along the listed edge/node boundary cycles. -/
structure Patch
    (G : Hypermap.{w}) (Gd : Hypermap.{u}) (Gr : Hypermap.{v})
    (hd : Gd.Dart → G.Dart) (hr : Gr.Dart → G.Dart)
    (bGd : List Gd.Dart) (bGr : List Gr.Dart) : Prop where
  injd : Function.Injective hd
  injr : Function.Injective hr
  cycleD : FunctionCycle Gd.edge bGd
  boundaryD_faceSimple : Gd.FaceSimple bGd
  cycleR : FunctionCycle Gr.node bGr
  boundaryR_nodup : bGr.Nodup
  map_boundaryR : bGr.map hr = (bGd.map hd).reverse
  coverR : ∀ x : G.Dart,
    (∃ xr : Gr.Dart, hr xr = x) ↔
      (¬ ∃ xd : Gd.Dart, hd xd = x) ∨ x ∈ bGd.map hd
  map_edgeD : ∀ xd : Gd.Dart, xd ∉ bGd →
    hd (Gd.edge xd) = G.edge (hd xd)
  map_nodeD : ∀ xd : Gd.Dart,
    hd (Gd.node xd) = G.node (hd xd)
  map_edgeR : ∀ xr : Gr.Dart,
    hr (Gr.edge xr) = G.edge (hr xr)
  map_nodeR : ∀ xr : Gr.Dart, xr ∉ bGr →
    hr (Gr.node xr) = G.node (hr xr)

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

/-- The uniqueness part of Coq `sfcycle`, derived from face-simplicity. -/
theorem boundaryD_nodup
    (P : Patch G Gd Gr hd hr bGd bGr) :
    bGd.Nodup :=
  P.boundaryD_faceSimple.nodup

/-- Plainness away from a distinguished boundary.  This is the Prop-valued
form of Coq `plainb [predC b]`. -/
def PlainOff (H : Hypermap.{z}) (b : List H.Dart) : Prop :=
  ∀ x : H.Dart, x ∉ b →
    H.edge (H.edge x) = x ∧ H.edge x ≠ x

def InDiskImage
    (_P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) : Prop :=
  ∃ xd : Gd.Dart, hd xd = x

def InRemainderImage
    (_P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) : Prop :=
  ∃ xr : Gr.Dart, hr xr = x

def OnBoundary
    (_P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) : Prop :=
  x ∈ bGd.map hd

theorem boundary_image_nodup
    (P : Patch G Gd Gr hd hr bGd bGr) :
    (bGd.map hd).Nodup :=
  P.boundaryD_nodup.map P.injd

theorem onBoundary_of_disk_boundary
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd : Gd.Dart} (hxd : xd ∈ bGd) :
    P.OnBoundary (hd xd) := by
  exact List.mem_map.mpr ⟨xd, hxd, rfl⟩

theorem inDiskImage_of_onBoundary
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x : G.Dart} (hx : P.OnBoundary x) :
    P.InDiskImage x := by
  rcases List.mem_map.mp hx with ⟨xd, hxd, rfl⟩
  exact ⟨xd, rfl⟩

theorem inRemainderImage_of_onBoundary
    (P : Patch G Gd Gr hd hr bGd bGr)
    {x : G.Dart} (hx : P.OnBoundary x) :
    P.InRemainderImage x := by
  have hx' : x ∈ bGr.map hr := by
    rw [P.map_boundaryR]
    simpa [OnBoundary] using hx
  rcases List.mem_map.mp hx' with ⟨xr, hxr, hxrEq⟩
  exact ⟨xr, hxrEq⟩

theorem cover
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.InDiskImage x ∨ P.InRemainderImage x := by
  by_cases hxd : P.InDiskImage x
  · exact Or.inl hxd
  · exact Or.inr ((P.coverR x).2 (Or.inl hxd))

/-- Coq's derived `im_hd`: the disk image is the complement of the remainder
image together with the common boundary. -/
theorem inDiskImage_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.InDiskImage x ↔ ¬ P.InRemainderImage x ∨ P.OnBoundary x := by
  constructor
  · intro hxd
    by_cases hxr : P.InRemainderImage x
    · rcases (P.coverR x).1 hxr with hnot | hb
      · exact False.elim (hnot hxd)
      · exact Or.inr hb
    · exact Or.inl hxr
  · rintro (hnot | hb)
    · rcases P.cover x with hxd | hxr
      · exact hxd
      · exact False.elim (hnot hxr)
    · exact P.inDiskImage_of_onBoundary hb

/-- The two patch images meet exactly on the glued boundary. -/
theorem in_both_iff_onBoundary
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.InDiskImage x ∧ P.InRemainderImage x ↔ P.OnBoundary x := by
  constructor
  · rintro ⟨hxd, hxr⟩
    rcases (P.coverR x).1 hxr with hnot | hb
    · exact False.elim (hnot hxd)
    · exact hb
  · intro hb
    exact ⟨P.inDiskImage_of_onBoundary hb,
      P.inRemainderImage_of_onBoundary hb⟩

theorem disk_boundary_iff_remainder_overlap
    (P : Patch G Gd Gr hd hr bGd bGr) (xd : Gd.Dart) :
    xd ∈ bGd ↔ P.InRemainderImage (hd xd) := by
  constructor
  · exact fun hxd =>
      P.inRemainderImage_of_onBoundary
        (P.onBoundary_of_disk_boundary hxd)
  · intro hxr
    have hb : P.OnBoundary (hd xd) :=
      (P.in_both_iff_onBoundary (hd xd)).1 ⟨⟨xd, rfl⟩, hxr⟩
    rcases List.mem_map.mp hb with ⟨yd, hyd, heq⟩
    exact P.injd heq ▸ hyd

theorem remainder_boundary_iff_disk_overlap
    (P : Patch G Gd Gr hd hr bGd bGr) (xr : Gr.Dart) :
    xr ∈ bGr ↔ P.InDiskImage (hr xr) := by
  constructor
  · intro hxr
    have hmem : hr xr ∈ bGr.map hr := List.mem_map.mpr ⟨xr, hxr, rfl⟩
    rw [P.map_boundaryR] at hmem
    exact P.inDiskImage_of_onBoundary (by simpa [OnBoundary] using hmem)
  · intro hxd
    have hb : P.OnBoundary (hr xr) :=
      (P.in_both_iff_onBoundary (hr xr)).1 ⟨hxd, ⟨xr, rfl⟩⟩
    have hmem : hr xr ∈ bGr.map hr := by
      rw [P.map_boundaryR]
      simpa [OnBoundary] using hb
    rcases List.mem_map.mp hmem with ⟨yr, hyr, heq⟩
    exact P.injr heq ▸ hyr

/-- Coq `hdErN`: crossing the glued boundary by a disk edge step is the same
as crossing it in the opposite orientation by a remainder node step. -/
theorem map_edgeD_eq_mapR_iff_mapD_eq_map_nodeR
    (P : Patch G Gd Gr hd hr bGd bGr)
    (xd : Gd.Dart) (xr : Gr.Dart) :
    hd (Gd.edge xd) = hr xr ↔ hd xd = hr (Gr.node xr) := by
  classical
  letI : Nonempty Gd.Dart := ⟨xd⟩
  letI : Nonempty Gr.Dart := ⟨xr⟩
  let ed : G.Dart → G.Dart := fun x =>
    hd (Gd.edge (Function.invFun hd x))
  let nr : G.Dart → G.Dart := fun x =>
    hr (Gr.node (Function.invFun hr x))
  have hEd (yd : Gd.Dart) : ed (hd yd) = hd (Gd.edge yd) := by
    change hd (Gd.edge (Function.invFun hd (hd yd))) = hd (Gd.edge yd)
    rw [Function.leftInverse_invFun P.injd]
  have hNr (yr : Gr.Dart) : nr (hr yr) = hr (Gr.node yr) := by
    change hr (Gr.node (Function.invFun hr (hr yr))) = hr (Gr.node yr)
    rw [Function.leftInverse_invFun P.injr]
  have hcEd : FunctionCycle ed (bGd.map hd) :=
    P.cycleD.map fun yd _ => hEd yd
  have hcNr0 : FunctionCycle nr (bGr.map hr) :=
    P.cycleR.map fun yr _ => hNr yr
  have hcNr : FunctionCycle nr (bGd.map hd).reverse := by
    rw [← P.map_boundaryR]
    exact hcNr0
  have hn : (bGd.map hd).Nodup := P.boundary_image_nodup
  constructor
  · intro hcross
    have hedgeBoundary : Gd.edge xd ∈ bGd :=
      (P.disk_boundary_iff_remainder_overlap (Gd.edge xd)).2
        ⟨xr, hcross.symm⟩
    have hxdBoundary : xd ∈ bGd :=
      (FunctionCycle.image_mem_iff P.cycleD Gd.edge.injective xd).1
        hedgeBoundary
    have hxdImage : hd xd ∈ bGd.map hd :=
      List.mem_map.mpr ⟨xd, hxdBoundary, rfl⟩
    have hinv := hcEd.reverse_leftInverse hcNr hn hxdImage
    calc
      hd xd = nr (ed (hd xd)) := hinv.symm
      _ = nr (hd (Gd.edge xd)) := by rw [hEd]
      _ = nr (hr xr) := by rw [hcross]
      _ = hr (Gr.node xr) := hNr xr
  · intro hcross
    have hnodeBoundary : Gr.node xr ∈ bGr :=
      (P.remainder_boundary_iff_disk_overlap (Gr.node xr)).2
        ⟨xd, hcross⟩
    have hxrBoundary : xr ∈ bGr :=
      (FunctionCycle.image_mem_iff P.cycleR Gr.node.injective xr).1
        hnodeBoundary
    have hxrImageR : hr xr ∈ bGr.map hr :=
      List.mem_map.mpr ⟨xr, hxrBoundary, rfl⟩
    have hxrImageD : hr xr ∈ bGd.map hd := by
      rw [← List.mem_reverse]
      rw [← P.map_boundaryR]
      exact hxrImageR
    have hinv := hcEd.reverse_rightInverse hcNr hn hxrImageD
    calc
      hd (Gd.edge xd) = ed (hd xd) := (hEd xd).symm
      _ = ed (hr (Gr.node xr)) := by rw [hcross]
      _ = ed (nr (hr xr)) := by rw [hNr]
      _ = hr xr := hinv

/-- Coq `bGdP`: every disk-boundary dart has a consistently oriented
remainder-boundary companion. -/
theorem exists_remainder_boundary_companion
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xd : Gd.Dart} (hxd : xd ∈ bGd) :
    ∃ xr : Gr.Dart,
      hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  have hedgeBoundary : Gd.edge xd ∈ bGd := P.cycleD.image_mem hxd
  rcases (P.disk_boundary_iff_remainder_overlap (Gd.edge xd)).1
      hedgeBoundary with ⟨xr, hxr⟩
  refine ⟨xr, hxr.symm, ?_⟩
  exact (P.map_edgeD_eq_mapR_iff_mapD_eq_map_nodeR xd xr).1 hxr.symm

/-- Coq `bGrP`: every remainder-boundary dart has a consistently oriented
disk-boundary companion. -/
theorem exists_disk_boundary_companion
    (P : Patch G Gd Gr hd hr bGd bGr)
    {xr : Gr.Dart} (hxr : xr ∈ bGr) :
    ∃ xd : Gd.Dart,
      hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  rcases (P.remainder_boundary_iff_disk_overlap xr).1 hxr with ⟨zd, hzd⟩
  let xd : Gd.Dart := Gd.edge.symm zd
  have hfirst : hd (Gd.edge xd) = hr xr := by
    simpa [xd] using hzd
  exact ⟨xd, hfirst,
    (P.map_edgeD_eq_mapR_iff_mapD_eq_map_nodeR xd xr).1 hfirst⟩

/-- Coq `card_patch`: the two dart sets overlap in exactly one copy of the
disk boundary. -/
theorem card_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Fintype.card Gd.Dart + Fintype.card Gr.Dart =
      bGd.length + Fintype.card G.Dart := by
  classical
  let D : Finset G.Dart := Finset.univ.image hd
  let R : Finset G.Dart := Finset.univ.image hr
  let B : Finset G.Dart := (bGd.map hd).toFinset
  have hDmem (x : G.Dart) : x ∈ D ↔ P.InDiskImage x := by
    simp [D, InDiskImage]
  have hRmem (x : G.Dart) : x ∈ R ↔ P.InRemainderImage x := by
    simp [R, InRemainderImage]
  have hBmem (x : G.Dart) : x ∈ B ↔ P.OnBoundary x := by
    simp [B, OnBoundary]
  have hUnion : D ∪ R = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rw [hDmem, hRmem]
    exact P.cover x
  have hInter : D ∩ R = B := by
    ext x
    simp only [Finset.mem_inter]
    rw [hDmem, hRmem, hBmem]
    exact P.in_both_iff_onBoundary x
  have hDcard : D.card = Fintype.card Gd.Dart := by
    simpa [D] using
      Finset.card_image_of_injective (Finset.univ : Finset Gd.Dart) P.injd
  have hRcard : R.card = Fintype.card Gr.Dart := by
    simpa [R] using
      Finset.card_image_of_injective (Finset.univ : Finset Gr.Dart) P.injr
  have hBcard : B.card = bGd.length := by
    simpa [B] using
      List.toFinset_card_of_nodup P.boundary_image_nodup
  have hIE := Finset.card_union_add_card_inter D R
  rw [hUnion, hInter, Finset.card_univ, hDcard, hRcard, hBcard] at hIE
  omega

/-- Coq `plain_patch`, in propositional form. -/
theorem plain_iff
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.Plain ↔ PlainOff Gd bGd ∧ Gr.Plain := by
  have hEdgeD (xd : Gd.Dart) :
      Gd.edge xd ∈ bGd ↔ xd ∈ bGd :=
    FunctionCycle.image_mem_iff P.cycleD Gd.edge.injective xd
  constructor
  · intro hplain
    constructor
    · intro xd hxd
      have hexd : Gd.edge xd ∉ bGd := by
        intro h
        exact hxd (hEdgeD xd |>.mp h)
      have hmap1 := P.map_edgeD xd hxd
      have hmap2 := P.map_edgeD (Gd.edge xd) hexd
      constructor
      · apply P.injd
        calc
          hd (Gd.edge (Gd.edge xd)) = G.edge (hd (Gd.edge xd)) := hmap2
          _ = G.edge (G.edge (hd xd)) := by rw [hmap1]
          _ = hd xd := (hplain (hd xd)).1
      · intro heq
        apply (hplain (hd xd)).2
        calc
          G.edge (hd xd) = hd (Gd.edge xd) := hmap1.symm
          _ = hd xd := congrArg hd heq
    · intro xr
      have hmap1 := P.map_edgeR xr
      have hmap2 := P.map_edgeR (Gr.edge xr)
      constructor
      · apply P.injr
        calc
          hr (Gr.edge (Gr.edge xr)) = G.edge (hr (Gr.edge xr)) := hmap2
          _ = G.edge (G.edge (hr xr)) := by rw [hmap1]
          _ = hr xr := (hplain (hr xr)).1
      · intro heq
        apply (hplain (hr xr)).2
        calc
          G.edge (hr xr) = hr (Gr.edge xr) := hmap1.symm
          _ = hr xr := congrArg hr heq
  · rintro ⟨hplainD, hplainR⟩ x
    by_cases hxr : P.InRemainderImage x
    · rcases hxr with ⟨xr, rfl⟩
      have hmap1 := P.map_edgeR xr
      have hmap2 := P.map_edgeR (Gr.edge xr)
      constructor
      · calc
          G.edge (G.edge (hr xr)) = G.edge (hr (Gr.edge xr)) := by rw [hmap1]
          _ = hr (Gr.edge (Gr.edge xr)) := hmap2.symm
          _ = hr xr := congrArg hr (hplainR xr).1
      · intro heq
        apply (hplainR xr).2
        apply P.injr
        calc
          hr (Gr.edge xr) = G.edge (hr xr) := hmap1
          _ = hr xr := heq
    · rcases P.cover x with hxd | hxr'
      · rcases hxd with ⟨xd, rfl⟩
        have hxdOff : xd ∉ bGd := by
          intro hmem
          exact hxr
            (P.inRemainderImage_of_onBoundary
              (P.onBoundary_of_disk_boundary hmem))
        have hexdOff : Gd.edge xd ∉ bGd := by
          intro hmem
          exact hxdOff ((hEdgeD xd).mp hmem)
        have hmap1 := P.map_edgeD xd hxdOff
        have hmap2 := P.map_edgeD (Gd.edge xd) hexdOff
        constructor
        · calc
            G.edge (G.edge (hd xd)) = G.edge (hd (Gd.edge xd)) := by rw [hmap1]
            _ = hd (Gd.edge (Gd.edge xd)) := hmap2.symm
            _ = hd xd := congrArg hd (hplainD xd hxdOff).1
        · intro heq
          apply (hplainD xd hxdOff).2
          apply P.injd
          calc
            hd (Gd.edge xd) = G.edge (hd xd) := hmap1
            _ = hd xd := heq
      · exact False.elim (hxr hxr')

/-- Coq `cubic_patch`, in propositional form. -/
theorem cubic_iff
    (P : Patch G Gd Gr hd hr bGd bGr) :
    G.Cubic ↔ Gd.Cubic ∧ Gr.Quasicubic bGr := by
  have hNodeR (xr : Gr.Dart) :
      Gr.node xr ∈ bGr ↔ xr ∈ bGr :=
    FunctionCycle.image_mem_iff P.cycleR Gr.node.injective xr
  constructor
  · intro hcubic
    constructor
    · intro xd
      have hmap1 := P.map_nodeD xd
      have hmap2 := P.map_nodeD (Gd.node xd)
      have hmap3 := P.map_nodeD (Gd.node (Gd.node xd))
      constructor
      · apply P.injd
        calc
          hd (Gd.node (Gd.node (Gd.node xd))) =
              G.node (hd (Gd.node (Gd.node xd))) := hmap3
          _ = G.node (G.node (hd (Gd.node xd))) := by rw [hmap2]
          _ = G.node (G.node (G.node (hd xd))) := by rw [hmap1]
          _ = hd xd := (hcubic (hd xd)).1
      · intro heq
        apply (hcubic (hd xd)).2
        calc
          G.node (hd xd) = hd (Gd.node xd) := hmap1.symm
          _ = hd xd := congrArg hd heq
    · intro xr hxr
      have hn1 : Gr.node xr ∉ bGr := by
        intro h
        exact hxr ((hNodeR xr).mp h)
      have hn2 : Gr.node (Gr.node xr) ∉ bGr := by
        intro h
        exact hn1 ((hNodeR (Gr.node xr)).mp h)
      have hmap1 := P.map_nodeR xr hxr
      have hmap2 := P.map_nodeR (Gr.node xr) hn1
      have hmap3 := P.map_nodeR (Gr.node (Gr.node xr)) hn2
      constructor
      · apply P.injr
        calc
          hr (Gr.node (Gr.node (Gr.node xr))) =
              G.node (hr (Gr.node (Gr.node xr))) := hmap3
          _ = G.node (G.node (hr (Gr.node xr))) := by rw [hmap2]
          _ = G.node (G.node (G.node (hr xr))) := by rw [hmap1]
          _ = hr xr := (hcubic (hr xr)).1
      · intro heq
        apply (hcubic (hr xr)).2
        calc
          G.node (hr xr) = hr (Gr.node xr) := hmap1.symm
          _ = hr xr := congrArg hr heq
  · rintro ⟨hcubicD, hcubicR⟩ x
    by_cases hxd : P.InDiskImage x
    · rcases hxd with ⟨xd, rfl⟩
      have hmap1 := P.map_nodeD xd
      have hmap2 := P.map_nodeD (Gd.node xd)
      have hmap3 := P.map_nodeD (Gd.node (Gd.node xd))
      constructor
      · calc
          G.node (G.node (G.node (hd xd))) =
              G.node (G.node (hd (Gd.node xd))) := by rw [hmap1]
          _ = G.node (hd (Gd.node (Gd.node xd))) := by rw [hmap2]
          _ = hd (Gd.node (Gd.node (Gd.node xd))) := hmap3.symm
          _ = hd xd := congrArg hd (hcubicD xd).1
      · intro heq
        apply (hcubicD xd).2
        apply P.injd
        calc
          hd (Gd.node xd) = G.node (hd xd) := hmap1
          _ = hd xd := heq
    · rcases P.cover x with hxd' | hxr
      · exact False.elim (hxd hxd')
      · rcases hxr with ⟨xr, rfl⟩
        have hxrOff : xr ∉ bGr := by
          intro hmem
          exact hxd
            (P.inDiskImage_of_onBoundary
              (by
                have hmem' : hr xr ∈ bGr.map hr :=
                  List.mem_map.mpr ⟨xr, hmem, rfl⟩
                rw [P.map_boundaryR] at hmem'
                simpa [OnBoundary] using hmem'))
        have hn1 : Gr.node xr ∉ bGr := by
          intro h
          exact hxrOff ((hNodeR xr).mp h)
        have hn2 : Gr.node (Gr.node xr) ∉ bGr := by
          intro h
          exact hn1 ((hNodeR (Gr.node xr)).mp h)
        have hmap1 := P.map_nodeR xr hxrOff
        have hmap2 := P.map_nodeR (Gr.node xr) hn1
        have hmap3 := P.map_nodeR (Gr.node (Gr.node xr)) hn2
        constructor
        · calc
            G.node (G.node (G.node (hr xr))) =
                G.node (G.node (hr (Gr.node xr))) := by rw [hmap1]
            _ = G.node (hr (Gr.node (Gr.node xr))) := by rw [hmap2]
            _ = hr (Gr.node (Gr.node (Gr.node xr))) := hmap3.symm
            _ = hr xr := congrArg hr (hcubicR xr hxrOff).1
        · intro heq
          apply (hcubicR xr hxrOff).2
          apply P.injr
          calc
            hr (Gr.node xr) = G.node (hr xr) := hmap1
            _ = hr xr := heq

theorem disk_boundary_edge_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (xd : Gd.Dart) :
    Gd.edge xd ∈ bGd ↔ xd ∈ bGd :=
  FunctionCycle.image_mem_iff P.cycleD Gd.edge.injective xd

theorem remainder_boundary_node_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (xr : Gr.Dart) :
    Gr.node xr ∈ bGr ↔ xr ∈ bGr :=
  FunctionCycle.image_mem_iff P.cycleR Gr.node.injective xr
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
