import FourColorTheorem.FourColor.Hypermap.Patch.Topology
import FourColorTheorem.FourColor.Hypermap.Patch.ImageEquiv

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v w z

variable {G : Hypermap.{w}} {Gd : Hypermap.{u}} {Gr : Hypermap.{v}}

namespace Patch

variable {hd : Gd.Dart → G.Dart} {hr : Gr.Dart → G.Dart}
variable {bGd : List Gd.Dart} {bGr : List Gr.Dart}

theorem faceBand_face_iff
    (xd : Gd.Dart) :
    Gd.FaceBand bGd (Gd.face xd) ↔ Gd.FaceBand bGd xd :=
  (FaceBand.congr_faceReachable (G := Gd)
    (PermReachable.forward Gd.face xd)).symm

theorem outer_face_iff
    (P : Patch G Gd Gr hd hr bGd bGr) (x : G.Dart) :
    P.Outer (G.face x) ↔ P.Outer x :=
  (P.outer_congr_reachable
    (PermReachable.forward G.face x)).symm

noncomputable def diskOffFaceBandEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    {xd : Gd.Dart // ¬ Gd.FaceBand bGd xd} ≃
      {x : G.Dart // ¬ P.Outer x} :=
  offImageEquiv hd (Gd.FaceBand bGd) P.Outer P.injd
    (fun xd => (P.outer_mapD_iff_faceBand xd).symm)
    (fun x => P.cover x |>.imp_right fun hxr =>
      ⟨x, hxr, PermReachable.refl G.face x⟩)

theorem faceOrbitCount_diskOffFaceBand
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Nat.card (PermOrbit
        (Gd.face.subtypePerm
          (p := fun xd => ¬ Gd.FaceBand bGd xd)
          (fun xd => not_congr (faceBand_face_iff (bGd := bGd) xd)))) =
      Nat.card (PermOrbit
        (G.face.subtypePerm
          (p := fun x => ¬ P.Outer x)
          (fun x => not_congr (P.outer_face_iff x)))) := by
  let e := P.diskOffFaceBandEquiv
  have hcomm (xd : {xd : Gd.Dart // ¬ Gd.FaceBand bGd xd}) :
      e ((Gd.face.subtypePerm
          (p := fun yd => ¬ Gd.FaceBand bGd yd)
          (fun yd => not_congr (faceBand_face_iff (bGd := bGd) yd))) xd) =
        (G.face.subtypePerm
          (p := fun x => ¬ P.Outer x)
          (fun x => not_congr (P.outer_face_iff x))) (e xd) := by
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    have hxdBoundary : xd.1 ∉ bGd := by
      intro hmem
      exact xd.2 ⟨xd, hmem, PermReachable.refl Gd.face xd⟩
    exact P.map_faceD_of_not_boundary xd hxdBoundary
  exact Nat.card_congr
    (permOrbitEquivOfConj e
      (Gd.face.subtypePerm
        (fun xd => not_congr (faceBand_face_iff (bGd := bGd) xd)))
      (G.face.subtypePerm
        (fun x => not_congr (P.outer_face_iff x))) hcomm)

/-- Map a remainder face orbit to the host face orbit containing its image. -/
noncomputable def remainderFaceOrbitMap
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.FaceOrbit →
      {o : G.FaceOrbit // PermOrbit.OrbitPred G.face P.Outer
        P.outer_face_iff o} :=
  Quotient.lift
    (fun xr => ⟨PermOrbit.of G.face (hr xr),
      ⟨hr xr, ⟨xr, rfl⟩, PermReachable.refl G.face (hr xr)⟩⟩)
    (by
      intro xr yr hxy
      apply Subtype.ext
      exact PermOrbit.of_eq_of G.face
        (P.map_faceR_reachable_of_reachable hxy))

theorem remainderFaceOrbitMap_injective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Injective P.remainderFaceOrbitMap := by
  intro o q hoq
  refine Quotient.inductionOn₂ o q ?_ hoq
  intro xr yr hxy
  have hhost : PermOrbit.of G.face (hr xr) =
      PermOrbit.of G.face (hr yr) := congrArg Subtype.val hxy
  exact Quot.sound
    ((P.map_faceR_reachable_iff xr yr).2 (Quotient.exact hhost))

theorem remainderFaceOrbitMap_surjective
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Function.Surjective P.remainderFaceOrbitMap := by
  rintro ⟨o, ho⟩
  refine Quotient.inductionOn o ?_ ho
  intro x hx
  rcases hx with ⟨y, ⟨xr, hxr⟩, hyx⟩
  refine ⟨PermOrbit.of Gr.face xr, ?_⟩
  apply Subtype.ext
  apply PermOrbit.of_eq_of G.face
  rw [hxr]
  exact hyx

noncomputable def remainderFaceOrbitEquiv
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.FaceOrbit ≃
      {o : G.FaceOrbit // PermOrbit.OrbitPred G.face P.Outer
        P.outer_face_iff o} :=
  Equiv.ofBijective P.remainderFaceOrbitMap
    ⟨P.remainderFaceOrbitMap_injective,
      P.remainderFaceOrbitMap_surjective⟩

theorem faceOrbitCount_remainderOuter
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.faceOrbitCount =
      Nat.card (PermOrbit
        (G.face.subtypePerm
          (p := P.Outer) P.outer_face_iff)) := by
  classical
  calc
    Gr.faceOrbitCount = Nat.card
        {o : G.FaceOrbit // PermOrbit.OrbitPred G.face P.Outer
          P.outer_face_iff o} :=
      Nat.card_congr P.remainderFaceOrbitEquiv
    _ = Nat.card (PermOrbit
        (G.face.subtypePerm
          (p := P.Outer) P.outer_face_iff)) :=
      Nat.card_congr
        (PermOrbit.restrictedOrbitEquiv G.face P.Outer
          P.outer_face_iff).symm

theorem faceOrbitCount_remainderOuter_eq
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gr.faceOrbitCount = G.FaceOrbitCountOf P.Outer := by
  classical
  rw [P.faceOrbitCount_remainderOuter]
  exact G.restrictedFaceOrbitCount_eq_faceOrbitCountOf
    P.Outer P.outer_face_iff

theorem faceOrbitCount_diskFaceBand
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Nat.card (PermOrbit
        (Gd.face.subtypePerm
          (p := fun xd => Gd.FaceBand bGd xd)
          (faceBand_face_iff (bGd := bGd)))) = bGd.length := by
  classical
  let orbitList : List Gd.FaceOrbit :=
    bGd.map (PermOrbit.of Gd.face)
  let selected : Gd.FaceOrbit → Prop :=
    PermOrbit.OrbitPred Gd.face (Gd.FaceBand bGd)
      (faceBand_face_iff (bGd := bGd))
  have hselected (o : Gd.FaceOrbit) :
      selected o ↔ o ∈ orbitList := by
    refine Quotient.inductionOn o ?_
    intro xd
    exact faceBand_iff_mem_faceOrbit_map (G := Gd)
  have hcard : Fintype.card {o : Gd.FaceOrbit // selected o} =
      orbitList.toFinset.card := by
    let e : {o : Gd.FaceOrbit // selected o} ≃
        {o : Gd.FaceOrbit // o ∈ orbitList.toFinset} :=
      Equiv.subtypeEquivRight (fun o => by
        simpa using hselected o)
    calc
      Fintype.card {o : Gd.FaceOrbit // selected o} =
          Nat.card {o : Gd.FaceOrbit // selected o} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card {o : Gd.FaceOrbit // o ∈ orbitList.toFinset} :=
        Nat.card_congr e
      _ = Fintype.card {o : Gd.FaceOrbit // o ∈ orbitList.toFinset} :=
        Nat.card_eq_fintype_card
      _ = orbitList.toFinset.card :=
        Fintype.card_coe orbitList.toFinset
  calc
    Nat.card (PermOrbit
        (Gd.face.subtypePerm
          (p := fun xd => Gd.FaceBand bGd xd)
          (faceBand_face_iff (bGd := bGd)))) =
        Nat.card {o : Gd.FaceOrbit // selected o} :=
      Nat.card_congr
        (PermOrbit.restrictedOrbitEquiv Gd.face
          (Gd.FaceBand bGd) (faceBand_face_iff (bGd := bGd)))
    _ = Fintype.card {o : Gd.FaceOrbit // selected o} :=
      Nat.card_eq_fintype_card
    _ = orbitList.toFinset.card := hcard
    _ = orbitList.length :=
      List.toFinset_card_of_nodup
        ((faceSimple_iff_nodup_faceOrbit_map Gd).mp
          P.boundaryD_faceSimple)
    _ = bGd.length := by simp [orbitList]

/-- The face-orbit identity used in Coq `genus_patch`. -/
theorem faceOrbitCount_patch
    (P : Patch G Gd Gr hd hr bGd bGr) :
    Gd.faceOrbitCount + Gr.faceOrbitCount =
      G.faceOrbitCount + bGd.length := by
  classical
  have hD := PermOrbit.card_eq_restricted_add_compl
    Gd.face (Gd.FaceBand bGd) (faceBand_face_iff (bGd := bGd))
  have hG := PermOrbit.card_eq_restricted_add_compl
    G.face P.Outer P.outer_face_iff
  have hBoundary := P.faceOrbitCount_diskFaceBand
  have hOff := P.faceOrbitCount_diskOffFaceBand
  have hR := P.faceOrbitCount_remainderOuter
  change Gd.faceOrbitCount = _ + _ at hD
  change G.faceOrbitCount = _ + _ at hG
  omega
end Patch

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
