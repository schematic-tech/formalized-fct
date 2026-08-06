
import FourColorTheorem.FourColor.Coloring.KempeMap
import FourColorTheorem.FourColor.Hypermap.Snip

/-!
Reverse snipping and ring-trace transfer.

This ports the second half of Gonthier's `revsnip.v`.  The reverse ring is
already developed in `Geometry`; here we compare the disk cut out by a ring
with the remainder cut out by its reverse ring.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u v

/-- MathComp `rotr 1`, expressed using mathlib's left rotation. -/
def rotateRightOne {α : Type u} (xs : List α) : List α :=
  xs.rotate (xs.length - 1)

@[simp]
theorem length_rotateRightOne {α : Type u} (xs : List α) :
    (rotateRightOne xs).length = xs.length := by
  simp [rotateRightOne]

theorem map_rotateRightOne {α : Type u} {β : Type v}
    (f : α → β) (xs : List α) :
    (rotateRightOne xs).map f = rotateRightOne (xs.map f) := by
  simp [rotateRightOne, List.map_rotate]

theorem rotateRightOne_rotate_one_of_ne_nil
    {α : Type u} {xs : List α} (hxs : xs ≠ []) :
    rotateRightOne (xs.rotate 1) = xs := by
  have hpos : 0 < xs.length := List.length_pos_iff_ne_nil.mpr hxs
  have hone : 1 ≤ xs.length := hpos
  rw [rotateRightOne, List.length_rotate, List.rotate_rotate,
    Nat.add_sub_of_le hone, List.rotate_length]

/-- Pull a coloring through a map which reflects host face orbits.  A host
face with no source representative receives the distinguished zero color. -/
noncomputable def faceClassColor
    (H : Hypermap.{u}) (A : Hypermap.{v})
    (π : A.Dart → H.Dart) (k : A.Dart → Color) (x : H.Dart) : Color :=
  by
    classical
    exact if hx : ∃ a : A.Dart, PermReachable H.face x (π a) then
      k (Classical.choose hx)
    else
      Color.zero

theorem faceClassColor_eq_of_reachable
    (H : Hypermap.{u}) (A : Hypermap.{v})
    (π : A.Dart → H.Dart) (k : A.Dart → Color)
    (hreflect : ∀ a b : A.Dart,
      PermReachable H.face (π a) (π b) →
        PermReachable A.face a b)
    (hk : A.Coloring k)
    {x : H.Dart} (a : A.Dart)
    (hxa : PermReachable H.face x (π a)) :
    faceClassColor H A π k x = k a := by
  let hex : ∃ b : A.Dart, PermReachable H.face x (π b) := ⟨a, hxa⟩
  rw [faceClassColor, dif_pos hex]
  have hchosen := Classical.choose_spec hex
  have hca :
      PermReachable H.face
        (π (Classical.choose hex)) (π a) :=
    PermReachable.trans H.face
      (PermReachable.symm H.face hchosen) hxa
  exact (Coloring.eq_of_face_reachable
    (G := A) hk (hreflect _ _ hca)).symm

theorem faceClassColor_eq_of_host_reachable
    (H : Hypermap.{u}) (A : Hypermap.{v})
    (π : A.Dart → H.Dart) (k : A.Dart → Color)
    (hreflect : ∀ a b : A.Dart,
      PermReachable H.face (π a) (π b) →
        PermReachable A.face a b)
    (hk : A.Coloring k)
    {x y : H.Dart}
    (hxy : PermReachable H.face x y) :
    faceClassColor H A π k x = faceClassColor H A π k y := by
  by_cases hx : ∃ a : A.Dart, PermReachable H.face x (π a)
  · rcases hx with ⟨a, hxa⟩
    rw [faceClassColor_eq_of_reachable H A π k hreflect hk a hxa]
    rw [faceClassColor_eq_of_reachable H A π k hreflect hk a
      (PermReachable.trans H.face (PermReachable.symm H.face hxy) hxa)]
  · have hy : ¬ ∃ a : A.Dart, PermReachable H.face y (π a) := by
      rintro ⟨a, hya⟩
      exact hx ⟨a, PermReachable.trans H.face hxy hya⟩
    simp [faceClassColor, hx, hy]

/-- Coq `rev_snip_disk`. -/
noncomputable def revSnipDisk
    (G : Hypermap.{u}) (r : List G.Dart)
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) : Hypermap.{u} :=
  snipDisk G (G.RevRing r) hplanar
    (SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr)

/-- Coq `rev_snip_rem`. -/
noncomputable def revSnipRemainder
    (G : Hypermap.{u}) (r : List G.Dart)
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) : Hypermap.{u} :=
  snipRemainder G (G.RevRing r) hplanar
    (SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr)

/-- Coq `rev_snipd_ring`. -/
def revSnipdRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) :
    List (revSnipDisk G r hplanar hPlain hr).Dart :=
  snipdRing hplanar
    (SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr)

/-- Coq `rev_snipr_ring`. -/
def revSniprRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) :
    List (revSnipRemainder G r hplanar hPlain hr).Dart :=
  sniprRing hplanar
    (SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr)

@[simp]
theorem map_revSniprRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) :
    (revSniprRing hplanar hPlain hr).map snipr = r.map G.edge := by
  change
    (sniprRing hplanar
      (SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr)).map snipr =
      r.map G.edge
  rw [map_sniprRing]
  simp [RevRing]

/-- The canonical-face-orbit version of the list equality at the start of
Coq `rev_ring_cotrace`.  The right rotation cancels the one-step rotation
forced by `rlink` around the source ring. -/
theorem map_faceOrbit_rotateRight_revSniprRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r) :
    (rotateRightOne (revSniprRing hplanar hPlain hr)).map
        (fun x => PermOrbit.of G.face (snipr x)) =
      (snipdRing hplanar hr).map
        (fun x => PermOrbit.of G.face (snipd x)) := by
  have hrne : r ≠ [] := by
    intro hrnil
    subst r
    exact not_properRing_nil (G := G) hproper
  have hedgeOrbit :
      (r.map G.edge).map (PermOrbit.of G.face) =
        (r.map (PermOrbit.of G.face)).rotate 1 := by
    have hrev :=
      RLinkCycle.map_faceOrbit_revRing (G := G) hr.1
    have h := congrArg List.reverse hrev
    simpa [RevRing, List.map_reverse, List.map_map,
      Function.comp_def] using h
  have hremOrbit :
      (revSniprRing hplanar hPlain hr).map
          (fun x => PermOrbit.of G.face (snipr x)) =
        (r.map G.edge).map (PermOrbit.of G.face) := by
    have h := congrArg (List.map (PermOrbit.of G.face))
      (map_revSniprRing hplanar hPlain hr)
    simpa only [List.map_map, Function.comp_apply] using h
  have hdiskOrbit :
      (snipdRing hplanar hr).map
          (fun x => PermOrbit.of G.face (snipd x)) =
        r.map (PermOrbit.of G.face) := by
    have h := congrArg (List.map (PermOrbit.of G.face))
      (map_snipdRing hplanar hr)
    simpa only [List.map_map, Function.comp_apply] using h
  calc
    (rotateRightOne (revSniprRing hplanar hPlain hr)).map
          (fun x => PermOrbit.of G.face (snipr x)) =
        rotateRightOne
          ((revSniprRing hplanar hPlain hr).map
            (fun x => PermOrbit.of G.face (snipr x))) :=
      map_rotateRightOne _ _
    _ = rotateRightOne ((r.map G.edge).map (PermOrbit.of G.face)) := by
      rw [hremOrbit]
    _ = rotateRightOne ((r.map (PermOrbit.of G.face)).rotate 1) := by
      rw [hedgeOrbit]
    _ = r.map (PermOrbit.of G.face) :=
      rotateRightOne_rotate_one_of_ne_nil
        (by simpa using hrne)
    _ = (snipdRing hplanar hr).map
          (fun x => PermOrbit.of G.face (snipd x)) := by
      exact hdiskOrbit.symm

/-- The coloring on the reverse-ring remainder induced by a coloring of the
original snip disk. -/
noncomputable def diskToReverseRemainderColor
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (kd : (snipDisk G r hplanar hr).Dart → Color) :
    (revSnipRemainder G r hplanar hPlain hr).Dart → Color := fun xr =>
  faceClassColor G (snipDisk G r hplanar hr) snipd kd (snipr xr)

/-- Forward coloring transfer used by Coq `rev_ring_cotrace`. -/
theorem coloring_diskToReverseRemainder
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    {kd : (snipDisk G r hplanar hr).Dart → Color}
    (hkd : (snipDisk G r hplanar hr).Coloring kd) :
    (revSnipRemainder G r hplanar hPlain hr).Coloring
      (diskToReverseRemainderColor hplanar hPlain hr kd) := by
  let Gd := snipDisk G r hplanar hr
  let hrr := SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  let Grr := snipRemainder G (G.RevRing r) hplanar hrr
  let Pd := snipPatch hplanar hr
  let Prr := snipPatch hplanar hrr
  let kr := diskToReverseRemainderColor hplanar hPlain hr kd
  have hJ : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hplanar
  have hreflectD : ∀ a b : Gd.Dart,
      PermReachable G.face (snipd a) (snipd b) →
        PermReachable Gd.face a b := by
    intro a b hab
    exact (snipDisk_faceReachable_iff hplanar hr a b).2 hab
  have hPlainR : Grr.Plain :=
    (Prr.plain_iff.mp hPlain).2
  have hedgeOff : ∀ xr : Grr.Dart, snipr xr ∉ G.RevRing r →
      kr (Grr.edge xr) ≠ kr xr := by
    intro xr hxOff
    let x : G.Dart := snipr xr
    have hxN : G.DiskN r x := by
      by_contra hxN
      apply xr.2
      exact ⟨
        (G.diskN_rev_ring hConn hJ hPlain hr hproper x).2 hxN,
        hxOff⟩
    let xd : Gd.Dart := ⟨x, hxN⟩
    let zd : Gd.Dart := Gd.face (Gd.edge xd)
    have hxXd : PermReachable G.face x (snipd xd) := by
      exact PermReachable.refl G.face x
    have hEdgeXZd :
        PermReachable G.face (G.edge x) (snipd zd) := by
      have hEdgeMap := Pd.map_edgeD_face_reachable_host_edge xd
      have hFaceMap := Pd.map_faceD_reachable (Gd.edge xd)
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hEdgeMap) hFaceMap
    have hkrX : kr xr = kd xd := by
      exact faceClassColor_eq_of_reachable G Gd snipd kd
        hreflectD hkd xd hxXd
    have hkrEdgeX : kr (Grr.edge xr) = kd zd := by
      change faceClassColor G Gd snipd kd
        (snipr (Grr.edge xr)) = kd zd
      rw [snipRemainder_edge_val]
      exact faceClassColor_eq_of_reachable G Gd snipd kd
        hreflectD hkd zd hEdgeXZd
    intro heq
    apply hkd.1 xd
    calc
      kd (Gd.edge xd) = kd zd := (hkd.2 (Gd.edge xd)).symm
      _ = kr (Grr.edge xr) := hkrEdgeX.symm
      _ = kr xr := heq
      _ = kd xd := hkrX
  constructor
  · intro xr
    by_cases hxRing : snipr xr ∈ G.RevRing r
    · have hEdgeOff : snipr (Grr.edge xr) ∉ G.RevRing r := by
        intro hEdgeRing
        have hxEdgeR : G.edge (snipr xr) ∈ r :=
          (mem_revRing_of_plain (G := G) hPlain).1 hxRing
        have hxR : snipr xr ∈ r := by
          have := (mem_revRing_of_plain (G := G) hPlain).1 hEdgeRing
          have hmap : snipr (Grr.edge xr) = G.edge (snipr xr) :=
            snipRemainder_edge_val hplanar hrr xr
          rw [hmap, Plain.edge_edge (G := G) hPlain] at this
          exact this
        apply G.diskN_edge_ring hJ hPlain hr hproper hxEdgeR
        simpa [Plain.edge_edge (G := G) hPlain] using
          (G.diskN_of_mem hxR)
      have hne := hedgeOff (Grr.edge xr) hEdgeOff
      intro heq
      apply hne
      rw [(hPlainR xr).1]
      exact heq.symm
    · exact hedgeOff xr hxRing
  · intro xr
    change faceClassColor G Gd snipd kd (snipr (Grr.face xr)) =
      faceClassColor G Gd snipd kd (snipr xr)
    exact (faceClassColor_eq_of_host_reachable G Gd snipd kd
      hreflectD hkd (Prr.map_faceR_reachable xr)).symm

/-- The coloring on the original snip disk induced by a coloring of the
reverse-ring remainder. -/
noncomputable def reverseRemainderToDiskColor
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (kr : (revSnipRemainder G r hplanar hPlain hr).Dart → Color) :
    (snipDisk G r hplanar hr).Dart → Color := fun xd =>
  faceClassColor G (revSnipRemainder G r hplanar hPlain hr)
    snipr kr (snipd xd)

/-- Backward coloring transfer used by Coq `rev_ring_cotrace`. -/
theorem coloring_reverseRemainderToDisk
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    {kr : (revSnipRemainder G r hplanar hPlain hr).Dart → Color}
    (hkr : (revSnipRemainder G r hplanar hPlain hr).Coloring kr) :
    (snipDisk G r hplanar hr).Coloring
      (reverseRemainderToDiskColor hplanar hPlain hr kr) := by
  let Gd := snipDisk G r hplanar hr
  let hrr := SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  let Grr := snipRemainder G (G.RevRing r) hplanar hrr
  let Prr := snipPatch hplanar hrr
  let kd := reverseRemainderToDiskColor hplanar hPlain hr kr
  have hJ : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hplanar
  have hreflectR : ∀ a b : Grr.Dart,
      PermReachable G.face (snipr a) (snipr b) →
        PermReachable Grr.face a b := by
    intro a b hab
    exact (Prr.map_faceR_reachable_iff a b).2 hab
  have hfaceEq : ∀ a : Gd.Dart, kd (Gd.face a) = kd a := by
    intro a
    change faceClassColor G Grr snipr kr (snipd (Gd.face a)) =
      faceClassColor G Grr snipr kr (snipd a)
    have hHost := snipDisk_faceReachable_projection hplanar hr
      (PermReachable.forward Gd.face a)
    exact (faceClassColor_eq_of_host_reachable G Grr snipr kr
      hreflectR hkr hHost).symm
  constructor
  · intro u
    let z : Gd.Dart := Gd.face (Gd.edge u)
    let x : G.Dart := snipd z
    have hxN : G.DiskN r x := z.2
    have hnodeN : G.DiskN r (G.node x) :=
      (G.diskN_node_iff (r := r)).2 hxN
    let nxr : Grr.Dart := ⟨G.node x, by
      intro hE
      exact ((G.diskN_rev_ring hConn hJ hPlain hr hproper
        (G.node x)).1 hE.1) hnodeN⟩
    have hnodeZ : Gd.node z = u := by
      exact Gd.node_face_edge u
    have huNode : snipd u = G.node x := by
      calc
        snipd u = snipd (Gd.node z) := congrArg snipd hnodeZ.symm
        _ = G.node (snipd z) := snipDisk_node_val hplanar hr z
        _ = G.node x := rfl
    have huReach : PermReachable G.face (snipd u) (snipr nxr) := by
      change PermReachable G.face (snipd u) (G.node x)
      rw [huNode]
      exact PermReachable.refl G.face (G.node x)
    have hxEdgeReach :
        PermReachable G.face x (snipr (Grr.edge nxr)) := by
      rw [snipRemainder_edge_val]
      change PermReachable G.face x (G.edge (G.node x))
      exact PermReachable.symm G.face (by
        simpa using PermReachable.forward G.face (G.edge (G.node x)))
    have hkdU : kd u = kr nxr := by
      exact faceClassColor_eq_of_reachable G Grr snipr kr
        hreflectR hkr nxr huReach
    have hkdZ : kd z = kr (Grr.edge nxr) := by
      exact faceClassColor_eq_of_reachable G Grr snipr kr
        hreflectR hkr (Grr.edge nxr) hxEdgeReach
    intro heq
    apply hkr.1 nxr
    calc
      kr (Grr.edge nxr) = kd z := hkdZ.symm
      _ = kd (Gd.edge u) := hfaceEq (Gd.edge u)
      _ = kd u := heq
      _ = kr nxr := hkdU
  · exact hfaceEq

theorem colorsOn_diskToReverseRemainder_boundary
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    {kd : (snipDisk G r hplanar hr).Dart → Color}
    (hkd : (snipDisk G r hplanar hr).Coloring kd) :
    (revSnipRemainder G r hplanar hPlain hr).colorsOn
        (diskToReverseRemainderColor hplanar hPlain hr kd)
        (rotateRightOne (revSniprRing hplanar hPlain hr)) =
      (snipDisk G r hplanar hr).colorsOn kd
        (snipdRing hplanar hr) := by
  let Gd := snipDisk G r hplanar hr
  let Grr := revSnipRemainder G r hplanar hPlain hr
  let pr := rotateRightOne (revSniprRing hplanar hPlain hr)
  let pd := snipdRing hplanar hr
  let kr := diskToReverseRemainderColor hplanar hPlain hr kd
  have hreflectD : ∀ a b : Gd.Dart,
      PermReachable G.face (snipd a) (snipd b) →
        PermReachable Gd.face a b := by
    intro a b hab
    exact (snipDisk_faceReachable_iff hplanar hr a b).2 hab
  have horbits :=
    map_faceOrbit_rotateRight_revSniprRing
      hplanar hPlain hr hproper
  change pr.map (fun x => PermOrbit.of G.face (snipr x)) =
    pd.map (fun x => PermOrbit.of G.face (snipd x)) at horbits
  change pr.map kr = pd.map kd
  apply List.ext_getElem
  · simpa only [List.length_map] using congrArg List.length horbits
  · intro i hipr hipd
    have hiprList : i < pr.length := by
      simpa only [List.length_map] using hipr
    have hipdList : i < pd.length := by
      simpa only [List.length_map] using hipd
    have hiOrbitsR : i <
        (pr.map (fun x => PermOrbit.of G.face (snipr x))).length := by
      simpa only [List.length_map] using hiprList
    have hiOrbitsD : i <
        (pd.map (fun x => PermOrbit.of G.face (snipd x))).length := by
      simpa only [List.length_map] using hipdList
    have hOrbitEq :
        (pr.map (fun x => PermOrbit.of G.face (snipr x)))[i]'hiOrbitsR =
          (pd.map (fun x => PermOrbit.of G.face (snipd x)))[i]'hiOrbitsD := by
      have hOpt := congrArg (fun xs => xs[i]?) horbits
      change
        (pr.map (fun x => PermOrbit.of G.face (snipr x)))[i]? =
          (pd.map (fun x => PermOrbit.of G.face (snipd x)))[i]? at hOpt
      rw [List.getElem?_eq_getElem hiOrbitsR,
        List.getElem?_eq_getElem hiOrbitsD] at hOpt
      exact Option.some.inj hOpt
    rw [List.getElem_map, List.getElem_map] at hOrbitEq
    have hReach :
        PermReachable G.face
          (snipr (pr[i]'hiprList)) (snipd (pd[i]'hipdList)) :=
      Quotient.exact hOrbitEq
    rw [List.getElem_map, List.getElem_map]
    exact faceClassColor_eq_of_reachable G Gd snipd kd
      hreflectD hkd (pd[i]'hipdList) hReach

theorem colorsOn_reverseRemainderToDisk_boundary
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    {kr : (revSnipRemainder G r hplanar hPlain hr).Dart → Color}
    (hkr : (revSnipRemainder G r hplanar hPlain hr).Coloring kr) :
    (snipDisk G r hplanar hr).colorsOn
        (reverseRemainderToDiskColor hplanar hPlain hr kr)
        (snipdRing hplanar hr) =
      (revSnipRemainder G r hplanar hPlain hr).colorsOn kr
        (rotateRightOne (revSniprRing hplanar hPlain hr)) := by
  let Gd := snipDisk G r hplanar hr
  let Grr := revSnipRemainder G r hplanar hPlain hr
  let pr := rotateRightOne (revSniprRing hplanar hPlain hr)
  let pd := snipdRing hplanar hr
  let kd := reverseRemainderToDiskColor hplanar hPlain hr kr
  let hrr := SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  let Prr := snipPatch hplanar hrr
  have hreflectR : ∀ a b : Grr.Dart,
      PermReachable G.face (snipr a) (snipr b) →
        PermReachable Grr.face a b := by
    intro a b hab
    exact (Prr.map_faceR_reachable_iff a b).2 hab
  have horbits :=
    map_faceOrbit_rotateRight_revSniprRing
      hplanar hPlain hr hproper
  change pr.map (fun x => PermOrbit.of G.face (snipr x)) =
    pd.map (fun x => PermOrbit.of G.face (snipd x)) at horbits
  change pd.map kd = pr.map kr
  apply List.ext_getElem
  · simpa only [List.length_map] using
      (congrArg List.length horbits).symm
  · intro i hipd hipr
    have hipdList : i < pd.length := by
      simpa only [List.length_map] using hipd
    have hiprList : i < pr.length := by
      simpa only [List.length_map] using hipr
    have hiOrbitsR : i <
        (pr.map (fun x => PermOrbit.of G.face (snipr x))).length := by
      simpa only [List.length_map] using hiprList
    have hiOrbitsD : i <
        (pd.map (fun x => PermOrbit.of G.face (snipd x))).length := by
      simpa only [List.length_map] using hipdList
    have hOrbitEq :
        (pr.map (fun x => PermOrbit.of G.face (snipr x)))[i]'hiOrbitsR =
          (pd.map (fun x => PermOrbit.of G.face (snipd x)))[i]'hiOrbitsD := by
      have hOpt := congrArg (fun xs => xs[i]?) horbits
      change
        (pr.map (fun x => PermOrbit.of G.face (snipr x)))[i]? =
          (pd.map (fun x => PermOrbit.of G.face (snipd x)))[i]? at hOpt
      rw [List.getElem?_eq_getElem hiOrbitsR,
        List.getElem?_eq_getElem hiOrbitsD] at hOpt
      exact Option.some.inj hOpt
    rw [List.getElem_map, List.getElem_map] at hOrbitEq
    have hReach :
        PermReachable G.face
          (snipd (pd[i]'hipdList)) (snipr (pr[i]'hiprList)) :=
      PermReachable.symm G.face (Quotient.exact hOrbitEq)
    rw [List.getElem_map, List.getElem_map]
    exact faceClassColor_eq_of_reachable G Grr snipr kr
      hreflectR hkr (pr[i]'hiprList) hReach

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
