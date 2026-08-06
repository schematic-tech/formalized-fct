import FourColorTheorem.FourColor.Hypermap.RevSnip.ColorTransfer

/-!
Reverse-ring trace equivalence and nontrivial-ring geometry.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- Coq `rev_ring_cotrace`: the original snip disk and the right-rotated
reverse-ring remainder realize exactly the same boundary traces. -/
theorem revRing_cotrace
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    (et : ColSeq) :
    (snipDisk G r hplanar hr).RingTrace (snipdRing hplanar hr) et ↔
      (revSnipRemainder G r hplanar hPlain hr).RingTrace
        (rotateRightOne (revSniprRing hplanar hPlain hr)) et := by
  constructor
  · rintro ⟨kd, hkd, hEt⟩
    let kr := diskToReverseRemainderColor hplanar hPlain hr kd
    refine ⟨kr,
      coloring_diskToReverseRemainder
        hplanar hConn hPlain hr hproper hkd, ?_⟩
    have hcolors := colorsOn_diskToReverseRemainder_boundary
      hplanar hPlain hr hproper hkd
    calc
      et = ColSeq.trace
          ((snipDisk G r hplanar hr).colorsOn kd
            (snipdRing hplanar hr)) := hEt
      _ = ColSeq.trace
          ((revSnipRemainder G r hplanar hPlain hr).colorsOn kr
            (rotateRightOne (revSniprRing hplanar hPlain hr))) :=
        congrArg ColSeq.trace hcolors.symm
  · rintro ⟨kr, hkr, hEt⟩
    let kd := reverseRemainderToDiskColor hplanar hPlain hr kr
    refine ⟨kd,
      coloring_reverseRemainderToDisk
        hplanar hConn hPlain hr hproper hkr, ?_⟩
    have hcolors := colorsOn_reverseRemainderToDisk_boundary
      hplanar hPlain hr hproper hkr
    calc
      et = ColSeq.trace
          ((revSnipRemainder G r hplanar hPlain hr).colorsOn kr
            (rotateRightOne (revSniprRing hplanar hPlain hr))) := hEt
      _ = ColSeq.trace
          ((snipDisk G r hplanar hr).colorsOn kd
            (snipdRing hplanar hr)) :=
        congrArg ColSeq.trace hcolors.symm

/-- Coq `nontrivial_ring_proper`: a ring with a face orbit strictly on each
side cannot be empty, a singleton, or the two darts of one edge. -/
theorem nontrivial_ring_proper
    {G : Hypermap.{u}} {r : List G.Dart} {m : Nat}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hBridgeless : G.Bridgeless) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (hnt : G.NontrivialRing m r) :
    G.ProperRing r := by
  cases r with
  | nil =>
      exact False.elim ((RLinkCycle.nonempty (G := G) hr.1) rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          have hxx : G.RLink x x := hr.1.2
          exact False.elim (hBridgeless x
            (PermReachable.symm G.face hxx))
      | cons y ys =>
          cases ys with
          | cons z zs =>
              exact properRing_of_length_gt_two (G := G) (by simp)
          | nil =>
              rw [properRing_cons]
              left
              intro hedgePath
              have hxy : G.edge x = y := hedgePath.1
              subst y
              let rr : List G.Dart := [x, G.edge x]
              have hrr : G.SimpleRLinkCycle rr := by
                simpa [rr] using hr
              have hJordan : G.Jordan :=
                Unavoidability.eulerPlanar_jordan G hplanar
              have hedgeMem : ∀ {a : G.Dart}, a ∈ rr → G.edge a ∈ rr := by
                intro a ha
                simp [rr] at ha ⊢
                rcases ha with rfl | rfl
                · exact Or.inr rfl
                · exact Or.inl (hPlain x).1
              have hstep : ∀ {a b : G.Dart}, G.CLink a b →
                  G.DiskN rr a → G.DiskN rr b := by
                intro a b hab haDisk
                rcases hab with hnode | hface
                · subst b
                  exact G.diskN_node_symm haDisk
                · subst b
                  apply (G.diskN_edge_face_iff hPlain).1
                  by_cases haMem : a ∈ rr
                  · exact G.diskN_of_mem (hedgeMem haMem)
                  · have hedgeNot : G.edge a ∉ rr := by
                      intro hedgeIn
                      apply haMem
                      have := hedgeMem hedgeIn
                      simpa [Plain.edge_edge (G := G) hPlain a] using this
                    exact (G.diskN_edge_iff_of_not_mem hJordan hPlain hrr
                      haMem hedgeNot).2 haDisk
              have hall : ∀ a : G.Dart, G.DiskN rr a := by
                intro a
                have hreach := Hypermap.Connected.cConnect (G := G) hConn x a
                induction hreach with
                | refl => exact G.diskN_of_mem (by simp [rr])
                | tail _ hab ih => exact hstep hab ih
              have houtsidePos :
                  0 < G.FaceOrbitCountOf (G.DiskFC rr) :=
                Nat.zero_lt_of_lt (by simpa [rr] using hnt.2)
              rcases (faceOrbitCountOf_pos_iff_exists (G := G)).1
                  houtsidePos with ⟨a, haOutside⟩
              exact False.elim (haOutside.1 (hall a))

/-- Coq `nontrivial_rev_ring`: reverse-ring duality exchanges the strict
inside and outside face-orbit sets. -/
theorem nontrivial_rev_ring
    {G : Hypermap.{u}} {r : List G.Dart} {m : Nat}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hBridgeless : G.Bridgeless) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (hnt : G.NontrivialRing m r) :
    G.NontrivialRing m (G.RevRing r) := by
  classical
  have hproper := nontrivial_ring_proper hplanar hConn hBridgeless
    hPlain hr hnt
  have hJordan : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hplanar
  have hinside :
      G.FaceOrbitCountOf (G.DiskF (G.RevRing r)) =
        G.FaceOrbitCountOf (G.DiskFC r) :=
    G.faceOrbitCountOf_congr (fun x => by
      exact (G.diskF_rev_ring hConn hJordan hPlain hr hproper x).trans Iff.rfl)
  have houtside :
      G.FaceOrbitCountOf (G.DiskFC (G.RevRing r)) =
        G.FaceOrbitCountOf (G.DiskF r) :=
    G.faceOrbitCountOf_congr (fun x => by
      rw [DiskFC, G.diskN_rev_ring hConn hJordan hPlain hr hproper x,
        FaceBand.revRing_iff_of_plain (G := G) hPlain hr.1, DiskF]
      simp only [not_not])
  constructor
  · simpa [hinside] using hnt.2
  · simpa [houtside] using hnt.1

/-- Coq `ring_disk_closed`: traces on the disk side of a nontrivial simple
ring are Kempe-closed when the host map is cubic. -/
theorem ringDiskClosed
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r) :
    Chromogram.KempeClosed
      ((snipDisk G r hplanar hr).RingTrace (snipdRing hplanar hr)) := by
  let hrr := SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  let Grr := revSnipRemainder G r hplanar hPlain hr
  let bGrr := revSniprRing hplanar hPlain hr
  let pr := rotateRightOne bGrr
  let Prr := snipPatch hplanar hrr
  have hcycle : FunctionCycle Grr.node bGrr := by
    exact cycle_sniprRing hplanar hrr
  have hnodup : bGrr.Nodup := by
    exact sniprRing_nodup hplanar hrr
  have hquasi : Grr.Quasicubic bGrr := by
    exact (Prr.cubic_iff.mp hCubic).2
  have geo : CyclePlanarPlainQuasicubic Grr pr :=
    { cycle := by
        change FunctionCycle Grr.node (bGrr.rotate (bGrr.length - 1))
        exact functionCycle_rotate hcycle hnodup (bGrr.length - 1)
      nodup := by
        change (bGrr.rotate (bGrr.length - 1)).Nodup
        exact List.nodup_rotate.mpr hnodup
      eulerPlanar := snipRemainder_eulerPlanar hplanar hrr
      plain := (Prr.plain_iff.mp hPlain).2
      quasicubic := by
        intro x hx
        apply hquasi x
        intro hmem
        apply hx
        change x ∈ bGrr.rotate (bGrr.length - 1)
        exact List.mem_rotate.mpr hmem }
  have hclosed : Chromogram.KempeClosed (Grr.RingTrace pr) :=
    Kempe_map Grr pr geo
  apply Chromogram.KempeClosed.congr
    (P := Grr.RingTrace pr)
    (Q := (snipDisk G r hplanar hr).RingTrace (snipdRing hplanar hr))
    (fun et => (revRing_cotrace hplanar hConn hPlain hr hproper et).symm)
  exact hclosed

/-- Source-compatible spelling of Coq's theorem name. -/
theorem ring_disk_closed
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain) (hCubic : G.Cubic)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r) :
    Chromogram.KempeClosed
      ((snipDisk G r hplanar hr).RingTrace (snipdRing hplanar hr)) :=
  ringDiskClosed hplanar hConn hPlain hCubic hr hproper

/-- Coq `colorable_from_ring`: compatible traces on the original disk and
the reverse-ring disk glue to a coloring of the host map. -/
theorem colorableFromRing
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    (et : ColSeq)
    (hDisk : (snipDisk G r hplanar hr).RingTrace
      (snipdRing hplanar hr) et)
    (hReverseDisk : (revSnipDisk G r hplanar hPlain hr).RingTrace
      (revSnipdRing hplanar hPlain hr) et.reverse) :
    G.FourColorable := by
  let hrr := SimpleRLinkCycle.revRing_of_plain (G := G) hPlain hr
  let Grr := revSnipRemainder G r hplanar hPlain hr
  let bGrr := revSniprRing hplanar hPlain hr
  let Prr := snipPatch hplanar hrr
  have hremRot : Grr.RingTrace (rotateRightOne bGrr) et :=
    (revRing_cotrace hplanar hConn hPlain hr hproper et).mp hDisk
  have hrem : Grr.RingTrace bGrr (ColSeq.rot1 et) := by
    have h := RingTrace.rotate_one (G := Grr) hremRot
    have hboundary : (rotateRightOne bGrr).rotate 1 = bGrr := by
      change (listUnrot1 bGrr).rotate 1 = bGrr
      exact list_rotate_one_unrot1 bGrr
    rw [hboundary] at h
    exact h
  apply Prr.colorable_patch.mpr
  refine ⟨et.reverse, hReverseDisk, ?_⟩
  simpa using hrem

/-- Source-compatible spelling of Coq's theorem name. -/
theorem colorable_from_ring
    {G : Hypermap.{u}} {r : List G.Dart}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r) (hproper : G.ProperRing r)
    (et : ColSeq)
    (hDisk : (snipDisk G r hplanar hr).RingTrace
      (snipdRing hplanar hr) et)
    (hReverseDisk : (revSnipDisk G r hplanar hPlain hr).RingTrace
      (revSnipdRing hplanar hPlain hr) et.reverse) :
    G.FourColorable :=
  colorableFromRing hplanar hConn hPlain hr hproper et hDisk hReverseDisk

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
