import FourColorTheorem.FourColor.Hypermap.RevSnip.RingGeometry

/-!
The ring-disk chord reduction.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- Coq `ring_disk_chord`: a chord in the snipped disk boundary cuts off a
strictly shorter nontrivial host ring.  This is the source proof's exact
two-chord argument: choose the chord side containing an arbitrary face in the
original disk interior. -/
theorem ringDiskChord
    {G : Hypermap.{u}} {r : List G.Dart} {m : Nat}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hBridgeless : G.Bridgeless) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (hNontrivial : G.NontrivialRing m r)
    (hNotChordless :
      ¬ (snipDisk G r hplanar hr).Chordless (snipdRing hplanar hr)) :
    ∃ r' : List G.Dart,
      G.SimpleRLinkCycle r' ∧
        G.NontrivialRing 0 r' ∧ r'.length < r.length := by
  classical
  let Gd := snipDisk G r hplanar hr
  let bGd := snipdRing hplanar hr
  have hBoundaryNodup : bGd.Nodup := snipdRing_nodup hplanar hr
  have hBoundarySimple : Gd.FaceSimple bGd :=
    faceSimple_snipdRing hplanar hr
  have hBoundaryCycle : FunctionCycle Gd.edge bGd :=
    cycle_snipdRing hplanar hr
  unfold Chordless at hNotChordless
  push Not at hNotChordless
  rcases hNotChordless with
    ⟨xd, hxd, yd, hyd, hadj, hnotNeighbors⟩
  rcases hadj with ⟨zd, hxdz, hedgeZdYd⟩
  have hzNotRing : snipd zd ∉ r := by
    intro hzRing
    have hzd : zd ∈ bGd :=
      (mem_snipdRing_iff hplanar hr zd).2 hzRing
    have hxdEqZd : xd = zd :=
      FaceSimple.eq_of_faceReachable_of_mem
        (G := Gd) hBoundarySimple hxd hzd hxdz
    have hedgeEq : Gd.edge zd = bGd.next zd hzd :=
      hBoundaryCycle.eq_next hBoundaryNodup zd hzd
    have hnextReach :
        PermReachable Gd.face (bGd.next zd hzd) yd := by
      rw [← hedgeEq]
      exact hedgeZdYd
    have hnextY : bGd.next zd hzd = yd :=
      FaceSimple.eq_of_faceReachable_of_mem
        (G := Gd) hBoundarySimple
        (List.next_mem bGd zd hzd) hyd hnextReach
    apply hnotNeighbors.2
    subst xd
    exact hnextY.symm
  have hxdHost : snipd xd ∈ r :=
    (mem_snipdRing_iff hplanar hr xd).1 hxd
  have hydHost : snipd yd ∈ r :=
    (mem_snipdRing_iff hplanar hr yd).1 hyd
  have hzDisk : G.DiskE r (snipd zd) := ⟨zd.2, hzNotRing⟩
  have hxdzHost :
      PermReachable G.face (snipd xd) (snipd zd) :=
    snipDisk_faceReachable_projection hplanar hr hxdz
  have hedgeZdYdHost :
      PermReachable G.face (G.edge (snipd zd)) (snipd yd) := by
    have hproj :=
      snipDisk_faceReachable_projection hplanar hr hedgeZdYd
    simpa [snipDisk_edge_val, hzNotRing] using hproj
  have hydEdgeZHost :
      PermReachable G.face (snipd yd) (G.edge (snipd zd)) :=
    PermReachable.symm G.face hedgeZdYdHost
  have hHostNext : snipd yd ≠ r.next (snipd xd) hxdHost := by
    intro hEq
    apply hnotNeighbors.2
    apply snipd_injective hplanar hr
    have hmap := List.next_map_injective snipd
      (snipd_injective hplanar hr) bGd hBoundaryNodup xd hxd
    have hmap' :
        r.next (snipd xd) hxdHost = snipd (bGd.next xd hxd) := by
      simpa only [bGd, map_snipdRing] using hmap
    exact hEq.trans hmap'
  have hHostPrev : snipd yd ≠ r.prev (snipd xd) hxdHost := by
    intro hEq
    apply hnotNeighbors.1
    apply snipd_injective hplanar hr
    have hmap := List.prev_map_injective snipd
      (snipd_injective hplanar hr) bGd hBoundaryNodup xd hxd
    have hmap' :
        r.prev (snipd xd) hxdHost = snipd (bGd.prev xd hxd) := by
      simpa only [bGd, map_snipdRing] using hmap
    exact hEq.trans hmap'
  have hxyNe : snipd xd ≠ snipd yd := by
    intro hEq
    exact hBridgeless (snipd zd)
      (PermReachable.trans G.face
        (PermReachable.symm G.face hxdzHost)
        (hEq ▸ hydEdgeZHost))
  rcases SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_witnesses
      (G := G) hPlain hr hxdHost hydHost (Ne.symm hxyNe)
      hxdzHost hydEdgeZHost with
    ⟨p₁, p₂, i, hdecomp, hcycle₁, hcycle₂⟩
  let r₀ := snipd yd :: p₁ ++ snipd xd :: p₂
  let cr₁ := snipd zd :: snipd yd :: p₁
  let cr₂ := G.edge (snipd zd) :: snipd xd :: p₂
  have hr₀ : G.SimpleRLinkCycle r₀ := by
    have hrot := SimpleRLinkCycle.rotate (G := G) i hr
    simpa [r₀, hdecomp] using hrot
  have hzDisk₀ : G.DiskE r₀ (snipd zd) := by
    have hrot := (DiskE.rotate (G := G) i).2 hzDisk
    simpa [r₀, hdecomp] using hrot
  have hcycle₁' : G.SimpleRLinkCycle cr₁ := by
    simpa [cr₁] using hcycle₁
  have hcycle₂' : G.SimpleRLinkCycle cr₂ := by
    simpa [cr₂] using hcycle₂
  have hp₂ : p₂ ≠ [] := by
    intro hp₂Nil
    subst p₂
    have hrotNodup : (r.rotate i).Nodup :=
      List.nodup_rotate.mpr hr.2.nodup
    have hxNotP₁ : snipd xd ∉ p₁ := by
      have hn : (snipd yd :: p₁ ++ [snipd xd]).Nodup := by
        simpa [hdecomp] using hrotNodup
      have hd : List.Disjoint p₁ [snipd xd] :=
        (List.nodup_cons.mp hn).2.disjoint
      exact fun hx => (List.disjoint_left.mp hd hx) (by simp)
    have hnextDecomp :
        (snipd yd :: p₁ ++ [snipd xd]).next (snipd xd)
            (by simp) = snipd yd :=
      List.next_cons_concat (l := p₁) (x := snipd xd)
        (snipd yd) hxyNe hxNotP₁
    have hrotated : r ~r (snipd yd :: p₁ ++ [snipd xd]) :=
      ⟨i, hdecomp⟩
    have hnextEq :=
      List.isRotated_next_eq hrotated hr.2.nodup hxdHost
    exact hHostNext (hnextEq.trans hnextDecomp).symm
  have hp₁ : p₁ ≠ [] := by
    intro hp₁Nil
    subst p₁
    have hrotNodup : (r.rotate i).Nodup :=
      List.nodup_rotate.mpr hr.2.nodup
    have hprevDecomp :
        (snipd yd :: snipd xd :: p₂).prev (snipd xd)
            (by simp) = snipd yd :=
      List.prev_cons_cons_of_ne' p₂ (snipd xd) (snipd yd)
        (snipd xd) (by simp) hxyNe rfl
    have hrotated : r ~r (snipd yd :: snipd xd :: p₂) :=
      ⟨i, by simpa using hdecomp⟩
    have hprevEq :=
      List.isRotated_prev_eq hrotated hr.2.nodup hxdHost
    exact hHostPrev (hprevEq.trans hprevDecomp).symm
  have hlength : 2 < r.length := by
    have hlen := congrArg List.length hdecomp
    have hp₁Pos : 0 < p₁.length := List.length_pos_iff_ne_nil.mpr hp₁
    have hp₂Pos : 0 < p₂.length := List.length_pos_iff_ne_nil.mpr hp₂
    simp only [List.length_rotate, List.length_cons, List.length_append] at hlen
    omega
  have hproper : G.ProperRing r :=
    properRing_of_length_gt_two (G := G) hlength
  have hproper₀ : G.ProperRing r₀ := by
    have hrot :=
      (properRing_rotate_iff_of_plain (G := G) hPlain i r).2 hproper
    simpa [r₀, hdecomp] using hrot
  have hzero : G.NontrivialRing 0 r := by
    exact ⟨Nat.zero_lt_of_lt hNontrivial.1,
      Nat.zero_lt_of_lt hNontrivial.2⟩
  rcases (G.nontrivialRing_zero_iff.mp hzero).1 with ⟨t, ht⟩
  have ht₀ : G.DiskF r₀ t := by
    have hrot := (DiskF.rotate (G := G) i).2 ht
    simpa [r₀, hdecomp] using hrot
  have hJordan : G.Jordan :=
    Unavoidability.eulerPlanar_jordan G hplanar
  by_cases ht₁ : G.DiskF cr₁ t
  · have hresult := G.nontrivialRing_zero_chord_prefix
      hConn hJordan hPlain hr₀ hproper₀ hzDisk₀
      (by simp) (by simp) hxdzHost
      hcycle₁' hcycle₂' hp₂ ⟨t, ht₁⟩
    refine ⟨cr₁, hcycle₁', hresult.1, ?_⟩
    have hlen : r₀.length = r.length := by
      have := congrArg List.length hdecomp
      simpa [r₀] using this.symm
    rw [← hlen]
    exact hresult.2
  · have hsplit := G.diskF_chord_prefix
      hConn hJordan hPlain hr₀ hproper₀ hzDisk₀
      (by simp) (by simp) hxdzHost hydEdgeZHost
      hcycle₁' hcycle₂' (u := t)
    have ht₂ : G.DiskF cr₂ t := by
      by_contra hnot₂
      exact ht₁ (hsplit.2 ⟨ht₀, hnot₂⟩)
    let r₀' := snipd xd :: p₂ ++ snipd yd :: p₁
    have hswap :
        r₀.rotate (snipd yd :: p₁).length = r₀' := by
      change
        ((snipd yd :: p₁) ++ (snipd xd :: p₂)).rotate
            (snipd yd :: p₁).length =
          (snipd xd :: p₂) ++ (snipd yd :: p₁)
      exact List.rotate_append_length_eq
        (snipd yd :: p₁) (snipd xd :: p₂)
    have hr₀' : G.SimpleRLinkCycle r₀' := by
      rw [← hswap]
      exact SimpleRLinkCycle.rotate
        (G := G) (snipd yd :: p₁).length hr₀
    have hproper₀' : G.ProperRing r₀' := by
      rw [← hswap]
      exact (properRing_rotate_iff_of_plain (G := G) hPlain
        (snipd yd :: p₁).length r₀).2 hproper₀
    have hedgeDisk₀ : G.DiskE r₀ (G.edge (snipd zd)) :=
      (G.diskE_edge_iff hJordan hPlain hr₀).2 hzDisk₀
    have hedgeDisk₀' : G.DiskE r₀' (G.edge (snipd zd)) := by
      rw [← hswap]
      exact (DiskE.rotate (G := G) (snipd yd :: p₁).length).2
        hedgeDisk₀
    have hcycleOther :
        G.SimpleRLinkCycle
          (G.edge (G.edge (snipd zd)) :: snipd yd :: p₁) := by
      simpa [Plain.edge_edge (G := G) hPlain] using hcycle₁'
    have hresult := G.nontrivialRing_zero_chord_prefix
      hConn hJordan hPlain hr₀' hproper₀' hedgeDisk₀'
      (by simp) (by simp) hydEdgeZHost
      hcycle₂' hcycleOther hp₁ ⟨t, ht₂⟩
    refine ⟨cr₂, hcycle₂', hresult.1, ?_⟩
    have hlen₀ : r₀.length = r.length := by
      have := congrArg List.length hdecomp
      simpa [r₀] using this.symm
    have hlenSwap : r₀'.length = r₀.length := by
      have := congrArg List.length hswap
      simpa using this.symm
    rw [← hlen₀, ← hlenSwap]
    change
      (G.edge (snipd zd) :: snipd xd :: p₂).length < r₀'.length
    exact hresult.2

/-- Source-compatible spelling of Coq's theorem name. -/
theorem ring_disk_chord
    {G : Hypermap.{u}} {r : List G.Dart} {m : Nat}
    (hplanar : G.EulerPlanar) (hConn : G.Connected)
    (hBridgeless : G.Bridgeless) (hPlain : G.Plain)
    (hr : G.SimpleRLinkCycle r)
    (hNontrivial : G.NontrivialRing m r)
    (hNotChordless :
      ¬ (snipDisk G r hplanar hr).Chordless (snipdRing hplanar hr)) :
    ∃ r' : List G.Dart,
      G.SimpleRLinkCycle r' ∧
        G.NontrivialRing 0 r' ∧ r'.length < r.length :=
  ringDiskChord hplanar hConn hBridgeless hPlain hr
    hNontrivial hNotChordless

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
