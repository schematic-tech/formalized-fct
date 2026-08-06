import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.SmallDisk

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

private theorem reverse_cons_eq_getLastD_cons_reverse_dropLast
    {α : Type*} (x : α) (p : List α) :
    (x :: p).reverse =
      (x :: p).getLastD x :: (x :: p).dropLast.reverse := by
  induction p generalizing x with
  | nil => simp [List.getLastD]
  | cons y p ih =>
      simpa [List.getLastD, List.reverse_cons] using
        congrArg (fun q : List α => q ++ [x]) (ih y)

private theorem dropLast_cons_append_singleton
    {α : Type*} (x y : α) (q : List α) :
    (x :: (q ++ [y])).dropLast = x :: q := by
  induction q generalizing x with
  | nil => simp
  | cons z q ih =>
      change x :: (z :: (q ++ [y])).dropLast = x :: z :: q
      rw [ih]

/-- Reverse all source edges along a path and append a dart in the face of
the old head.  This is the path calculation defining Coq's `rx :: rp`. -/
private theorem RLinkPath.reverseEdges_append_of_faceReachable
    (hPlain : G.Plain)
    {x ry : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p)
    (hxry : PermReachable G.face x ry) :
    G.RLinkPath (G.edge ((x :: p).getLastD x))
      (((x :: p).dropLast.reverse.map G.edge) ++ [ry]) := by
  rcases List.eq_nil_or_concat p with hpNil | ⟨q, y, hpShape⟩
  · subst p
    simpa [List.getLastD, RLinkPath, RLink,
      Hypermap.Plain.edge_edge (G := G) hPlain] using hxry
  · subst p
    have hp' : G.RLinkPath x (q ++ [y]) := by simpa using hp
    have hrev : G.RLinkPath (G.edge y)
        ((q.reverse.map G.edge) ++ [G.edge x]) :=
      RLinkPath.reverse_edges_of_plain (G := G) hPlain hp'
    have hlast : G.RLink (G.edge x) ry := by
      unfold RLink
      simpa [Hypermap.Plain.edge_edge (G := G) hPlain] using hxry
    have hs := RLinkPath.snoc (G := G) (q.reverse.map G.edge) hrev hlast
    have hdrop : (x :: q.concat y).dropLast = x :: q := by
      simpa [List.concat_eq_append] using
        dropLast_cons_append_singleton x y q
    simp only [hdrop]
    simpa [List.getLastD, List.reverse_cons, List.map_append,
      List.append_assoc] using hs

/-- Every source dart before the final endpoint of an `rlink` path has its
opposite dart in the same face-closed kernel. -/
private theorem RLinkPath.edge_kernel_prefix
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x (p ++ [y]))
    (hkernel : ∀ z : G.Dart, z ∈ x :: (p ++ [y]) → G.Kernel r z) :
    ∀ z : G.Dart, z ∈ x :: p → G.Kernel r (G.edge z) := by
  induction p generalizing x with
  | nil =>
      intro z hz
      have hxy : G.RLink x y := by
        simpa [RLinkPath] using hp
      have hyKernel : G.Kernel r y := hkernel y (by simp)
      have hxEdge : G.Kernel r (G.edge x) :=
        G.kernel_faceClosed r hyKernel (PermReachable.symm G.face hxy)
      simp at hz
      subst z
      exact hxEdge
  | cons w p ih =>
      have hparts : G.RLink x w ∧ G.RLinkPath w (p ++ [y]) := by
        simpa [RLinkPath, List.append_assoc] using hp
      have hwKernel : G.Kernel r w := hkernel w (by simp)
      have hxEdge : G.Kernel r (G.edge x) :=
        G.kernel_faceClosed r hwKernel
          (PermReachable.symm G.face hparts.1)
      have htailKernel :
          ∀ z : G.Dart, z ∈ w :: (p ++ [y]) → G.Kernel r z := by
        intro z hz
        exact hkernel z (by simp [hz])
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxEdge
      · exact ih hparts.2 htailKernel z hz

/-- Coq's reversed `pre_hom_ring` construction.  The selected disk of the
new image ring is the strict complement of the old selected disk. -/
theorem PreHomRing.exists_reverse
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hopen : ¬ G.RLink ((x :: p).getLastD x) x)
    (hproper : H.ProperRing ((x :: p).map h)) :
    ∃ rx : G.Dart, ∃ rp : List G.Dart,
      PreHomRing r h rx rp ∧
        ¬ G.RLink ((rx :: rp).getLastD rx) rx ∧
          (rx :: rp).length = (x :: p).length ∧
            ∀ v : H.Dart,
              H.DiskF ((rx :: rp).map h) v ↔
                H.DiskFC ((x :: p).map h) v := by
  rcases List.eq_nil_or_concat p with hpNil | ⟨p₁, y, hpShape⟩
  · subst p
    simp [ProperRing] at hproper
  · subst p
    simp only [List.concat_eq_append] at hpre hopen hproper ⊢
    let pref : List G.Dart := x :: p₁
    let a : G.Dart := pref.getLastD x
    have hpathShape : G.RLinkPath x (p₁ ++ [y]) := hpre.path
    have haY : G.RLink a y := by
      simpa [pref, a] using
        RLinkPath.last_link_of_append_cons (G := G)
          (p := p₁) (q := []) hpathShape
    have hxKernel : G.Kernel r x := hpre.kernel x (by simp)
    have hyKernel : G.Kernel r y := hpre.kernel y (by simp)
    have htargetClose : H.RLink (h y) (h x) := by
      simpa [List.getLastD] using hpre.imageClosing
    have hxToEdgeHY :
        PermReachable H.face (h x) (H.edge (h y)) :=
      PermReachable.symm H.face htargetClose
    rcases hembed.faceReachable_lift (G.kernel_faceClosed r)
        hxKernel hxToEdgeHY with ⟨ry, hxry, hry⟩
    have hryKernel : G.Kernel r ry :=
      G.kernel_faceClosed r hxKernel hxry
    let rx : G.Dart := G.edge a
    let rp : List G.Dart :=
      (pref.dropLast.reverse.map G.edge) ++ [ry]
    have hcandidateFull :
        rx :: rp = (pref.reverse.map G.edge) ++ [ry] := by
      rw [reverse_cons_eq_getLastD_cons_reverse_dropLast x p₁]
      simp [rx, rp, a, pref, List.getLastD,
        List.getLast?_eq_getLast_of_ne_nil]
    have hcandidatePath : G.RLinkPath rx rp := by
      have hpPref : G.RLinkPath x p₁ :=
        RLinkPath.prefix_of_append (G := G) hpathShape
      simpa [rx, rp, pref, a] using
        RLinkPath.reverseEdges_append_of_faceReachable
          (G := G) hG.plain (p := p₁) hpPref hxry
    have hprefixEdgeKernel :
        ∀ z : G.Dart, z ∈ pref → G.Kernel r (G.edge z) := by
      intro z hz
      exact RLinkPath.edge_kernel_prefix (G := G) (r := r)
        hpathShape (by
          intro w hw
          exact hpre.kernel w (by simpa [List.append_assoc] using hw))
        z (by simpa [pref] using hz)
    have hcandidateKernel :
        ∀ z : G.Dart, z ∈ rx :: rp → G.Kernel r z := by
      intro z hz
      rw [hcandidateFull, List.mem_append] at hz
      rcases hz with hz | hz
      · rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
        exact hprefixEdgeKernel w (List.mem_reverse.mp hw)
      · simp at hz
        subst z
        exact hryKernel
    have hmapRev :
        (pref.reverse.map G.edge).map h =
          ((pref.map h).map H.edge).reverse := by
      rw [List.map_reverse, List.map_map, List.map_reverse, List.map_map]
      congr 1
      apply List.map_congr_left
      intro z hz
      exact hG.embedFunctor hH hembed
        (hpre.kernel z (by
          have hz' : z = x ∨ z ∈ p₁ := by simpa [pref] using hz
          rcases hz' with rfl | hz'
          · simp
          · simp [hz'])) (hprefixEdgeKernel z hz)
    have hcandidateMap :
        (rx :: rp).map h =
          (H.RevRing ((x :: (p₁ ++ [y])).map h)).rotate 1 := by
      rw [hcandidateFull, List.map_append, hmapRev]
      simp only [List.map_singleton, hry]
      simp [RevRing, List.map_append, List.map_map,
        List.rotate_cons_succ, pref,
        List.append_assoc]
    have htargetCycle :
        H.SimpleRLinkCycle
          ((H.RevRing ((x :: (p₁ ++ [y])).map h)).rotate 1) :=
      SimpleRLinkCycle.rotate (G := H) 1
        (SimpleRLinkCycle.revRing_of_plain
          (G := H) hH.plain hpre.imageCycle)
    have hcandidateCycle : H.SimpleRLinkCycle ((rx :: rp).map h) := by
      rw [hcandidateMap]
      exact htargetCycle
    have hcandidateOpen :
        ¬ G.RLink ((rx :: rp).getLastD rx) rx := by
      have hlastCandidate : (rx :: rp).getLastD rx = ry := by
        simp [rp, List.getLastD]
      rw [hlastCandidate]
      intro hryRx
      have hrxKernel : G.Kernel r rx := hcandidateKernel rx (by simp)
      have hedgeRyKernel : G.Kernel r (G.edge ry) :=
        G.kernel_faceClosed r hrxKernel
          (PermReachable.symm G.face hryRx)
      have hedgeRyMap : h (G.edge ry) = h y := by
        calc
          h (G.edge ry) = H.edge (h ry) :=
            hG.embedFunctor hH hembed hryKernel hedgeRyKernel
          _ = H.edge (H.edge (h y)) := by rw [hry]
          _ = h y := Hypermap.Plain.edge_edge (G := H) hH.plain _
      have hedgeRyY : PermReachable G.face (G.edge ry) y :=
        PermReachable.trans G.face hryRx haY
      have hedgeRyEqY : G.edge ry = y :=
        hembed.injective_of_faceReachable (G.kernel_faceClosed r)
          hedgeRyKernel hedgeRyY hedgeRyMap
      have hedgeYEqRy : G.edge y = ry := by
        calc
          G.edge y = G.edge (G.edge ry) := by rw [hedgeRyEqY]
          _ = ry := Hypermap.Plain.edge_edge (G := G) hG.plain _
      apply hopen
      have hclose : G.RLink y x := by
        unfold RLink
        rw [hedgeYEqRy]
        exact PermReachable.symm G.face hxry
      simpa [List.getLastD] using hclose
    have hcandidateLength :
        (rx :: rp).length = (x :: (p₁ ++ [y])).length := by
      rw [hcandidateFull]
      simp [pref]
    have hconnected : H.Connected :=
      Unavoidability.connectedMinimalCounterexamples_proved H hH
    have hJordan : H.Jordan :=
      Unavoidability.eulerPlanar_jordan H hH.planar
    refine ⟨rx, rp, ⟨hcandidatePath, hcandidateKernel,
      hcandidateCycle⟩, hcandidateOpen, hcandidateLength, ?_⟩
    intro v
    rw [hcandidateMap]
    exact (DiskF.rotate (G := H) 1).trans
      (H.diskF_rev_ring hconnected hJordan hH.plain
        hpre.imageCycle hproper v)

/-- The second forbidden-ring assertion in Coq `embed_full`.  Birkhoff forces
the complement of a short nonclosing image ring to have the small face count;
`PreHomRing.exists_reverse` then turns that complement into the selected disk
of another pre-hom ring, contradicting `smallDiskPreHomRing_closes`. -/
theorem shortPreHomRing_closes
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hshort : p.length ≤ 4) :
    G.RLink ((x :: p).getLastD x) x := by
  by_contra hopen
  let q : List H.Dart := (x :: p).map h
  have hqCycle : H.SimpleRLinkCycle q := by
    simpa [q] using hpre.imageCycle
  have hqShort : q.length ≤ 5 := by
    simp [q]
    omega
  have hproper : H.ProperRing q := by
    simpa [q] using hpre.imageProper_of_not_closing hG hH hembed hopen
  have hinside :
      (if q.length = 5 then 1 else 0) <
        H.FaceOrbitCountOf (H.DiskF q) := by
    by_contra hnot
    have hsmall :
        H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤
          if (x :: p).length = 5 then 1 else 0 := by
      simpa [q] using (show
        H.FaceOrbitCountOf (H.DiskF q) ≤
          if q.length = 5 then 1 else 0 by omega)
    exact hopen (hG.smallDiskPreHomRing_closes hH hembed hpre hsmall)
  have hconnected : H.Connected :=
    Unavoidability.connectedMinimalCounterexamples_proved H hH
  have hcubic : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hBirkhoff :=
    Birkhoff.Birkhoff hH hconnected hcubic q hqShort hqCycle
  have houtside :
      H.FaceOrbitCountOf (H.DiskFC q) ≤
        if q.length = 5 then 1 else 0 := by
    by_contra hnot
    have houtsideGt :
        (if q.length = 5 then 1 else 0) <
          H.FaceOrbitCountOf (H.DiskFC q) := by omega
    exact hBirkhoff ⟨hinside, houtsideGt⟩
  rcases hpre.exists_reverse hG hH hembed hopen (by simpa [q] using hproper) with
    ⟨rx, rp, hpreRev, hopenRev, hlenRev, hdiskRev⟩
  have hcountRev :
      H.FaceOrbitCountOf (H.DiskF ((rx :: rp).map h)) =
        H.FaceOrbitCountOf (H.DiskFC q) :=
    H.faceOrbitCountOf_congr (fun v => by
      simpa [q] using hdiskRev v)
  have hsmallRev :
      H.FaceOrbitCountOf (H.DiskF ((rx :: rp).map h)) ≤
        if (rx :: rp).length = 5 then 1 else 0 := by
    rw [hcountRev, hlenRev]
    simpa [q] using houtside
  exact hopenRev
    (hG.smallDiskPreHomRing_closes hH hembed hpreRev hsmallRev)

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
