import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingShortening

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `edge_perimeter`.  A plain edge cannot have both of its darts on an
embeddable perimeter. -/
theorem edgePerimeter
    (hG : G.Embeddable r) (x : G.Dart) :
    x ∉ r ∨ G.edge x ∉ r := by
  by_contra h
  push Not at h
  rcases h with ⟨hx, hex⟩
  have hnodeSymm : G.node.symm (G.edge x) ∈ r := by
    apply (FunctionCycle.image_mem_iff hG.cycle G.node.injective
      (G.node.symm (G.edge x))).mp
    simpa using hex
  have hfaceMem : G.face x ∈ r := by
    have hface : G.face x = G.node.symm (G.edge x) := by
      calc
        G.face x = G.face (G.edge (G.edge x)) := by
          rw [Hypermap.Plain.edge_edge (G := G) hG.plain x]
        _ = G.node.symm (G.edge x) := G.face_edge_eq_node_symm (G.edge x)
    rw [hface]
    exact hnodeSymm
  have hfaceFixed : G.face x = x :=
    (Hypermap.FaceSimple.eq_of_faceReachable_of_mem
      (G := G) hG.faceSimple hx hfaceMem
      (PermReachable.forward G.face x)).symm
  have harity : G.arity x = 1 := by
    rw [G.arity_eq_minimalPeriod x]
    exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfaceFixed
  have hbounds := (hG.ringArity hx).bounds
  omega

/-- Convert a nonempty function cycle to an `rlink` cycle when each function
step is an `rlink`. -/
private theorem rLinkCycle_of_functionCycle
    {f : G.Dart → G.Dart} {q : List G.Dart}
    (hq : FunctionCycle f q) (hne : q ≠ [])
    (hlink : ∀ y : G.Dart, y ∈ q → G.RLink y (f y)) :
    G.RLinkCycle q := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons y p =>
      have path_of_functionPath :
          ∀ {z : G.Dart} {s : List G.Dart},
            FunctionPath f z s → z ∈ y :: p →
              (∀ w : G.Dart, w ∈ s → w ∈ y :: p) →
                G.RLinkPath z s := by
        intro z s hs
        induction s generalizing z with
        | nil => simp
        | cons w s ih =>
            intro hz hall
            have hs' : f z = w ∧ FunctionPath f w s := by
              simpa [FunctionPath] using hs
            refine ⟨by simpa [hs'.1] using hlink z hz, ?_⟩
            exact ih hs'.2 (hall w (by simp))
              (fun t ht => hall t (by simp [ht]))
      refine ⟨path_of_functionPath hq.1 (by simp)
        (fun w hw => by simp [hw]), ?_⟩
      have hlastMem : (y :: p).getLastD y ∈ y :: p := by
        simp [List.getLastD]
      exact Eq.mp
        (congrArg
          (fun z => G.RLink ((y :: p).getLastD y) z) hq.2)
        (hlink ((y :: p).getLastD y) hlastMem)

/-- Coq `URrrc`: reversing an embeddable node perimeter gives a simple
`rlink` cycle. -/
theorem reversePerimeterSimpleRLinkCycle
    (hG : G.Embeddable r) (hne : r ≠ []) :
    G.SimpleRLinkCycle r.reverse := by
  have hfun : FunctionCycle G.node.symm r.reverse := by
    simpa using
      (Birkhoff.functionCycle_reverse_of_symm
        (σ := G.node.symm) hG.cycle hG.nodup)
  have hcycle : G.RLinkCycle r.reverse := by
    apply rLinkCycle_of_functionCycle hfun
    · simpa using hne
    · intro y _hy
      unfold RLink
      simpa [G.face_edge_eq_node_symm y] using
        PermReachable.forward G.face (G.edge y)
  exact ⟨hcycle,
    FaceSimple.perm (G := G) (List.reverse_perm r).symm hG.faceSimple⟩

/-- Coq `URerc`: cross the reversed perimeter cycle through the plain edge
involution. -/
theorem edgePerimeterSimpleRLinkCycle
    (hG : G.Embeddable r) (hne : r ≠ []) :
    G.SimpleRLinkCycle (G.RevRing r.reverse) :=
  SimpleRLinkCycle.revRing_of_plain (G := G) hG.plain
    (hG.reversePerimeterSimpleRLinkCycle hne)

theorem faceBand_edgePerimeter_iff
    (hG : G.Embeddable r) (hne : r ≠ []) (x : G.Dart) :
    G.FaceBand (G.RevRing r.reverse) x ↔ G.FaceBand r x := by
  exact
    (FaceBand.revRing_iff_of_plain (G := G) hG.plain
      (hG.reversePerimeterSimpleRLinkCycle hne).cycle).trans
      (FaceBand.perm (G := G) (List.reverse_perm r))

private theorem diskN_subset_of_functionCycle
    {f : G.Dart → G.Dart} {q : List G.Dart}
    (hq : FunctionCycle f q)
    (hf : ∀ y : G.Dart, y ∈ q → G.node.symm y = f y)
    {x : G.Dart} (hx : G.DiskN q x) :
    x ∈ q := by
  rcases hx with ⟨y, hy, hreach⟩
  have hstart : G.node.symm y ∈ q := by
    rw [hf y hy]
    exact hq.image_mem hy
  induction hreach with
  | refl => exact hstart
  | tail _ hstep ih => exact False.elim (hstep.1 ih)

/-- A node-cycle perimeter, read in reverse, has no `DiskN` darts beyond the
perimeter itself. -/
theorem diskN_reversePerimeter_subset
    (hG : G.Embeddable r) {x : G.Dart}
    (hx : G.DiskN r.reverse x) :
    x ∈ r := by
  have hfun : FunctionCycle G.node.symm r.reverse := by
    simpa using
      (Birkhoff.functionCycle_reverse_of_symm
        (σ := G.node.symm) hG.cycle hG.nodup)
  have hxRev : x ∈ r.reverse :=
    diskN_subset_of_functionCycle hfun (fun _ _ => rfl) hx
  simpa using hxRev

theorem mem_edgePerimeter_iff
    (hG : G.Embeddable r) (x : G.Dart) :
    x ∈ G.RevRing r.reverse ↔ G.edge x ∈ r := by
  rw [mem_revRing_of_plain (G := G) hG.plain, List.mem_reverse]

/-- Coq `erc_ok`: the crossed perimeter is a proper ring. -/
theorem edgePerimeterProper
    (hG : G.Embeddable r) (hne : r ≠ []) :
    G.ProperRing (G.RevRing r.reverse) := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons a as =>
      cases as with
      | nil =>
          have hnode : G.node a = a := by
            simpa [FunctionCycle, FunctionPath, List.getLastD] using hG.cycle.2
          have hnodeSymm : G.node.symm a = a := by
            apply G.node.injective
            simp [hnode]
          have hbridge : PermReachable G.face a (G.edge a) := by
            have hstep := PermReachable.forward G.face (G.edge a)
            rw [G.face_edge_eq_node_symm a, hnodeSymm] at hstep
            exact PermReachable.symm G.face hstep
          exact False.elim (hG.bridgeless a hbridge)
      | cons b bs =>
          cases bs with
          | nil =>
              change G.ProperRing [G.edge a, G.edge b]
              rw [properRing_cons]
              left
              intro hpath
              have haEdgeB : a = G.edge b := by
                have h := (EdgePath.cons (G := G)
                  (G.edge a) (G.edge b) []).mp hpath |>.1
                simpa [Hypermap.Plain.edge_edge (G := G) hG.plain a] using h
              have hb : b ∈ [a, b] := by simp
              have heb : G.edge b ∈ [a, b] := by simp [← haEdgeB]
              rcases hG.edgePerimeter b with hbNot | hebNot
              · exact hbNot hb
              · exact hebNot heb
          | cons c cs =>
              apply G.properRing_of_length_gt_two
              simp

/-- The chord dart selected off the literal perimeter lies in the edge
interior of Coq's crossed perimeter cycle. -/
theorem edge_mem_diskE_edgePerimeter
    (hG : G.Embeddable r) {x : G.Dart}
    (hxOff : x ∉ r) (hedgeOff : G.edge x ∉ r)
    (hxBand : G.FaceBand r x) :
    G.DiskE (G.RevRing r.reverse) (G.edge x) := by
  have hne : r ≠ [] := by
    intro hr
    subst r
    exact Hypermap.FaceBand.nil (G := G) hxBand
  have hrr := hG.reversePerimeterSimpleRLinkCycle hne
  have hproperCross := hG.edgePerimeterProper hne
  have hproperReverse : G.ProperRing r.reverse :=
    (properRing_revRing_iff_of_plain (G := G) hG.plain r.reverse).1
      hproperCross
  have hnotReverse : ¬ G.DiskN r.reverse (G.edge x) := by
    intro hdisk
    exact hedgeOff
      (diskN_reversePerimeter_subset (r := r) hG (x := G.edge x) hdisk)
  have hJordan : G.Jordan := hG.jordan
  have hdisk : G.DiskN (G.RevRing r.reverse) (G.edge x) :=
    (G.diskN_rev_ring hG.connected hJordan hG.plain hrr
      hproperReverse (G.edge x)).2 hnotReverse
  have hnotMem : G.edge x ∉ G.RevRing r.reverse := by
    rw [hG.mem_edgePerimeter_iff]
    simpa [Hypermap.Plain.edge_edge (G := G) hG.plain x] using hxOff
  exact ⟨hdisk, hnotMem⟩

theorem diskN_edgePerimeter_off
    (hG : G.Embeddable r) (hne : r ≠ []) {x : G.Dart}
    (hx : G.DiskN (G.RevRing r.reverse) x) :
    x ∉ r := by
  have hrr := hG.reversePerimeterSimpleRLinkCycle hne
  have hproperCross := hG.edgePerimeterProper hne
  have hproperReverse : G.ProperRing r.reverse :=
    (properRing_revRing_iff_of_plain (G := G) hG.plain r.reverse).1
      hproperCross
  have hJordan : G.Jordan := hG.jordan
  have hnotReverse : ¬ G.DiskN r.reverse x :=
    (G.diskN_rev_ring hG.connected hJordan hG.plain hrr
      hproperReverse x).1 hx
  intro hxr
  apply hnotReverse
  exact G.diskN_of_mem (by simpa using hxr)

/-- The fully oriented chord data at Coq's crossed perimeter `erc`. -/
def PerimeterChord (G : Hypermap.{u}) (r : List G.Dart)
    (z : G.Dart) : Prop :=
  ∃ y₁ y₂ : G.Dart, ∃ p₁ p₂ : List G.Dart, ∃ i : Nat,
    y₁ ∈ G.RevRing r.reverse ∧
      y₂ ∈ G.RevRing r.reverse ∧
        PermReachable G.face y₁ z ∧
          PermReachable G.face y₂ (G.edge z) ∧
            (G.RevRing r.reverse).rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
              G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂) ∧
                G.SimpleRLinkCycle (z :: y₂ :: p₁) ∧
                  G.SimpleRLinkCycle (G.edge z :: y₁ :: p₂) ∧
                    G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂) ∧
                      G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) z ∧
                        ∀ x : G.Dart,
                          G.DiskN (z :: y₂ :: p₁) x → x ∉ r

/-- Construct the first chord ring in `chordless_perimeter`, retaining the
same-decomposition complementary ring needed by `diskF_chord_ring`. -/
theorem perimeterChord
    (hG : G.Embeddable r) {z : G.Dart}
    (hzDisk : G.DiskE (G.RevRing r.reverse) z)
    (hzBand : G.FaceBand (G.RevRing r.reverse) z)
    (hedgeBand : G.FaceBand (G.RevRing r.reverse) (G.edge z)) :
    PerimeterChord G r z := by
  have hne : r ≠ [] := by
    intro hr
    subst r
    apply Hypermap.FaceBand.nil (G := G)
    simpa [RevRing] using hzBand
  let q := G.RevRing r.reverse
  have hq : G.SimpleRLinkCycle q :=
    hG.edgePerimeterSimpleRLinkCycle hne
  rcases hzBand with ⟨y₁, hy₁, hy₁z⟩
  rcases hedgeBand with ⟨y₂, hy₂, hy₂ez⟩
  have hy₂y₁ : y₂ ≠ y₁ := by
    intro heq
    subst y₂
    exact hG.bridgeless z
      (PermReachable.trans G.face
        (PermReachable.symm G.face hy₁z) hy₂ez)
  rcases
      SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_witnesses
        (G := G) hG.plain hq hy₁ hy₂ hy₂y₁ hy₁z hy₂ez with
    ⟨p₁, p₂, i, hdecomp, hcycle₁, hcycle₂⟩
  have hbaseCycle : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂) := by
    have hrot := SimpleRLinkCycle.rotate (G := G) i hq
    simpa [q, hdecomp] using hrot
  have hproperQ : G.ProperRing q := hG.edgePerimeterProper hne
  have hbaseProper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂) := by
    have hrot : G.ProperRing (q.rotate i) :=
      (properRing_rotate_iff_of_plain (G := G) hG.plain i q).2 hproperQ
    simpa [hdecomp] using hrot
  have hsourceDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) z := by
    have hrot : G.DiskE (q.rotate i) z :=
      (DiskE.rotate (G := G) i).2 hzDisk
    simpa [q, hdecomp] using hrot
  have hJordan : G.Jordan := hG.jordan
  have hfirstOff :
      ∀ x : G.Dart, G.DiskN (z :: y₂ :: p₁) x → x ∉ r := by
    intro x hx
    have hxBase : G.DiskN (y₂ :: p₁ ++ y₁ :: p₂) x :=
      (G.diskN_chord_prefix hG.connected hJordan hG.plain
        hbaseCycle hbaseProper hsourceDisk
        (by simp) (by simp) hcycle₁ hcycle₂ (u := x)).1 hx |>.1
    have hxQ : G.DiskN q x := by
      have hrot : G.DiskN (q.rotate i) x := by
        simpa [q, hdecomp] using hxBase
      exact (DiskN.rotate (G := G) i).1 hrot
    exact hG.diskN_edgePerimeter_off hne hxQ
  exact ⟨y₁, y₂, p₁, p₂, i, hy₁, hy₂, hy₁z, hy₂ez,
    hdecomp, hbaseCycle, hcycle₁, hcycle₂, hbaseProper,
    hsourceDisk, hfirstOff⟩

theorem perimeterChord_of_off_faceBand
    (hG : G.Embeddable r) {x : G.Dart}
    (hxOff : x ∉ r) (hedgeOff : G.edge x ∉ r)
    (hxBand : G.FaceBand r x)
    (hedgeBand : G.FaceBand r (G.edge x)) :
    PerimeterChord G r (G.edge x) := by
  have hne : r ≠ [] := by
    intro hr
    subst r
    exact Hypermap.FaceBand.nil (G := G) hxBand
  have hzDisk :
      G.DiskE (G.RevRing r.reverse) (G.edge x) :=
    hG.edge_mem_diskE_edgePerimeter hxOff hedgeOff hxBand
  have hzBand :
      G.FaceBand (G.RevRing r.reverse) (G.edge x) :=
    (hG.faceBand_edgePerimeter_iff hne (G.edge x)).2 hedgeBand
  have hedgeZBand :
      G.FaceBand (G.RevRing r.reverse) (G.edge (G.edge x)) := by
    rw [Hypermap.Plain.edge_edge (G := G) hG.plain x]
    exact (hG.faceBand_edgePerimeter_iff hne x).2 hxBand
  exact hG.perimeterChord hzDisk hzBand hedgeZBand

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
