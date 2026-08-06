import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.Perimeter

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- The strong-induction invariant in Coq `nt_dFerc`.  The head may be a
new chord dart, while every tail dart remains on the crossed perimeter and
the selected Jordan disk stays off the literal perimeter. -/
structure PerimeterInteriorRing
    (G : Hypermap.{u}) (r p : List G.Dart) : Prop where
  simpleCycle : G.SimpleRLinkCycle p
  proper : G.ProperRing p
  tailPerimeter : ∀ x : G.Dart, x ∈ p.tail →
    x ∈ G.RevRing r.reverse
  diskOff : ∀ x : G.Dart, G.DiskN p x → x ∉ r

namespace PerimeterInteriorRing

/-- The first recursive branch of Coq `nt_dFerc`: when
`efex := edge (face (edge x))` lies in the current edge interior, cut at its
perimeter projection.  The resulting chord ring is strictly shorter and
preserves the complete induction invariant. -/
theorem shortenEfex
    (hG : G.Embeddable r)
    {x : G.Dart} {p : List G.Dart}
    (P : PerimeterInteriorRing G r (x :: p))
    (hnoF : ∀ y : G.Dart, ¬ G.DiskF (x :: p) y)
    (hefexE : G.DiskE (x :: p)
      (G.edge (G.face (G.edge x)))) :
    ∃ q : List G.Dart,
      q.length < (x :: p).length ∧
        PerimeterInteriorRing G r q ∧
          ∀ y : G.Dart, ¬ G.DiskF q y := by
  let efex : G.Dart := G.edge (G.face (G.edge x))
  have hJordan : G.Jordan := hG.jordan
  have hxDisk : G.DiskN (x :: p) x :=
    G.diskN_of_mem (by simp)
  have hxOff : x ∉ r := P.diskOff x hxDisk
  have hxCubic := hG.quasicubic x hxOff
  have hfaceEfex : G.face efex = G.node x := by
    dsimp [efex]
    rw [face_edge_eq_node_symm]
    rw [← Hypermap.node_node_eq_face_edge_of_period_three
      (G := G) hxCubic.1]
    simp
  have hnodeDisk : G.DiskN (x :: p) (G.node x) :=
    (diskN_node_iff (G := G) (r := x :: p)).2 hxDisk
  have hnodeBand : G.FaceBand (x :: p) (G.node x) := by
    by_contra h
    exact hnoF (G.node x) ⟨hnodeDisk, h⟩
  have hefexBand : G.FaceBand (x :: p) efex := by
    have hre : PermReachable G.face efex (G.node x) := by
      simpa [hfaceEfex] using PermReachable.forward G.face efex
    exact (FaceBand.congr_faceReachable (G := G) hre).2 hnodeBand
  rcases hefexBand with ⟨y₁, hy₁Ring, hy₁Efex⟩
  have hy₁NeX : y₁ ≠ x := by
    intro h
    subst y₁
    apply Bridgeless.not_faceReachable_node (G := G) hG.bridgeless x
    exact PermReachable.trans G.face hy₁Efex
      (by simpa [hfaceEfex] using PermReachable.forward G.face efex)
  have hy₁Tail : y₁ ∈ p := by
    simpa [hy₁NeX] using hy₁Ring
  cases hp : p with
  | nil => simp [hp] at hy₁Tail
  | cons y₂ s =>
      have hxy₂ : G.RLink x y₂ := by
        have hpath : G.RLinkPath x (y₂ :: s) := by
          simpa [hp] using P.simpleCycle.cycle.path
        exact (RLinkPath.cons (G := G) x y₂ s).mp hpath |>.1
      have hedgeEfex : G.edge efex = G.face (G.edge x) := by
        simp [efex, Hypermap.Plain.edge_edge (G := G) hG.plain]
      have hy₂EdgeEfex :
          PermReachable G.face y₂ (G.edge efex) := by
        have hy₂FaceEdge :
            PermReachable G.face y₂ (G.face (G.edge x)) :=
          PermReachable.trans G.face
            (PermReachable.symm G.face hxy₂)
            (PermReachable.forward G.face (G.edge x))
        simpa [hedgeEfex] using hy₂FaceEdge
      have hy₂NeY₁ : y₂ ≠ y₁ := by
        intro h
        subst y₂
        apply hG.bridgeless efex
        exact PermReachable.trans G.face
          (PermReachable.symm G.face hy₁Efex) hy₂EdgeEfex
      have hy₁S : y₁ ∈ s := by
        have : y₁ ∈ y₂ :: s := by simpa [hp] using hy₁Tail
        simpa [hy₂NeY₁.symm] using this
      rcases (List.mem_iff_append).1 hy₁S with
        ⟨p₁, p₂, hs⟩
      let q₂ : List G.Dart := p₂ ++ [x]
      have hdecomp :
          (x :: y₂ :: s).rotate 1 = y₂ :: p₁ ++ y₁ :: q₂ := by
        simp [List.rotate_cons_succ, hs, q₂, List.append_assoc]
      have hbaseCycle :
          G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: q₂) := by
        have hrot := SimpleRLinkCycle.rotate (G := G) 1 P.simpleCycle
        simpa [hp, hdecomp] using hrot
      have hbaseProper :
          G.ProperRing (y₂ :: p₁ ++ y₁ :: q₂) := by
        have hrot : G.ProperRing ((x :: y₂ :: s).rotate 1) :=
          (properRing_rotate_iff_of_plain (G := G) hG.plain 1
            (x :: y₂ :: s)).2 (by simpa [hp] using P.proper)
        simpa [hdecomp] using hrot
      have hefexBase :
          G.DiskE (y₂ :: p₁ ++ y₁ :: q₂) efex := by
        have hrot : G.DiskE ((x :: y₂ :: s).rotate 1) efex :=
          (DiskE.rotate (G := G) 1).2 (by simpa [hp, efex] using hefexE)
        simpa [hdecomp] using hrot
      have hefexRy₂ : G.RLink efex y₂ := by
        unfold RLink
        have hreach := RLink.face_edge_source_reachable (G := G) hxy₂
        simpa [hedgeEfex] using hreach
      have hfirst : G.SimpleRLinkCycle (efex :: y₂ :: p₁) :=
        SimpleRLinkCycle.chord_prefix_of_decomposition
          (G := G) hbaseCycle hefexRy₂ hy₁Efex
      have hsecond :
          G.SimpleRLinkCycle (G.edge efex :: y₁ :: q₂) :=
        SimpleRLinkCycle.edge_chord_suffix_of_decomposition
          (G := G) hG.plain hbaseCycle hy₁Efex hy₂EdgeEfex
      have hedgeEfexBase :
          G.DiskE (y₂ :: p₁ ++ y₁ :: q₂) (G.edge efex) :=
        G.diskE_edge hJordan hbaseCycle hefexBase
      have hfirstProper : G.ProperRing (efex :: y₂ :: p₁) :=
        G.properRing_chord_prefix_of_diskE_edge hedgeEfexBase (by simp)
      have hshort :
          (efex :: y₂ :: p₁).length < (x :: p).length := by
        have hlt := G.length_chord_prefix_lt_of_decomposition
          hdecomp (x := efex) (by simp [q₂])
        simpa [hp] using hlt
      have htailPerimeter :
          ∀ z : G.Dart, z ∈ (efex :: y₂ :: p₁).tail →
            z ∈ G.RevRing r.reverse := by
        intro z hz
        apply P.tailPerimeter z
        simp only [List.tail_cons] at hz ⊢
        rw [hp, hs]
        simp only [List.mem_cons, List.mem_append] at hz ⊢
        tauto
      have hdiskOff :
          ∀ z : G.Dart, G.DiskN (efex :: y₂ :: p₁) z → z ∉ r := by
        intro z hz
        have hzBase : G.DiskN (y₂ :: p₁ ++ y₁ :: q₂) z :=
          (G.diskN_chord_prefix hG.connected hJordan hG.plain
            hbaseCycle hbaseProper hefexBase (by simp) (by simp)
            hfirst hsecond (u := z)).1 hz |>.1
        have hzRot : G.DiskN ((x :: y₂ :: s).rotate 1) z := by
          simpa [hdecomp] using hzBase
        have hzOld : G.DiskN (x :: y₂ :: s) z :=
          (DiskN.rotate (G := G) 1).1 hzRot
        exact P.diskOff z (by simpa [hp] using hzOld)
      have hnoF' : ∀ z : G.Dart,
          ¬ G.DiskF (efex :: y₂ :: p₁) z := by
        intro z hz
        have hzBase : G.DiskF (y₂ :: p₁ ++ y₁ :: q₂) z :=
          (G.diskF_chord_prefix hG.connected hJordan hG.plain
            hbaseCycle hbaseProper hefexBase (by simp) (by simp)
            hy₁Efex hy₂EdgeEfex hfirst hsecond (u := z)).1 hz |>.1
        have hzRot : G.DiskF ((x :: y₂ :: s).rotate 1) z := by
          simpa [hdecomp] using hzBase
        have hzOld : G.DiskF (x :: y₂ :: s) z :=
          (DiskF.rotate (G := G) 1).1 hzRot
        exact hnoF z (by simpa [hp] using hzOld)
      have hshort' :
          (efex :: y₂ :: p₁).length < (x :: y₂ :: s).length := by
        simpa [hp] using hshort
      exact ⟨efex :: y₂ :: p₁, hshort',
        ⟨hfirst, hfirstProper, htailPerimeter, hdiskOff⟩, hnoF'⟩

/-- The complementary recursive branch of Coq `nt_dFerc`.  If `efex` is not
in the current edge interior, the first tail dart is `face (edge x)`.  The
perimeter arity bound excludes a later occurrence of `node x`, so
`enx := edge (node x)` is an interior chord and yields a shorter invariant
ring. -/
theorem shortenEnx
    (hG : G.Embeddable r)
    {x : G.Dart} {p : List G.Dart}
    (P : PerimeterInteriorRing G r (x :: p))
    (hnoF : ∀ y : G.Dart, ¬ G.DiskF (x :: p) y)
    (hefexNotE : ¬ G.DiskE (x :: p)
      (G.edge (G.face (G.edge x)))) :
    ∃ q : List G.Dart,
      q.length < (x :: p).length ∧
        PerimeterInteriorRing G r q ∧
          ∀ y : G.Dart, ¬ G.DiskF q y := by
  let fex : G.Dart := G.face (G.edge x)
  let efex : G.Dart := G.edge fex
  let enx : G.Dart := G.edge (G.node x)
  have hJordan : G.Jordan := hG.jordan
  have hxDisk : G.DiskN (x :: p) x :=
    G.diskN_of_mem (by simp)
  have hxOff : x ∉ r := P.diskOff x hxDisk
  have hxCubic := hG.quasicubic x hxOff
  have hfexEq : fex = G.node (G.node x) := by
    exact (Hypermap.node_node_eq_face_edge_of_period_three
      (G := G) hxCubic.1).symm
  have hfaceEfex : G.face efex = G.node x := by
    dsimp [efex]
    rw [face_edge_eq_node_symm]
    rw [hfexEq]
    simp
  have hedgeEnx : G.edge enx = G.node x := by
    simp [enx, Hypermap.Plain.edge_edge (G := G) hG.plain]
  have hfaceEnx : G.face enx = x := by
    exact G.face_edge_node x
  have hfexDisk : G.DiskN (x :: p) fex := by
    exact G.diskN_face_edge_of_mem (r := x :: p) (x := x) (by simp)
  have hfexNotE : ¬ G.DiskE (x :: p) fex := by
    intro hfexE
    have hedgeFexE : G.DiskE (x :: p) (G.edge fex) :=
      G.diskE_edge hJordan P.simpleCycle hfexE
    exact hefexNotE (by simpa [efex, fex] using hedgeFexE)
  have hfexMem : fex ∈ x :: p := by
    by_contra hfexNot
    exact hfexNotE ⟨hfexDisk, hfexNot⟩
  have hfexNeX : fex ≠ x := by
    intro h
    have hreach : PermReachable G.face (G.edge x) fex := by
      exact PermReachable.forward G.face (G.edge x)
    exact hG.bridgeless x
      (PermReachable.symm G.face (by simpa [h] using hreach))
  have hfexTail : fex ∈ p := by
    simpa [hfexNeX] using hfexMem
  cases hp : p with
  | nil => simp [hp] at hfexTail
  | cons y s =>
      have hxy : G.RLink x y := by
        have hpath : G.RLinkPath x (y :: s) := by
          simpa [hp] using P.simpleCycle.cycle.path
        exact (RLinkPath.cons (G := G) x y s).mp hpath |>.1
      have hxfex : G.RLink x fex := by
        unfold RLink
        exact PermReachable.forward G.face (G.edge x)
      have hyEq : y = fex :=
        SimpleRLinkCycle.eq_of_same_rlink_source
          (G := G) P.simpleCycle (by simp [hp]) hfexMem hxy hxfex
      subst y
      have hnodeDisk : G.DiskN (x :: fex :: s) (G.node x) :=
        (diskN_node_iff (G := G) (r := x :: fex :: s)).2
          (by simpa [hp] using hxDisk)
      have hnodeBand : G.FaceBand (x :: fex :: s) (G.node x) := by
        by_contra h
        exact hnoF (G.node x) (by simpa [hp] using
          (show G.DiskF (x :: fex :: s) (G.node x) from
            ⟨hnodeDisk, h⟩))
      have hfexPerimeter : fex ∈ G.RevRing r.reverse := by
        apply P.tailPerimeter fex
        simp [hp]
      have hefexPerimeter : efex ∈ r := by
        have := (hG.mem_edgePerimeter_iff fex).1 hfexPerimeter
        simpa [efex] using this
      have hnodeNotS : G.node x ∉ s := by
        intro hnodeS
        have hnodeCrossed : G.node x ∈ G.RevRing r.reverse := by
          apply P.tailPerimeter (G.node x)
          simp [hp, hnodeS]
        have henxPerimeter : enx ∈ r := by
          have := (hG.mem_edgePerimeter_iff (G.node x)).1 hnodeCrossed
          simpa [enx] using this
        have hnodeSymmEnx : G.node.symm enx ∈ r := by
          apply (FunctionCycle.image_mem_iff hG.cycle G.node.injective
            (G.node.symm enx)).mp
          simpa using henxPerimeter
        have hfaceNodePerimeter : G.face (G.node x) ∈ r := by
          have hid : G.node.symm enx = G.face (G.node x) := by
            calc
              G.node.symm enx = G.face (G.edge enx) :=
                (face_edge_eq_node_symm (G := G) enx).symm
              _ = G.face (G.node x) := by rw [hedgeEnx]
          simpa [hid] using hnodeSymmEnx
        have hfaceNodeReachEfex :
            PermReachable G.face (G.face (G.node x)) efex := by
          have hback :
              PermReachable G.face (G.face (G.node x)) (G.node x) := by
            simpa using PermReachable.backward G.face (G.face (G.node x))
          have htoEfex : PermReachable G.face (G.node x) efex := by
            exact PermReachable.symm G.face
              (by simpa [hfaceEfex] using
                PermReachable.forward G.face efex)
          exact PermReachable.trans G.face hback htoEfex
        have hfaceNodeEq : G.face (G.node x) = efex :=
          FaceSimple.eq_of_faceReachable_of_mem
            (G := G) hG.faceSimple hfaceNodePerimeter hefexPerimeter
              hfaceNodeReachEfex
        have hperiodTwo : G.face (G.face (G.node x)) = G.node x := by
          rw [hfaceNodeEq, hfaceEfex]
        have hdiv : G.arity (G.node x) ∣ 2 := by
          apply G.arity_dvd_of_face_iterate_eq_self
          simpa [Function.iterate_succ_apply'] using hperiodTwo
        have harityLe : G.arity (G.node x) ≤ 2 :=
          Nat.le_of_dvd (by omega) hdiv
        have hefexReachNode :
            PermReachable G.face efex (G.node x) := by
          simpa [hfaceEfex] using PermReachable.forward G.face efex
        have harityEq : G.arity efex = G.arity (G.node x) :=
          G.arity_eq_of_faceReachable hefexReachNode
        have harityGe : 3 ≤ G.arity efex :=
          (hG.ringArity hefexPerimeter).bounds.1
        omega
      have hnodeNeX : G.node x ≠ x := hxCubic.2
      have hnodeNeFex : G.node x ≠ fex := by
        intro h
        have h' : G.node x = G.node (G.node x) := h.trans hfexEq
        exact hnodeNeX (G.node.injective h'.symm)
      have hnodeNotMem : G.node x ∉ x :: fex :: s := by
        simp [hnodeNeX, hnodeNeFex, hnodeNotS]
      have hnodeE : G.DiskE (x :: fex :: s) (G.node x) :=
        ⟨hnodeDisk, hnodeNotMem⟩
      have henxE : G.DiskE (x :: fex :: s) enx := by
        have := G.diskE_edge hJordan
          (by simpa [hp] using P.simpleCycle) hnodeE
        simpa [enx] using this
      have hxEnx : PermReachable G.face x enx := by
        exact PermReachable.symm G.face
          (by simpa [hfaceEnx] using PermReachable.forward G.face enx)
      rcases hnodeBand with ⟨y₂, hy₂Ring, hy₂Node⟩
      have hy₂EdgeEnx : PermReachable G.face y₂ (G.edge enx) := by
        simpa [hedgeEnx] using hy₂Node
      have hy₂NeX : y₂ ≠ x := by
        intro h
        subst y₂
        exact Bridgeless.not_faceReachable_node
          (G := G) hG.bridgeless x hy₂Node
      have hy₂NeFex : y₂ ≠ fex := by
        intro h
        subst y₂
        apply Bridgeless.not_faceReachable_node_left
          (G := G) hG.bridgeless (G.node x)
        simpa [hfexEq] using hy₂Node
      have hy₂S : y₂ ∈ s := by
        simpa [hy₂NeX, hy₂NeFex] using hy₂Ring
      rcases (List.mem_iff_append).1 hy₂S with
        ⟨p₁, p₂, hs⟩
      let i : Nat := (x :: fex :: p₁).length
      have hdecomp :
          (x :: fex :: s).rotate i = y₂ :: p₂ ++ x :: fex :: p₁ := by
        have hsplit :
            x :: fex :: s = (x :: fex :: p₁) ++ y₂ :: p₂ := by
          simp [hs]
        rw [hsplit]
        simp [i]
      have hbaseCycle :
          G.SimpleRLinkCycle (y₂ :: p₂ ++ x :: fex :: p₁) := by
        have hrot := SimpleRLinkCycle.rotate (G := G) i
          (by simpa [hp] using P.simpleCycle)
        simpa [hdecomp] using hrot
      have hbaseProper :
          G.ProperRing (y₂ :: p₂ ++ x :: fex :: p₁) := by
        have hrot : G.ProperRing ((x :: fex :: s).rotate i) :=
          (properRing_rotate_iff_of_plain (G := G) hG.plain i
            (x :: fex :: s)).2 (by simpa [hp] using P.proper)
        simpa [hdecomp] using hrot
      have henxBase :
          G.DiskE (y₂ :: p₂ ++ x :: fex :: p₁) enx := by
        have hrot : G.DiskE ((x :: fex :: s).rotate i) enx :=
          (DiskE.rotate (G := G) i).2 henxE
        simpa [hdecomp] using hrot
      have henxRy₂ : G.RLink enx y₂ := by
        unfold RLink
        simpa [hedgeEnx] using
          (PermReachable.symm G.face hy₂Node)
      have hfirst : G.SimpleRLinkCycle (enx :: y₂ :: p₂) :=
        SimpleRLinkCycle.chord_prefix_of_decomposition
          (G := G) hbaseCycle henxRy₂ hxEnx
      have hsecond :
          G.SimpleRLinkCycle (G.edge enx :: x :: fex :: p₁) :=
        SimpleRLinkCycle.edge_chord_suffix_of_decomposition
          (G := G) hG.plain hbaseCycle hxEnx hy₂EdgeEnx
      have hfirstProper : G.ProperRing (enx :: y₂ :: p₂) :=
        G.properRing_chord_prefix_of_diskE_edge
          (by simpa [hedgeEnx] using
            G.diskE_edge hJordan hbaseCycle henxBase)
          (by simp)
      have hshort :
          (enx :: y₂ :: p₂).length < (x :: fex :: s).length := by
        exact G.length_chord_prefix_lt_of_decomposition
          hdecomp (x := enx) (by simp)
      have htailPerimeter :
          ∀ z : G.Dart, z ∈ (enx :: y₂ :: p₂).tail →
            z ∈ G.RevRing r.reverse := by
        intro z hz
        apply P.tailPerimeter z
        simp only [List.tail_cons] at hz ⊢
        rw [hp, hs]
        simp only [List.mem_cons, List.mem_append] at hz ⊢
        tauto
      have hdiskOff :
          ∀ z : G.Dart, G.DiskN (enx :: y₂ :: p₂) z → z ∉ r := by
        intro z hz
        have hzBase : G.DiskN (y₂ :: p₂ ++ x :: fex :: p₁) z :=
          (G.diskN_chord_prefix hG.connected hJordan hG.plain
            hbaseCycle hbaseProper henxBase (by simp) (by simp)
            hfirst hsecond (u := z)).1 hz |>.1
        have hzRot : G.DiskN ((x :: fex :: s).rotate i) z := by
          simpa [hdecomp] using hzBase
        have hzOld : G.DiskN (x :: fex :: s) z :=
          (DiskN.rotate (G := G) i).1 hzRot
        exact P.diskOff z (by simpa [hp] using hzOld)
      have hnoF' : ∀ z : G.Dart,
          ¬ G.DiskF (enx :: y₂ :: p₂) z := by
        intro z hz
        have hzBase : G.DiskF (y₂ :: p₂ ++ x :: fex :: p₁) z :=
          (G.diskF_chord_prefix hG.connected hJordan hG.plain
            hbaseCycle hbaseProper henxBase (by simp) (by simp)
            hxEnx hy₂EdgeEnx hfirst hsecond (u := z)).1 hz |>.1
        have hzRot : G.DiskF ((x :: fex :: s).rotate i) z := by
          simpa [hdecomp] using hzBase
        have hzOld : G.DiskF (x :: fex :: s) z :=
          (DiskF.rotate (G := G) i).1 hzRot
        exact hnoF z (by simpa [hp] using hzOld)
      exact ⟨enx :: y₂ :: p₂, hshort,
        ⟨hfirst, hfirstProper, htailPerimeter, hdiskOff⟩, hnoF'⟩

/-- Coq `nt_dFerc`: every proper simple recursive chord ring satisfying the
crossed-perimeter support and off-perimeter disk invariants has a strict
interior face.  Strong induction follows the two checked `efex`/`enx`
shortening branches above. -/
theorem diskF_nonempty
    (hG : G.Embeddable r)
    {p : List G.Dart}
    (P : PerimeterInteriorRing G r p) :
    ∃ y : G.Dart, G.DiskF p y := by
  let Q : Nat → Prop := fun n =>
    ∀ q : List G.Dart, q.length = n →
      PerimeterInteriorRing G r q →
        ∃ y : G.Dart, G.DiskF q y
  have hQ : ∀ n : Nat, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hqLen hq
        by_contra hnone
        push Not at hnone
        cases hqEq : q with
        | nil =>
            have : ¬ G.ProperRing q := by simp [hqEq]
            exact (this hq.proper).elim
        | cons x s =>
            have hq' : PerimeterInteriorRing G r (x :: s) := by
              simpa [hqEq] using hq
            have hnone' : ∀ y : G.Dart,
                ¬ G.DiskF (x :: s) y := by
              simpa [hqEq] using hnone
            have impossible_of_shorter
                {q' : List G.Dart}
                (hshort : q'.length < (x :: s).length)
                (hq'Inv : PerimeterInteriorRing G r q')
                (hq'None : ∀ y : G.Dart, ¬ G.DiskF q' y) : False := by
              have hlt : q'.length < n := by
                calc
                  q'.length < (x :: s).length := hshort
                  _ = q.length := by rw [hqEq]
                  _ = n := hqLen
              rcases ih q'.length hlt q' rfl hq'Inv with ⟨y, hy⟩
              exact hq'None y hy
            by_cases hefex : G.DiskE (x :: s)
                (G.edge (G.face (G.edge x)))
            · rcases hq'.shortenEfex hG hnone' hefex with
                ⟨q', hshort, hq'Inv, hq'None⟩
              exact impossible_of_shorter hshort hq'Inv hq'None
            · rcases hq'.shortenEnx hG hnone' hefex with
                ⟨q', hshort, hq'Inv, hq'None⟩
              exact impossible_of_shorter hshort hq'Inv hq'None
  exact hQ p.length p rfl P

end PerimeterInteriorRing

/-- Coq `dFerc_ac`: once the selected perimeter chord ring has one strict
interior face, its strict face side is exactly the configuration kernel. -/
theorem diskF_chordPrefix_iff_kernel_of_nonempty
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    {z y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hbaseCycle : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hbaseProper : G.ProperRing (y₂ :: p₁ ++ y₁ :: p₂))
    (hzDisk : G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) z)
    (hy₁z : PermReachable G.face y₁ z)
    (hy₂ez : PermReachable G.face y₂ (G.edge z))
    (hfirst : G.SimpleRLinkCycle (z :: y₂ :: p₁))
    (hsecond : G.SimpleRLinkCycle (G.edge z :: y₁ :: p₂))
    (hbaseBand : ∀ x : G.Dart,
      G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) x ↔ G.FaceBand r x)
    (hinside : ∃ y : G.Dart, G.DiskF (z :: y₂ :: p₁) y) :
    ∀ x : G.Dart,
      G.DiskF (z :: y₂ :: p₁) x ↔ G.Kernel r x := by
  have hJordan : G.Jordan := hG.jordan
  have hfirstBand : ∀ {x : G.Dart},
      G.FaceBand (z :: y₂ :: p₁) x → G.FaceBand r x := by
    intro x hx
    apply (hbaseBand x).1
    exact (FaceBand.chord_prefix_union (G := G)
      (u := x) hy₁z hy₂ez).1 (Or.inl hx)
  have hdiskToKernel : ∀ {x : G.Dart},
      G.DiskF (z :: y₂ :: p₁) x → G.Kernel r x := by
    intro x hx
    have hsplit := G.diskF_chord_prefix
      hG.connected hJordan hG.plain hbaseCycle hbaseProper hzDisk
      (by simp) (by simp) hy₁z hy₂ez hfirst hsecond (u := x)
    have hxBase : G.DiskF (y₂ :: p₁ ++ y₁ :: p₂) x :=
      (hsplit.1 hx).1
    intro hxBand
    exact hxBase.2 ((hbaseBand x).2 hxBand)
  have hkernelDiskToF : ∀ {x : G.Dart},
      G.Kernel r x → G.DiskN (z :: y₂ :: p₁) x →
        G.DiskF (z :: y₂ :: p₁) x := by
    intro x hxKernel hxDisk
    refine ⟨hxDisk, ?_⟩
    intro hxBand
    exact hxKernel (hfirstBand hxBand)
  rcases hinside with ⟨y, hyF⟩
  have hyKernel : G.Kernel r y := hdiskToKernel hyF
  intro x
  constructor
  · exact hdiskToKernel
  · intro hxKernel
    have heeyKernel : G.Kernel r (G.edge (G.edge y)) := by
      simpa [Hypermap.Plain.edge_edge (G := G) hG.plain y] using hyKernel
    rcases hembed.simplePath (G.kernel_faceClosed r) heeyKernel hxKernel with
      ⟨p, hp, hlast, hpNe, _hpSimple, hpKernel⟩
    cases p with
    | nil => exact False.elim (hpNe rfl)
    | cons t ts =>
        have hfirstLink : G.RLink (G.edge y) t := hp.1
        have hyt : PermReachable G.face y t := by
          simpa [RLink,
            Hypermap.Plain.edge_edge (G := G) hG.plain y] using hfirstLink
        have htF : G.DiskF (z :: y₂ :: p₁) t :=
          G.diskF_of_faceReachable hyt hyF
        have htailPath : G.RLinkPath t ts := hp.2
        have hpropagate :
            ∀ {a : G.Dart} {s : List G.Dart},
              G.RLinkPath a s →
                G.DiskF (z :: y₂ :: p₁) a →
                  (∀ w : G.Dart, w ∈ s → G.Kernel r w) →
                    G.DiskF (z :: y₂ :: p₁)
                      ((a :: s).getLastD a) := by
          intro a s hs haF hall
          induction s generalizing a with
          | nil => simpa [List.getLastD] using haF
          | cons b s ih =>
              have hs' : G.RLink a b ∧ G.RLinkPath b s := by
                simpa [RLinkPath] using hs
              have hbKernel : G.Kernel r b := hall b (by simp)
              have hedgeAKernel : G.Kernel r (G.edge a) :=
                G.kernel_faceClosed r hbKernel
                  (PermReachable.symm G.face hs'.1)
              have haNotMem : a ∉ z :: y₂ :: p₁ := by
                intro haMem
                exact haF.2
                  (FaceBand.of_mem (G := G) haMem
                    (PermReachable.refl G.face a))
              have hedgeADisk :
                  G.DiskN (z :: y₂ :: p₁) (G.edge a) :=
                (G.diskE_edge hJordan hfirst ⟨haF.1, haNotMem⟩).1
              have hedgeAF : G.DiskF (z :: y₂ :: p₁) (G.edge a) :=
                hkernelDiskToF hedgeAKernel hedgeADisk
              have hbF : G.DiskF (z :: y₂ :: p₁) b :=
                G.diskF_of_faceReachable hs'.1 hedgeAF
              exact ih hs'.2 hbF
                (fun w hw => hall w (by simp [hw]))
        have hlastF :
            G.DiskF (z :: y₂ :: p₁) ((t :: ts).getLastD t) :=
          hpropagate htailPath htF
            (fun w hw => (hpKernel w (by simp [hw])).1)
        have hlastEq :
            ((G.edge y :: t :: ts).getLastD (G.edge y)) =
              (t :: ts).getLastD t := by
          simp [List.getLastD]
        rw [hlastEq] at hlast
        exact G.diskF_of_faceReachable hlast hlastF

/-- Coq `chordless_perimeter`: an edge whose two darts miss the literal
perimeter cannot have both incident faces in the perimeter face band. -/
theorem chordlessPerimeter
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart}
    (hxOff : x ∉ r) (hedgeOff : G.edge x ∉ r) :
    G.Kernel r x ∨ G.Kernel r (G.edge x) := by
  by_cases hxKernel : G.Kernel r x
  · exact Or.inl hxKernel
  by_cases hedgeKernel : G.Kernel r (G.edge x)
  · exact Or.inr hedgeKernel
  have hxBand : G.FaceBand r x := by
    exact Classical.not_not.mp hxKernel
  have hedgeBand : G.FaceBand r (G.edge x) := by
    exact Classical.not_not.mp hedgeKernel
  have hne : r ≠ [] := by
    intro hr
    subst r
    exact Hypermap.FaceBand.nil (G := G) hxBand
  let z : G.Dart := G.edge x
  have hc : PerimeterChord G r z := by
    dsimp [z]
    exact hG.perimeterChord_of_off_faceBand
      hxOff hedgeOff hxBand hedgeBand
  rcases hc with
    ⟨y₁, y₂, p₁, p₂, i, hy₁Q, hy₂Q, hy₁z, hy₂ez,
      hdecomp, hbaseCycle, hfirst, hsecond, hbaseProper,
      hzDisk, hfirstOff⟩
  let q : List G.Dart := G.RevRing r.reverse
  have hqdecomp : q.rotate i = y₂ :: p₁ ++ y₁ :: p₂ := by
    simpa [q] using hdecomp
  have hqCycle : G.SimpleRLinkCycle q :=
    hG.edgePerimeterSimpleRLinkCycle hne
  have hJordan : G.Jordan := hG.jordan
  have hbaseBand : ∀ u : G.Dart,
      G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) u ↔ G.FaceBand r u := by
    intro u
    calc
      G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) u ↔
          G.FaceBand (q.rotate i) u := by rw [hdecomp]
      _ ↔ G.FaceBand q u := FaceBand.rotate (G := G) i
      _ ↔ G.FaceBand r u := hG.faceBand_edgePerimeter_iff hne u
  have hedgeZDisk :
      G.DiskE (y₂ :: p₁ ++ y₁ :: p₂) (G.edge z) :=
    G.diskE_edge hJordan hbaseCycle hzDisk
  have hfirstProper : G.ProperRing (z :: y₂ :: p₁) :=
    G.properRing_chord_prefix_of_diskE_edge hedgeZDisk (by simp)
  have hfirstTail : ∀ u : G.Dart, u ∈ (z :: y₂ :: p₁).tail →
      u ∈ q := by
    intro u hu
    have huBase : u ∈ y₂ :: p₁ ++ y₁ :: p₂ := by
      simp only [List.tail_cons] at hu
      simp only [List.mem_cons, List.mem_append] at hu ⊢
      tauto
    have huRot : u ∈ q.rotate i := by
      rw [hqdecomp]
      exact huBase
    simpa [List.mem_rotate] using huRot
  have hfirstInv : PerimeterInteriorRing G r (z :: y₂ :: p₁) :=
    ⟨hfirst, hfirstProper, hfirstTail, hfirstOff⟩
  rcases hfirstInv.diskF_nonempty hG with ⟨y, hyFirst⟩
  have hfirstKernel := hG.diskF_chordPrefix_iff_kernel_of_nonempty
    hembed hbaseCycle hbaseProper hzDisk hy₁z hy₂ez hfirst hsecond
      hbaseBand ⟨y, hyFirst⟩
  have hyKernel : G.Kernel r y := (hfirstKernel y).1 hyFirst
  have hpartition : ∀ u : G.Dart,
      G.DiskNPartition
        (y₂ :: p₁ ++ y₁ :: p₂)
        (z :: y₂ :: p₁)
        (G.edge z :: y₁ :: p₂) u := by
    intro u
    exact G.diskNPartition_chord_prefix
      hG.connected hJordan hG.plain hbaseCycle hbaseProper hzDisk
        (by simp) (by simp) hfirst hsecond u
  have hySplit := G.diskF_chord_prefix
    hG.connected hJordan hG.plain hbaseCycle hbaseProper hzDisk
      (by simp) (by simp) hy₁z hy₂ez hfirst hsecond (u := y)
  have hyNotSecond : ¬ G.DiskF (G.edge z :: y₁ :: p₂) y :=
    (hySplit.1 hyFirst).2
  have hsecondProper : G.ProperRing (G.edge z :: y₁ :: p₂) := by
    apply G.properRing_chord_prefix_of_diskE_edge
      (r := y₂ :: p₁ ++ y₁ :: p₂)
      (x := G.edge z) (y₂ := y₁) (p₁ := p₂)
    · simpa [Hypermap.Plain.edge_edge (G := G) hG.plain z] using hzDisk
    · simp
  have hsecondTail :
      ∀ u : G.Dart, u ∈ (G.edge z :: y₁ :: p₂).tail → u ∈ q := by
    intro u hu
    have huBase : u ∈ y₂ :: p₁ ++ y₁ :: p₂ := by
      simp only [List.tail_cons] at hu
      simp only [List.mem_cons, List.mem_append] at hu ⊢
      tauto
    have huRot : u ∈ q.rotate i := by
      rw [hqdecomp]
      exact huBase
    simpa [List.mem_rotate] using huRot
  have hsecondOff :
      ∀ u : G.Dart, G.DiskN (G.edge z :: y₁ :: p₂) u → u ∉ r := by
    intro u hu
    have huBase : G.DiskN (y₂ :: p₁ ++ y₁ :: p₂) u :=
      (hpartition u).1.1 (Or.inr hu)
    have huRot : G.DiskN (q.rotate i) u := by
      rw [hqdecomp]
      exact huBase
    have huQ : G.DiskN q u := (DiskN.rotate (G := G) i).1 huRot
    exact hG.diskN_edgePerimeter_off hne huQ
  have hsecondInv :
      PerimeterInteriorRing G r (G.edge z :: y₁ :: p₂) :=
    ⟨hsecond, hsecondProper, hsecondTail, hsecondOff⟩
  rcases hsecondInv.diskF_nonempty hG with ⟨w, hwSecond⟩
  let j : Nat := (y₂ :: p₁).length
  have hswap :
      (y₂ :: p₁ ++ y₁ :: p₂).rotate j =
        y₁ :: p₂ ++ y₂ :: p₁ := by
    simp [j]
  have hswapCycle :
      G.SimpleRLinkCycle (y₁ :: p₂ ++ y₂ :: p₁) := by
    have hrot := SimpleRLinkCycle.rotate (G := G) j hbaseCycle
    rw [hswap] at hrot
    exact hrot
  have hswapProper : G.ProperRing (y₁ :: p₂ ++ y₂ :: p₁) := by
    have hrot : G.ProperRing
        ((y₂ :: p₁ ++ y₁ :: p₂).rotate j) :=
      (properRing_rotate_iff_of_plain (G := G) hG.plain j
        (y₂ :: p₁ ++ y₁ :: p₂)).2 hbaseProper
    rw [hswap] at hrot
    exact hrot
  have hedgeZSwapDisk :
      G.DiskE (y₁ :: p₂ ++ y₂ :: p₁) (G.edge z) := by
    have hrot : G.DiskE
        ((y₂ :: p₁ ++ y₁ :: p₂).rotate j) (G.edge z) :=
      (DiskE.rotate (G := G) j).2 hedgeZDisk
    rw [hswap] at hrot
    exact hrot
  have hy₁eez : PermReachable G.face y₁ (G.edge (G.edge z)) := by
    simpa [Hypermap.Plain.edge_edge (G := G) hG.plain z] using hy₁z
  have hfirstSwap :
      G.SimpleRLinkCycle (G.edge z :: y₁ :: p₂) := hsecond
  have hsecondSwap :
      G.SimpleRLinkCycle (G.edge (G.edge z) :: y₂ :: p₁) := by
    simpa [Hypermap.Plain.edge_edge (G := G) hG.plain z] using hfirst
  have hswapBand : ∀ u : G.Dart,
      G.FaceBand (y₁ :: p₂ ++ y₂ :: p₁) u ↔ G.FaceBand r u := by
    intro u
    calc
      G.FaceBand (y₁ :: p₂ ++ y₂ :: p₁) u ↔
          G.FaceBand ((y₂ :: p₁ ++ y₁ :: p₂).rotate j) u := by
            rw [hswap]
      _ ↔ G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) u :=
        FaceBand.rotate (G := G) j
      _ ↔ G.FaceBand r u := hbaseBand u
  have hsecondKernel := hG.diskF_chordPrefix_iff_kernel_of_nonempty
    hembed hswapCycle hswapProper hedgeZSwapDisk
      hy₂ez hy₁eez hfirstSwap hsecondSwap hswapBand ⟨w, hwSecond⟩
  exact (hyNotSecond ((hsecondKernel y).2 hyKernel)).elim

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
