
import FourColorTheorem.FourColor.Coloring.Birkhoff
import FourColorTheorem.FourColor.Reducibility.Soundness
import FourColorTheorem.FourColor.Hypermap.WalkupCubicity

/-!
Extension of configuration preembeddings to patches.

This is the Lean port boundary for Coq `embed.v`.  The low-level path and
preembedding vocabulary remains in `Embedding.lean`; this module is above
`QuizEmbedding`, `Birkhoff`, and `Patch`, avoiding the import cycle that would
result from putting the extension argument next to the vocabulary.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u v

/-- The well-founded induction invariant in Coq `embed_functor`: the cycle's
head is the unique currently noncentral boundary dart, its tail is central,
and the selected Jordan disk remains inside the configuration kernel. -/
structure KernelBadCycle
    (G : Hypermap.{u}) (H : Hypermap.{u})
    (r : List G.Dart) (h : G.Dart → H.Dart) where
  head : G.Dart
  tail : List G.Dart
  headNotCentral : ¬ EdgeCentral G H h head
  simpleCycle : G.SimpleRLinkCycle (head :: tail)
  tailCentral : ∀ x : G.Dart, x ∈ tail →
    G.Kernel r x ∧ EdgeCentral G H h x
  diskKernel : ∀ x : G.Dart, G.DiskN (head :: tail) x → G.Kernel r x

namespace KernelBadCycle

variable {G H : Hypermap.{u}}
variable {r : List G.Dart} {h : G.Dart → H.Dart}

/-- The finite Jordan disk used as the well-founded measure in Coq
`embed_functor`. -/
noncomputable def diskFinset
    (B : KernelBadCycle G H r h) : Finset G.Dart := by
  classical
  exact Finset.univ.filter (G.DiskN (B.head :: B.tail))

@[simp]
theorem mem_diskFinset
    (B : KernelBadCycle G H r h) (x : G.Dart) :
    x ∈ B.diskFinset ↔ G.DiskN (B.head :: B.tail) x := by
  classical
  simp [diskFinset]

/-- Cardinal form of the well-founded disk measure. -/
noncomputable def diskCard
    (B : KernelBadCycle G H r h) : Nat :=
  B.diskFinset.card

theorem cycleKernel
    (B : KernelBadCycle G H r h) :
    ∀ x : G.Dart, x ∈ B.head :: B.tail → G.Kernel r x := by
  intro x hx
  exact B.diskKernel x (G.diskN_of_mem hx)

/-- Coq's local `proper_xp1` argument, including the one- and two-dart
degenerate cases. -/
theorem proper_of_simpleCycle_tail_edgeCentral
    {x : G.Dart} {p : List G.Dart}
    (hxNot : ¬ EdgeCentral G H h x)
    (hcycle : G.SimpleRLinkCycle (x :: p))
    (hpCentral : ∀ y : G.Dart, y ∈ p → EdgeCentral G H h y)
    (hBridgeless : G.Bridgeless)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    G.ProperRing (x :: p) := by
  cases htail : p with
  | nil =>
      have hloop : G.RLink x x := by
        simpa [htail, List.getLastD] using hcycle.cycle.closing
      exact False.elim
        (hBridgeless x (PermReachable.symm G.face hloop))
  | cons y ys =>
      cases ys with
      | nil =>
          rw [properRing_cons]
          left
          intro hEdge
          have hxy : G.edge x = y := by
            simpa [EdgePath] using hEdge
          have hyCentral : EdgeCentral G H h y :=
            hpCentral y (by simp [htail])
          have hxCentral : EdgeCentral G H h x :=
            (edgeCentral_edge_iff G H hPlainG hPlainH h x).1
              (by simpa [hxy] using hyCentral)
          exact hxNot hxCentral
      | cons z zs =>
          exact G.properRing_of_length_gt_two (by simp)

theorem proper
    (B : KernelBadCycle G H r h)
    (hBridgeless : G.Bridgeless)
    (hPlainG : G.Plain) (hPlainH : H.Plain) :
    G.ProperRing (B.head :: B.tail) :=
  proper_of_simpleCycle_tail_edgeCentral B.headNotCentral B.simpleCycle
    (fun x hx => (B.tailCentral x hx).2) hBridgeless hPlainG hPlainH

end KernelBadCycle

/-- Coq `embeddable r`: the perimeter is a face-simple node cycle in a planar,
bridgeless, plain, connected map, the map is cubic off the perimeter, accepted
ring faces have arity three through six, and the kernel has radius two. -/
structure Embeddable (G : Hypermap.{u}) (r : List G.Dart) : Prop where
  cycle : FunctionCycle G.node r
  faceSimple : G.FaceSimple r
  planar : G.EulerPlanar
  bridgeless : G.Bridgeless
  plain : G.Plain
  quasicubic : G.Quasicubic r
  connected : G.Connected
  ringArity : ∀ ⦃x : G.Dart⦄, x ∈ r → G.GoodRingArity x
  kernelRadiusTwo : G.RadiusTwo (G.Kernel r)

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

theorem nodup (hG : G.Embeddable r) :
    r.Nodup :=
  hG.faceSimple.nodup

theorem cyclePlanarPlainQuasicubic
    (hG : G.Embeddable r) :
    CyclePlanarPlainQuasicubic G r where
  cycle := hG.cycle
  nodup := hG.nodup
  eulerPlanar := hG.planar
  plain := hG.plain
  quasicubic := hG.quasicubic

theorem planarBridgelessPlainConnected
    (hG : G.Embeddable r) :
    G.PlanarBridgelessPlainConnected where
  base := {
    base := {
      planar := hG.planar
      bridgeless := hG.bridgeless
    }
    plain := hG.plain
  }
  connected := hG.connected

/-- Euler planarity gives the Jordan separation principle used throughout the
embedding-extension argument. -/
theorem jordan (hG : G.Embeddable r) : G.Jordan :=
  Unavoidability.eulerPlanar_jordan G hG.planar

/-- The orientation step in Coq `embed_functor`.  A proper simple `rlink`
cycle contained in the configuration kernel has one of its two Jordan sides
entirely in that kernel. -/
theorem diskN_subset_kernel_or_revRing
    (hG : G.Embeddable r)
    {q : List G.Dart}
    (hq : G.SimpleRLinkCycle q)
    (hproper : G.ProperRing q)
    (hqKernel : ∀ x : G.Dart, x ∈ q → G.Kernel r x) :
    (∀ x : G.Dart, G.DiskN q x → G.Kernel r x) ∨
      ∀ x : G.Dart, G.DiskN (G.RevRing q) x → G.Kernel r x := by
  have hJordan : G.Jordan := hG.jordan
  by_cases hhit : ∃ z : G.Dart, z ∈ r ∧ G.DiskF q z
  · right
    intro y hyRev hyBand
    rcases hyBand with ⟨z, hzRing, hzy⟩
    rcases hhit with ⟨t, htRing, htDisk⟩
    have htzNode : PermReachable G.node t z :=
      hG.cycle.permReachable_of_mem_mem htRing hzRing
    have htzNodeSymm : PermReachable G.node.symm t z :=
      (permReachable_symmPerm_iff G.node).2 htzNode
    have hzDiskN : G.DiskN q z :=
      G.diskN_of_nodeSymmReachable htzNodeSymm htDisk.1
    have hzNotBand : ¬ G.FaceBand q z := by
      intro hzBand
      rcases hzBand with ⟨w, hwq, hwz⟩
      have hzKernel : G.Kernel r z :=
        G.kernel_faceClosed r (hqKernel w hwq) hwz
      exact hzKernel
        (Hypermap.FaceBand.of_mem (G := G) hzRing
          (PermReachable.refl G.face z))
    have hzDisk : G.DiskF q z := ⟨hzDiskN, hzNotBand⟩
    have hyDisk : G.DiskF q y :=
      G.diskF_of_faceReachable hzy hzDisk
    exact (G.diskN_rev_ring hG.connected hJordan hG.plain hq hproper y).1
      hyRev hyDisk.1
  · left
    intro y hyDisk hyBand
    by_cases hyBandQ : G.FaceBand q y
    · rcases hyBandQ with ⟨z, hzq, hzy⟩
      exact (G.kernel_faceClosed r (hqKernel z hzq) hzy) hyBand
    · have hyDiskF : G.DiskF q y := ⟨hyDisk, hyBandQ⟩
      rcases hyBand with ⟨z, hzRing, hzy⟩
      have hzDiskF : G.DiskF q z :=
        G.diskF_of_faceReachable
          (PermReachable.symm G.face hzy) hyDiskF
      exact hhit ⟨z, hzRing, hzDiskF⟩

/-- A failed kernel edge equation yields the exact well-founded induction
state used by Coq `embed_functor`, with the Jordan side oriented into the
kernel. -/
theorem exists_kernelBadCycle_of_not_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hPlainH : H.Plain)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart}
    (hx : G.Kernel r x)
    (hex : G.Kernel r (G.edge x))
    (hxNot : ¬ EdgeCentral G H h x) :
    Nonempty (KernelBadCycle G H r h) := by
  rcases hembed.exists_simpleCycle_tail_edgeCentral
      (G.kernel_faceClosed r) hex hx with
    ⟨p, hcycle, hpCentral⟩
  let q : List G.Dart := x :: p
  have hqKernel : ∀ z : G.Dart, z ∈ q → G.Kernel r z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact (hpCentral z hz).1
  have hproper : G.ProperRing q :=
    KernelBadCycle.proper_of_simpleCycle_tail_edgeCentral hxNot hcycle
      (fun z hz => (hpCentral z hz).2) hG.bridgeless hG.plain hPlainH
  rcases hG.diskN_subset_kernel_or_revRing hcycle hproper hqKernel with
    hdirect | hreverse
  · exact ⟨{
      head := x
      tail := p
      headNotCentral := hxNot
      simpleCycle := hcycle
      tailCentral := by
        intro z hz
        exact ⟨hdirect z (G.diskN_of_mem (by simp [hz])),
          (hpCentral z hz).2⟩
      diskKernel := hdirect
    }⟩
  · let qrot : List G.Dart := q.rotate 1
    let qrev : List G.Dart := G.RevRing qrot
    have hshape : qrev = G.edge x :: G.RevRing p := by
      simp [qrev, qrot, q, RevRing, List.rotate_cons_succ,
        List.map_append]
    have hcycleRev : G.SimpleRLinkCycle qrev :=
      SimpleRLinkCycle.revRing_of_plain (G := G) hG.plain
        (SimpleRLinkCycle.rotate (G := G) 1 hcycle)
    have hpermRot : qrot.Perm q := by
      exact List.rotate_perm q 1
    have hpermRev : qrev.Perm (G.RevRing q) := by
      simpa [qrev, RevRing] using
        (List.reverse_perm (qrot.map G.edge)).trans
          ((hpermRot.map G.edge).trans
            (List.reverse_perm (q.map G.edge)).symm)
    have hrevKernel : ∀ z : G.Dart, G.DiskN qrev z → G.Kernel r z := by
      intro z hz
      exact hreverse z ((DiskN.perm (G := G) hpermRev).1 hz)
    have hheadNot : ¬ EdgeCentral G H h (G.edge x) := by
      intro hcentral
      exact hxNot
        ((edgeCentral_edge_iff G H hG.plain hPlainH h x).1 hcentral)
    exact ⟨{
      head := G.edge x
      tail := G.RevRing p
      headNotCentral := hheadNot
      simpleCycle := by simpa [hshape] using hcycleRev
      tailCentral := by
        intro z hz
        have hzDisk : G.DiskN qrev z := by
          rw [hshape]
          exact G.diskN_of_mem (by simp [hz])
        have hedgeMem : G.edge z ∈ p :=
          (mem_revRing_of_plain (G := G) hG.plain).1 hz
        have hedgeCentral : EdgeCentral G H h (G.edge z) :=
          (hpCentral (G.edge z) hedgeMem).2
        exact ⟨hrevKernel z hzDisk,
          (edgeCentral_edge_iff G H hG.plain hPlainH h z).1
            hedgeCentral⟩
      diskKernel := by
        intro z hz
        apply hrevKernel z
        simpa [hshape] using hz
    }⟩

/-- The first case of Coq's strict-descent argument: the next two darts in the
cubic node orbit cannot both be edge-central, since then face commutation
forces the bad head itself to be edge-central. -/
theorem badCycle_not_both_nodeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    (B : KernelBadCycle G H r h) :
    ¬ (EdgeCentral G H h (G.node B.head) ∧
      EdgeCentral G H h (G.node (G.node B.head))) := by
  rintro ⟨hcentralN, hcentralNN⟩
  let q : List G.Dart := B.head :: B.tail
  have hxDisk : G.DiskN q B.head :=
    G.diskN_of_mem (by simp [q])
  have hnxDisk : G.DiskN q (G.node B.head) :=
    (diskN_node_iff (G := G) (r := q)).2 hxDisk
  have hnnxDisk : G.DiskN q (G.node (G.node B.head)) :=
    (diskN_node_iff (G := G) (r := q)).2 hnxDisk
  have hxKernel : G.Kernel r B.head := B.diskKernel B.head hxDisk
  have hnxKernel : G.Kernel r (G.node B.head) :=
    B.diskKernel (G.node B.head) hnxDisk
  have hnnxKernel : G.Kernel r (G.node (G.node B.head)) :=
    B.diskKernel (G.node (G.node B.head)) hnnxDisk
  have hxOffRing : B.head ∉ r := G.kernel_off_ring hxKernel
  have hcubicX := hG.quasicubic B.head hxOffRing
  have hcubicH : H.Cubic :=
    Unavoidability.cubicMinimalCounterexamples_proved H hH
  have hsourceFace :
      G.face (G.edge B.head) = G.node (G.node B.head) := by
    apply G.node.injective
    rw [G.node_face_edge, hcubicX.1]
  have htargetFace :
      H.face (H.edge (h B.head)) = H.node (H.node (h B.head)) := by
    apply H.node.injective
    rw [H.node_face_edge, (hcubicH (h B.head)).1]
  have hedgeKernel : G.Kernel r (G.edge B.head) := by
    apply G.kernel_faceClosed r hnnxKernel
    have hreach :
        PermReachable G.face (G.edge B.head)
          (G.node (G.node B.head)) := by
      simpa [hsourceFace] using
        PermReachable.forward G.face (G.edge B.head)
    exact PermReachable.symm G.face hreach
  have hmapN : h (G.node B.head) = H.node (h B.head) :=
    hembed.map_node_of_edgeCentral_node (G.kernel_faceClosed r)
      hxKernel hcentralN
  have hmapNN :
      h (G.node (G.node B.head)) = H.node (h (G.node B.head)) :=
    hembed.map_node_of_edgeCentral_node (G.kernel_faceClosed r)
      hnxKernel hcentralNN
  apply B.headNotCentral
  unfold EdgeCentral
  apply H.face.injective
  calc
    H.face (h (G.edge B.head)) = h (G.face (G.edge B.head)) :=
      (hembed.face hedgeKernel).symm
    _ = h (G.node (G.node B.head)) := by rw [hsourceFace]
    _ = H.node (H.node (h B.head)) := by rw [hmapNN, hmapN]
    _ = H.face (H.edge (h B.head)) := htargetFace.symm


end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
