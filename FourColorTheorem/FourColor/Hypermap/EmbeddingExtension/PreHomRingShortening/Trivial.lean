import FourColorTheorem.FourColor.Hypermap.EmbeddingExtension.PreHomRingShortening.ShorterPrefix
import Schematic.Math.GraphTheory.Embedding.Geometry.LocalPeriod

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u v

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- Coq `trivial_hom_ring`.  A kernel-contained source path whose image is a
simple closed `rlink` ring with no strict selected face already closes in the
source.  The proof is the two-stage chord shortening from `embed.v`, with
strong induction on the source tail length. -/
theorem trivialHomRing
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    (hG : G.Embeddable r)
    (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {x : G.Dart} {p : List G.Dart}
    (hpre : PreHomRing r h x p)
    (hzero : H.FaceOrbitCountOf (H.DiskF ((x :: p).map h)) ≤ 0) :
    G.RLink ((x :: p).getLastD x) x := by
  let P : Nat → Prop := fun n =>
    ∀ (x : G.Dart) (p : List G.Dart), p.length = n →
      PreHomRing r h x p →
        (∀ u : H.Dart, ¬ H.DiskF ((x :: p).map h) u) →
          G.RLink ((x :: p).getLastD x) x
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x p hpLen hpre hnoDisk
        rcases hpre.exists_interior_split_face_of_no_diskF hH hnoDisk with
          ⟨z, p₁, p₂, hp, hlast, hp₁Ne, hp₂Ne, hzFace⟩
        let y := (x :: p).getLastD x
        let eny := G.edge (G.node y)
        let enny := G.edge (G.node (G.node y))
        have henyRz : G.RLink eny z := by
          by_cases hnodeMem : H.node (h y) ∈ (x :: p).map h
          · exact hpre.edge_node_last_rLink_of_mem hG hH hembed
              hp hlast hp₁Ne hp₂Ne hzFace hnodeMem
          · rcases hpre.exists_shorter_suffix hH hembed hnoDisk
                hp hlast hp₁Ne hp₂Ne hzFace hnodeMem with
              ⟨q, hpreQ, hlastQ, hshortQ, hnoQ⟩
            have hlt : q.length < n := by simpa [hpLen] using hshortQ
            have hrec := ih q.length hlt z q rfl hpreQ hnoQ
            rw [hlastQ] at hrec
            exact hrec
        have hennyRx : G.RLink enny x := by
          by_cases hnnMem : H.node (H.node (h y)) ∈ (x :: p).map h
          · exact hpre.edge_node_node_last_rLink_of_mem hG hH hembed
              hp hlast hp₁Ne hzFace henyRz hnnMem
          · rcases hpre.exists_shorter_prefix hG hH hembed hnoDisk
                hp hlast hp₁Ne hp₂Ne hzFace henyRz hnnMem with
              ⟨q, hpreQ, hlastQ, hshortQ, hnoQ⟩
            have hlt : q.length < n := by simpa [hpLen] using hshortQ
            have hrec := ih q.length hlt x q rfl hpreQ hnoQ
            rw [hlastQ] at hrec
            exact hrec
        have hyMem : y ∈ x :: p := by
          have hne : x :: p ≠ [] := List.cons_ne_nil x p
          dsimp [y, List.getLastD]
          exact List.getLast_mem hne
        have hyKernel : G.Kernel r y := hpre.kernel y hyMem
        have hyOffRing : y ∉ r := G.kernel_off_ring hyKernel
        have hyCubic := hG.quasicubic y hyOffRing
        have hennyReach :
            PermReachable G.face (G.node (G.node y)) x := by
          change PermReachable G.face (G.edge enny) x at hennyRx
          have hedgeEnny : G.edge enny = G.node (G.node y) := by
            simp [enny, Hypermap.Plain.edge_edge (G := G) hG.plain]
          rw [hedgeEnny] at hennyRx
          exact hennyRx
        have hedgeToNN :
            PermReachable G.face (G.edge y) (G.node (G.node y)) := by
          rw [Hypermap.node_node_eq_face_edge_of_period_three
            (G := G) hyCubic.1]
          exact PermReachable.forward G.face (G.edge y)
        unfold RLink
        exact PermReachable.trans G.face hedgeToNN hennyReach
  have hnoDisk : ∀ u : H.Dart,
      ¬ H.DiskF ((x :: p).map h) u :=
    no_diskF_of_faceOrbitCount_le_zero hzero
  exact hP p.length x p rfl hpre hnoDisk

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
