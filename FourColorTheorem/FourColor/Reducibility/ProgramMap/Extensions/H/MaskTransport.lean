import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.H.FreshFaces

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
theorem h_exists_old_faceReachable_or_point
    (P : PointedHypermap) (u : P.h.map.Dart) :
    (∃ x : P.map.Dart,
      PermReachable P.h.map.face u (P.hOld x)) ∨
      PermReachable P.h.map.face P.h.point u := by
  change (∃ x : P.map.Dart,
      PermReachable (Hypermap.extensionH P.map P.point).face
        u (Hypermap.extensionHOld P.map P.point x)) ∨
    PermReachable (Hypermap.extensionH P.map P.point).face ExtDart.new u
  exact Hypermap.extensionH_exists_old_faceReachable_or_new
    (G := P.map) P.point u

theorem h_exists_old_faceReachable_or_freshFace_of_proper
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    (u : P.h.map.Dart) :
    (∃ x : P.map.Dart,
      PermReachable P.h.map.face u (P.hOld x)) ∨
      Hypermap.extensionHFreshFace P.map P.point u := by
  change (∃ x : P.map.Dart,
      PermReachable (Hypermap.extensionH P.map P.point).face
        u (Hypermap.extensionHOld P.map P.point x)) ∨
    Hypermap.extensionHFreshFace P.map P.point u
  exact Hypermap.extensionH_exists_old_faceReachable_or_freshFace_of_proper
    (G := P.map) P.point hproper u

theorem hOld_exists_selectMask_ringAdj_iff
    (P : PointedHypermap) (m : CfMask)
    (ring kernel : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.h.map.Dart,
      y ∈ CfMask.selectMask m (ring.map P.hOld) (kernel.map P.hOld) ∧
        P.h.map.RingAdj (P.hOld x) y) ↔
      ∃ y : P.map.Dart,
        y ∈ CfMask.selectMask m ring kernel ∧ P.map.RingAdj x y := by
  exact OldDartTransport.exists_selectMask_map_iff
    P.hOld (hOld_ringAdj_iff P) m ring kernel x

theorem hOld_exists_map_ringAdj_iff
    (P : PointedHypermap) (r : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.h.map.Dart,
      y ∈ r.map P.hOld ∧ P.h.map.RingAdj (P.hOld x) y) ↔
      ∃ y : P.map.Dart, y ∈ r ∧ P.map.RingAdj x y := by
  exact OldDartTransport.exists_mem_map_iff
    P.hOld (hOld_ringAdj_iff P) r x

theorem hOld_faceBand_two_prefixes_map_iff
    (P : PointedHypermap) (b0 b1 : Bool)
    (a b : P.h.map.Dart) (r : List P.map.Dart) {x : P.map.Dart} :
    P.h.map.FaceBand
        ((if b0 then [a] else []) ++ (if b1 then [b] else []) ++
          r.map P.hOld)
        (P.hOld x) ↔
      (b0 = true ∧ PermReachable P.h.map.face a (P.hOld x)) ∨
        (b1 = true ∧ PermReachable P.h.map.face b (P.hOld x)) ∨
          P.map.FaceBand r x := by
  rw [Hypermap.FaceBand.two_optional_prefixes,
    hOld_faceBand_iff P]

theorem hOld_exists_two_prefixes_map_ringAdj_iff
    (P : PointedHypermap) (b0 b1 : Bool)
    (a b : P.h.map.Dart) (r : List P.map.Dart) {x : P.map.Dart} :
    (∃ y : P.h.map.Dart,
      y ∈ (if b0 then [a] else []) ++ (if b1 then [b] else []) ++
          r.map P.hOld ∧
        P.h.map.RingAdj (P.hOld x) y) ↔
      (b0 = true ∧ P.h.map.RingAdj (P.hOld x) a) ∨
        (b1 = true ∧ P.h.map.RingAdj (P.hOld x) b) ∨
          ∃ y : P.map.Dart, y ∈ r ∧ P.map.RingAdj x y := by
  rw [Hypermap.RingAdj.exists_mem_two_optional_prefixes,
    hOld_exists_map_ringAdj_iff P r]

theorem hOld_lift_maskAdjSound
    (P : PointedHypermap) {adj orig : List P.map.Dart}
    (hsound :
      ∀ x : P.map.Dart,
        P.map.FaceBand adj x ↔
          ∃ y : P.map.Dart, y ∈ orig ∧ P.map.RingAdj x y)
    {x : P.map.Dart} :
    P.h.map.FaceBand (adj.map P.hOld) (P.hOld x) ↔
      ∃ y : P.h.map.Dart,
        y ∈ orig.map P.hOld ∧ P.h.map.RingAdj (P.hOld x) y := by
  exact OldDartTransport.liftFaceBandRingAdj P.hOld
    (fun r => hOld_faceBand_iff P) (hOld_ringAdj_iff P) hsound

end Schematic.Math.GraphTheory.FourColor.PointedHypermap
