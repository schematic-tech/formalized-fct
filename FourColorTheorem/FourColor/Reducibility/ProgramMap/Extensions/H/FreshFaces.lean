import FourColorTheorem.FourColor.Reducibility.ProgramMap.Extensions.H.RingTransport

namespace Schematic.Math.GraphTheory.FourColor.PointedHypermap
theorem h_not_faceReachable_point_old
    (P : PointedHypermap) (x : P.map.Dart) :
    ¬ PermReachable P.h.map.face P.h.point (P.hOld x) := by
  change ¬ PermReachable (Hypermap.extensionH P.map P.point).face
    ExtDart.new (Hypermap.extensionHOld P.map P.point x)
  exact Hypermap.extensionH_not_faceReachable_new_old
    (G := P.map) (x0 := P.point) x

theorem h_not_faceReachable_point_node_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    ¬ PermReachable P.h.map.face P.h.point
      (P.h.map.node P.h.point) := by
  change ¬ PermReachable (Hypermap.extensionH P.map P.point).face
    ExtDart.new ((Hypermap.extensionH P.map P.point).node ExtDart.new)
  have hyLong :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper
      (G := P.map) P.point hproper
  have hnode :
      (Hypermap.extensionH P.map P.point).node ExtDart.new =
        ExtDart.old (ExtDart.old ExtDart.newEdge) := by
    unfold Hypermap.extensionH Hypermap.extensionN
    change Hypermap.ExtensionN.node
        (Hypermap.extensionY P.map P.point) ExtDart.new ExtDart.new =
      ExtDart.old (ExtDart.old ExtDart.newEdge)
    rw [Hypermap.ExtensionN.node_new, if_pos hyLong,
      Hypermap.extensionY_node_new]
    rfl
  intro h
  have hfresh :=
    (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
      (G := P.map) P.point hproper).1 h
  rw [hnode] at hfresh
  rcases hfresh with hnew | holdNew | holdOldNew
  · cases hnew
  · cases holdNew
  · cases holdOldNew

theorem h_ringAdj_point_node_point
    (P : PointedHypermap)
    (hproper : P.ProperRingHead) :
    P.h.map.RingAdj P.h.point (P.h.map.node P.h.point) := by
  change (Hypermap.extensionH P.map P.point).RingAdj
    ExtDart.new ((Hypermap.extensionH P.map P.point).node ExtDart.new)
  have hyLong :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper
      (G := P.map) P.point hproper
  have hnode :
      (Hypermap.extensionH P.map P.point).node ExtDart.new =
        ExtDart.old (ExtDart.old ExtDart.newEdge) := by
    unfold Hypermap.extensionH Hypermap.extensionN
    change Hypermap.ExtensionN.node
        (Hypermap.extensionY P.map P.point) ExtDart.new ExtDart.new =
      ExtDart.old (ExtDart.old ExtDart.newEdge)
    rw [Hypermap.ExtensionN.node_new, if_pos hyLong,
      Hypermap.extensionY_node_new]
    rfl
  rw [hnode]
  refine ⟨ExtDart.old (ExtDart.old ExtDart.new), ?_, ?_⟩
  · have h1 :
        PermReachable (Hypermap.extensionH P.map P.point).face
          ExtDart.new (ExtDart.old ExtDart.new) := by
      have hstep :=
        PermReachable.forward
          (Hypermap.extensionH P.map P.point).face ExtDart.new
      simpa [Hypermap.extensionH_face_new] using hstep
    have h2 :
        PermReachable (Hypermap.extensionH P.map P.point).face
          (ExtDart.old ExtDart.new)
          (ExtDart.old (ExtDart.old ExtDart.new)) := by
      have hstep :=
        PermReachable.forward
          (Hypermap.extensionH P.map P.point).face
          (ExtDart.old ExtDart.new)
      simpa [Hypermap.extensionH_face_old_new] using hstep
    exact PermReachable.trans
      (Hypermap.extensionH P.map P.point).face h1 h2
  · exact PermReachable.refl (Hypermap.extensionH P.map P.point).face
      (ExtDart.old (ExtDart.old ExtDart.newEdge))

theorem h_faceBand_two_prefixes_map_point_iff
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (b0 b1 : Bool) (r : List P.map.Dart) :
    P.h.map.FaceBand
        ((if b0 then [P.h.map.node P.h.point] else []) ++
          (if b1 then [P.h.point] else []) ++ r.map P.hOld)
        P.h.point ↔
      b1 = true := by
  rw [Hypermap.FaceBand.two_optional_prefixes]
  have hnode :
      ¬ PermReachable P.h.map.face (P.h.map.node P.h.point)
        P.h.point := by
    intro h
    exact h_not_faceReachable_point_node_point P hproper
      (PermReachable.symm P.h.map.face h)
  have hold : ¬ P.h.map.FaceBand (r.map P.hOld) P.h.point := by
    rintro ⟨z, hz, hzp⟩
    rcases List.mem_map.mp hz with ⟨x, _hx, rfl⟩
    exact h_not_faceReachable_point_old P x
      (PermReachable.symm P.h.map.face hzp)
  change
      (b0 = true ∧
            PermReachable P.h.map.face (P.h.map.node P.h.point) P.h.point) ∨
        (b1 = true ∧
            PermReachable P.h.map.face P.h.point P.h.point) ∨
          P.h.map.FaceBand (r.map P.hOld) P.h.point ↔
        b1 = true
  constructor
  · rintro (h0 | htail)
    · exact False.elim (hnode h0.2)
    · rcases htail with h1 | htail
      · exact h1.1
      · exact False.elim (hold htail)
  · intro hb1
    exact Or.inr (Or.inl
      ⟨hb1, PermReachable.refl P.h.map.face P.h.point⟩)

theorem h_exists_map_ringAdj_point_iff
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    (r : List P.map.Dart) :
    (∃ y : P.h.map.Dart,
      y ∈ r.map P.hOld ∧ P.h.map.RingAdj P.h.point y) ↔
      ∃ x : P.map.Dart,
        x ∈ r ∧
          P.map.FaceBand
            [P.map.face (P.map.edge P.point), P.point,
              P.map.node P.point] x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx,
      (h_ringAdj_point_old_iff_faceBand_of_proper_long
        P hproper hlong).1 hxy⟩
  · rintro ⟨x, hx, hband⟩
    exact ⟨P.hOld x, List.mem_map.mpr ⟨x, hx, rfl⟩,
      (h_ringAdj_point_old_iff_faceBand_of_proper_long
        P hproper hlong).2 hband⟩

theorem h_exists_two_prefixes_map_ringAdj_point_iff
    (P : PointedHypermap)
    (hproper : P.ProperRingHead)
    (hlong : P.LongRingHead)
    (b0 b1 : Bool) (r : List P.map.Dart) :
    (∃ y : P.h.map.Dart,
      y ∈ (if b0 then [P.h.map.node P.h.point] else []) ++
          (if b1 then [P.h.point] else []) ++ r.map P.hOld ∧
        P.h.map.RingAdj P.h.point y) ↔
      b0 = true ∨
        (b1 = true ∧ P.h.map.RingAdj P.h.point P.h.point) ∨
          ∃ x : P.map.Dart,
            x ∈ r ∧
              P.map.FaceBand
                [P.map.face (P.map.edge P.point), P.point,
                  P.map.node P.point] x := by
  rw [Hypermap.RingAdj.exists_mem_two_optional_prefixes,
    h_exists_map_ringAdj_point_iff P hproper hlong]
  constructor
  · rintro (h0 | htail)
    · exact Or.inl h0.1
    · rcases htail with h1 | hold
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hold)
  · rintro (h0 | htail)
    · exact Or.inl ⟨h0, h_ringAdj_point_node_point P hproper⟩
    · rcases htail with h1 | hold
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hold)

theorem h_faceReachable_node_point_old_iff
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    {x : P.map.Dart} :
    PermReachable P.h.map.face (P.h.map.node P.h.point) (P.hOld x) ↔
      PermReachable P.map.face (P.map.node P.point) x := by
  change PermReachable
      (Hypermap.extensionH P.map P.point).face
      ((Hypermap.extensionH P.map P.point).node ExtDart.new)
      (Hypermap.extensionHOld P.map P.point x) ↔
    PermReachable P.map.face (P.map.node P.point) x
  unfold Hypermap.extensionH Hypermap.extensionHOld
  change PermReachable
      (Hypermap.extensionN (Hypermap.extensionY P.map P.point) ExtDart.new).face
      (Hypermap.ExtensionN.node
        (Hypermap.extensionY P.map P.point) ExtDart.new ExtDart.new)
      (ExtDart.old (Hypermap.extensionYOld P.map P.point x)) ↔
    PermReachable P.map.face (P.map.node P.point) x
  rw [Hypermap.ExtensionN.node_new]
  have hyLong :
      (Hypermap.extensionY P.map P.point).LongRingHead ExtDart.new :=
    Hypermap.extensionY_long_new_of_proper
      (G := P.map) P.point hproper
  rw [if_pos hyLong]
  rw [Hypermap.extensionY_node_new]
  exact Iff.trans
    (Hypermap.extensionN_old_faceReachable_iff
      (G := Hypermap.extensionY P.map P.point) ExtDart.new
      (x := ExtDart.old ExtDart.newEdge)
      (y := Hypermap.extensionYOld P.map P.point x))
    (Hypermap.extensionY_faceReachable_old_newEdge_old_iff
      (G := P.map) (x0 := P.point))

theorem h_faceBand_point_node_point_old_iff
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    {x : P.map.Dart} :
    P.h.map.FaceBand [P.h.point, P.h.map.node P.h.point] (P.hOld x) ↔
      PermReachable P.map.face (P.map.node P.point) x := by
  rw [Hypermap.FaceBand.pair]
  constructor
  · rintro (hpoint | hnode)
    · exact False.elim (h_not_faceReachable_point_old P x hpoint)
    · exact (h_faceReachable_node_point_old_iff P hproper).1 hnode
  · intro hnode
    exact Or.inr ((h_faceReachable_node_point_old_iff P hproper).2 hnode)

theorem hOld_forall_mem_not_faceBand_point_node_iff
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    (r : List P.map.Dart) :
    (∀ z : P.h.map.Dart,
      z ∈ r.map P.hOld →
        ¬ P.h.map.FaceBand [P.h.point, P.h.map.node P.h.point] z) ↔
      ∀ x : P.map.Dart,
        x ∈ r → ¬ PermReachable P.map.face (P.map.node P.point) x := by
  constructor
  · intro h x hx hface
    exact h (P.hOld x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      ((h_faceBand_point_node_point_old_iff P hproper).2 hface)
  · intro h z hz hband
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact h x hx ((h_faceBand_point_node_point_old_iff P hproper).1 hband)

theorem hOld_ringAdj_node_point_iff
    (P : PointedHypermap) (hproper : P.ProperRingHead)
    {x : P.map.Dart} :
    P.h.map.RingAdj (P.hOld x) (P.h.map.node P.h.point) ↔
      P.map.RingAdj x (P.map.node P.point) := by
  have hface :
      PermReachable P.h.map.face (P.h.map.node P.h.point)
        (P.hOld (P.map.node P.point)) :=
    (h_faceReachable_node_point_old_iff P hproper).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  constructor
  · intro h
    have h' :=
      Hypermap.RingAdj.of_faceReachable_right (G := P.h.map) h hface
    exact (hOld_ringAdj_iff P).1 h'
  · intro h
    have h' : P.h.map.RingAdj (P.hOld x)
        (P.hOld (P.map.node P.point)) :=
      (hOld_ringAdj_iff P).2 h
    exact Hypermap.RingAdj.of_faceReachable_right (G := P.h.map) h'
      (PermReachable.symm P.h.map.face hface)

end Schematic.Math.GraphTheory.FourColor.PointedHypermap
