import FourColorTheorem.FourColor.Reducibility.ContractMinimal.EdgeDeletionGeometry

/-! Restriction and reflection of contracts through edge deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}} {cc : Finset G.Dart}
/-- The original selected contract restricted to the surviving darts. -/
def contractDeleteContract
    (hplain : G.Plain) (x : G.Dart) (cc : Finset G.Dart) :
    Finset (G.contractDeleteMap hplain x).Dart :=
  Finset.univ.filter
    (fun w => G.contractDeleteInclusion hplain x w ∈ cc)

@[simp]
theorem mem_contractDeleteContract
    (hplain : G.Plain) (x : G.Dart) (cc : Finset G.Dart)
    (w : (G.contractDeleteMap hplain x).Dart) :
    w ∈ G.contractDeleteContract hplain x cc ↔
      G.contractDeleteInclusion hplain x w ∈ cc := by
  simp [contractDeleteContract]

/-- The inclusion as a finite embedding, used for contract-cardinality
descent. -/
def contractDeleteEmbedding
    (hplain : G.Plain) (x : G.Dart) :
    (G.contractDeleteMap hplain x).Dart ↪ G.Dart where
  toFun := G.contractDeleteInclusion hplain x
  inj' := G.contractDeleteInclusion_injective hplain x

theorem map_contractDeleteContract_subset
    (hplain : G.Plain) (x : G.Dart) (cc : Finset G.Dart) :
    (G.contractDeleteContract hplain x cc).map
        (G.contractDeleteEmbedding hplain x) ⊆ cc := by
  intro y hy
  rcases Finset.mem_map.1 hy with ⟨w, hw, rfl⟩
  exact (G.mem_contractDeleteContract hplain x cc w).1 hw

/-- Selecting the deleted dart forces a strict drop in contract size. -/
theorem card_contractDeleteContract_lt
    (hplain : G.Plain) {x : G.Dart} {cc : Finset G.Dart}
    (hx : x ∈ cc) :
    (G.contractDeleteContract hplain x cc).card < cc.card := by
  rw [← Finset.card_map (G.contractDeleteEmbedding hplain x)]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · intro hxmap
    rcases Finset.mem_map.1 hxmap with ⟨w, _, hw⟩
    exact (G.contractDeleteInclusion_ne hplain x w).1 hw
  · rw [Finset.insert_subset_iff]
    exact ⟨hx, G.map_contractDeleteContract_subset hplain x cc⟩

/-- Contract-closure membership reflects exactly through the deletion
inclusion. -/
theorem mem_contractDeleteClosure_iff
    (hplain : G.Plain) (x : G.Dart) (cc : Finset G.Dart)
    (w : (G.contractDeleteMap hplain x).Dart) :
    w ∈ (G.contractDeleteMap hplain x).contractClosure
        (G.contractDeleteContract hplain x cc) ↔
      G.contractDeleteInclusion hplain x w ∈ G.contractClosure cc := by
  rw [(G.contractDeleteMap hplain x).mem_contractClosure_iff_self_or_edge_of_plain
      (G.contractDelete_plain hplain x),
    G.mem_contractClosure_iff_self_or_edge_of_plain hplain]
  rw [G.mem_contractDeleteContract hplain x cc,
    G.mem_contractDeleteContract hplain x cc]
  rw [G.contractDeleteInclusion_edge hplain x]

private theorem prev_append_cons_eq_getLast
    {α : Type _} [DecidableEq α]
    (pre post : List α) (y : α)
    (hpre : pre ≠ []) (hy : y ∉ pre) :
    (pre ++ y :: post).prev y (by simp) = pre.getLast hpre := by
  induction pre with
  | nil => contradiction
  | cons a pre ih =>
      have hya : y ≠ a := by
        intro h
        exact hy (by simp [h])
      cases pre with
      | nil =>
          simp [List.prev, hya]
      | cons b pre =>
          have hyTail : y ∉ b :: pre := by
            simpa [hya] using hy
          have hyb : y ≠ b := by
            intro h
            exact hyTail (by simp [h])
          change (a :: b :: (pre ++ y :: post)).prev y (by simp) =
            (a :: b :: pre).getLast hpre
          rw [List.prev_ne_cons_cons (pre ++ y :: post) y a b
            (by simp) hya hyb]
          simpa using ih (by simp) hyTail

private theorem getLastD_eq_getLast_of_ne_nil
    {α : Type _} (l : List α) (fallback : α) (hl : l ≠ []) :
    l.getLastD fallback = l.getLast hl := by
  induction l generalizing fallback with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil => simp [List.getLastD]
      | cons b l =>
          rw [List.getLastD_cons, List.getLast_cons (by simp)]
          exact ih a (by simp)

private theorem getLastD_cons_append_right
    {α : Type _} (y : α) (left right : List α)
    (hright : right ≠ []) :
    (y :: (left ++ right)).getLastD y = right.getLast hright := by
  rw [getLastD_eq_getLast_of_ne_nil
    (y :: (left ++ right)) y (by simp)]
  simpa only [List.cons_append] using
    List.getLast_append_of_right_ne_nil (y :: left) right hright

private theorem SimpleRLinkCycle.exists_rotated_cons_prev
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {y : G.Dart} (hy : y ∈ r) :
    ∃ r₁ : List G.Dart,
      G.SimpleRLinkCycle (y :: r₁) ∧
        (y :: r₁).Perm r ∧ y ∉ r₁ ∧
          (y :: r₁).getLastD y = r.prev y hy := by
  rcases (List.mem_iff_append).1 hy with ⟨pre, post, hsplit⟩
  subst r
  have hnodup : (pre ++ y :: post).Nodup := by
    exact FaceSimple.nodup (G := G) hr.faceSimple
  have hyPre : y ∉ pre := by
    intro hypre
    exact (List.nodup_append.1 hnodup).2.2 y hypre y (by simp) rfl
  by_cases hpre : pre = []
  · subst pre
    refine ⟨post, ?_, ?_, ?_, ?_⟩
    · simpa using hr
    · exact List.Perm.refl _
    · exact (List.nodup_cons.1 (by simpa using hnodup)).1
    · calc
        (y :: post).getLastD y = (y :: post).getLast (by simp) :=
          getLastD_eq_getLast_of_ne_nil (y :: post) y (by simp)
        _ = (y :: post).prev y (by simp) :=
          (List.prev_getLast_cons post y (by simp)).symm
  · let r₁ := post ++ pre
    have hrot : (pre ++ y :: post).rotate pre.length = y :: r₁ := by
      rw [List.rotate_append_length_eq]
      rfl
    have hcycleRot : G.SimpleRLinkCycle (y :: r₁) := by
      simpa [hrot] using
        SimpleRLinkCycle.rotate (G := G) pre.length hr
    refine ⟨r₁, ?_, ?_, ?_, ?_⟩
    · exact hcycleRot
    · rw [← hrot]
      exact List.rotate_perm (pre ++ y :: post) pre.length
    · exact (List.nodup_cons.1
        (FaceSimple.nodup (G := G) hcycleRot.faceSimple)).1
    · calc
        (y :: r₁).getLastD y = pre.getLast hpre := by
          exact getLastD_cons_append_right y post pre hpre
        _ = (pre ++ y :: post).prev y (by simp) :=
          (prev_append_cons_eq_getLast pre post y hpre hyPre).symm

theorem contractDelete_facePermReachable_of_original
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart}
    (hww' : PermReachable G.face
      (G.contractDeleteInclusion hplain x w)
      (G.contractDeleteInclusion hplain x w')) :
    PermReachable (G.contractDeleteMap hplain x).face w w' := by
  apply (G.contractDelete_facePermReachable_iff hplain hbridgeless x).2
  by_cases hwBand : G.FaceBand [x, G.edge x]
      (G.contractDeleteInclusion hplain x w)
  · exact Or.inl ⟨hwBand,
      FaceBand.of_faceReachable (G := G) hwBand hww'⟩
  · exact Or.inr ⟨hwBand, hww'⟩

theorem contractDelete_faceSimple_map
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).FaceSimple p) :
    G.FaceSimple
      (p.map (G.contractDeleteInclusion hplain x)) := by
  unfold FaceSimple at hp ⊢
  rw [List.pairwise_map]
  exact hp.imp (by
    intro w w' hnot hreach
    exact hnot
      (G.contractDelete_facePermReachable_of_original
        hplain hbridgeless x hreach))

/-- A deleted-map contour link whose target is outside the merged face band
is an ordinary original contour link. -/
theorem contractDelete_rLink_of_target_not_faceBand
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {w w' : (G.contractDeleteMap hplain x).Dart}
    (hlink : (G.contractDeleteMap hplain x).RLink w w')
    (hw'Band : ¬ G.FaceBand [x, G.edge x]
      (G.contractDeleteInclusion hplain x w')) :
    G.RLink (G.contractDeleteInclusion hplain x w)
      (G.contractDeleteInclusion hplain x w') := by
  unfold RLink at hlink ⊢
  have hface :=
    (G.contractDelete_facePermReachable_iff
      hplain hbridgeless x).1 hlink
  rw [G.contractDeleteInclusion_edge hplain x] at hface
  rcases hface with hbands | hordinary
  · exact False.elim (hw'Band hbands.2)
  · exact hordinary.2

private theorem contractDelete_rLinkPath_map_of_targets_not_faceBand
    (hplain : G.Plain) (hbridgeless : G.Bridgeless) (x : G.Dart)
    {w : (G.contractDeleteMap hplain x).Dart}
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).RLinkPath w p)
    (hband : ∀ z : (G.contractDeleteMap hplain x).Dart, z ∈ p →
      ¬ G.FaceBand [x, G.edge x]
        (G.contractDeleteInclusion hplain x z)) :
    G.RLinkPath (G.contractDeleteInclusion hplain x w)
      (p.map (G.contractDeleteInclusion hplain x)) := by
  induction p generalizing w with
  | nil => simp
  | cons z p ih =>
      constructor
      · exact G.contractDelete_rLink_of_target_not_faceBand
          hplain hbridgeless x hp.1 (hband z (by simp))
      · exact ih hp.2 (by
          intro y hy
          exact hband y (by simp [hy]))

private theorem contractDelete_mappedRLinkPath_of_prev
    (hplain : G.Plain) (x : G.Dart)
    {a : (G.contractDeleteMap hplain x).Dart}
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hnodup : (a :: p).Nodup)
    (hall : ∀ y : (G.contractDeleteMap hplain x).Dart,
      (hy : y ∈ p) →
        G.RLink
          (G.contractDeleteInclusion hplain x ((a :: p).prev y (by simp [hy])))
          (G.contractDeleteInclusion hplain x y)) :
    G.RLinkPath (G.contractDeleteInclusion hplain x a)
      (p.map (G.contractDeleteInclusion hplain x)) := by
  induction p generalizing a with
  | nil => simp
  | cons b p ih =>
      have hba : b ≠ a := by
        exact fun h => (List.nodup_cons.1 hnodup).1 (by simp [h])
      have hab := hall b (by simp)
      have hab' : G.RLink
          (G.contractDeleteInclusion hplain x a)
          (G.contractDeleteInclusion hplain x b) := by
        have hprev : (a :: b :: p).prev b (by simp) = a :=
          List.prev_cons_cons_of_ne p b a (by simp) hba
        simpa [hprev] using hab
      constructor
      · exact hab'
      · apply ih (List.nodup_cons.1 hnodup).2
        intro y hy
        have hya : y ≠ a := by
          intro h
          apply (List.nodup_cons.1 hnodup).1
          rw [← h]
          exact by simp [hy]
        have hyb : y ≠ b := by
          intro h
          apply (List.nodup_cons.1
            (List.nodup_cons.1 hnodup).2).1
          rw [← h]
          exact hy
        have h := hall y (by simp [hy])
        change G.RLink
          (G.contractDeleteInclusion hplain x
            ((b :: p).prev y (by simp [hy])))
          (G.contractDeleteInclusion hplain x y)
        convert h using 1
        exact congrArg (G.contractDeleteInclusion hplain x)
          (List.prev_ne_cons_cons p y a b (by simp [hy]) hya hyb).symm

private theorem contractDelete_exists_failed_mapped_prev
    (hplain : G.Plain) (x : G.Dart)
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).SimpleRLinkCycle p)
    (hnot : ¬ G.RLinkCycle
      (p.map (G.contractDeleteInclusion hplain x))) :
    ∃ w : (G.contractDeleteMap hplain x).Dart,
      ∃ hw : w ∈ p,
        ¬ G.RLink
          (G.contractDeleteInclusion hplain x (p.prev w hw))
          (G.contractDeleteInclusion hplain x w) := by
  by_contra hnone
  push Not at hnone
  apply hnot
  cases p with
  | nil => exact False.elim hp.cycle
  | cons a p =>
      have hnodup : (a :: p).Nodup :=
        FaceSimple.nodup (G := G.contractDeleteMap hplain x) hp.faceSimple
      constructor
      · apply contractDelete_mappedRLinkPath_of_prev hplain x hnodup
        intro y hy
        exact hnone y (by simp [hy])
      · have hclose := hnone a (by simp)
        rw [List.prev_getLast_cons] at hclose
        change G.RLink
          ((List.map (G.contractDeleteInclusion hplain x) (a :: p)).getLastD
            (G.contractDeleteInclusion hplain x a))
          (G.contractDeleteInclusion hplain x a)
        rw [List.getLastD_map,
          getLastD_eq_getLast_of_ne_nil (a :: p) a (by simp)]
        exact hclose

theorem contractDelete_edgePath_map_iff
    (hplain : G.Plain) (x : G.Dart)
    (w : (G.contractDeleteMap hplain x).Dart)
    (p : List (G.contractDeleteMap hplain x).Dart) :
    G.EdgePath (G.contractDeleteInclusion hplain x w)
        (p.map (G.contractDeleteInclusion hplain x)) ↔
      (G.contractDeleteMap hplain x).EdgePath w p := by
  induction p generalizing w with
  | nil => simp [EdgePath]
  | cons z p ih =>
      simp only [List.map_cons, EdgePath.cons]
      rw [← G.contractDeleteInclusion_edge hplain x]
      constructor
      · rintro ⟨hedge, hp⟩
        exact ⟨G.contractDeleteInclusion_injective hplain x hedge,
          (ih z).1 hp⟩
      · rintro ⟨hedge, hp⟩
        exact ⟨congrArg (G.contractDeleteInclusion hplain x) hedge,
          (ih z).2 hp⟩

theorem contractDelete_properRing_map
    (hplain : G.Plain) (x : G.Dart)
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).ProperRing p) :
    G.ProperRing (p.map (G.contractDeleteInclusion hplain x)) := by
  cases p with
  | nil => exact False.elim hp
  | cons w p =>
      rcases hp with hp | hp
      · left
        intro hmap
        exact hp ((G.contractDelete_edgePath_map_iff hplain x w p).1 hmap)
      · right
        simpa using hp

private theorem contractDelete_mapped_contractRing
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    {cc : Finset G.Dart} (x : G.Dart)
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).ContractRing
      (G.contractDeleteContract hplain x cc) p)
    (hcycle : G.RLinkCycle
      (p.map (G.contractDeleteInclusion hplain x))) :
    G.ContractRing cc (p.map (G.contractDeleteInclusion hplain x)) where
  cycle := ⟨hcycle,
    G.contractDelete_faceSimple_map hplain hbridgeless x hp.cycle.faceSimple⟩
  proper := G.contractDelete_properRing_map hplain x hp.proper
  tail_contract := by
    intro y hy
    cases p with
    | nil => simp at hy
    | cons a p =>
        rcases List.mem_map.1 hy with ⟨w, hw, rfl⟩
        exact (G.mem_contractDeleteClosure_iff hplain x cc w).1
          (hp.tail_contract w (by simpa using hw))

private theorem ProperRing.two_le_length
    {r : List G.Dart} (hr : G.ProperRing r) :
    2 ≤ r.length := by
  cases r with
  | nil => exact False.elim hr
  | cons a r =>
      cases r with
      | nil => simp [ProperRing, EdgePath] at hr
      | cons b r => simp

/-- A contract ring in the twice-deleted recursive map reflects to a
contract ring in the original map.  This is the loop-repair block in Coq
`contract_coloring`. -/
theorem contractDelete_contractRing_reflect
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    {cc : Finset G.Dart} {x : G.Dart}
    (hx : x ∈ cc)
    {p : List (G.contractDeleteMap hplain x).Dart}
    (hp : (G.contractDeleteMap hplain x).ContractRing
      (G.contractDeleteContract hplain x cc) p) :
    ∃ q : List G.Dart, G.ContractRing cc q := by
  classical
  let f := G.contractDeleteInclusion hplain x
  by_cases hcycle : G.RLinkCycle (p.map f)
  · exact ⟨p.map f,
      G.contractDelete_mapped_contractRing
        hplain hbridgeless x hp hcycle⟩
  · rcases contractDelete_exists_failed_mapped_prev
      hplain x hp.cycle hcycle with ⟨w, hw, hfail⟩
    rcases hp.cycle.exists_rotated_cons_prev hw with
      ⟨p₁, hpRot, hpPerm, hwNot, hlast⟩
    let last := (w :: p₁).getLastD w
    have hclosing : (G.contractDeleteMap hplain x).RLink last w := by
      exact hpRot.cycle.closing
    have hface :=
      (G.contractDelete_facePermReachable_iff
        hplain hbridgeless x).1 hclosing
    rw [G.contractDeleteInclusion_edge hplain x] at hface
    have hbands :
        G.FaceBand [x, G.edge x] (G.edge (f last)) ∧
          G.FaceBand [x, G.edge x] (f w) := by
      rcases hface with hbands | hordinary
      · exact hbands
      · exfalso
        apply hfail
        unfold RLink
        rw [← hlast]
        exact hordinary.2
    rcases hbands.1 with ⟨x₀, hx₀mem, hx₀edge⟩
    rcases hbands.2 with ⟨x₁, hx₁mem, hx₁w⟩
    have hx₀x₁ : x₀ ≠ x₁ := by
      intro heq
      subst x₁
      apply hfail
      unfold RLink
      rw [← hlast]
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hx₀edge) hx₁w
    have hedgeX₀ : G.edge x₀ = x₁ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₀mem hx₁mem
      rcases hx₀mem with hx₀ | hx₀ <;> rcases hx₁mem with hx₁ | hx₁
      · exact False.elim (hx₀x₁ (hx₀.trans hx₁.symm))
      · calc
          G.edge x₀ = G.edge x := by rw [hx₀]
          _ = x₁ := hx₁.symm
      · calc
          G.edge x₀ = G.edge (G.edge x) := by rw [hx₀]
          _ = x := Plain.edge_edge (G := G) hplain x
          _ = x₁ := hx₁.symm
      · exact False.elim (hx₀x₁ (hx₀.trans hx₁.symm))
    have htailBand : ∀ z : (G.contractDeleteMap hplain x).Dart,
        z ∈ p₁ → ¬ G.FaceBand [x, G.edge x] (f z) := by
      intro z hz hzBand
      apply FaceSimple.not_faceReachable_head
        (G := G.contractDeleteMap hplain x) hpRot.faceSimple hz
      apply (G.contractDelete_facePermReachable_iff
        hplain hbridgeless x).2
      exact Or.inl ⟨hbands.2, hzBand⟩
    have hfirst : G.RLink x₀ (f w) := by
      unfold RLink
      rw [hedgeX₀]
      exact hx₁w
    have hmappedPath : G.RLinkPath (f w) (p₁.map f) :=
      contractDelete_rLinkPath_map_of_targets_not_faceBand
        hplain hbridgeless x hpRot.cycle.path htailBand
    let q₁ := x₀ :: (w :: p₁).map f
    have hqLast : q₁.getLastD x₀ = f last := by
      dsimp [q₁, last]
      simp only [List.getLastD_cons]
      exact List.getLastD_map
    have hqCycle : G.RLinkCycle q₁ := by
      constructor
      · exact ⟨hfirst, hmappedPath⟩
      · rw [hqLast]
        unfold RLink
        exact PermReachable.symm G.face hx₀edge
    have hqFaceSimple : G.FaceSimple q₁ := by
      unfold q₁ FaceSimple
      rw [List.pairwise_cons]
      constructor
      · intro y hy hxy
        rcases List.mem_map.1 hy with ⟨z, hz, rfl⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · apply hfail
          unfold RLink
          rw [← hlast]
          exact PermReachable.trans G.face
            (PermReachable.symm G.face hx₀edge) hxy
        · exact htailBand z hz ⟨x₀, hx₀mem, hxy⟩
      · exact G.contractDelete_faceSimple_map
          hplain hbridgeless x hpRot.faceSimple
    have hpLen : 2 ≤ p.length := hp.proper.two_le_length
    have hrotLen : (w :: p₁).length = p.length := hpPerm.length_eq
    have hqProper : G.ProperRing q₁ := by
      apply G.properRing_of_length_gt_two
      have hrotTwo : 2 ≤ (w :: p₁).length := by omega
      simpa only [q₁, List.length_cons, List.length_map] using
        Nat.lt_succ_of_le hrotTwo
    have hqSimple : G.SimpleRLinkCycle q₁ :=
      ⟨hqCycle, hqFaceSimple⟩
    cases p with
    | nil => exact False.elim hp.cycle.cycle
    | cons a p =>
        have haRot : a ∈ w :: p₁ :=
          hpPerm.mem_iff.mpr (by simp)
        have hfaQ₁ : f a ∈ q₁ := by
          exact List.mem_cons_of_mem x₀ (List.mem_map_of_mem haRot)
        rcases hqSimple.exists_rotated_cons (G := G) hfaQ₁ with
          ⟨q₂, hqRot, hqPerm, hfaNot⟩
        refine ⟨f a :: q₂, hqRot, ?_, ?_⟩
        · apply G.properRing_of_length_gt_two
          have hqLen : q₁.length = (a :: p).length + 1 := by
            calc
              q₁.length = 1 + (w :: p₁).length := by
                simp only [q₁, List.length_cons, List.length_map]
                omega
              _ = 1 + (a :: p).length := congrArg (1 + ·) hrotLen
              _ = (a :: p).length + 1 := Nat.add_comm _ _
          rw [hqPerm.length_eq, hqLen]
          omega
        · intro y hy
          have hyQ₂ : y ∈ q₂ := by simpa using hy
          have hyQ₁ : y ∈ q₁ := hqPerm.mem_iff.mp
            (List.mem_cons_of_mem (f a) hyQ₂)
          rw [List.mem_cons] at hyQ₁
          rcases hyQ₁ with hyX₀ | hyMap
          · subst y
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₀mem
            rcases hx₀mem with rfl | rfl
            · exact G.mem_contractClosure_self hx
            · exact G.mem_contractClosure_edge hx
          · rcases List.mem_map.1 hyMap with ⟨z, hzRot, rfl⟩
            have hzP : z ∈ a :: p := hpPerm.mem_iff.mp hzRot
            have hza : z ≠ a := by
              intro hza
              subst z
              exact hfaNot hy
            have hzTail : z ∈ p := by simpa [hza] using hzP
            exact (G.mem_contractDeleteClosure_iff hplain x cc z).1
              (hp.tail_contract z hzTail)

/-- Deleting a selected plain edge removes exactly its two darts. -/
theorem contractDelete_dart_card_add_two
    (hplain : G.Plain) (x : G.Dart) :
    Fintype.card (G.contractDeleteMap hplain x).Dart + 2 =
      Fintype.card G.Dart := by
  exact G.permFace.walkupE_walkupE_dart_card_add_two
    (G.contractDeleteEdgeDart hplain x)

theorem contractDelete_dart_card_lt
    (hplain : G.Plain) (x : G.Dart) :
    Fintype.card (G.contractDeleteMap hplain x).Dart <
      Fintype.card G.Dart := by
  rw [← G.contractDelete_dart_card_add_two hplain x]
  omega

/-- The no-contract-ring invariant descends through selected-edge deletion. -/
theorem contractDelete_noContractRing
    (hplain : G.Plain) (hbridgeless : G.Bridgeless)
    {cc : Finset G.Dart} {x : G.Dart} (hx : x ∈ cc)
    (hnoRing : ∀ q : List G.Dart, ¬ G.ContractRing cc q) :
    ∀ p : List (G.contractDeleteMap hplain x).Dart,
      ¬ (G.contractDeleteMap hplain x).ContractRing
        (G.contractDeleteContract hplain x cc) p := by
  intro p hp
  rcases G.contractDelete_contractRing_reflect
      hplain hbridgeless hx hp with ⟨q, hq⟩
  exact hnoRing q hq

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
