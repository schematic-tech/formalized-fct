import FourColorTheorem.FourColor.Coloring.KempeMap.BoundaryColoring

/-!
Extension of a reduced coloring across the deleted darts.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The coloring-extension core of Coq `invh_col_s`.  The only chromogram
fact used by the construction is the displayed inequality `e3 ≠ e2`; its
derivation from the first two recursive trace colors is kept separate. -/
theorem Coloring.extend_kempeReduction
    (G : Hypermap.{u}) (z : G.Dart) (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x)
    (hfaceAvail : G.face z = z ∨
      (G.face z ≠ z ∧ G.face z ≠ G.edge z))
    {k : (G.kempeReduction z hplain).Dart -> Color}
    (hk : (G.kempeReduction z hplain).Coloring k)
    (e1 : Color) :
    let base := G.kempeFillColor z hplain k e1 e1
    let e2 := base (G.face (G.edge z))
    let e3 := if G.face z = z then e1 + e2 else base (G.face z)
    let k0 := G.kempeFillColor z hplain k e3 e2
    e3 ≠ e2 ->
      G.Coloring k0 ∧
        (forall u, k u = k0 (G.kempeProjection z hplain u)) ∧
        (G.face z = z -> k0 z + k0 (G.node z) = e1) := by
  dsimp only
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  let base := G.kempeFillColor z hplain k e1 e1
  let e2 := base (G.face (G.edge z))
  let e3 := if G.face z = z then e1 + e2 else base (G.face z)
  let k0 := G.kempeFillColor z hplain k e3 e2
  intro he32
  have he32' : e3 ≠ e2 := by
    simpa [e3, e2, base] using he32
  have hagree (u : H.Dart) : k u = k0 (proj u) := by
    have hu := G.kempeProjection_ne_deleted z hplain u
    change k u = G.kempeFillColor z hplain k e3 e2 (proj u)
    rw [G.kempeFillColor_of_ne z hplain k e3 e2 (proj u) hu.1 hu.2]
    congr 1
  have hcoloring : G.Coloring k0 := by
    constructor
    · intro x
      by_cases hxz : x = z
      · subst x
        rw [show k0 (G.edge z) = e2 by
          exact G.kempeFillColor_edge z hplain k e3 e2]
        rw [show k0 z = e3 by exact G.kempeFillColor_z z hplain k e3 e2]
        exact he32'.symm
      · by_cases hxe : x = G.edge z
        · subst x
          rw [Plain.edge_edge (G := G) hplain z]
          rw [show k0 z = e3 by exact G.kempeFillColor_z z hplain k e3 e2]
          rw [show k0 (G.edge z) = e2 by
            exact G.kempeFillColor_edge z hplain k e3 e2]
          exact he32'
        · let u := G.kempeLiftDart z hplain x hxz hxe
          have hprojU : proj u = x := by rfl
          have hprojEdge : proj (H.edge u) = G.edge x := by
            change G.kempeProjection z hplain
              ((G.kempeReduction z hplain).edge u) = G.edge x
            rw [G.kempeProjection_edge]
            exact congrArg G.edge hprojU
          intro heq
          apply Coloring.edge_ne (G := H) hk u
          calc
            k (H.edge u) = k0 (proj (H.edge u)) := hagree (H.edge u)
            _ = k0 (G.edge x) := congrArg k0 hprojEdge
            _ = k0 x := heq
            _ = k u := (hagree u).symm
    · intro x
      by_cases hxz : x = z
      · subst x
        by_cases hfixed : G.face z = z
        · rw [hfixed]
        · rcases hfaceAvail with h | hsurvive
          · exact False.elim (hfixed h)
          · change
              G.kempeFillColor z hplain k e3 e2 (G.face z) =
                G.kempeFillColor z hplain k e3 e2 z
            rw [G.kempeFillColor_of_ne z hplain k e3 e2
              (G.face z) hsurvive.1 hsurvive.2]
            rw [G.kempeFillColor_z]
            rw [show e3 = base (G.face z) by simp [e3, hfixed]]
            exact (G.kempeFillColor_of_ne z hplain k e1 e1
              (G.face z) hsurvive.1 hsurvive.2).symm
      · by_cases hxe : x = G.edge z
        · subst x
          let t := G.face (G.edge z)
          by_cases hte : t = G.edge z
          · change k0 t = k0 (G.edge z)
            rw [hte]
          · have htz : t ≠ z := by
              intro h
              have hnodeT : G.node t = z := by
                change G.node (G.face (G.edge z)) = z
                rw [Plain.node_face_eq_edge (G := G) hplain (G.edge z),
                  Plain.edge_edge (G := G) hplain z]
              have hfixed : G.node z = z := by
                calc
                  G.node z = G.node t := congrArg G.node h.symm
                  _ = z := hnodeT
              exact hnode z hfixed
            change k0 t = k0 (G.edge z)
            change
              G.kempeFillColor z hplain k e3 e2 t =
                G.kempeFillColor z hplain k e3 e2 (G.edge z)
            rw [G.kempeFillColor_of_ne z hplain k e3 e2 t htz hte]
            rw [G.kempeFillColor_edge]
            rw [show e2 = base t by rfl]
            exact (G.kempeFillColor_of_ne z hplain k e1 e1 t htz hte).symm
        · let u := G.kempeLiftDart z hplain x hxz hxe
          have hprojU : proj u = x := by rfl
          let y := proj (H.face u)
          have hySurvive := G.kempeProjection_ne_deleted z hplain (H.face u)
          have hbaseY : base y = k (H.face u) := by
            change G.kempeFillColor z hplain k e1 e1 y = k (H.face u)
            rw [G.kempeFillColor_of_ne z hplain k e1 e1 y
              hySurvive.1 hySurvive.2]
            congr 1
          have hk0Y : k0 y = k (H.face u) := by
            change G.kempeFillColor z hplain k e3 e2 y = k (H.face u)
            rw [G.kempeFillColor_of_ne z hplain k e3 e2 y
              hySurvive.1 hySurvive.2]
            congr 1
          have hp : G.edge (G.kempeSpliceNode z y) = x := by
            have hp0 := G.kempeProjection_face_relation z hplain hnode u
            simpa [y, proj] using hp0
          have hrhs : k0 x = base y := by
            calc
              k0 x = k0 (proj u) := congrArg k0 hprojU.symm
              _ = k u := (hagree u).symm
              _ = k (H.face u) := (Coloring.face_eq (G := H) hk u).symm
              _ = base y := hbaseY.symm
          have hnodeFaceEdge :
              G.node (G.face (G.edge z)) = z := by
            rw [Plain.node_face_eq_edge (G := G) hplain (G.edge z),
              Plain.edge_edge (G := G) hplain z]
          by_cases hyT : y = G.face (G.edge z)
          · have hnodeY : G.node y = z := by rw [hyT, hnodeFaceEdge]
            have hp' : G.edge (G.node (G.edge z)) = x := by
              simpa [kempeSpliceNode, hnodeY] using hp
            have hfaceX : G.face x = G.edge z := by
              rw [← hp']
              exact G.face_edge_node (G.edge z)
            rw [hfaceX]
            calc
              k0 (G.edge z) = e2 :=
                G.kempeFillColor_edge z hplain k e3 e2
              _ = base y := by simp [e2, hyT]
              _ = k0 x := hrhs.symm
          · by_cases hyF : y = G.face z
            · have hnodeY : G.node y = G.edge z := by
                rw [hyF]
                exact Plain.node_face_eq_edge (G := G) hplain z
              have hnodeYz : G.node y ≠ z := by
                rw [hnodeY]
                exact Plain.edge_ne (G := G) hplain z
              have hp' : G.edge (G.node z) = x := by
                rw [kempeSpliceNode, if_neg hnodeYz, if_pos hnodeY] at hp
                exact hp
              have hfaceX : G.face x = z := by
                rw [← hp']
                exact G.face_edge_node z
              have hfixed : G.face z ≠ z := by
                intro h
                exact hySurvive.1 (hyF.trans h)
              rw [hfaceX]
              calc
                k0 z = e3 := G.kempeFillColor_z z hplain k e3 e2
                _ = base y := by simp [e3, hfixed, hyF]
                _ = k0 x := hrhs.symm
            · have hnodeYz : G.node y ≠ z := by
                intro h
                apply hyT
                apply G.node.injective
                rw [h, hnodeFaceEdge]
              have hnodeYe : G.node y ≠ G.edge z := by
                intro h
                apply hyF
                apply G.node.injective
                rw [h, Plain.node_face_eq_edge (G := G) hplain z]
              have hp' : G.edge (G.node y) = x := by
                simpa [kempeSpliceNode, hnodeYz, hnodeYe] using hp
              have hfaceX : G.face x = y := by
                rw [← hp']
                exact G.face_edge_node y
              rw [hfaceX]
              exact (hk0Y.trans hbaseY.symm).trans hrhs.symm
  refine ⟨hcoloring, hagree, ?_⟩
  intro hfixed
  have hnodeEdge : G.node z = G.edge z := by
    rw [← Plain.node_face_eq_edge (G := G) hplain z, hfixed]
  change k0 z + k0 (G.node z) = e1
  rw [show k0 z = e3 by exact G.kempeFillColor_z z hplain k e3 e2]
  rw [hnodeEdge, show k0 (G.edge z) = e2 by
    exact G.kempeFillColor_edge z hplain k e3 e2]
  simp [e3, hfixed]

/-- Exact Coq `invh_col_s` for an aligned boundary. -/
theorem Coloring.invh_col_s_aligned
    (G : Hypermap.{u}) (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hnode : forall x : G.Dart, G.node x ≠ x)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hquasi : G.Quasicubic (z :: G.node z :: p))
    (hselect : G.face z = z ∨ G.face z ∉ z :: G.node z :: p)
    {k : (G.kempeReduction z hplain).Dart -> Color}
    (hk : (G.kempeReduction z hplain).Coloring k)
    (e1 : Color) :
    let D := G.kempeBoundaryData_aligned z p hplain hnode hcycle
      hnodup hquasi hselect
    let base := G.kempeFillColor z hplain k e1 e1
    let e2 := base (G.face (G.edge z))
    let e3 := if G.face z = z then e1 + e2 else base (G.face z)
    let k0 := G.kempeFillColor z hplain k e3 e2
    (if G.face z = z then [e1, Color.zero]
      else (ColSeq.urtrace ((D.lifted hplain).map k)).take 2).Nodup ->
      G.Coloring k0 ∧
        (forall u, k u = k0 (G.kempeProjection z hplain u)) ∧
        (G.face z = z -> k0 z + k0 (G.node z) = e1) := by
  dsimp only
  let D := G.kempeBoundaryData_aligned z p hplain hnode hcycle
    hnodup hquasi hselect
  let base := G.kempeFillColor z hplain k e1 e1
  let e2 := base (G.face (G.edge z))
  let e3 := if G.face z = z then e1 + e2 else base (G.face z)
  let k0 := G.kempeFillColor z hplain k e3 e2
  intro huniq
  change
    (if G.face z = z then [e1, Color.zero]
      else (ColSeq.urtrace ((D.lifted hplain).map k)).take 2).Nodup at huniq
  have hfaceAvail : G.face z = z ∨
      (G.face z ≠ z ∧ G.face z ≠ G.edge z) := by
    rcases D.faceCovered with hfixed | hmem
    · exact Or.inl hfixed
    · exact Or.inr (D.survives (G.face z) hmem)
  have he32 : e3 ≠ e2 := by
    by_cases hfixed : G.face z = z
    · have huniq' : [e1, Color.zero].Nodup := by
        simpa [hfixed] using huniq
      have he10 : e1 ≠ Color.zero := by simpa using huniq'
      intro heq
      apply he10
      apply Color.add_right_cancel
      have heq' : e1 + e2 = e2 := by
        simpa [e3, hfixed] using heq
      simpa using heq'
    · let q := G.node (G.edge z) :: G.face z :: G.node z :: p
      have hDproj : D.projected = q := by
        simp [D, kempeBoundaryData_aligned, hfixed, q]
      have hcolors : (D.lifted hplain).map k = q.map base := by
        rw [D.lifted_colors_eq_projected hplain k e1, hDproj]
      let a := base (G.node (G.edge z))
      let b := base (G.face z)
      let cs := (G.node z :: p).map base
      have huniq2 : (ColSeq.urtrace (a :: b :: cs)).take 2 |>.Nodup := by
        rw [if_neg hfixed, hcolors] at huniq
        simpa [q, a, b, cs] using huniq
      have hneLast := ne_last_of_take_two_urtrace_nodup a b cs huniq2
      have hnodeLast :
          G.node ((G.node z :: p).getLastD (G.node z)) = z := by
        simpa [List.getLastD] using hcycle.2
      have hnodeFaceEdge : G.node (G.face (G.edge z)) = z := by
        rw [Plain.node_face_eq_edge (G := G) hplain (G.edge z),
          Plain.edge_edge (G := G) hplain z]
      have hlast :
          (G.node z :: p).getLastD (G.node z) = G.face (G.edge z) := by
        apply G.node.injective
        rw [hnodeLast, hnodeFaceEdge]
      have hlastColor : (a :: b :: cs).getLastD Color.zero = e2 := by
        cases p with
        | nil =>
            change base (G.node z) = base (G.face (G.edge z))
            exact congrArg base hlast
        | cons x xs =>
            have hlast' :
                (x :: xs).getLastD x = G.face (G.edge z) := by
              simpa [List.getLastD] using hlast
            change (base x :: xs.map base).getLastD Color.zero =
              base (G.face (G.edge z))
            calc
              (base x :: xs.map base).getLastD Color.zero =
                  (base x :: xs.map base).getLastD (base x) := by
                cases xs <;> simp [List.getLastD]
              _ = base ((x :: xs).getLastD x) := by
                simpa using
                  (List.getLastD_map (f := base) (l := x :: xs) (a := x))
              _ = base (G.face (G.edge z)) := congrArg base hlast'
      intro heq
      apply hneLast
      rw [hlastColor]
      simpa [e3, hfixed, b] using heq
  have hext := Coloring.extend_kempeReduction G z hplain hnode
    hfaceAvail hk e1
  simpa [base, e2, e3, k0] using hext he32


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
