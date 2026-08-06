import FourColorTheorem.FourColor.Coloring.KempeMap.FixedWitness

/-!
The nonfixed-face recursive Kempe witness.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The complete nonfixed-face branch of the final Coq `Kempe_map` split. -/
theorem kempeWitness_nonfixed_of_reduction_closed
    (G : Hypermap.{u})
    (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hquasi : G.Quasicubic (z :: G.node z :: p))
    (hfaceOut : G.face z ∉ z :: G.node z :: p)
    {k : G.Dart -> Color} (hk : G.Coloring k)
    (hclosed :
      let hnode := Coloring.node_ne_self G hk
      let D := G.kempeBoundaryData_aligned z p hplain hnode hcycle
        hnodup hquasi (Or.inr hfaceOut)
      Chromogram.KempeClosed
        ((G.kempeReduction z hplain).RingTrace
          (listUnrot1 (D.lifted hplain)))) :
    G.KempeWitness
      (listUnrot1 (z :: G.node z :: p))
      (ColSeq.trace
        (G.colorsOn k (listUnrot1 (z :: G.node z :: p)))) := by
  classical
  let r := z :: G.node z :: p
  let hnode := Coloring.node_ne_self G hk
  let D := G.kempeBoundaryData_aligned z p hplain hnode hcycle
    hnodup hquasi (Or.inr hfaceOut)
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  let s := D.lifted hplain
  let sr := listUnrot1 s
  let kH : H.Dart -> Color := k ∘ proj
  let q := G.node (G.edge z) :: G.face z :: G.node z :: p
  have hfixed : G.face z ≠ z := by
    intro h
    exact hfaceOut (by simp [h])
  have hkH : H.Coloring kH := by
    exact Coloring.comp_kempeProjection G z hplain hk
  have hDproj : D.projected = q := by
    simp [D, kempeBoundaryData_aligned, hfixed, q]
  have hfaceColor : k (G.face z) = k z :=
    Coloring.face_eq (G := G) hk z
  have hcolorsH :
      s.map kH =
        k (G.node (G.edge z)) :: k z :: k (G.node z) :: p.map k := by
    calc
      s.map kH = D.projected.map k := by
        simpa [s, kH, proj] using D.lifted_map_projection hplain k
      _ = q.map k := by rw [hDproj]
      _ = _ := by simp [q, hfaceColor]
  have hnodeLast :
      G.node ((G.node z :: p).getLastD (G.node z)) = z := by
    simpa [List.getLastD] using hcycle.2
  have hnodeFaceEdge : G.node (G.face (G.edge z)) = z := by
    rw [Plain.node_face_eq_edge (G := G) hplain (G.edge z),
      Plain.edge_edge (G := G) hplain z]
  have hlastDart :
      (G.node z :: p).getLastD (G.node z) = G.face (G.edge z) := by
    apply G.node.injective
    rw [hnodeLast, hnodeFaceEdge]
  have hlastColor :
      ((G.node z :: p).map k).getLastD (k (G.node z)) =
        k (G.edge z) := by
    calc
      ((G.node z :: p).map k).getLastD (k (G.node z)) =
          k ((G.node z :: p).getLastD (G.node z)) := by
        simpa using
          (List.getLastD_map (f := k) (l := G.node z :: p)
            (a := G.node z))
      _ = k (G.face (G.edge z)) := congrArg k hlastDart
      _ = k (G.edge z) := Coloring.face_eq (G := G) hk (G.edge z)
  let e1 := k (G.edge z) + k z
  let e2 := k (G.edge z) + k (G.node (G.edge z))
  let tail := (k z + k (G.node z)) ::
    ColSeq.pairSums (k (G.node z)) (p.map k)
  have hrel := urtrace_nonfixed_relation_of_tail_last
    (k z) (k (G.node z)) (k (G.node (G.edge z)))
    (k (G.edge z)) (p.map k) hlastColor
  have hsourceRel : ColSeq.urtrace (r.map k) = e1 :: tail := by
    simpa [r, e1, tail] using hrel.1
  have hreducedRel : ColSeq.urtrace (s.map kH) =
      e2 :: (e2 + e1) :: tail := by
    rw [hcolorsH]
    simpa [e1, e2, tail] using hrel.2
  have he1 : e1 ≠ Color.zero := by
    intro heq
    apply Coloring.ne_edge (G := G) hk z
    exact ((Color.add_eq_zero_iff_eq (k (G.edge z)) (k z)).mp heq).symm
  have htraceH : H.RingTrace sr (ColSeq.urtrace (s.map kH)) := by
    exact ⟨kH, hkH, by
      simpa [sr] using (H.trace_colorsOn_listUnrot1 kH s).symm⟩
  have hclosed' : Chromogram.KempeClosed (H.RingTrace sr) := by
    simpa [hnode, D, H, s, sr] using hclosed
  rcases (hclosed' _ htraceH).2 with ⟨w, hw, hall⟩
  have hwShape : Chromogram.matchg []
      (e2 :: (e2 + e1) :: tail) w = true := by
    rw [← hreducedRel]
    exact hw
  have hadm := nonfixedKempeAdmissible_of_match e1 e2 tail w he1 hwShape
  have hsourceTrace :
      ColSeq.trace (G.colorsOn k (listUnrot1 r)) =
        ColSeq.urtrace (r.map k) :=
    G.trace_colorsOn_listUnrot1 k r
  refine ⟨nonfixedKempeGram w, ?_, ?_⟩
  · rw [hsourceTrace, hsourceRel]
    exact match_nonfixedKempeGram e1 e2 tail w he1 hwShape
  · intro et het
    cases et with
    | nil =>
        have hne := nonfixedKempeGram_ne_nil_of_admissible hadm
        cases hg : nonfixedKempeGram w with
        | nil => exact False.elim (hne hg)
        | cons g gs => simp [hg, Chromogram.matchg] at het
    | cons e tail' =>
        rcases match_nonfixedKempeGram_exists e tail' w hadm het with
          ⟨e0, huniq2, hrecMatch⟩
        rcases hall _ hrecMatch with ⟨k1, hk1, hrecTrace⟩
        have hrecUr :
            e0 :: (e0 + e) :: tail' = ColSeq.urtrace (s.map k1) := by
          calc
            e0 :: (e0 + e) :: tail' =
                ColSeq.trace (H.colorsOn k1 sr) := hrecTrace
            _ = ColSeq.trace ((listUnrot1 s).map k1) := rfl
            _ = ColSeq.urtrace (s.map k1) :=
              H.trace_colorsOn_listUnrot1 k1 s
        have huniq :
            (ColSeq.urtrace (s.map k1)).take 2 |>.Nodup := by
          rw [← hrecUr]
          simpa using huniq2
        have huniq' :
            (if G.face z = z then [Color.zero, Color.zero]
              else (ColSeq.urtrace ((D.lifted hplain).map k1)).take 2).Nodup := by
          simpa [hfixed, s] using huniq
        rcases Coloring.invh_col_s_aligned G z p hplain hnode hcycle
          hnodup hquasi (Or.inr hfaceOut) hk1 Color.zero huniq' with
          ⟨hk0, hagree, _⟩
        let base := G.kempeFillColor z hplain k1 Color.zero Color.zero
        let ce := base (G.face (G.edge z))
        let cz := if G.face z = z then Color.zero + ce else base (G.face z)
        let k0 := G.kempeFillColor z hplain k1 cz ce
        have hk0' : G.Coloring k0 := by
          simpa [base, ce, cz, k0] using hk0
        have hagree' : forall u, k1 u = k0 (proj u) := by
          simpa [base, ce, cz, k0, proj] using hagree
        have hmap : s.map k1 = q.map k0 := by
          calc
            s.map k1 = s.map (k0 ∘ proj) := by
              apply List.map_congr_left
              intro u _
              exact hagree' u
            _ = D.projected.map k0 := by
              simpa [s, proj] using D.lifted_map_projection hplain k0
            _ = q.map k0 := by rw [hDproj]
        have hfaceColor0 : k0 (G.face z) = k0 z :=
          Coloring.face_eq (G := G) hk0' z
        have hqColors0 : q.map k0 =
            k0 (G.node (G.edge z)) :: k0 z ::
              k0 (G.node z) :: p.map k0 := by
          simp [q, hfaceColor0]
        have hlastColor0 :
            ((G.node z :: p).map k0).getLastD (k0 (G.node z)) =
              k0 (G.edge z) := by
          calc
            ((G.node z :: p).map k0).getLastD (k0 (G.node z)) =
                k0 ((G.node z :: p).getLastD (G.node z)) := by
              simpa using
                (List.getLastD_map (f := k0) (l := G.node z :: p)
                  (a := G.node z))
            _ = k0 (G.face (G.edge z)) := congrArg k0 hlastDart
            _ = k0 (G.edge z) :=
              Coloring.face_eq (G := G) hk0' (G.edge z)
        let e10 := k0 (G.edge z) + k0 z
        let e20 := k0 (G.edge z) + k0 (G.node (G.edge z))
        let tail0 := (k0 z + k0 (G.node z)) ::
          ColSeq.pairSums (k0 (G.node z)) (p.map k0)
        have hrel0 := urtrace_nonfixed_relation_of_tail_last
          (k0 z) (k0 (G.node z)) (k0 (G.node (G.edge z)))
          (k0 (G.edge z)) (p.map k0) hlastColor0
        have hsourceRel0 : ColSeq.urtrace (r.map k0) = e10 :: tail0 := by
          simpa [r, e10, tail0] using hrel0.1
        have hreducedRel0 : ColSeq.urtrace (s.map k1) =
            e20 :: (e20 + e10) :: tail0 := by
          rw [hmap, hqColors0]
          simpa [e10, e20, tail0] using hrel0.2
        have hcompare :
            e0 :: (e0 + e) :: tail' =
              e20 :: (e20 + e10) :: tail0 :=
          hrecUr.trans hreducedRel0
        injection hcompare with he20 hrest
        injection hrest with hsecond htail
        have he10 : e = e10 := by
          rw [← he20] at hsecond
          exact Color.add_left_cancel hsecond
        have hsourceTrace0 :
            ColSeq.trace (G.colorsOn k0 (listUnrot1 r)) =
              ColSeq.urtrace (r.map k0) :=
          G.trace_colorsOn_listUnrot1 k0 r
        refine ⟨k0, hk0', ?_⟩
        rw [hsourceTrace0, hsourceRel0, ← he10, ← htail]


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
