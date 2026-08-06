import FourColorTheorem.FourColor.Coloring.KempeMap.ReductionPlanarity

/-!
The fixed-face recursive Kempe witness.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- The complete fixed-face branch of the final Coq `Kempe_map` split. -/
theorem kempeWitness_fixed_of_reduction_closed
    (G : Hypermap.{u})
    (z : G.Dart) (p : List G.Dart)
    (hplain : G.Plain)
    (hcycle : FunctionCycle G.node (z :: G.node z :: p))
    (hnodup : (z :: G.node z :: p).Nodup)
    (hquasi : G.Quasicubic (z :: G.node z :: p))
    (hfixed : G.face z = z)
    {k : G.Dart -> Color} (hk : G.Coloring k)
    (hclosed :
      let hnode := Coloring.node_ne_self G hk
      let D := G.kempeBoundaryData_aligned z p hplain hnode hcycle
        hnodup hquasi (Or.inl hfixed)
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
    hnodup hquasi (Or.inl hfixed)
  let H := G.kempeReduction z hplain
  let proj := G.kempeProjection z hplain
  let s := D.lifted hplain
  let sr := listUnrot1 s
  let kH : H.Dart -> Color := k ∘ proj
  have hkH : H.Coloring kH := by
    exact Coloring.comp_kempeProjection G z hplain hk
  have hDproj : D.projected = p := by
    simp [D, kempeBoundaryData_aligned, hfixed]
  have hcolorsH : s.map kH = p.map k := by
    calc
      s.map kH = D.projected.map k := by
        simpa [s, kH, proj] using D.lifted_map_projection hplain k
      _ = p.map k := by rw [hDproj]
  have htraceH :
      H.RingTrace sr (ColSeq.urtrace (s.map kH)) := by
    exact ⟨kH, hkH, by
      simpa [sr] using (H.trace_colorsOn_listUnrot1 kH s).symm⟩
  have hclosed' : Chromogram.KempeClosed (H.RingTrace sr) := by
    simpa [hnode, D, H, s, sr] using hclosed
  rcases (hclosed' _ htraceH).2 with ⟨w, hw, hall⟩
  have hshape := Coloring.urtrace_aligned_of_face_fixed G z p hplain
    hk hcycle hfixed
  let e1 := k z + k (G.node z)
  have he1 : e1 ≠ Color.zero := by simpa [e1] using hshape.1
  have hsourceTrace :
      ColSeq.trace (G.colorsOn k (listUnrot1 r)) =
        ColSeq.urtrace (r.map k) :=
    G.trace_colorsOn_listUnrot1 k r
  refine ⟨fixedKempeGram e1 w, ?_, ?_⟩
  · rw [hsourceTrace]
    change Chromogram.matchg []
      (ColSeq.urtrace ((z :: G.node z :: p).map k))
      (fixedKempeGram e1 w) = true
    rw [hshape.2]
    apply match_fixedKempeGram e1 w _ he1
    simpa [hcolorsH] using hw
  · intro et het
    rcases match_fixedKempeGram_iff e1 w et he1 het with
      ⟨e2, he2, et2, het2w, ret⟩
    rcases hall et2 het2w with ⟨k1, hk1, het2⟩
    have het2Trace : et2 = ColSeq.urtrace (s.map k1) := by
      calc
        et2 = ColSeq.trace (H.colorsOn k1 sr) := het2
        _ = ColSeq.trace ((listUnrot1 s).map k1) := rfl
        _ = ColSeq.urtrace (s.map k1) :=
          H.trace_colorsOn_listUnrot1 k1 s
    have huniq : [e2, Color.zero].Nodup := by simpa using he2
    have huniq' :
        (if G.face z = z then [e2, Color.zero]
          else (ColSeq.urtrace
            ((D.lifted hplain).map k1)).take 2).Nodup := by
      simpa [hfixed] using huniq
    rcases Coloring.invh_col_s_aligned G z p hplain hnode hcycle
      hnodup hquasi (Or.inl hfixed) hk1 e2 huniq' with
      ⟨hk0, hagree, hsum⟩
    let base := G.kempeFillColor z hplain k1 e2 e2
    let ce := base (G.face (G.edge z))
    let cz := if G.face z = z then e2 + ce else base (G.face z)
    let k0 := G.kempeFillColor z hplain k1 cz ce
    have hk0' : G.Coloring k0 := by simpa [base, ce, cz, k0] using hk0
    have hagree' : forall u, k1 u = k0 (proj u) := by
      simpa [base, ce, cz, k0, proj] using hagree
    have hsum' : k0 z + k0 (G.node z) = e2 := by
      simpa [base, ce, cz, k0] using hsum hfixed
    have hmap : s.map k1 = p.map k0 := by
      calc
        s.map k1 = s.map (k0 ∘ proj) := by
          apply List.map_congr_left
          intro u _
          exact hagree' u
        _ = D.projected.map k0 := by
          simpa [s, proj] using D.lifted_map_projection hplain k0
        _ = p.map k0 := by rw [hDproj]
    have het2p : et2 = ColSeq.urtrace (p.map k0) :=
      het2Trace.trans (congrArg ColSeq.urtrace hmap)
    have hshape0 := Coloring.urtrace_aligned_of_face_fixed G z p hplain
      hk0' hcycle hfixed
    have hsourceTrace0 :
        ColSeq.trace (G.colorsOn k0 (listUnrot1 r)) =
          ColSeq.urtrace (r.map k0) :=
      G.trace_colorsOn_listUnrot1 k0 r
    refine ⟨k0, hk0', ?_⟩
    rw [ret, hsourceTrace0]
    change e2 :: e2 :: et2 =
      ColSeq.urtrace ((z :: G.node z :: p).map k0)
    rw [hshape0.2, hsum', het2p]


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
