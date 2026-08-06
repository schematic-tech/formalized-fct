import FourColorTheorem.FourColor.Coloring.KempeMap.NonfixedWitness

/-!
The recursive Kempe-map theorem for planar plain quasicubic boundaries.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

/-- Coq `Kempe_map`: ring traces of a duplicate-free planar, plain,
quasicubic node cycle are Kempe-closed. -/
theorem kempeMap
    (G : Hypermap.{u})
    (r : List G.Dart)
    (geo : CyclePlanarPlainQuasicubic G r) :
    Chromogram.KempeClosed (G.RingTrace r) := by
  classical
  let P : Nat -> Prop := fun n =>
    ∀ (G : Hypermap.{u}) (r : List G.Dart),
      Fintype.card G.Dart = n ->
      CyclePlanarPlainQuasicubic G r ->
      Chromogram.KempeClosed (G.RingTrace r)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro G r hcard geo et htrace
        constructor
        · intro g
          exact RingTrace.perm (G := G) htrace g
        · rcases htrace with ⟨k, hk, het⟩
          cases r with
          | nil =>
              have hetNil : et = [] := by
                simpa [Hypermap.colorsOn, ColSeq.trace, ColSeq.ptrace,
                  ColSeq.ctrace] using het
              refine ⟨[], by simp [hetNil], ?_⟩
              intro et' het'
              have het'Nil : et' = [] := by
                cases et' with
                | nil => rfl
                | cons e es =>
                    cases es <;> cases e <;>
                      simp [Chromogram.matchg] at het'
              subst et'
              exact ⟨k, hk, by simp [Hypermap.colorsOn, ColSeq.trace]⟩
          | cons x xs =>
              have hx : x ∈ x :: xs := by simp
              rcases exists_face_fixed_or_face_not_mem_nodeCycle G
                geo.eulerPlanar geo.plain geo.cycle hx with
                ⟨z, hzr, hselect⟩
              have hnode : forall y : G.Dart, G.node y ≠ y :=
                Coloring.node_ne_self G hk
              rcases CyclePlanarPlainQuasicubic.exists_aligned G geo
                hzr (hnode z) with
                ⟨a, p, haLe, halign⟩
              let ra := z :: G.node z :: p
              have geoA : CyclePlanarPlainQuasicubic G ra := by
                have hrot := CyclePlanarPlainQuasicubic.rotate G geo a
                simpa [ra, halign] using hrot
              have hselectA : G.face z = z ∨ G.face z ∉ ra := by
                rcases hselect with hfixed | hout
                · exact Or.inl hfixed
                · right
                  intro hmem
                  apply hout
                  have hmemRot : G.face z ∈ (x :: xs).rotate a := by
                    simpa [ra, halign] using hmem
                  exact List.mem_rotate.mp hmemRot
              let D := G.kempeBoundaryData_aligned z p geoA.plain hnode
                geoA.cycle geoA.nodup geoA.quasicubic hselectA
              let H := G.kempeReduction z geoA.plain
              let s := D.lifted geoA.plain
              let sr := listUnrot1 s
              have geoS : CyclePlanarPlainQuasicubic H s :=
                { cycle := D.lifted_cycle geoA.plain hnode
                  nodup := D.lifted_nodup geoA.plain
                  eulerPlanar := G.kempeReduction_eulerPlanar z geoA.plain
                    geoA.eulerPlanar
                  plain := G.kempeReduction_plain z geoA.plain
                  quasicubic := D.lifted_quasicubic geoA.plain hnode
                    geoA.cycle (by simp) geoA.quasicubic }
              have geoSR : CyclePlanarPlainQuasicubic H sr := by
                exact CyclePlanarPlainQuasicubic.rotate H geoS (s.length - 1)
              have hsmallG : Fintype.card H.Dart < Fintype.card G.Dart := by
                exact lt_of_lt_of_le
                  ((G.walkupN z).walkupE_dart_card_lt
                    (G.kempeEdgeDart z geoA.plain))
                  (by
                    rw [G.walkupN_dart_card]
                    exact Nat.sub_le (Fintype.card G.Dart) 1)
              have hsmall : Fintype.card H.Dart < n := by
                simpa [hcard] using hsmallG
              have hclosedH : Chromogram.KempeClosed (H.RingTrace sr) :=
                ih (Fintype.card H.Dart) hsmall H sr rfl geoSR
              have hcore : G.KempeWitness (listUnrot1 ra)
                  (ColSeq.trace (G.colorsOn k (listUnrot1 ra))) := by
                rcases hselectA with hfixed | hfaceOut
                · apply kempeWitness_fixed_of_reduction_closed G z p
                    geoA.plain geoA.cycle geoA.nodup geoA.quasicubic
                    hfixed hk
                  simpa [hnode, D, H, s, sr] using hclosedH
                · apply kempeWitness_nonfixed_of_reduction_closed G z p
                    geoA.plain geoA.cycle geoA.nodup geoA.quasicubic
                    hfaceOut hk
                  simpa [hnode, D, H, s, sr] using hclosedH
              have hAligned : G.KempeWitness ra
                  (ColSeq.trace (G.colorsOn k ra)) := by
                have hrot := KempeWitness.rotate_one (G := G) hcore
                have htraceRot := G.trace_colorsOn_rotate k
                  (listUnrot1 ra) 1
                have htraceEq :
                    ColSeq.rot1
                        (ColSeq.trace (G.colorsOn k (listUnrot1 ra))) =
                      ColSeq.trace (G.colorsOn k ra) := by
                  simpa using htraceRot.symm
                simpa [htraceEq] using hrot
              let b := (x :: xs).length - a
              have hback : ra.rotate b = x :: xs := by
                calc
                  ra.rotate b = ((x :: xs).rotate a).rotate b := by
                    rw [halign]
                  _ = (x :: xs).rotate (a + b) :=
                    List.rotate_rotate (x :: xs) a b
                  _ = (x :: xs).rotate (x :: xs).length := by
                    rw [show a + b = (x :: xs).length by
                      exact Nat.add_sub_of_le haLe]
                  _ = x :: xs := List.rotate_length (x :: xs)
              have hbackWitness := KempeWitness.rotate (G := G) hAligned b
              have htraceBack := G.trace_colorsOn_rotate k ra b
              have htarget :
                  (ColSeq.rot1^[b])
                      (ColSeq.trace (G.colorsOn k ra)) = et := by
                rw [hback] at htraceBack
                exact htraceBack.symm.trans het.symm
              simpa [hback, htarget] using hbackWitness
  have hfinal := hP (Fintype.card G.Dart)
  dsimp [P] at hfinal
  exact hfinal G r rfl geo

/-- Source-compatible spelling of Coq's theorem name. -/
theorem Kempe_map
    (G : Hypermap.{u})
    (r : List G.Dart)
    (geo : CyclePlanarPlainQuasicubic G r) :
    Chromogram.KempeClosed (G.RingTrace r) :=
  kempeMap G r geo


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
