import FourColorTheorem.FourColor.Presentation.UnavoidabilitySoundness.ConversePart4

/-! Soundness of the second converse-part transformation. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

noncomputable section

universe u

theorem convPart12_ds1
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let ef3x : G.Dart := G.edge (G.face (G.face (G.face x)))
    G.arity (G.edge (G.invFace2 effx)) =
      G.arity (G.edge (G.face (G.face ef3x))) := by
  dsimp
  simp [Hypermap.invFace2]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  nth_rewrite 2 [← Hypermap.arity_face]
  congr 1
  have fEnne (y : G.Dart) : G.face y = G.node (G.node (G.edge y)) := by
    exact Hypermap.Plain.face_eq_node_node_edge_of_cubic
      (G := G) hPlain hCubic y
  simp only [fEnne]
  simp [Hypermap.Plain.edge_edge (G := G) hPlain, (hCubic _).1]

theorem convPart12_ds2
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let ef3x : G.Dart := G.edge (G.face (G.face (G.face x)))
    G.edge (G.face (G.invFace2 effx)) = G.face ef3x := by
  dsimp
  simp [Hypermap.invFace2]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [← Hypermap.Plain.node_face_eq_edge (G := G) hPlain
    (G.face (G.face x))]
  rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hCubic]

theorem convPart12_df21
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) (x : G.Dart) :
    let ef3x : G.Dart := G.edge (G.face (G.face (G.face x)))
    let ef4x : G.Dart := G.edge (G.face (G.face (G.face (G.face x))))
    G.arity (G.edge (G.face (G.face ef4x))) =
      G.arity
        (G.edge ((G.face : G.Dart → G.Dart)^[G.arity ef3x - 2] ef3x)) := by
  dsimp
  let ef3x : G.Dart := G.edge (G.face (G.face (G.face x)))
  have hge : 2 ≤ G.arity ef3x := by
    have h5 := Hypermap.arity_ge_five_of_pentagonal (G := G) hpenta ef3x
    omega
  have hback :
      (G.face : G.Dart → G.Dart)^[G.arity ef3x - 2] ef3x =
        (G.face.symm : G.Dart → G.Dart)^[2] ef3x := by
    apply (G.face.injective.iterate 2)
    calc
      (G.face : G.Dart → G.Dart)^[2]
          ((G.face : G.Dart → G.Dart)^[G.arity ef3x - 2] ef3x) =
          (G.face : G.Dart → G.Dart)^[2 + (G.arity ef3x - 2)] ef3x := by
            rw [Function.iterate_add_apply]
      _ = (G.face : G.Dart → G.Dart)^[G.arity ef3x] ef3x := by
            congr 1
            omega
      _ = ef3x := G.face_iterate_arity ef3x
      _ = (G.face : G.Dart → G.Dart)^[2]
          ((G.face.symm : G.Dart → G.Dart)^[2] ef3x) := by
            simp [Function.iterate_succ_apply]
  rw [hback]
  rw [← Hypermap.arity_face]
  congr 1
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [← Hypermap.edge_node_eq_face_symm (G := G)]
  rw [← Hypermap.edge_node_eq_face_symm (G := G)]
  have fEnne (y : G.Dart) : G.face y = G.node (G.node (G.edge y)) := by
    exact Hypermap.Plain.face_eq_node_node_edge_of_cubic
      (G := G) hPlain hCubic y
  simp only [ef3x, fEnne]
  simp [Hypermap.Plain.edge_edge (G := G) hPlain, (hCubic _).1]

private theorem convPart12_head_arity
    {G : Hypermap.{u}} (hPlain : G.Plain) (x : G.Dart) :
    G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x)))) =
      G.arity (SubpartLoc.move SubpartLoc.Pspoke G
        ((G.face : G.Dart → G.Dart)^[4] x)) := by
  dsimp [SubpartLoc.move]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]

private theorem convPart12_s1_arity
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (SubpartLoc.move SubpartLoc.Pspoke G
        (G.invFace2 (G.edge (G.face (G.face x))))) =
      G.arity (SubpartLoc.move SubpartLoc.Phat G
        ((G.face : G.Dart → G.Dart)^[3] x)) := by
  dsimp [SubpartLoc.move]
  simpa using convPart12_ds1 (G := G) hPlain hCubic x

private theorem convPart12_s2_arity
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (x : G.Dart) :
    G.arity (SubpartLoc.move SubpartLoc.Pspoke G
        (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
      G.arity (SubpartLoc.move SubpartLoc.Pspoke G
        ((G.face : G.Dart → G.Dart)^[3] x)) := by
  dsimp [SubpartLoc.move]
  rw [convPart12_ds2 (G := G) hPlain hCubic x]
  exact Hypermap.arity_face (G := G)
    (G.edge (G.face (G.face (G.face x))))

theorem convPart12_f21_free_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart} {s2 s1 h23 : PRange}
    {tail q3 : Part}
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons s2 s1 (Part.Pcons h23 PRange.Pr59 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons s2 s1 (Part.Pcons h23 PRange.Pr59 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with ⟨⟨Es2, Es1⟩, ⟨⟨Eh23, _Efree⟩, _⟩⟩
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : s2 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hhat2 : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  constructor
  · simpa [Part.convPart12] using hhead
  · simp [Part.convPart12, Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hhat2,
      G.face_face_invFace2, hq3]

theorem convPart12_spoke5_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart} {s1 h23 f21 : PRange}
    {tail q3 : Part} (hf21 : f21 ≠ PRange.Pr59)
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons PRange.Pr55 s1 (Part.Pcons h23 f21 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons PRange.Pr55 s1 (Part.Pcons h23 f21 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with ⟨⟨Es2, Es1⟩, ⟨⟨Eh23, Ef21⟩, _⟩⟩
  have hn : G.arity (G.edge (G.face (G.face (G.face x)))) = 5 := by
    simpa [SubpartLoc.move, PRange.contains, Function.iterate_succ_apply]
      using Es2
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hDs2 := convPart12_ds2 (G := G) hPlain hCubic x
  have hDf := convPart12_df21 (G := G) hPlain hCubic hpenta x
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : PRange.Pr55 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hf21' : f21 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Phat G
          ((G.face : G.Dart → G.Dart)^[4] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]
      simpa [Function.iterate_succ_apply, hn] using hDf.symm]
    simpa [Function.iterate_succ_apply] using Ef21
  cases f21 <;> simp [Part.convPart12] at hf21 ⊢
  all_goals
    constructor
    · exact hhead
    · simp [Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hf21',
        G.face_face_invFace2, hq3]

theorem convPart12_spoke6_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart} {s1 h23 f21 : PRange}
    {tail q3 : Part} (hf21 : f21 ≠ PRange.Pr59)
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons PRange.Pr66 s1 (Part.Pcons h23 f21 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons PRange.Pr66 s1 (Part.Pcons h23 f21 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with ⟨⟨Es2, Es1⟩, ⟨⟨Eh23, Ef21⟩, _⟩⟩
  have hn : G.arity (G.edge (G.face (G.face (G.face x)))) = 6 := by
    simpa [SubpartLoc.move, PRange.contains, Function.iterate_succ_apply]
      using Es2
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hDs2 := convPart12_ds2 (G := G) hPlain hCubic x
  have hDf := convPart12_df21 (G := G) hPlain hCubic hpenta x
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : PRange.Pr66 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hhat2 : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hf21' : f21 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Phat G
          ((G.face : G.Dart → G.Dart)^[4] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]
      simpa [Function.iterate_succ_apply, hn] using hDf.symm]
    simpa [Function.iterate_succ_apply] using Ef21
  cases f21 <;> simp [Part.convPart12] at hf21 ⊢
  all_goals
    constructor
    · exact hhead
    · simp [Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hhat2, hf21',
        G.face_face_invFace2, hq3]

theorem convPart12_spoke7_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart} {s1 h23 f21 : PRange}
    {tail q3 : Part} (hf21 : f21 ≠ PRange.Pr59)
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons PRange.Pr77 s1 (Part.Pcons h23 f21 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons PRange.Pr77 s1 (Part.Pcons h23 f21 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with ⟨⟨Es2, Es1⟩, ⟨⟨Eh23, Ef21⟩, _⟩⟩
  have hn : G.arity (G.edge (G.face (G.face (G.face x)))) = 7 := by
    simpa [SubpartLoc.move, PRange.contains, Function.iterate_succ_apply]
      using Es2
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hDs2 := convPart12_ds2 (G := G) hPlain hCubic x
  have hDf := convPart12_df21 (G := G) hPlain hCubic hpenta x
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : PRange.Pr77 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hhat2 : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hfan1 : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hf21' : f21 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Phat G
          ((G.face : G.Dart → G.Dart)^[4] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]
      simpa [Function.iterate_succ_apply, hn] using hDf.symm]
    simpa [Function.iterate_succ_apply] using Ef21
  cases f21 <;> simp [Part.convPart12] at hf21 ⊢
  all_goals
    constructor
    · exact hhead
    · simp [Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hhat2, hfan1, hf21',
        G.face_face_invFace2, hq3]

theorem convPart12_pcons6_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart} {s1 h12 h23 f21 : PRange}
    {tail q3 : Part}
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons6 s1 h12 (Part.Pcons h23 f21 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons6 s1 h12 (Part.Pcons h23 f21 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with ⟨⟨⟨Es2, Es1⟩, Eh12⟩, ⟨⟨Eh23, Ef21⟩, _⟩⟩
  have hn : G.arity (G.edge (G.face (G.face (G.face x)))) = 6 := by
    simpa [SubpartLoc.move, PRange.contains, Function.iterate_succ_apply]
      using Es2
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hDs2 := convPart12_ds2 (G := G) hPlain hCubic x
  have hDf := convPart12_df21 (G := G) hPlain hCubic hpenta x
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : PRange.Pr66 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hh12 : h12 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
          ((G.face : G.Dart → G.Dart)^[3] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]]
    simpa [Function.iterate_succ_apply] using Eh12
  have hf21' : f21 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Phat G
          ((G.face : G.Dart → G.Dart)^[4] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]
      simpa [Function.iterate_succ_apply, hn] using hDf.symm]
    simpa [Function.iterate_succ_apply] using Ef21
  constructor
  · simpa [Part.convPart12] using hhead
  · simp [Part.convPart12, Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hh12,
      hf21', G.face_face_invFace2, hq3]

theorem convPart12_pcons7_sound
    {G : Hypermap.{u}} (hPlain : G.Plain) (hCubic : G.Cubic)
    (hpenta : G.Pentagonal) {x : G.Dart}
    {s1 h12 f21 h23 f22 : PRange} {tail q3 : Part}
    (hfit : Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
      (Part.Pcons7 s1 h12 f21 (Part.Pcons h23 f22 tail)) = true)
    (hq3 : Part.fitp G (G.edge (G.face (G.face x))) q3 = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12
      (Part.Pcons7 s1 h12 f21 (Part.Pcons h23 f22 tail))
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  simp [Part.fitp] at hfit
  rcases hfit with
    ⟨⟨⟨⟨Es2, Es1⟩, Eh12⟩, Ef21⟩, ⟨⟨Eh23, Ef22⟩, _⟩⟩
  have hn : G.arity (G.edge (G.face (G.face (G.face x)))) = 7 := by
    simpa [SubpartLoc.move, PRange.contains, Function.iterate_succ_apply]
      using Es2
  have hhead :
      h23 (G.arity (SubpartLoc.move SubpartLoc.Phat G
        (G.edge (G.face (G.face x))))) = true := by
    rw [convPart12_head_arity (G := G) hPlain x]
    simpa [Function.iterate_succ_apply] using Eh23
  have hDs2 := convPart12_ds2 (G := G) hPlain hCubic x
  have hDf := convPart12_df21 (G := G) hPlain hCubic hpenta x
  have hhatInv : PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true :=
    PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  have hs1 : s1 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.invFace2 (G.edge (G.face (G.face x)))))) = true := by
    rw [convPart12_s1_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es1
  have hs2 : PRange.Pr77 (G.arity (SubpartLoc.move SubpartLoc.Pspoke G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [convPart12_s2_arity (G := G) hPlain hCubic x]
    simpa [Function.iterate_succ_apply] using Es2
  have hh12 : h12 (G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Phat G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
          ((G.face : G.Dart → G.Dart)^[3] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]]
    simpa [Function.iterate_succ_apply] using Eh12
  have hf21' : f21 (G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Pfan1 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
          ((G.face : G.Dart → G.Dart)^[3] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]]
    simpa [Function.iterate_succ_apply] using Ef21
  have hf22' : f22 (G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x))))))) = true := by
    rw [show G.arity (SubpartLoc.move SubpartLoc.Pfan2 G
      (G.face (G.invFace2 (G.edge (G.face (G.face x)))))) =
        G.arity (SubpartLoc.move SubpartLoc.Phat G
          ((G.face : G.Dart → G.Dart)^[4] x)) by
      dsimp [SubpartLoc.move]
      rw [hDs2]
      simpa [Function.iterate_succ_apply, hn] using hDf.symm]
    simpa [Function.iterate_succ_apply] using Ef22
  constructor
  · simpa [Part.convPart12] using hhead
  · simp [Part.convPart12, Part.pconsS, Part.fitp, hs1, hhatInv, hs2, hh12,
      hf21', hf22', G.face_face_invFace2, hq3]

def ConvPart12Sound : Prop :=
  ∀ ⦃G : Hypermap.{u}⦄,
    G.Plain →
      G.Cubic →
        G.Pentagonal →
          ∀ {x : G.Dart} {p : Part},
            Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x) p = true →
              let effx : G.Dart := G.edge (G.face (G.face x))
              let up := Part.convPart12 p
              up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) =
                true ∧
                ∀ {q3 : Part},
                  Part.fitp G effx q3 = true →
                    Part.fitp G (G.invFace2 effx) (up.2 q3) = true

theorem convPart12_pointwise_to_universal
    {G : Hypermap.{u}} {x : G.Dart} {p : Part}
    (h : ∀ {q3 : Part},
      Part.fitp G (G.edge (G.face (G.face x))) q3 = true →
        let effx : G.Dart := G.edge (G.face (G.face x))
        let up := Part.convPart12 p
        up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
          Part.fitp G (G.invFace2 effx) (up.2 q3) = true) :
    let effx : G.Dart := G.edge (G.face (G.face x))
    let up := Part.convPart12 p
    up.1 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      ∀ {q3 : Part},
        Part.fitp G effx q3 = true →
          Part.fitp G (G.invFace2 effx) (up.2 q3) = true := by
  dsimp
  constructor
  · exact (h (q3 := Part.Pnil) (by simp [Part.fitp])).1
  · intro q3 hq3
    exact (h hq3).2

theorem convPart12_default_sound
    {G : Hypermap.{u}} (hpenta : G.Pentagonal) {x : G.Dart} :
    let effx : G.Dart := G.edge (G.face (G.face x))
    PRange.Pr59 (G.arity (SubpartLoc.move SubpartLoc.Phat G effx)) = true ∧
      ∀ {q3 : Part},
        Part.fitp G effx q3 = true →
          Part.fitp G (G.invFace2 effx) Part.Pnil = true := by
  dsimp
  constructor
  · exact PRange.contains_Pr59_of_ge_five
      (Hypermap.arity_ge_five_of_pentagonal hpenta _)
  · intro q3 hq3
    simp [Part.fitp]

theorem convPart12Sound : ConvPart12Sound.{u} := by
  intro G hPlain hCubic hpenta x p hfit
  cases p with
  | Pnil =>
      simpa [Part.convPart12] using
        convPart12_default_sound (G := G) (x := x) hpenta
  | Pcons s2 s1 p2 =>
      cases p2 with
      | Pnil =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons h23 f21 tail =>
          by_cases hf21 : f21 = PRange.Pr59
          · subst f21
            exact convPart12_pointwise_to_universal
              (G := G) (x := x)
              (p := Part.Pcons s2 s1
                (Part.Pcons h23 PRange.Pr59 tail))
              (fun {q3} hq3 =>
                convPart12_f21_free_sound (G := G) hPlain hCubic hpenta
                  (x := x) (s2 := s2) (s1 := s1) (h23 := h23)
                  (tail := tail) (q3 := q3) hfit hq3)
          · cases s2 with
            | Pr55 =>
                exact convPart12_pointwise_to_universal
                  (G := G) (x := x)
                  (p := Part.Pcons PRange.Pr55 s1
                    (Part.Pcons h23 f21 tail))
                  (fun {q3} hq3 =>
                    convPart12_spoke5_sound (G := G) hPlain hCubic hpenta
                      (x := x) (s1 := s1) (h23 := h23) (f21 := f21)
                      (tail := tail) (q3 := q3) hf21 hfit hq3)
            | Pr66 =>
                exact convPart12_pointwise_to_universal
                  (G := G) (x := x)
                  (p := Part.Pcons PRange.Pr66 s1
                    (Part.Pcons h23 f21 tail))
                  (fun {q3} hq3 =>
                    convPart12_spoke6_sound (G := G) hPlain hCubic hpenta
                      (x := x) (s1 := s1) (h23 := h23) (f21 := f21)
                      (tail := tail) (q3 := q3) hf21 hfit hq3)
            | Pr77 =>
                exact convPart12_pointwise_to_universal
                  (G := G) (x := x)
                  (p := Part.Pcons PRange.Pr77 s1
                    (Part.Pcons h23 f21 tail))
                  (fun {q3} hq3 =>
                    convPart12_spoke7_sound (G := G) hPlain hCubic hpenta
                      (x := x) (s1 := s1) (h23 := h23) (f21 := f21)
                      (tail := tail) (q3 := q3) hf21 hfit hq3)
            | Pr88 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr99 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr56 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr67 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr78 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr89 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr57 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr68 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr79 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr58 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr69 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
            | Pr59 =>
                simpa [Part.convPart12] using
                  convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons6 _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons7 _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons8 _ _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
  | Pcons6 s1 h12 p2 =>
      cases p2 with
      | Pcons h23 f21 tail =>
          exact convPart12_pointwise_to_universal
            (G := G) (x := x)
            (p := Part.Pcons6 s1 h12 (Part.Pcons h23 f21 tail))
            (fun {q3} hq3 =>
              convPart12_pcons6_sound (G := G) hPlain hCubic hpenta
                (x := x) (s1 := s1) (h12 := h12) (h23 := h23)
                (f21 := f21) (tail := tail) (q3 := q3) hfit hq3)
      | Pnil =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons6 _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons7 _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons8 _ _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
  | Pcons7 s1 h12 f21 p2 =>
      cases p2 with
      | Pcons h23 f22 tail =>
          exact convPart12_pointwise_to_universal
            (G := G) (x := x)
            (p := Part.Pcons7 s1 h12 f21 (Part.Pcons h23 f22 tail))
            (fun {q3} hq3 =>
              convPart12_pcons7_sound (G := G) hPlain hCubic hpenta
                (x := x) (s1 := s1) (h12 := h12) (f21 := f21)
                (h23 := h23) (f22 := f22) (tail := tail) (q3 := q3)
                hfit hq3)
      | Pnil =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons6 _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons7 _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
      | Pcons8 _ _ _ _ _ =>
          simpa [Part.convPart12] using
            convPart12_default_sound (G := G) (x := x) hpenta
  | Pcons8 _ _ _ _ _ =>
      simpa [Part.convPart12] using
        convPart12_default_sound (G := G) (x := x) hpenta

theorem conversePartSound_of_convPart4_convPart12
    (h4 : ConvPart4Sound.{u}) (h12 : ConvPart12Sound.{u}) :
    ConversePartSound.{u} := by
  intro G hG hCubic hpenta x p hfit
  have hPlain : G.Plain := hG.plain
  have hfits := hfit
  simp [Part.exactFitp] at hfits
  rcases hfits with ⟨hsize, hfitp⟩
  let effx : G.Dart := G.edge (G.face (G.face x))
  rcases h4eq : Part.convPart4 p with ⟨h45, q4⟩
  have h4sound := h4 hPlain hCubic hpenta (x := x) (p := p) hfitp
  simp [h4eq] at h4sound
  rcases h4sound with ⟨Eh45, hq4⟩
  have hfit2 :
      Part.fitp G ((G.face : G.Dart → G.Dart)^[2] x)
        (Part.drop 2 p) = true :=
    Part.fitp_drop_of_eq_true (G := G) 2 hfitp
  rcases h5eq : Part.convPart5 h45 (Part.drop 2 p) with ⟨u, q5⟩
  have h5sound := Part.convPart5_sound (G := G) hpenta
    (h45 := h45) (p := Part.drop 2 p)
    (y := (G.face : G.Dart → G.Dart)^[2] x) Eh45 hfit2
  simp [h5eq] at h5sound
  rcases h5sound with ⟨hu, hq5⟩
  have hq : Part.fitp G (G.face effx) (q4 q5) = true := hq4 hq5
  have hfit3 :
      Part.fitp G ((G.face : G.Dart → G.Dart)^[3] x)
        (Part.drop 3 p) = true :=
    Part.fitp_drop_of_eq_true (G := G) 3 hfitp
  rcases h12eq : Part.convPart12 (Part.drop 3 p) with ⟨h23, q12⟩
  have h12sound := h12 hPlain hCubic hpenta (x := x)
    (p := Part.drop 3 p) hfit3
  simp [h12eq] at h12sound
  rcases h12sound with ⟨Eh23, hq12⟩
  have hfit5 :
      Part.fitp G ((G.face : G.Dart → G.Dart)^[5] x)
        (Part.drop 5 p) = true :=
    Part.fitp_drop_of_eq_true (G := G) 5 hfitp
  have hsize5 : G.arity x = 5 + (Part.drop 5 p).size := by
    rw [hsize, Part.size_drop]
    have hge : 5 ≤ p.size := by
      simpa [← hsize] using Hypermap.arity_ge_five_of_pentagonal hpenta x
    omega
  have hq3 :
      Part.fitp G effx
        (Part.convPart3 h23 (Part.drop 5 p) (q4 q5)) = true := by
    exact Part.convPart3_sound (G := G) hPlain Eh23 hsize5 hfit5 hq
  have htail :
      Part.fitp G (G.invFace2 effx)
        (q12 (Part.convPart3 h23 (Part.drop 5 p) (q4 q5))) = true :=
    hq12 hq3
  rw [Part.tightFitp, Part.converse]
  simp only [h4eq, h5eq, h12eq]
  rw [Bool.and_eq_true]
  constructor
  · simpa [effx, SubpartLoc.move, G.arity_invFace2] using hu
  · exact htail

theorem conversePartSound : ConversePartSound.{u} :=
  conversePartSound_of_convPart4_convPart12
    convPart4Sound convPart12Sound


end

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
