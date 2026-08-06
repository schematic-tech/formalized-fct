import FourColorTheorem.FourColor.Theorem.Cube.Construction

namespace Schematic.Math.GraphTheory
namespace FourColor

universe u
namespace Hypermap

variable (G : Hypermap.{u})
namespace Cube

variable {G}

open CubeTag
theorem main_face_forward_base
    (x : G.CubeDart)
    (hx : faceFamily x.1 = 0) :
    PermReachable G.face x.2 (((hypermap (G := G)).face x).2) := by
  rcases x with ⟨tag, x⟩
  cases tag <;>
    simp [faceFamily, hypermap_face_ctN, hypermap_face_ctEN,
      hypermap_face_ctF, hypermap_face_ctNF] at hx ⊢
  · exact PermReachable.refl G.face x
  · exact PermReachable.refl G.face x
  · exact PermReachable.refl G.face x
  · exact PermReachable.forward G.face x

theorem main_face_link_base
    {x y : G.CubeDart}
    (hx : faceFamily x.1 = 0)
    (hxy : PermLink (hypermap (G := G)).face x y) :
    PermReachable G.face x.2 y.2 := by
  cases hxy
  ·
      exact main_face_forward_base (G := G) x hx
  ·
      have hx' :
          faceFamily (((hypermap (G := G)).face.symm x).1) = 0 := by
        rw [faceFamily_face_symm (G := G) x, hx]
      have hforward :
          PermReachable G.face
            ((hypermap (G := G)).face.symm x).2 x.2 := by
        simpa using
          main_face_forward_base (G := G)
            ((hypermap (G := G)).face.symm x) hx'
      exact PermReachable.symm G.face hforward

theorem main_faceReachable_base
    {x y : G.CubeDart}
    (hxy : PermReachable (hypermap (G := G)).face x y)
    (hx : faceFamily x.1 = 0) :
    PermReachable G.face x.2 y.2 := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact PermReachable.refl G.face x.2
  · intro b c hxb hbc ih
    have hb : faceFamily b.1 = 0 := by
      rw [faceFamily_of_reachable (G := G) hxb, hx]
    exact PermReachable.trans G.face ih
      (main_face_link_base (G := G) hb hbc)

/-- Sum target for the three classes of `cube G` face orbits: original face,
edge, and node orbits. -/
abbrev FaceOrbitCode :=
  G.FaceOrbit ⊕ (G.EdgeOrbit ⊕ G.NodeOrbit)

noncomputable def faceOrbitCode : G.CubeDart → FaceOrbitCode (G := G)
  | (ctE, x) => Sum.inr (Sum.inl (PermOrbit.of G.edge x))
  | (ctFE, x) => Sum.inr (Sum.inr (PermOrbit.of G.node x))
  | (_, x) => Sum.inl (PermOrbit.of G.face x)

theorem faceOrbitCode_face (x : G.CubeDart) :
    faceOrbitCode ((hypermap (G := G)).face x) = faceOrbitCode x := by
  rcases x with ⟨tag, x⟩
  cases tag <;>
    simp [faceOrbitCode, hypermap_face_ctN, hypermap_face_ctEN,
      hypermap_face_ctF, hypermap_face_ctNF, hypermap_face_ctE,
      hypermap_face_ctFE, PermOrbit.of_apply]

theorem faceOrbitCode_face_symm (x : G.CubeDart) :
    faceOrbitCode ((hypermap (G := G)).face.symm x) = faceOrbitCode x := by
  have h := faceOrbitCode_face (G := G) ((hypermap (G := G)).face.symm x)
  simpa using h.symm

theorem faceOrbitCode_of_link
    {x y : G.CubeDart}
    (hxy : PermLink (hypermap (G := G)).face x y) :
    faceOrbitCode x = faceOrbitCode y := by
  cases hxy
  · exact (faceOrbitCode_face (G := G) x).symm
  · exact (faceOrbitCode_face_symm (G := G) x).symm

theorem faceOrbitCode_of_reachable
    {x y : G.CubeDart}
    (hxy : PermReachable (hypermap (G := G)).face x y) :
    faceOrbitCode x = faceOrbitCode y := by
  induction hxy with
  | refl =>
      rfl
  | tail hxb hbc ih =>
      exact ih.trans (faceOrbitCode_of_link (G := G) hbc)

theorem main_face_forward_lift (x : G.Dart) :
    PermReachable (hypermap (G := G)).face
      (ctNF, x) (ctNF, G.face x) := by
  have h1 :
      PermReachable (hypermap (G := G)).face
        (ctNF, x) (ctN, G.face x) := by
    simpa [hypermap_face_ctNF] using
      PermReachable.forward (hypermap (G := G)).face (ctNF, x)
  have h2 :
      PermReachable (hypermap (G := G)).face
        (ctN, G.face x) (ctEN, G.face x) := by
    simpa [hypermap_face_ctN] using
      PermReachable.forward (hypermap (G := G)).face (ctN, G.face x)
  have h3 :
      PermReachable (hypermap (G := G)).face
        (ctEN, G.face x) (ctF, G.face x) := by
    simpa [hypermap_face_ctEN] using
      PermReachable.forward (hypermap (G := G)).face (ctEN, G.face x)
  have h4 :
      PermReachable (hypermap (G := G)).face
        (ctF, G.face x) (ctNF, G.face x) := by
    simpa [hypermap_face_ctF] using
      PermReachable.forward (hypermap (G := G)).face (ctF, G.face x)
  exact PermReachable.trans (hypermap (G := G)).face h1
    (PermReachable.trans (hypermap (G := G)).face h2
      (PermReachable.trans (hypermap (G := G)).face h3 h4))

theorem edge_face_forward_lift (x : G.Dart) :
    PermReachable (hypermap (G := G)).face
      (ctE, x) (ctE, G.edge x) := by
  simpa [hypermap_face_ctE] using
    PermReachable.forward (hypermap (G := G)).face (ctE, x)

theorem node_face_forward_lift (x : G.Dart) :
    PermReachable (hypermap (G := G)).face
      (ctFE, x) (ctFE, G.node x) := by
  simpa [hypermap_face_ctFE] using
    PermReachable.forward (hypermap (G := G)).face (ctFE, x)

theorem main_faceReachable_lift
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (hypermap (G := G)).face (ctNF, x) (ctNF, y) := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact PermReachable.refl (hypermap (G := G)).face (ctNF, x)
  · intro b c hxb hbc ih
    have hstep :
        PermReachable (hypermap (G := G)).face (ctNF, b) (ctNF, c) := by
      cases hbc
      · exact main_face_forward_lift (G := G) b
      · have hforward := main_face_forward_lift (G := G) (G.face.symm b)
        simpa using PermReachable.symm (hypermap (G := G)).face hforward
    exact PermReachable.trans (hypermap (G := G)).face ih hstep

theorem edge_faceReachable_lift
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    PermReachable (hypermap (G := G)).face (ctE, x) (ctE, y) := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact PermReachable.refl (hypermap (G := G)).face (ctE, x)
  · intro b c hxb hbc ih
    have hstep :
        PermReachable (hypermap (G := G)).face (ctE, b) (ctE, c) := by
      cases hbc
      · exact edge_face_forward_lift (G := G) b
      · have hforward := edge_face_forward_lift (G := G) (G.edge.symm b)
        simpa using PermReachable.symm (hypermap (G := G)).face hforward
    exact PermReachable.trans (hypermap (G := G)).face ih hstep

theorem node_faceReachable_lift
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    PermReachable (hypermap (G := G)).face (ctFE, x) (ctFE, y) := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact PermReachable.refl (hypermap (G := G)).face (ctFE, x)
  · intro b c hxb hbc ih
    have hstep :
        PermReachable (hypermap (G := G)).face (ctFE, b) (ctFE, c) := by
      cases hbc
      · exact node_face_forward_lift (G := G) b
      · have hforward := node_face_forward_lift (G := G) (G.node.symm b)
        simpa using PermReachable.symm (hypermap (G := G)).face hforward
    exact PermReachable.trans (hypermap (G := G)).face ih hstep

noncomputable def faceOrbitToCode :
    (hypermap (G := G)).FaceOrbit → FaceOrbitCode (G := G) :=
  Quotient.lift (faceOrbitCode (G := G)) (by
    intro x y hxy
    exact faceOrbitCode_of_reachable (G := G) hxy)

noncomputable def faceOrbitOfFaceOrbit :
    G.FaceOrbit → (hypermap (G := G)).FaceOrbit :=
  Quotient.lift
    (fun x : G.Dart => PermOrbit.of (hypermap (G := G)).face (ctNF, x))
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of (hypermap (G := G)).face
        (main_faceReachable_lift (G := G) hxy))

noncomputable def faceOrbitOfEdgeOrbit :
    G.EdgeOrbit → (hypermap (G := G)).FaceOrbit :=
  Quotient.lift
    (fun x : G.Dart => PermOrbit.of (hypermap (G := G)).face (ctE, x))
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of (hypermap (G := G)).face
        (edge_faceReachable_lift (G := G) hxy))

noncomputable def faceOrbitOfNodeOrbit :
    G.NodeOrbit → (hypermap (G := G)).FaceOrbit :=
  Quotient.lift
    (fun x : G.Dart => PermOrbit.of (hypermap (G := G)).face (ctFE, x))
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of (hypermap (G := G)).face
        (node_faceReachable_lift (G := G) hxy))

noncomputable def faceOrbitOfCode :
    FaceOrbitCode (G := G) → (hypermap (G := G)).FaceOrbit
  | Sum.inl o => faceOrbitOfFaceOrbit (G := G) o
  | Sum.inr (Sum.inl o) => faceOrbitOfEdgeOrbit (G := G) o
  | Sum.inr (Sum.inr o) => faceOrbitOfNodeOrbit (G := G) o

theorem faceOrbit_main_to_nf (x : G.Dart) :
    PermOrbit.of (hypermap (G := G)).face (ctN, x) =
      PermOrbit.of (hypermap (G := G)).face (ctNF, x) := by
  have h1 :
      PermReachable (hypermap (G := G)).face (ctN, x) (ctEN, x) := by
    simpa [hypermap_face_ctN] using
      PermReachable.forward (hypermap (G := G)).face (ctN, x)
  have h2 :
      PermReachable (hypermap (G := G)).face (ctEN, x) (ctF, x) := by
    simpa [hypermap_face_ctEN] using
      PermReachable.forward (hypermap (G := G)).face (ctEN, x)
  have h3 :
      PermReachable (hypermap (G := G)).face (ctF, x) (ctNF, x) := by
    simpa [hypermap_face_ctF] using
      PermReachable.forward (hypermap (G := G)).face (ctF, x)
  exact PermOrbit.of_eq_of (hypermap (G := G)).face
    (PermReachable.trans (hypermap (G := G)).face h1
      (PermReachable.trans (hypermap (G := G)).face h2 h3))

theorem faceOrbit_en_to_nf (x : G.Dart) :
    PermOrbit.of (hypermap (G := G)).face (ctEN, x) =
      PermOrbit.of (hypermap (G := G)).face (ctNF, x) := by
  have h1 :
      PermReachable (hypermap (G := G)).face (ctEN, x) (ctF, x) := by
    simpa [hypermap_face_ctEN] using
      PermReachable.forward (hypermap (G := G)).face (ctEN, x)
  have h2 :
      PermReachable (hypermap (G := G)).face (ctF, x) (ctNF, x) := by
    simpa [hypermap_face_ctF] using
      PermReachable.forward (hypermap (G := G)).face (ctF, x)
  exact PermOrbit.of_eq_of (hypermap (G := G)).face
    (PermReachable.trans (hypermap (G := G)).face h1 h2)

theorem faceOrbit_f_to_nf (x : G.Dart) :
    PermOrbit.of (hypermap (G := G)).face (ctF, x) =
      PermOrbit.of (hypermap (G := G)).face (ctNF, x) := by
  exact PermOrbit.of_eq_of (hypermap (G := G)).face
    (by
      simpa [hypermap_face_ctF] using
        PermReachable.forward (hypermap (G := G)).face (ctF, x))

noncomputable def faceOrbitEquiv :
    (hypermap (G := G)).FaceOrbit ≃ FaceOrbitCode (G := G) where
  toFun := faceOrbitToCode (G := G)
  invFun := faceOrbitOfCode (G := G)
  left_inv := by
    intro o
    refine Quotient.inductionOn o ?_
    intro x
    rcases x with ⟨tag, x⟩
    cases tag
    · change
        PermOrbit.of (hypermap (G := G)).face (ctNF, x) =
          PermOrbit.of (hypermap (G := G)).face (ctN, x)
      exact (faceOrbit_main_to_nf (G := G) x).symm
    · change
        PermOrbit.of (hypermap (G := G)).face (ctNF, x) =
          PermOrbit.of (hypermap (G := G)).face (ctEN, x)
      exact (faceOrbit_en_to_nf (G := G) x).symm
    · change
        PermOrbit.of (hypermap (G := G)).face (ctNF, x) =
          PermOrbit.of (hypermap (G := G)).face (ctF, x)
      exact (faceOrbit_f_to_nf (G := G) x).symm
    · rfl
    · rfl
    · rfl
  right_inv := by
    intro s
    rcases s with o | o
    · refine Quotient.inductionOn o ?_
      intro x
      rfl
    · rcases o with o | o
      · refine Quotient.inductionOn o ?_
        intro x
        rfl
      · refine Quotient.inductionOn o ?_
        intro x
        rfl

theorem faceOrbitCount_eq :
    (hypermap (G := G)).faceOrbitCount =
      G.faceOrbitCount + (G.edgeOrbitCount + G.nodeOrbitCount) := by
  unfold Hypermap.faceOrbitCount Hypermap.edgeOrbitCount
    Hypermap.nodeOrbitCount
  rw [Nat.card_congr (faceOrbitEquiv (G := G))]
  simp [FaceOrbitCode]

end Cube

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
