import FourColorTheorem.FourColor.Theorem.Cube.FaceOrbits

namespace Schematic.Math.GraphTheory
namespace FourColor

universe u
namespace Hypermap

variable (G : Hypermap.{u})
namespace Cube

variable {G}

open CubeTag
theorem reachable_n_to_nf (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctN, x) (ctNF, x) :=
  (hypermap (G := G)).facePermReachable_reachable <|
    (PermReachable.trans (hypermap (G := G)).face
      (by
        simpa [hypermap_face_ctN] using
          PermReachable.forward (hypermap (G := G)).face (ctN, x))
      (PermReachable.trans (hypermap (G := G)).face
        (by
          simpa [hypermap_face_ctEN] using
            PermReachable.forward (hypermap (G := G)).face (ctEN, x))
        (by
          simpa [hypermap_face_ctF] using
            PermReachable.forward (hypermap (G := G)).face (ctF, x))))

theorem reachable_en_to_nf (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctEN, x) (ctNF, x) :=
  (hypermap (G := G)).facePermReachable_reachable <|
    (PermReachable.trans (hypermap (G := G)).face
      (by
        simpa [hypermap_face_ctEN] using
          PermReachable.forward (hypermap (G := G)).face (ctEN, x))
      (by
        simpa [hypermap_face_ctF] using
          PermReachable.forward (hypermap (G := G)).face (ctF, x)))

theorem reachable_f_to_nf (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctF, x) (ctNF, x) :=
  (hypermap (G := G)).facePermReachable_reachable <|
    (by
      simpa [hypermap_face_ctF] using
        PermReachable.forward (hypermap (G := G)).face (ctF, x))

theorem reachable_nf_to_edge (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctNF, x) (ctNF, G.edge x) := by
  have h1 :
      (hypermap (G := G)).Reachable (ctNF, x) (ctEN, x) :=
    (hypermap (G := G)).reachable_symm (reachable_en_to_nf (G := G) x)
  have h2 :
      (hypermap (G := G)).Reachable (ctEN, x) (ctNF, G.edge x) := by
    simpa [edgeFun] using (hypermap (G := G)).reachable_edge (ctEN, x)
  exact h1.trans h2

theorem reachable_nf_to_node (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctNF, x) (ctNF, G.node x) := by
  have h1 :
      (hypermap (G := G)).Reachable (ctNF, x) (ctEN, x) :=
    (hypermap (G := G)).reachable_symm (reachable_en_to_nf (G := G) x)
  have h2 :
      (hypermap (G := G)).Reachable (ctEN, x) (ctFE, x) := by
    simpa [nodeFun] using (hypermap (G := G)).reachable_node (ctEN, x)
  have h3 :
      (hypermap (G := G)).Reachable (ctFE, x) (ctFE, G.node x) :=
    (hypermap (G := G)).facePermReachable_reachable
      (node_face_forward_lift (G := G) x)
  have h4 :
      (hypermap (G := G)).Reachable (ctFE, G.node x) (ctN, G.node x) := by
    simpa [edgeFun] using
      (hypermap (G := G)).reachable_edge (ctFE, G.node x)
  exact h1.trans (h2.trans (h3.trans (h4.trans
    (reachable_n_to_nf (G := G) (G.node x)))))

theorem reachable_nf_to_face (x : G.Dart) :
    (hypermap (G := G)).Reachable (ctNF, x) (ctNF, G.face x) :=
  (hypermap (G := G)).facePermReachable_reachable
    (main_face_forward_lift (G := G) x)

theorem reachable_nf_of_base_link
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (hypermap (G := G)).Reachable (ctNF, x) (ctNF, y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact reachable_nf_to_edge (G := G) x
  · subst y
    exact reachable_nf_to_node (G := G) x
  · subst y
    exact reachable_nf_to_face (G := G) x

theorem reachable_nf_of_base_reachable
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (hypermap (G := G)).Reachable (ctNF, x) (ctNF, y) := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact (hypermap (G := G)).reachable_refl (ctNF, x)
  · intro b c hxb hbc ih
    exact ih.trans (reachable_nf_of_base_link (G := G) hbc)

theorem tag_reachable_to_nf (x : G.CubeDart) :
    (hypermap (G := G)).Reachable x (ctNF, x.2) := by
  rcases x with ⟨tag, x⟩
  cases tag
  · exact reachable_n_to_nf (G := G) x
  · exact reachable_en_to_nf (G := G) x
  · exact reachable_f_to_nf (G := G) x
  · exact (hypermap (G := G)).reachable_refl (ctNF, x)
  · have h1 :
        (hypermap (G := G)).Reachable (ctE, x) (ctF, G.edge x) := by
      simpa [edgeFun] using (hypermap (G := G)).reachable_edge (ctE, x)
    have h2 :
        (hypermap (G := G)).Reachable (ctF, G.edge x) (ctNF, G.edge x) :=
      reachable_f_to_nf (G := G) (G.edge x)
    have h3 :
        (hypermap (G := G)).Reachable (ctNF, G.edge x) (ctNF, x) :=
      (hypermap (G := G)).reachable_symm (reachable_nf_to_edge (G := G) x)
    exact h1.trans (h2.trans h3)
  · have h1 :
        (hypermap (G := G)).Reachable (ctFE, x) (ctN, x) := by
      simpa [edgeFun] using (hypermap (G := G)).reachable_edge (ctFE, x)
    exact h1.trans (reachable_n_to_nf (G := G) x)

theorem base_reachable_of_cube_link
    {x y : G.CubeDart}
    (hxy : (hypermap (G := G)).Link x y) :
    G.Reachable x.2 y.2 := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    rcases x with ⟨tag, x⟩
    cases tag
    · exact G.reachable_refl x
    · exact G.reachable_edge x
    · exact (G.reachable_face x).trans (G.reachable_node (G.face x))
    · exact (G.reachable_face x).trans (G.reachable_node (G.face x))
    · exact G.reachable_edge x
    · exact G.reachable_refl x
  · subst y
    rcases x with ⟨tag, x⟩
    cases tag
    · exact G.reachable_node x
    · exact G.reachable_refl x
    · exact G.reachable_edge x
    · exact (G.reachable_face x).trans (G.reachable_node (G.face x))
    · exact G.reachable_refl x
    · exact (G.reachable_edge x).trans (G.reachable_face (G.edge x))
  · subst y
    rcases x with ⟨tag, x⟩
    cases tag
    · simpa [hypermap_face_ctN] using G.reachable_refl x
    · simpa [hypermap_face_ctEN] using G.reachable_refl x
    · simpa [hypermap_face_ctF] using G.reachable_refl x
    · simpa [hypermap_face_ctNF] using G.reachable_face x
    · simpa [hypermap_face_ctE] using G.reachable_edge x
    · simpa [hypermap_face_ctFE] using G.reachable_node x

theorem base_reachable_of_cube_reachable
    {x y : G.CubeDart}
    (hxy : (hypermap (G := G)).Reachable x y) :
    G.Reachable x.2 y.2 := by
  refine Relation.ReflTransGen.recOn hxy ?_ ?_
  · exact G.reachable_refl x.2
  · intro b c hxb hbc ih
    exact ih.trans (base_reachable_of_cube_link (G := G) hbc)

noncomputable def componentToBase :
    (hypermap (G := G)).Component → G.Component :=
  Quotient.lift
    (fun x : G.CubeDart => G.componentOf x.2)
    (by
      intro x y hxy
      exact G.componentOf_eq_componentOf
        (base_reachable_of_cube_reachable (G := G) hxy))

noncomputable def componentOfBase :
    G.Component → (hypermap (G := G)).Component :=
  Quotient.lift
    (fun x : G.Dart => (hypermap (G := G)).componentOf (ctNF, x))
    (by
      intro x y hxy
      exact (hypermap (G := G)).componentOf_eq_componentOf
        (reachable_nf_of_base_reachable (G := G) hxy))

noncomputable def componentEquiv :
    (hypermap (G := G)).Component ≃ G.Component where
  toFun := componentToBase (G := G)
  invFun := componentOfBase (G := G)
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    change
      (hypermap (G := G)).componentOf (ctNF, x.2) =
        (hypermap (G := G)).componentOf x
    exact (hypermap (G := G)).componentOf_eq_componentOf
      ((hypermap (G := G)).reachable_symm (tag_reachable_to_nf (G := G) x))
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    rfl

end Cube

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
