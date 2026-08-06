import FourColorTheorem.FourColor.Configuration.QuizEmbedding.ListSplitting
import Schematic.Math.GraphTheory.Embedding.Geometry.LocalPeriod

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}

theorem edgeCentral_qstepR_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hex : A (G.edge x))
    (hcentral : EdgeCentral G H h x)
    (hmap : h (qstepR G x) = qstepR H (h x)) :
    EdgeCentral G H h (qstepR G x) := by
  have hedgeStep : A (G.edge (qstepR G x)) := by
    have hpre :
        G.face.symm (G.edge x) = G.edge (qstepR G x) := by
      apply G.face.injective
      simp [qstepR]
    have hreach :
        PermReachable G.face (G.edge x) (G.edge (qstepR G x)) := by
      simpa [hpre] using PermReachable.backward G.face (G.edge x)
    exact hclosed hex hreach
  unfold EdgeCentral at hcentral ⊢
  apply H.face.injective
  calc
    H.face (h (G.edge (qstepR G x))) =
        h (G.face (G.edge (qstepR G x))) := by
          rw [hface hedgeStep]
    _ = h (G.edge x) := by
          simp [qstepR]
    _ = H.edge (h x) := hcentral
    _ = H.face (H.edge (H.node (H.edge (h x)))) := by
          simp
    _ = H.face (H.edge (h (qstepR G x))) := by
          simpa [qstepR] using
            congrArg (fun y : H.Dart => H.face (H.edge y)) hmap.symm

theorem edgeCentral_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hx : A x)
    (hmap : h (G.node x) = H.node (h x)) :
    EdgeCentral G H h (G.node x) := by
  have hbackA : A (G.face.symm x) :=
    hclosed hx (PermReachable.backward G.face x)
  have hfaceSymm : h (G.face.symm x) = H.face.symm (h x) := by
    apply H.face.injective
    rw [← hface hbackA]
    simp
  unfold EdgeCentral
  calc
    h (G.edge (G.node x)) = h (G.face.symm x) := by
      rw [edge_node_eq_face_symm G x]
    _ = H.face.symm (h x) := hfaceSymm
    _ = H.edge (H.node (h x)) := by
      symm
      rw [edge_node_eq_face_symm H (h x)]
    _ = H.edge (h (G.node x)) := by rw [hmap]

theorem map_edge_node_node_eq_face_symm_node_of_map_node
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hnx : A (G.node x))
    (hmapNode : h (G.node x) = H.node (h x)) :
    h (G.edge (G.node (G.node x))) =
      H.face.symm (H.node (h x)) := by
  have hbackA : A (G.face.symm (G.node x)) :=
    hclosed hnx (PermReachable.backward G.face (G.node x))
  have hfaceSymm :
      h (G.face.symm (G.node x)) = H.face.symm (h (G.node x)) := by
    apply H.face.injective
    rw [← hface hbackA]
    simp
  calc
    h (G.edge (G.node (G.node x))) =
        h (G.face.symm (G.node x)) := by
          rw [edge_node_eq_face_symm G (G.node x)]
    _ = H.face.symm (h (G.node x)) := hfaceSymm
    _ = H.face.symm (H.node (h x)) := by rw [hmapNode]

theorem edgeCentral_edge_node_node_of_map_node
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hex : A (G.edge x))
    (hnx : A (G.node x))
    (hcentral : EdgeCentral G H h x)
    (hmapNode : h (G.node x) = H.node (h x)) :
    EdgeCentral G H h (G.edge (G.node (G.node x))) := by
  have hperiodX :
      G.node (G.node (G.node x)) = x := by
    apply G.node.injective
    exact (hCubicG (G.node x) hnx).1
  have hnodeNodeX :
      G.node (G.node x) = G.face (G.edge x) := by
    apply G.node.injective
    rw [hperiodX, G.node_face_edge]
  have hnode2 : h (G.node (G.node x)) = H.node (H.node (h x)) := by
    calc
      h (G.node (G.node x)) = h (G.face (G.edge x)) := by
        rw [hnodeNodeX]
      _ = H.face (h (G.edge x)) := hface hex
      _ = H.face (H.edge (h x)) := by
        unfold EdgeCentral at hcentral
        rw [hcentral]
      _ = H.node (H.node (h x)) :=
        (Hypermap.Cubic.node_node_eq_face_edge (G := H) hCubicH (h x)).symm
  have hbackA : A (G.face.symm (G.node x)) :=
    hclosed hnx (PermReachable.backward G.face (G.node x))
  have hfaceSymm :
      h (G.face.symm (G.node x)) = H.face.symm (h (G.node x)) := by
    apply H.face.injective
    rw [← hface hbackA]
    simp
  have hy :
      h (G.edge (G.node (G.node x))) =
        H.face.symm (H.node (h x)) := by
    calc
      h (G.edge (G.node (G.node x))) =
          h (G.face.symm (G.node x)) := by
            rw [edge_node_eq_face_symm G (G.node x)]
      _ = H.face.symm (h (G.node x)) := hfaceSymm
      _ = H.face.symm (H.node (h x)) := by rw [hmapNode]
  unfold EdgeCentral
  calc
    h (G.edge (G.edge (G.node (G.node x)))) =
        h (G.node (G.node x)) := by
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
    _ = H.node (H.node (h x)) := hnode2
    _ = H.edge (H.face.symm (H.node (h x))) := by
          rw [← Hypermap.Plain.node_face_eq_edge (G := H) hPlainH
            (H.face.symm (H.node (h x)))]
          simp
    _ = H.edge (h (G.edge (G.node (G.node x)))) := by rw [hy]

theorem edgeCentral_qstepR_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hx : A x)
    (hmap : h (qstepR G (G.node x)) = qstepR H (H.node (h x))) :
    EdgeCentral G H h (qstepR G (G.node x)) := by
  have hx₁ : A (G.face.symm x) :=
    hclosed hx (PermReachable.backward G.face x)
  have hx₂ : A (G.face.symm (G.face.symm x)) :=
    hclosed hx₁ (PermReachable.backward G.face (G.face.symm x))
  have hfaceSymm₁ : h (G.face.symm x) = H.face.symm (h x) := by
    apply H.face.injective
    rw [← hface hx₁]
    simp
  have hfaceSymm₂ :
      h (G.face.symm (G.face.symm x)) =
        H.face.symm (H.face.symm (h x)) := by
    apply H.face.injective
    rw [← hface hx₂]
    simp [hfaceSymm₁]
  have hedgeGeom :
      G.edge (qstepR G (G.node x)) =
        G.face.symm (G.face.symm x) := by
    rw [qstepR]
    rw [edge_node_eq_face_symm G (G.edge (G.node x))]
    rw [edge_node_eq_face_symm G x]
  have htargetGeom :
      H.edge (qstepR H (H.node (h x))) =
        H.face.symm (H.face.symm (h x)) := by
    rw [qstepR]
    rw [edge_node_eq_face_symm H (H.edge (H.node (h x)))]
    rw [edge_node_eq_face_symm H (h x)]
  unfold EdgeCentral
  calc
    h (G.edge (qstepR G (G.node x))) =
        h (G.face.symm (G.face.symm x)) := by
          rw [hedgeGeom]
    _ = H.face.symm (H.face.symm (h x)) := hfaceSymm₂
    _ = H.edge (qstepR H (H.node (h x))) := htargetGeom.symm
    _ = H.edge (h (qstepR G (G.node x))) := by rw [hmap]

theorem node_node_eq_face_edge_of_period_three
    {x : G.Dart}
    (hperiod : G.node (G.node (G.node x)) = x) :
    G.node (G.node x) = G.face (G.edge x) :=
  Hypermap.node_node_eq_face_edge_of_period_three hperiod

theorem node_qstepL_node_eq_face_face_edge
    (hPlain : G.Plain) (x : G.Dart)
    (hperiodX : G.node (G.node (G.node x)) = x)
    (hperiodZ :
      G.node (G.node (G.node (G.edge (G.node (G.node x))))) =
        G.edge (G.node (G.node x))) :
    G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)) := by
  rw [qstepL]
  rw [node_node_eq_face_edge_of_period_three (G := G) hperiodZ]
  rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [node_node_eq_face_edge_of_period_three (G := G) hperiodX]

theorem node_qstepL_node_eq_face_face_edge_of_node_mem
    {A : G.Dart → Prop}
    (hPlain : G.Plain) (hCubic : G.CubicOn A)
    (hclosed : G.FaceClosed A) {x : G.Dart}
    (hnodeA : A (G.node x)) :
    G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)) := by
  have hperiodX : G.node (G.node (G.node x)) = x := by
    apply G.node.injective
    exact (hCubic (G.node x) hnodeA).1
  have hzA : A (G.edge (G.node (G.node x))) := by
    rw [edge_node_eq_face_symm G (G.node x)]
    exact hclosed hnodeA
      (PermReachable.backward G.face (G.node x))
  exact node_qstepL_node_eq_face_face_edge
    (G := G) hPlain x hperiodX (hCubic _ hzA).1

theorem node_qstepL_node_eq_face_face_edge_of_edge_mem
    {A : G.Dart → Prop}
    (hPlain : G.Plain) (hCubic : G.CubicOn A)
    (hclosed : G.FaceClosed A) {x : G.Dart}
    (hedgeA : A (G.edge x)) :
    G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)) := by
  let a := G.face (G.edge x)
  let b := G.face a
  have haA : A a :=
    hclosed hedgeA (PermReachable.forward G.face (G.edge x))
  have hbA : A b :=
    hclosed haA (PermReachable.forward G.face a)
  have hperiodX : G.node (G.node (G.node x)) = x := by
    have haPeriod := (hCubic a haA).1
    have hnodeA : G.node a = x := by simp [a]
    rw [← hnodeA]
    exact congrArg G.node haPeriod
  have hnodeNodeX : G.node (G.node x) = a :=
    node_node_eq_face_edge_of_period_three (G := G) hperiodX
  have hnodeB : G.node b = G.edge (G.node (G.node x)) := by
    rw [hnodeNodeX]
    exact Hypermap.Plain.node_face_eq_edge (G := G) hPlain a
  have hperiodZ :
      G.node (G.node (G.node (G.edge (G.node (G.node x))))) =
        G.edge (G.node (G.node x)) := by
    rw [← hnodeB]
    exact congrArg G.node (hCubic b hbA).1
  exact node_qstepL_node_eq_face_face_edge
    (G := G) hPlain x hperiodX hperiodZ

theorem edge_qstepR_node_eq_face_symm_face_symm
    (x : G.Dart) :
    G.edge (qstepR G (G.node x)) =
      G.face.symm (G.face.symm x) := by
  rw [qstepR]
  rw [edge_node_eq_face_symm G (G.edge (G.node x))]
  rw [edge_node_eq_face_symm G x]

theorem faceBand_concat_node_self
    {a : List G.Dart} (x : G.Dart) :
    G.FaceBand (a ++ [G.node x]) (G.node x) :=
  (Hypermap.FaceBand.concat (G := G)).2
    (Or.inr (PermReachable.refl G.face (G.node x)))

theorem faceBand_concat_node_edge_node_of_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand a x) :
    G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) := by
  have hx' :
      G.FaceBand a (G.edge (G.node x)) := by
    rw [edge_node_eq_face_symm G x]
    exact Hypermap.FaceBand.of_faceReachable (G := G) hx
      (PermReachable.backward G.face x)
  exact (Hypermap.FaceBand.concat (G := G)).2 (Or.inl hx')

theorem faceBand_edge_node_of_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand a x) :
    G.FaceBand a (G.edge (G.node x)) := by
  rw [edge_node_eq_face_symm G x]
  exact Hypermap.FaceBand.of_faceReachable (G := G) hx
    (PermReachable.backward G.face x)

theorem faceBand_concat_node_edge_node_node
    {a : List G.Dart} (x : G.Dart) :
    G.FaceBand (a ++ [G.node x]) (G.edge (G.node (G.node x))) := by
  have hreach :
      PermReachable G.face (G.node x)
        (G.edge (G.node (G.node x))) := by
    rw [edge_node_eq_face_symm G (G.node x)]
    exact PermReachable.backward G.face (G.node x)
  exact (Hypermap.FaceBand.concat (G := G)).2 (Or.inr hreach)

theorem faceBand_concat_node_edge_edge_node_node_of_edge_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hnodeNodeX : G.node (G.node x) = G.face (G.edge x))
    (hex : G.FaceBand a (G.edge x)) :
    G.FaceBand (a ++ [G.node x])
      (G.edge (G.edge (G.node (G.node x)))) := by
  have hnode2 :
      G.FaceBand a (G.node (G.node x)) := by
    rw [hnodeNodeX]
    exact Hypermap.FaceBand.of_faceReachable (G := G) hex
      (PermReachable.forward G.face (G.edge x))
  have hgeom :
      G.edge (G.edge (G.node (G.node x))) =
        G.node (G.node x) := by
    rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [hgeom]
  exact (Hypermap.FaceBand.concat (G := G)).2 (Or.inl hnode2)

theorem faceBand_concat_node_edge_node_of_source_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand a x) :
    G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) :=
  faceBand_concat_node_edge_node_of_faceBand (G := G) hx

theorem faceBand_concat_node_edge_edge_node
    {a : List G.Dart} (hPlain : G.Plain) (x : G.Dart) :
    G.FaceBand (a ++ [G.node x]) (G.edge (G.edge (G.node x))) := by
  have hgeom :
      G.edge (G.edge (G.node x)) = G.node x := by
    rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [hgeom]
  exact faceBand_concat_node_self (G := G) (a := a) x

theorem faceBand_concat_edge_node_qstepL_node_self
    {a : List G.Dart} (x : G.Dart) :
    G.FaceBand
      (a ++ [G.edge (G.node (qstepL G (G.node x)))])
      (G.edge (G.node (qstepL G (G.node x)))) :=
  (Hypermap.FaceBand.concat (G := G)).2
    (Or.inr (PermReachable.refl G.face
      (G.edge (G.node (qstepL G (G.node x))))))

theorem faceBand_edge_edge_node_qstepL_node_of_edge_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hqstep :
      G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)))
    (hex : G.FaceBand a (G.edge x)) :
    G.FaceBand a
      (G.edge (G.edge (G.node (qstepL G (G.node x))))) := by
  have hface1 : G.FaceBand a (G.face (G.edge x)) :=
    Hypermap.FaceBand.of_faceReachable (G := G) hex
      (PermReachable.forward G.face (G.edge x))
  have hface2 : G.FaceBand a (G.face (G.face (G.edge x))) :=
    Hypermap.FaceBand.of_faceReachable (G := G) hface1
      (PermReachable.forward G.face (G.face (G.edge x)))
  have hnode :
      G.FaceBand a (G.node (qstepL G (G.node x))) := by
    rw [hqstep]
    exact hface2
  have hgeom :
      G.edge (G.edge (G.node (qstepL G (G.node x)))) =
        G.node (qstepL G (G.node x)) := by
    rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [hgeom]
  exact hnode

theorem faceBand_concat_edge_node_qstepL_node_edge_of_edge_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hqstep :
      G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)))
    (hex : G.FaceBand a (G.edge x)) :
    G.FaceBand
      (a ++ [G.edge (G.node (qstepL G (G.node x)))])
      (G.edge (G.edge (G.node (qstepL G (G.node x))))) := by
  exact (Hypermap.FaceBand.concat (G := G)).2
    (Or.inl
      (faceBand_edge_edge_node_qstepL_node_of_edge_faceBand
        (G := G) hPlain hqstep hex))

theorem faceBand_concat_qstepR_node_self
    {a : List G.Dart} (x : G.Dart) :
    G.FaceBand (a ++ [qstepR G (G.node x)])
      (qstepR G (G.node x)) :=
  (Hypermap.FaceBand.concat (G := G)).2
    (Or.inr (PermReachable.refl G.face (qstepR G (G.node x))))

theorem faceBand_edge_qstepR_node_of_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand a x) :
    G.FaceBand a (G.edge (qstepR G (G.node x))) := by
  have hx₁ : G.FaceBand a (G.face.symm x) :=
    Hypermap.FaceBand.of_faceReachable (G := G) hx
      (PermReachable.backward G.face x)
  have hx₂ : G.FaceBand a (G.face.symm (G.face.symm x)) :=
    Hypermap.FaceBand.of_faceReachable (G := G) hx₁
      (PermReachable.backward G.face (G.face.symm x))
  have hgeom :
      G.edge (qstepR G (G.node x)) =
        G.face.symm (G.face.symm x) :=
    edge_qstepR_node_eq_face_symm_face_symm (G := G) x
  rw [hgeom]
  exact hx₂

theorem faceBand_concat_qstepR_node_edge_of_faceBand
    {a : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand a x) :
    G.FaceBand (a ++ [qstepR G (G.node x)])
      (G.edge (qstepR G (G.node x))) := by
  exact (Hypermap.FaceBand.concat (G := G)).2
    (Or.inl (faceBand_edge_qstepR_node_of_faceBand (G := G) hx))

theorem faceBand_concat_qstepR_node_edge_edge_of_plain
    {a : List G.Dart} (hPlain : G.Plain) (x : G.Dart) :
    G.FaceBand (a ++ [qstepR G (G.node x)])
      (G.edge (G.edge (qstepR G (G.node x)))) := by
  have hgeom :
      G.edge (G.edge (qstepR G (G.node x))) =
        qstepR G (G.node x) := by
    rw [Hypermap.Plain.edge_edge (G := G) hPlain]
  rw [hgeom]
  exact faceBand_concat_qstepR_node_self (G := G) (a := a) x

theorem faceBand_qaskL_next_roots
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hnodeNodeX : G.node (G.node x) = G.face (G.edge x))
    (hex : G.FaceBand a (G.edge x)) :
    G.FaceBand (a ++ [G.node x])
        (G.edge (G.node (G.node x))) ∧
      G.FaceBand (a ++ [G.node x])
        (G.edge (G.edge (G.node (G.node x)))) :=
  ⟨faceBand_concat_node_edge_node_node (G := G) (a := a) x,
    faceBand_concat_node_edge_edge_node_node_of_edge_faceBand
      (G := G) hPlain hnodeNodeX hex⟩

theorem faceBand_qaskR_next_roots
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hx : G.FaceBand a x) :
    G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) ∧
      G.FaceBand (a ++ [G.node x])
        (G.edge (G.edge (G.node x))) :=
  ⟨faceBand_concat_node_edge_node_of_faceBand (G := G) hx,
    faceBand_concat_node_edge_edge_node (G := G) hPlain x⟩

theorem faceBand_qaskLL_next_roots
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hqstep :
      G.node (qstepL G (G.node x)) = G.face (G.face (G.edge x)))
    (hex : G.FaceBand a (G.edge x)) :
    G.FaceBand
        (a ++ [G.edge (G.node (qstepL G (G.node x)))])
        (G.edge (G.node (qstepL G (G.node x)))) ∧
      G.FaceBand
        (a ++ [G.edge (G.node (qstepL G (G.node x)))])
        (G.edge (G.edge (G.node (qstepL G (G.node x))))) :=
  ⟨faceBand_concat_edge_node_qstepL_node_self (G := G) (a := a) x,
    faceBand_concat_edge_node_qstepL_node_edge_of_edge_faceBand
      (G := G) hPlain hqstep hex⟩

theorem faceBand_qaskRR_next_roots
    {a : List G.Dart} {x : G.Dart}
    (hPlain : G.Plain)
    (hx : G.FaceBand a x) :
    G.FaceBand (a ++ [qstepR G (G.node x)])
        (G.edge (qstepR G (G.node x))) ∧
      G.FaceBand (a ++ [qstepR G (G.node x)])
        (G.edge (G.edge (qstepR G (G.node x)))) :=
  ⟨faceBand_concat_qstepR_node_edge_of_faceBand (G := G) hx,
    faceBand_concat_qstepR_node_edge_edge_of_plain (G := G) hPlain x⟩


end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
