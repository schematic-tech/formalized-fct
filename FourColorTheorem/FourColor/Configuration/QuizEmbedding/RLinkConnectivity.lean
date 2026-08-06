import FourColorTheorem.FourColor.Configuration.QuizEmbedding.CentralSteps

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}
theorem rlinkConnected_faceBand_concat_edgeCentral_of_bridges
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hconn :
      G.RLinkConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hto : ∀ ⦃y : G.Dart⦄,
      PermReachable G.face x y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfrom : ∀ ⦃y : G.Dart⦄,
      PermReachable G.face x y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y) :
    G.RLinkConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ [x]) y ∧ A y ∧ EdgeCentral G H h y) := by
  exact RLinkConnected.faceBand_concat_of_bridges (G := G)
    (a := a) (x := x)
    (C := fun y : G.Dart => A y ∧ EdgeCentral G H h y)
    hconn
    (by
      intro y hy hC
      rcases hto hy hC.1 hC.2 with ⟨b, hbBand, hbA, hbCentral, hyb⟩
      exact ⟨b, hbBand, ⟨hbA, hbCentral⟩, hyb⟩)
    (by
      intro y hy hC
      rcases hfrom hy hC.1 hC.2 with ⟨b, hbBand, hbA, hbCentral, hby⟩
      exact ⟨b, hbBand, ⟨hbA, hbCentral⟩, hby⟩)

theorem rlinkConnected_faceBand_append_edgeCentral_of_bridges
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a s : List G.Dart}
    (hconn :
      G.RLinkConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hto : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfrom : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y) :
    G.RLinkConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ s) y ∧ A y ∧ EdgeCentral G H h y) := by
  exact RLinkConnected.faceBand_append_of_bridges (G := G)
    (a := a) (s := s)
    (C := fun y : G.Dart => A y ∧ EdgeCentral G H h y)
    hconn
    (by
      intro y hy hC
      rcases hto hy hC.1 hC.2 with ⟨b, hbBand, hbA, hbCentral, hyb⟩
      exact ⟨b, hbBand, ⟨hbA, hbCentral⟩, hyb⟩)
    (by
      intro y hy hC
      rcases hfrom hy hC.1 hC.2 with ⟨b, hbBand, hbA, hbCentral, hby⟩
      exact ⟨b, hbBand, ⟨hbA, hbCentral⟩, hby⟩)

theorem rlinkConnected_faceBand_two_append_edgeCentral_of_bridges
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a s t : List G.Dart}
    (hconn :
      G.RLinkConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (htoS : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfromS : ∀ ⦃y : G.Dart⦄,
      G.FaceBand s y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand a b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y)
    (htoT : ∀ ⦃y : G.Dart⦄,
      G.FaceBand t y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand (a ++ s) b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) y b)
    (hfromT : ∀ ⦃y : G.Dart⦄,
      G.FaceBand t y → A y → EdgeCentral G H h y →
        ∃ b : G.Dart, G.FaceBand (a ++ s) b ∧ A b ∧
          EdgeCentral G H h b ∧
            Relation.ReflTransGen (fun u v : G.Dart => G.RLink u v) b y) :
    G.RLinkConnected
      (fun y : G.Dart =>
        G.FaceBand ((a ++ s) ++ t) y ∧ A y ∧ EdgeCentral G H h y) := by
  have hconnS :
      G.RLinkConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ s) y ∧ A y ∧ EdgeCentral G H h y) :=
    rlinkConnected_faceBand_append_edgeCentral_of_bridges (G := G)
      (H := H) (h := h) (A := A) (a := a) (s := s)
      hconn htoS hfromS
  exact rlinkConnected_faceBand_append_edgeCentral_of_bridges (G := G)
    (H := H) (h := h) (A := A) (a := a ++ s) (s := t)
    hconnS htoT hfromT

theorem rlinkPathConnected_faceBand_concat_node_edgeCentral_of_bridge
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hbridgeBand : G.FaceBand a (G.edge (G.node x)))
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x))
    (hbridgeA : A (G.edge (G.node x)))
    (hbridgeCentral : EdgeCentral G H h (G.edge (G.node x))) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ [G.node x]) y ∧ A y ∧ EdgeCentral G H h y) :=
  RLinkPathConnected.faceBand_concat_node_of_bridge (G := G) hPlainG
    (a := a) (x := x)
    (C := fun y : G.Dart => A y ∧ EdgeCentral G H h y)
    hconn hbridgeBand
    ⟨hnodeA, hnodeCentral⟩
    ⟨hbridgeA, hbridgeCentral⟩

theorem rlinkPathConnected_faceBand_concat_edgeCentral_of_node_eq_bridge
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {u v : G.Dart}
    (hPlainG : G.Plain)
    (huv : G.node u = v)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hbridgeBand : G.FaceBand a (G.edge v))
    (hvA : A v)
    (hvCentral : EdgeCentral G H h v)
    (hbridgeA : A (G.edge v))
    (hbridgeCentral : EdgeCentral G H h (G.edge v)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ [v]) y ∧ A y ∧ EdgeCentral G H h y) :=
  RLinkPathConnected.faceBand_concat_of_node_eq_bridge (G := G)
    hPlainG (a := a) (u := u) (v := v)
    (C := fun y : G.Dart => A y ∧ EdgeCentral G H h y)
    huv hconn hbridgeBand
    ⟨hvA, hvCentral⟩
    ⟨hbridgeA, hbridgeCentral⟩

theorem rlinkPathConnected_faceBand_concat_node_edgeCentral_of_source
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hxA : A x)
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ [G.node x]) y ∧ A y ∧ EdgeCentral G H h y) := by
  have hbridgeBand : G.FaceBand a (G.edge (G.node x)) :=
    faceBand_edge_node_of_faceBand (G := G) hxBand
  have hbridgeA : A (G.edge (G.node x)) := by
    rw [edge_node_eq_face_symm G x]
    exact hclosed hxA (PermReachable.backward G.face x)
  have hbridgeCentral : EdgeCentral G H h (G.edge (G.node x)) :=
    (edgeCentral_edge_iff (G := G) (H := H)
      hPlainG hPlainH h (G.node x)).2 hnodeCentral
  exact rlinkPathConnected_faceBand_concat_node_edgeCentral_of_bridge
    (G := G) (H := H) (h := h) (A := A)
    hPlainG hconn hbridgeBand hnodeA hnodeCentral
    hbridgeA hbridgeCentral

theorem rlinkPathConnected_walkQ_node_qask0_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ G.walkQ (G.node x) Question.Qask0) y ∧
          A y ∧ EdgeCentral G H h y) := by
  simpa [Hypermap.walkQ] using hconn

theorem rlinkPathConnected_walkQ_node_qask1_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    {qa : QArity}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hxA : A x)
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x)) :
    G.RLinkPathConnected
      (fun y : G.Dart =>
        G.FaceBand (a ++ G.walkQ (G.node x) (Question.Qask1 qa)) y ∧
          A y ∧ EdgeCentral G H h y) := by
  simpa [Hypermap.walkQ] using
    rlinkPathConnected_faceBand_concat_node_edgeCentral_of_source
      (G := G) (H := H) (h := h) (A := A)
      (a := a) (x := x)
      hPlainG hPlainH hclosed hconn hxBand hxA hnodeA hnodeCentral

theorem rlinkPathConnected_qaskL_head_state_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain) (hCubicG : G.CubicOn A)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hexBand : G.FaceBand a (G.edge x))
    (hxA : A x)
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x)) :
    G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [G.node x]) y ∧
            A y ∧ EdgeCentral G H h y) ∧
      G.FaceBand (a ++ [G.node x]) (G.edge (G.node (G.node x))) ∧
        G.FaceBand (a ++ [G.node x])
          (G.edge (G.edge (G.node (G.node x)))) := by
  have hperiodX : G.node (G.node (G.node x)) = x := by
    apply G.node.injective
    exact (hCubicG (G.node x) hnodeA).1
  have hnodeNodeX : G.node (G.node x) = G.face (G.edge x) :=
    node_node_eq_face_edge_of_period_three (G := G) hperiodX
  exact ⟨
    rlinkPathConnected_faceBand_concat_node_edgeCentral_of_source
      (G := G) (H := H) (h := h) (A := A)
      (a := a) (x := x)
      hPlainG hPlainH hclosed hconn hxBand hxA hnodeA hnodeCentral,
    faceBand_qaskL_next_roots (G := G) (a := a) (x := x)
      hPlainG hnodeNodeX hexBand⟩

theorem rlinkPathConnected_qaskR_head_state_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hxA : A x)
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x)) :
    G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [G.node x]) y ∧
            A y ∧ EdgeCentral G H h y) ∧
      G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) ∧
        G.FaceBand (a ++ [G.node x])
          (G.edge (G.edge (G.node x))) := by
  exact ⟨
    rlinkPathConnected_faceBand_concat_node_edgeCentral_of_source
      (G := G) (H := H) (h := h) (A := A)
      (a := a) (x := x)
      hPlainG hPlainH hclosed hconn hxBand hxA hnodeA hnodeCentral,
    faceBand_qaskR_next_roots (G := G) (a := a) (x := x)
      hPlainG hxBand⟩

theorem rlinkPathConnected_qaskLR_head_state_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain) (hCubicG : G.CubicOn A)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hexBand : G.FaceBand a (G.edge x))
    (hxA : A x)
    (hnodeA : A (G.node x))
    (hnodeCentral : EdgeCentral G H h (G.node x)) :
    G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [G.node x]) y ∧
            A y ∧ EdgeCentral G H h y) ∧
      G.FaceBand (a ++ [G.node x]) (G.edge (G.node (G.node x))) ∧
        G.FaceBand (a ++ [G.node x])
          (G.edge (G.edge (G.node (G.node x)))) ∧
          G.FaceBand (a ++ [G.node x]) (G.edge (G.node x)) ∧
            G.FaceBand (a ++ [G.node x])
              (G.edge (G.edge (G.node x))) := by
  have hL := rlinkPathConnected_qaskL_head_state_edgeCentral
    (G := G) (H := H) (h := h) (A := A)
    (a := a) (x := x)
    hPlainG hPlainH hCubicG hclosed hconn hxBand hexBand
    hxA hnodeA hnodeCentral
  have hR := faceBand_qaskR_next_roots (G := G) (a := a) (x := x)
    hPlainG hxBand
  exact ⟨hL.1, hL.2.1, hL.2.2, hR.1, hR.2⟩

theorem rlinkPathConnected_qaskLL_head_state_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain) (hCubicG : G.CubicOn A)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hexBand : G.FaceBand a (G.edge x))
    (hexA : A (G.edge x))
    (hheadA : A (G.edge (G.node (qstepL G (G.node x)))))
    (hheadCentral :
      EdgeCentral G H h (G.edge (G.node (qstepL G (G.node x))))) :
    G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand
              (a ++ [G.edge (G.node (qstepL G (G.node x)))]) y ∧
            A y ∧ EdgeCentral G H h y) ∧
      G.FaceBand
          (a ++ [G.edge (G.node (qstepL G (G.node x)))])
          (G.edge (G.node (qstepL G (G.node x)))) ∧
        G.FaceBand
          (a ++ [G.edge (G.node (qstepL G (G.node x)))])
          (G.edge (G.edge (G.node (qstepL G (G.node x))))) := by
  let head : G.Dart := G.edge (G.node (qstepL G (G.node x)))
  let u : G.Dart := G.node (G.node head)
  have huv : G.node u = head := by
    dsimp [u]
    exact (hCubicG head (by simpa [head] using hheadA)).1
  have hqstep :
      G.node (qstepL G (G.node x)) =
        G.face (G.face (G.edge x)) :=
    node_qstepL_node_eq_face_face_edge_of_edge_mem
      (G := G) hPlainG hCubicG hclosed hexA
  have hbridgeBand : G.FaceBand a (G.edge head) := by
    dsimp [head]
    exact faceBand_edge_edge_node_qstepL_node_of_edge_faceBand
      (G := G) hPlainG hqstep hexBand
  have hbridgeA : A (G.edge head) := by
    have hface1 : A (G.face (G.edge x)) :=
      hclosed hexA (PermReachable.forward G.face (G.edge x))
    have hface2 : A (G.face (G.face (G.edge x))) :=
      hclosed hface1
        (PermReachable.forward G.face (G.face (G.edge x)))
    have hnode :
        A (G.node (qstepL G (G.node x))) := by
      rw [hqstep]
      exact hface2
    have hgeom :
        G.edge head = G.node (qstepL G (G.node x)) := by
      dsimp [head]
      rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
    rw [hgeom]
    exact hnode
  have hbridgeCentral : EdgeCentral G H h (G.edge head) := by
    dsimp [head]
    exact (edgeCentral_edge_iff (G := G) (H := H)
      hPlainG hPlainH h
      (G.edge (G.node (qstepL G (G.node x))))).2 hheadCentral
  have hconnHead :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [head]) y ∧ A y ∧ EdgeCentral G H h y) :=
    rlinkPathConnected_faceBand_concat_edgeCentral_of_node_eq_bridge
      (G := G) (H := H) (h := h) (A := A)
      (a := a) (u := u) (v := head)
      hPlainG huv hconn hbridgeBand
      (by simpa [head] using hheadA)
      (by simpa [head] using hheadCentral)
      hbridgeA hbridgeCentral
  have hroots := faceBand_qaskLL_next_roots
    (G := G) (a := a) (x := x) hPlainG hqstep hexBand
  exact ⟨by simpa [head] using hconnHead, hroots.1, hroots.2⟩

theorem rlinkPathConnected_qaskRR_head_state_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop} {a : List G.Dart} {x : G.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain) (hCubicG : G.CubicOn A)
    (hclosed : G.FaceClosed A)
    (hconn :
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y))
    (hxBand : G.FaceBand a x)
    (hxA : A x)
    (hheadA : A (qstepR G (G.node x)))
    (hheadCentral : EdgeCentral G H h (qstepR G (G.node x))) :
    G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [qstepR G (G.node x)]) y ∧
            A y ∧ EdgeCentral G H h y) ∧
      G.FaceBand (a ++ [qstepR G (G.node x)])
          (G.edge (qstepR G (G.node x))) ∧
        G.FaceBand (a ++ [qstepR G (G.node x)])
          (G.edge (G.edge (qstepR G (G.node x)))) := by
  let head : G.Dart := qstepR G (G.node x)
  let u : G.Dart := G.node (G.node head)
  have huv : G.node u = head := by
    dsimp [u]
    exact (hCubicG head (by simpa [head] using hheadA)).1
  have hbridgeBand : G.FaceBand a (G.edge head) := by
    dsimp [head]
    exact faceBand_edge_qstepR_node_of_faceBand (G := G) hxBand
  have hbridgeA : A (G.edge head) := by
    have hx₁ : A (G.face.symm x) :=
      hclosed hxA (PermReachable.backward G.face x)
    have hx₂ : A (G.face.symm (G.face.symm x)) :=
      hclosed hx₁
        (PermReachable.backward G.face (G.face.symm x))
    have hgeom :
        G.edge head = G.face.symm (G.face.symm x) := by
      dsimp [head]
      exact edge_qstepR_node_eq_face_symm_face_symm (G := G) x
    rw [hgeom]
    exact hx₂
  have hbridgeCentral : EdgeCentral G H h (G.edge head) := by
    dsimp [head]
    exact (edgeCentral_edge_iff (G := G) (H := H)
      hPlainG hPlainH h (qstepR G (G.node x))).2 hheadCentral
  have hconnHead :
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ [head]) y ∧ A y ∧ EdgeCentral G H h y) :=
    rlinkPathConnected_faceBand_concat_edgeCentral_of_node_eq_bridge
      (G := G) (H := H) (h := h) (A := A)
      (a := a) (u := u) (v := head)
      hPlainG huv hconn hbridgeBand
      (by simpa [head] using hheadA)
      (by simpa [head] using hheadCentral)
      hbridgeA hbridgeCentral
  have hroots := faceBand_qaskRR_next_roots
    (G := G) (a := a) (x := x) hPlainG hxBand
  exact ⟨by simpa [head] using hconnHead, hroots.1, hroots.2⟩

theorem rlinkPathConnected_walkQ_node_edgeCentral
    {H : Hypermap.{u}} {h : G.Dart → H.Dart}
    {A : G.Dart → Prop}
    (hPlainG : G.Plain) (hPlainH : H.Plain) (hCubicG : G.CubicOn A)
    (hclosed : G.FaceClosed A) :
    ∀ {q : Question} {x : G.Dart} {a : List G.Dart},
      G.FaceBand a x →
      G.FaceBand a (G.edge x) →
      (∀ y : G.Dart, y ∈ a → A y) →
      G.RLinkPathConnected
        (fun y : G.Dart => G.FaceBand a y ∧ A y ∧ EdgeCentral G H h y) →
      (∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) q →
        A y ∧ EdgeCentral G H h y) →
      G.RLinkPathConnected
        (fun y : G.Dart =>
          G.FaceBand (a ++ G.walkQ (G.node x) q) y ∧
            A y ∧ EdgeCentral G H h y) := by
  intro q
  induction q with
  | Qask0 =>
      intro x a _hxBand _hexBand _hsources hconn _hall
      exact rlinkPathConnected_walkQ_node_qask0_edgeCentral
        (G := G) (H := H) (h := h) (A := A) (a := a) (x := x)
        hconn
  | Qask1 qa =>
      intro x a hxBand _hexBand hsources hconn hall
      have hxA : A x :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hxBand
      have hhead : A (G.node x) ∧ EdgeCentral G H h (G.node x) :=
        hall (by simp [Hypermap.walkQ])
      exact rlinkPathConnected_walkQ_node_qask1_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x) (qa := qa)
        hPlainG hPlainH hclosed hconn hxBand hxA hhead.1 hhead.2
  | QaskL qa q ih =>
      intro x a hxBand hexBand hsources hconn hall
      let a1 : List G.Dart := a ++ [G.node x]
      let xL : G.Dart := G.edge (G.node (G.node x))
      have hxA : A x :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hxBand
      have hhead : A (G.node x) ∧ EdgeCentral G H h (G.node x) :=
        hall (by simp [Hypermap.walkQ])
      have hstate := rlinkPathConnected_qaskL_head_state_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x)
        hPlainG hPlainH hCubicG hclosed hconn
        hxBand hexBand hxA hhead.1 hhead.2
      have hsources1 : ∀ y : G.Dart, y ∈ a1 → A y := by
        intro y hy
        dsimp [a1] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources y hy
        · simp at hy
          subst y
          exact hhead.1
      have hallTail :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node xL) q →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by simpa [Hypermap.walkQ, xL] using Or.inr hy)
      have hrec := ih hstate.2.1 hstate.2.2 hsources1 hstate.1 hallTail
      simpa [Hypermap.walkQ, a1, xL, List.append_assoc] using hrec
  | QaskR qa q ih =>
      intro x a hxBand hexBand hsources hconn hall
      let a1 : List G.Dart := a ++ [G.node x]
      let xR : G.Dart := G.edge (G.node x)
      have hxA : A x :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hxBand
      have hhead : A (G.node x) ∧ EdgeCentral G H h (G.node x) :=
        hall (by simp [Hypermap.walkQ])
      have hstate := rlinkPathConnected_qaskR_head_state_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x)
        hPlainG hPlainH hclosed hconn
        hxBand hxA hhead.1 hhead.2
      have hsources1 : ∀ y : G.Dart, y ∈ a1 → A y := by
        intro y hy
        dsimp [a1] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources y hy
        · simp at hy
          subst y
          exact hhead.1
      have hallTail :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node xR) q →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by simpa [Hypermap.walkQ, xR] using Or.inr hy)
      have hrec := ih hstate.2.1 hstate.2.2 hsources1 hstate.1 hallTail
      simpa [Hypermap.walkQ, a1, xR, List.append_assoc] using hrec
  | QaskLR qa ql qr ihL ihR =>
      intro x a hxBand hexBand hsources hconn hall
      let a1 : List G.Dart := a ++ [G.node x]
      let xL : G.Dart := G.edge (G.node (G.node x))
      let xR : G.Dart := G.edge (G.node x)
      have hxA : A x :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hxBand
      have hhead : A (G.node x) ∧ EdgeCentral G H h (G.node x) :=
        hall (by simp [Hypermap.walkQ])
      have hstate := rlinkPathConnected_qaskLR_head_state_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x)
        hPlainG hPlainH hCubicG hclosed hconn
        hxBand hexBand hxA hhead.1 hhead.2
      have hsources1 : ∀ y : G.Dart, y ∈ a1 → A y := by
        intro y hy
        dsimp [a1] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources y hy
        · simp at hy
          subst y
          exact hhead.1
      have hallLeft :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node xL) ql →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by
          simpa [Hypermap.walkQ, qstepL, xL] using
            (Or.inr (Or.inl hy) :
              y = G.node x ∨
                y ∈ G.walkQ (G.node xL) ql ∨
                  y ∈ G.walkQ (qstepR G (G.node x)) qr))
      have hconnLeft := ihL hstate.2.1 hstate.2.2.1
        hsources1 hstate.1 hallLeft
      let aL : List G.Dart := a1 ++ G.walkQ (G.node xL) ql
      have hxRBandL : G.FaceBand aL xR :=
        FaceBand.subset (G := G)
          (fun z hz => by
            dsimp [aL]
            exact List.mem_append_left _ hz)
          hstate.2.2.2.1
      have hexRBandL : G.FaceBand aL (G.edge xR) :=
        FaceBand.subset (G := G)
          (fun z hz => by
            dsimp [aL]
            exact List.mem_append_left _ hz)
          hstate.2.2.2.2
      have hsourcesL : ∀ y : G.Dart, y ∈ aL → A y := by
        intro y hy
        dsimp [aL] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources1 y hy
        · exact (hallLeft hy).1
      have hallRight :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node xR) qr →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by
          simpa [Hypermap.walkQ, qstepR, xR] using
            (Or.inr (Or.inr hy) :
              y = G.node x ∨
                y ∈ G.walkQ (qstepL G (G.node x)) ql ∨
                  y ∈ G.walkQ (G.node xR) qr))
      have hconnRight := ihR hxRBandL hexRBandL
        hsourcesL hconnLeft hallRight
      simpa [Hypermap.walkQ, a1, aL, xL, xR, List.append_assoc] using
        hconnRight
  | QaskLL qa q ih =>
      intro x a _hxBand hexBand hsources hconn hall
      let head : G.Dart := G.edge (G.node (qstepL G (G.node x)))
      have hexA : A (G.edge x) :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hexBand
      have hhead : A head ∧ EdgeCentral G H h head := by
        dsimp [head]
        exact hall (by simp [Hypermap.walkQ])
      have hstate := rlinkPathConnected_qaskLL_head_state_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x)
        hPlainG hPlainH hCubicG hclosed hconn
        hexBand hexA hhead.1 hhead.2
      let a1 : List G.Dart := a ++ [head]
      have hsources1 : ∀ y : G.Dart, y ∈ a1 → A y := by
        intro y hy
        dsimp [a1] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources y hy
        · simp at hy
          subst y
          exact hhead.1
      have hallTail :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node head) q →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by simpa [Hypermap.walkQ, head] using Or.inr hy)
      have hrec := ih hstate.2.1 hstate.2.2
        hsources1 (by simpa [a1, head] using hstate.1) hallTail
      simpa [Hypermap.walkQ, a1, head, List.append_assoc] using hrec
  | QaskRR qa q ih =>
      intro x a hxBand _hexBand hsources hconn hall
      let head : G.Dart := qstepR G (G.node x)
      let xRR : G.Dart := G.edge head
      have hxA : A x :=
        FaceClosed.of_faceBand_sources (G := G) hclosed hsources hxBand
      have hhead : A head ∧ EdgeCentral G H h head := by
        dsimp [head]
        exact hall (by simp [Hypermap.walkQ])
      have hstate := rlinkPathConnected_qaskRR_head_state_edgeCentral
        (G := G) (H := H) (h := h) (A := A)
        (a := a) (x := x)
        hPlainG hPlainH hCubicG hclosed hconn
        hxBand hxA hhead.1 hhead.2
      let a1 : List G.Dart := a ++ [head]
      have hsources1 : ∀ y : G.Dart, y ∈ a1 → A y := by
        intro y hy
        dsimp [a1] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsources y hy
        · simp at hy
          subst y
          exact hhead.1
      have hallTail :
          ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node xRR) q →
            A y ∧ EdgeCentral G H h y := by
        intro y hy
        exact hall (by simpa [Hypermap.walkQ, head, xRR] using Or.inr hy)
      have hrec := ih hstate.2.1 hstate.2.2
        hsources1 (by simpa [a1, head] using hstate.1) hallTail
      simpa [Hypermap.walkQ, a1, head, xRR, List.append_assoc] using hrec

theorem edgeCentral_edge_node_qstepL_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart}
    (hex : A (G.edge x))
    (hcentral : EdgeCentral G H h x)
    (hmapHead :
      h (G.edge (G.node (qstepL G (G.node x)))) =
        H.edge (H.node (qstepL H (H.node (h x))))) :
    EdgeCentral G H h (G.edge (G.node (qstepL G (G.node x)))) := by
  let y := G.edge (G.node (qstepL G (G.node x)))
  have hfaceEdge : A (G.face (G.edge x)) :=
    hclosed hex (PermReachable.forward G.face (G.edge x))
  have hfaceFace :
      h (G.face (G.face (G.edge x))) =
        H.face (H.face (h (G.edge x))) := by
    rw [hface hfaceEdge]
    rw [hface hex]
  have hnodeSource :
      h (G.node (qstepL G (G.node x))) =
        H.node (qstepL H (H.node (h x))) := by
    calc
      h (G.node (qstepL G (G.node x))) =
          h (G.face (G.face (G.edge x))) := by
            rw [node_qstepL_node_eq_face_face_edge_of_edge_mem
              (G := G) hPlainG hCubicG hclosed hex]
      _ = H.face (H.face (h (G.edge x))) := hfaceFace
      _ = H.face (H.face (H.edge (h x))) := by
            unfold EdgeCentral at hcentral
            rw [hcentral]
      _ = H.node (qstepL H (H.node (h x))) := by
            rw [node_qstepL_node_eq_face_face_edge
              (G := H) hPlainH (h x)
              (hCubicH (h x)).1
              (hCubicH (H.edge (H.node (H.node (h x))))).1]
  unfold EdgeCentral
  calc
    h (G.edge y) = h (G.node (qstepL G (G.node x))) := by
      rw [show G.edge y = G.node (qstepL G (G.node x)) by
        simp [y, Hypermap.Plain.edge_edge (G := G) hPlainG]]
    _ = H.node (qstepL H (H.node (h x))) := hnodeSource
    _ = H.edge (H.edge (H.node (qstepL H (H.node (h x))))) := by
          rw [Hypermap.Plain.edge_edge (G := H) hPlainH]
    _ = H.edge (h y) := by
          simp [y, hmapHead]

end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
