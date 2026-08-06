import FourColorTheorem.FourColor.Configuration.QuizEmbedding.RLinkConnectivity

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

namespace ValidQuizFor

variable {G}
theorem map_walkQ_qask1_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity}
    (hmap :
      (G.walkQ xG (Question.Qask1 qa)).map f =
        H.walkQ xH (Question.Qask1 qa)) :
    f xG = xH := by
  simpa [Hypermap.walkQ] using hmap

theorem map_walkQ_qaskL_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity} {q : Question}
    (hmap :
      (G.walkQ xG (Question.QaskL qa q)).map f =
        H.walkQ xH (Question.QaskL qa q)) :
    f xG = xH ∧
      (G.walkQ (qstepL G xG) q).map f =
        H.walkQ (qstepL H xH) q := by
  simpa [Hypermap.walkQ] using hmap

theorem map_walkQ_qaskR_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity} {q : Question}
    (hmap :
      (G.walkQ xG (Question.QaskR qa q)).map f =
        H.walkQ xH (Question.QaskR qa q)) :
    f xG = xH ∧
      (G.walkQ (qstepR G xG) q).map f =
        H.walkQ (qstepR H xH) q := by
  simpa [Hypermap.walkQ] using hmap

theorem map_walkQ_qaskLR_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity}
    {qL qR : Question}
    (hmap :
      (G.walkQ xG (Question.QaskLR qa qL qR)).map f =
        H.walkQ xH (Question.QaskLR qa qL qR)) :
    f xG = xH ∧
      (G.walkQ (qstepL G xG) qL).map f =
        H.walkQ (qstepL H xH) qL ∧
        (G.walkQ (qstepR G xG) qR).map f =
          H.walkQ (qstepR H xH) qR := by
  simp [Hypermap.walkQ, List.map_append] at hmap
  rcases hmap with ⟨hhead, htail⟩
  have hsplit := List.append_inj htail
    (by simp [Hypermap.length_walkQ])
  exact ⟨hhead, hsplit.1, hsplit.2⟩

theorem map_walkQ_qaskLL_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity} {q : Question}
    (hmap :
      (G.walkQ xG (Question.QaskLL qa q)).map f =
        H.walkQ xH (Question.QaskLL qa q)) :
    f (G.edge (G.node (qstepL G xG))) =
        H.edge (H.node (qstepL H xH)) ∧
      (G.walkQ (qstepL G (qstepL G xG)) q).map f =
        H.walkQ (qstepL H (qstepL H xH)) q := by
  simpa [Hypermap.walkQ] using hmap

theorem map_walkQ_qaskRR_decomp
    {H : Hypermap.{u}} {f : G.Dart → H.Dart}
    {xG : G.Dart} {xH : H.Dart} {qa : QArity} {q : Question}
    (hmap :
      (G.walkQ xG (Question.QaskRR qa q)).map f =
        H.walkQ xH (Question.QaskRR qa q)) :
    f (qstepR G xG) = qstepR H xH ∧
      (G.walkQ (qstepR G (qstepR G xG)) q).map f =
        H.walkQ (qstepR H (qstepR H xH)) q := by
  simpa [Hypermap.walkQ] using hmap

theorem edgeCentral_walkQ_node_qask1_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity}
    (hx : A x)
    (hmap :
      (G.walkQ (G.node x) (Question.Qask1 qa)).map h =
        H.walkQ (H.node (h x)) (Question.Qask1 qa)) :
    ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) (Question.Qask1 qa) →
      EdgeCentral G H h y := by
  have hnodeMap : h (G.node x) = H.node (h x) :=
    map_walkQ_qask1_decomp (G := G) (H := H) hmap
  intro y hy
  simp [Hypermap.walkQ] at hy
  subst y
  exact edgeCentral_node_of_map (G := G) (H := H) (A := A)
    (h := h) hclosed hface hx hnodeMap

theorem edgeCentral_node_and_map_walkQ_qaskL_tail
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity} {q : Question}
    (hx : A x)
    (hmap :
      (G.walkQ (G.node x) (Question.QaskL qa q)).map h =
        H.walkQ (H.node (h x)) (Question.QaskL qa q)) :
    EdgeCentral G H h (G.node x) ∧
      (G.walkQ (qstepL G (G.node x)) q).map h =
        H.walkQ (qstepL H (H.node (h x))) q := by
  rcases map_walkQ_qaskL_decomp (G := G) (H := H) hmap with
    ⟨hnodeMap, htail⟩
  exact
    ⟨edgeCentral_node_of_map (G := G) (H := H) (A := A)
      (h := h) hclosed hface hx hnodeMap,
      htail⟩

theorem edgeCentral_node_and_map_walkQ_qaskR_tail
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity} {q : Question}
    (hx : A x)
    (hmap :
      (G.walkQ (G.node x) (Question.QaskR qa q)).map h =
        H.walkQ (H.node (h x)) (Question.QaskR qa q)) :
    EdgeCentral G H h (G.node x) ∧
      (G.walkQ (qstepR G (G.node x)) q).map h =
        H.walkQ (qstepR H (H.node (h x))) q := by
  rcases map_walkQ_qaskR_decomp (G := G) (H := H) hmap with
    ⟨hnodeMap, htail⟩
  exact
    ⟨edgeCentral_node_of_map (G := G) (H := H) (A := A)
      (h := h) hclosed hface hx hnodeMap,
      htail⟩

theorem edgeCentral_node_and_map_walkQ_qaskLR_tails
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity} {qL qR : Question}
    (hx : A x)
    (hmap :
      (G.walkQ (G.node x) (Question.QaskLR qa qL qR)).map h =
        H.walkQ (H.node (h x)) (Question.QaskLR qa qL qR)) :
    EdgeCentral G H h (G.node x) ∧
      (G.walkQ (qstepL G (G.node x)) qL).map h =
        H.walkQ (qstepL H (H.node (h x))) qL ∧
        (G.walkQ (qstepR G (G.node x)) qR).map h =
          H.walkQ (qstepR H (H.node (h x))) qR := by
  rcases map_walkQ_qaskLR_decomp (G := G) (H := H) hmap with
    ⟨hnodeMap, htailL, htailR⟩
  exact
    ⟨edgeCentral_node_of_map (G := G) (H := H) (A := A)
      (h := h) hclosed hface hx hnodeMap,
      htailL, htailR⟩

theorem edgeCentral_qstepR_node_and_map_walkQ_qaskRR_tail
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity} {q : Question}
    (hx : A x)
    (hmap :
      (G.walkQ (G.node x) (Question.QaskRR qa q)).map h =
        H.walkQ (H.node (h x)) (Question.QaskRR qa q)) :
    EdgeCentral G H h (qstepR G (G.node x)) ∧
      (G.walkQ (qstepR G (qstepR G (G.node x))) q).map h =
        H.walkQ (qstepR H (qstepR H (H.node (h x)))) q := by
  rcases map_walkQ_qaskRR_decomp (G := G) (H := H) hmap with
    ⟨hhead, htail⟩
  exact
    ⟨edgeCentral_qstepR_node_of_map (G := G) (H := H) (A := A)
      (h := h) hclosed hface hx hhead,
      htail⟩

theorem edgeCentral_edge_node_qstepL_node_and_map_walkQ_qaskLL_tail
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z))
    {x : G.Dart} {qa : QArity} {q : Question}
    (hex : A (G.edge x))
    (hcentral : EdgeCentral G H h x)
    (hmap :
      (G.walkQ (G.node x) (Question.QaskLL qa q)).map h =
        H.walkQ (H.node (h x)) (Question.QaskLL qa q)) :
    EdgeCentral G H h (G.edge (G.node (qstepL G (G.node x)))) ∧
      (G.walkQ (qstepL G (qstepL G (G.node x))) q).map h =
        H.walkQ (qstepL H (qstepL H (H.node (h x)))) q := by
  rcases map_walkQ_qaskLL_decomp (G := G) (H := H) hmap with
    ⟨hhead, htail⟩
  exact
    ⟨edgeCentral_edge_node_qstepL_node_of_map
      (G := G) (H := H) (A := A) (h := h)
      hPlainG hPlainH hCubicG hCubicH hclosed hface
      hex hcentral hhead,
      htail⟩

theorem edgeCentral_walkQ_node_of_map
    {H : Hypermap.{u}} {A : G.Dart → Prop} {h : G.Dart → H.Dart}
    (hPlainG : G.Plain) (hPlainH : H.Plain)
    (hCubicG : G.CubicOn A) (hCubicH : H.Cubic)
    (hclosed : G.FaceClosed A)
    (hface : ∀ ⦃z : G.Dart⦄, A z → h (G.face z) = H.face (h z)) :
    ∀ {q : Question} {x : G.Dart},
      A x → A (G.edge x) → EdgeCentral G H h x →
      (∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) q → A y) →
      (G.walkQ (G.node x) q).map h =
        H.walkQ (H.node (h x)) q →
      ∀ ⦃y : G.Dart⦄, y ∈ G.walkQ (G.node x) q →
        EdgeCentral G H h y := by
  intro q
  induction q with
  | Qask0 =>
      intro x _hx _hex _hcentral _hall _hmap y hy
      simp [Hypermap.walkQ] at hy
  | Qask1 qa =>
      intro x hx _hex _hcentral _hall hmap y hy
      exact edgeCentral_walkQ_node_qask1_of_map
        (G := G) (H := H) (A := A) (h := h)
        hclosed hface hx hmap hy
  | QaskL qa q ih =>
      intro x hx hex hcentral hall hmap y hy
      rcases map_walkQ_qaskL_decomp (G := G) (H := H) hmap with
        ⟨hnodeMap, htail⟩
      have hnx : A (G.node x) := by
        exact hall (by simp [Hypermap.walkQ])
      let xL : G.Dart := G.edge (G.node (G.node x))
      have hcentralNode : EdgeCentral G H h (G.node x) :=
        edgeCentral_node_of_map (G := G) (H := H) (A := A)
          (h := h) hclosed hface hx hnodeMap
      have hcentralL : EdgeCentral G H h xL := by
        dsimp [xL]
        exact edgeCentral_edge_node_node_of_map_node
          (G := G) (H := H) (A := A) (h := h)
          hPlainG hPlainH hCubicG hCubicH hclosed hface
          hex hnx hcentral hnodeMap
      have hxL : A xL := by
        have hgeom : xL = G.face.symm (G.node x) := by
          dsimp [xL]
          rw [edge_node_eq_face_symm G (G.node x)]
        rw [hgeom]
        exact hclosed hnx (PermReachable.backward G.face (G.node x))
      have hedgeL : A (G.edge xL) := by
        have hnode2 : A (G.node (G.node x)) := by
          have hperiodX : G.node (G.node (G.node x)) = x :=
            (hCubicG x hx).1
          rw [node_node_eq_face_edge_of_period_three
            (G := G) hperiodX]
          exact hclosed hex (PermReachable.forward G.face (G.edge x))
        have hgeom : G.edge xL = G.node (G.node x) := by
          dsimp [xL]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hnode2
      have hmapL :
          h xL = H.face.symm (H.node (h x)) := by
        dsimp [xL]
        exact map_edge_node_node_eq_face_symm_node_of_map_node
          (G := G) (H := H) (A := A) (h := h)
          hclosed hface hnx hnodeMap
      have hnodeMapL :
          H.node (h xL) = qstepL H (H.node (h x)) := by
        rw [hmapL, qstepL_eq_node_face_symm]
      have htail' :
          (G.walkQ (G.node xL) q).map h =
            H.walkQ (H.node (h xL)) q := by
        simpa [xL, hnodeMapL] using htail
      have hallTail :
          ∀ ⦃z : G.Dart⦄, z ∈ G.walkQ (G.node xL) q → A z := by
        intro z hz
        exact hall (by simpa [Hypermap.walkQ, xL] using Or.inr hz)
      simp [Hypermap.walkQ] at hy
      rcases hy with rfl | hyTail
      · exact hcentralNode
      · exact ih hxL hedgeL hcentralL hallTail htail' hyTail
  | QaskR qa q ih =>
      intro x hx _hex _hcentral hall hmap y hy
      rcases map_walkQ_qaskR_decomp (G := G) (H := H) hmap with
        ⟨hnodeMap, htail⟩
      let xR : G.Dart := G.edge (G.node x)
      have hcentralNode : EdgeCentral G H h (G.node x) :=
        edgeCentral_node_of_map (G := G) (H := H) (A := A)
          (h := h) hclosed hface hx hnodeMap
      have hcentralR : EdgeCentral G H h xR := by
        dsimp [xR]
        exact (edgeCentral_edge_iff (G := G) (H := H)
          hPlainG hPlainH h (G.node x)).2 hcentralNode
      have hnx : A (G.node x) := by
        exact hall (by simp [Hypermap.walkQ])
      have hxR : A xR := by
        have hgeom : xR = G.face.symm x := by
          dsimp [xR]
          rw [edge_node_eq_face_symm G x]
        rw [hgeom]
        exact hclosed hx (PermReachable.backward G.face x)
      have hedgeR : A (G.edge xR) := by
        have hgeom : G.edge xR = G.node x := by
          dsimp [xR]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hnx
      have hmapR : h xR = H.edge (H.node (h x)) := by
        dsimp [xR]
        unfold EdgeCentral at hcentralNode
        simpa [hnodeMap] using hcentralNode
      have hnodeMapR :
          H.node (h xR) = qstepR H (H.node (h x)) := by
        rw [hmapR]
        rfl
      have htail' :
          (G.walkQ (G.node xR) q).map h =
            H.walkQ (H.node (h xR)) q := by
        simpa [xR, hnodeMapR] using htail
      have hallTail :
          ∀ ⦃z : G.Dart⦄, z ∈ G.walkQ (G.node xR) q → A z := by
        intro z hz
        exact hall (by simpa [Hypermap.walkQ, xR] using Or.inr hz)
      simp [Hypermap.walkQ] at hy
      rcases hy with rfl | hyTail
      · exact hcentralNode
      · exact ih hxR hedgeR hcentralR hallTail htail' hyTail
  | QaskLR qa qL qR ihL ihR =>
      intro x hx hex hcentral hall hmap y hy
      rcases map_walkQ_qaskLR_decomp (G := G) (H := H) hmap with
        ⟨hnodeMap, htailL, htailR⟩
      have hnx : A (G.node x) := by
        exact hall (by simp [Hypermap.walkQ])
      let xL : G.Dart := G.edge (G.node (G.node x))
      let xR : G.Dart := G.edge (G.node x)
      have hcentralNode : EdgeCentral G H h (G.node x) :=
        edgeCentral_node_of_map (G := G) (H := H) (A := A)
          (h := h) hclosed hface hx hnodeMap
      have hcentralL : EdgeCentral G H h xL := by
        dsimp [xL]
        exact edgeCentral_edge_node_node_of_map_node
          (G := G) (H := H) (A := A) (h := h)
          hPlainG hPlainH hCubicG hCubicH hclosed hface
          hex hnx hcentral hnodeMap
      have hcentralR : EdgeCentral G H h xR := by
        dsimp [xR]
        exact (edgeCentral_edge_iff (G := G) (H := H)
          hPlainG hPlainH h (G.node x)).2 hcentralNode
      have hxL : A xL := by
        have hgeom : xL = G.face.symm (G.node x) := by
          dsimp [xL]
          rw [edge_node_eq_face_symm G (G.node x)]
        rw [hgeom]
        exact hclosed hnx (PermReachable.backward G.face (G.node x))
      have hedgeL : A (G.edge xL) := by
        have hnode2 : A (G.node (G.node x)) := by
          have hperiodX : G.node (G.node (G.node x)) = x :=
            (hCubicG x hx).1
          rw [node_node_eq_face_edge_of_period_three
            (G := G) hperiodX]
          exact hclosed hex (PermReachable.forward G.face (G.edge x))
        have hgeom : G.edge xL = G.node (G.node x) := by
          dsimp [xL]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hnode2
      have hxR : A xR := by
        have hgeom : xR = G.face.symm x := by
          dsimp [xR]
          rw [edge_node_eq_face_symm G x]
        rw [hgeom]
        exact hclosed hx (PermReachable.backward G.face x)
      have hedgeR : A (G.edge xR) := by
        have hgeom : G.edge xR = G.node x := by
          dsimp [xR]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hnx
      have hmapL :
          h xL = H.face.symm (H.node (h x)) := by
        dsimp [xL]
        exact map_edge_node_node_eq_face_symm_node_of_map_node
          (G := G) (H := H) (A := A) (h := h)
          hclosed hface hnx hnodeMap
      have hnodeMapL :
          H.node (h xL) = qstepL H (H.node (h x)) := by
        rw [hmapL, qstepL_eq_node_face_symm]
      have hmapR : h xR = H.edge (H.node (h x)) := by
        dsimp [xR]
        unfold EdgeCentral at hcentralNode
        simpa [hnodeMap] using hcentralNode
      have hnodeMapR :
          H.node (h xR) = qstepR H (H.node (h x)) := by
        rw [hmapR]
        rfl
      have htailL' :
          (G.walkQ (G.node xL) qL).map h =
            H.walkQ (H.node (h xL)) qL := by
        simpa [xL, hnodeMapL] using htailL
      have htailR' :
          (G.walkQ (G.node xR) qR).map h =
            H.walkQ (H.node (h xR)) qR := by
        simpa [xR, hnodeMapR] using htailR
      have hallTailL :
          ∀ ⦃z : G.Dart⦄, z ∈ G.walkQ (G.node xL) qL → A z := by
        intro z hz
        have hz' :
            z ∈ G.walkQ (qstepL G (G.node x)) qL := by
          simpa [xL] using hz
        exact hall (by
          simp [Hypermap.walkQ, List.mem_append, hz'])
      have hallTailR :
          ∀ ⦃z : G.Dart⦄, z ∈ G.walkQ (G.node xR) qR → A z := by
        intro z hz
        have hz' :
            z ∈ G.walkQ (qstepR G (G.node x)) qR := by
          simpa [xR] using hz
        exact hall (by
          simp [Hypermap.walkQ, List.mem_append, hz'])
      simp [Hypermap.walkQ, List.mem_append] at hy
      rcases hy with rfl | hyL | hyR
      · exact hcentralNode
      · exact ihL hxL hedgeL hcentralL hallTailL htailL' hyL
      · exact ihR hxR hedgeR hcentralR hallTailR htailR' hyR
  | QaskLL qa q ih =>
      intro x _hx hex hcentral hall hmap y hy
      rcases map_walkQ_qaskLL_decomp (G := G) (H := H) hmap with
        ⟨hhead, htail⟩
      let xLL : G.Dart := G.edge (G.node (qstepL G (G.node x)))
      have hxLL : A xLL := by
        exact hall (by simp [Hypermap.walkQ, xLL])
      have hedgeLL : A (G.edge xLL) := by
        have hface1 : A (G.face (G.edge x)) :=
          hclosed hex (PermReachable.forward G.face (G.edge x))
        have hface2 : A (G.face (G.face (G.edge x))) :=
          hclosed hface1
            (PermReachable.forward G.face (G.face (G.edge x)))
        have hnode :
            A (G.node (qstepL G (G.node x))) := by
          rw [node_qstepL_node_eq_face_face_edge_of_edge_mem
            (G := G) hPlainG hCubicG hclosed hex]
          exact hface2
        have hgeom :
            G.edge xLL = G.node (qstepL G (G.node x)) := by
          dsimp [xLL]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hnode
      have hcentralLL : EdgeCentral G H h xLL := by
        dsimp [xLL]
        exact edgeCentral_edge_node_qstepL_node_of_map
          (G := G) (H := H) (A := A) (h := h)
          hPlainG hPlainH hCubicG hCubicH hclosed hface
          hex hcentral hhead
      have hnodeMapLL :
          H.node (h xLL) =
            qstepL H (qstepL H (H.node (h x))) := by
        dsimp [xLL]
        rw [hhead]
        rfl
      have htail' :
          (G.walkQ (G.node xLL) q).map h =
            H.walkQ (H.node (h xLL)) q := by
        simpa [xLL, hnodeMapLL] using htail
      have hallTail :
          ∀ ⦃z : G.Dart⦄, z ∈ G.walkQ (G.node xLL) q → A z := by
        intro z hz
        exact hall (by simpa [Hypermap.walkQ, xLL] using Or.inr hz)
      simp [Hypermap.walkQ] at hy
      rcases hy with rfl | hyTail
      · exact hcentralLL
      · exact ih hxLL hedgeLL hcentralLL hallTail htail' hyTail
  | QaskRR qa q ih =>
      intro x hx _hex _hcentral hall hmap y hy
      rcases map_walkQ_qaskRR_decomp (G := G) (H := H) hmap with
        ⟨hhead, htail⟩
      let zR : G.Dart := qstepR G (G.node x)
      let xRR : G.Dart := G.edge zR
      have hzR : A zR := by
        exact hall (by simp [Hypermap.walkQ, zR])
      have hcentralZR : EdgeCentral G H h zR :=
        edgeCentral_qstepR_node_of_map (G := G) (H := H) (A := A)
          (h := h) hclosed hface hx hhead
      have hcentralRR : EdgeCentral G H h xRR := by
        dsimp [xRR]
        exact (edgeCentral_edge_iff (G := G) (H := H)
          hPlainG hPlainH h zR).2 hcentralZR
      have hxRR : A xRR := by
        have hx₁ : A (G.face.symm x) :=
          hclosed hx (PermReachable.backward G.face x)
        have hx₂ : A (G.face.symm (G.face.symm x)) :=
          hclosed hx₁
            (PermReachable.backward G.face (G.face.symm x))
        have hgeom :
            xRR = G.face.symm (G.face.symm x) := by
          dsimp [xRR, zR]
          rw [qstepR]
          rw [edge_node_eq_face_symm G (G.edge (G.node x))]
          rw [edge_node_eq_face_symm G x]
        rw [hgeom]
        exact hx₂
      have hedgeRR : A (G.edge xRR) := by
        have hgeom : G.edge xRR = zR := by
          dsimp [xRR]
          rw [Hypermap.Plain.edge_edge (G := G) hPlainG]
        rw [hgeom]
        exact hzR
      have hmapRR : h xRR = H.edge (qstepR H (H.node (h x))) := by
        have hcentralZR' := hcentralZR
        unfold EdgeCentral at hcentralZR'
        have hheadZ : h zR = qstepR H (H.node (h x)) := by
          simpa [zR] using hhead
        dsimp [xRR]
        rw [hcentralZR', hheadZ]
      have hnodeMapRR :
          H.node (h xRR) =
            qstepR H (qstepR H (H.node (h x))) := by
        rw [hmapRR]
        rfl
      have htail' :
          (G.walkQ (G.node xRR) q).map h =
            H.walkQ (H.node (h xRR)) q := by
        simpa [xRR, zR, hnodeMapRR] using htail
      have hallTail :
          ∀ ⦃w : G.Dart⦄, w ∈ G.walkQ (G.node xRR) q → A w := by
        intro w hw
        exact hall (by simpa [Hypermap.walkQ, xRR, zR] using Or.inr hw)
      simp [Hypermap.walkQ] at hy
      rcases hy with rfl | hyTail
      · exact hcentralZR
      · exact ih hxRR hedgeRR hcentralRR hallTail htail' hyTail


end ValidQuizFor

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
