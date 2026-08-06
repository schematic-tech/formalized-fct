import FourColorTheorem.FourColor.Theorem.Cube.Reachability

namespace Schematic.Math.GraphTheory
namespace FourColor

universe u
namespace Hypermap

variable (G : Hypermap.{u})
namespace Cube

variable {G}

open CubeTag
theorem componentCount_eq :
    (hypermap (G := G)).componentCount = G.componentCount :=
  Nat.card_congr (componentEquiv (G := G))

theorem plain :
    (hypermap (G := G)).Plain := by
  intro x
  constructor
  · exact edgeFun_edgeFun x
  · rcases x with ⟨tag, x⟩
    cases tag <;> intro h <;> cases h

theorem cubic :
    (hypermap (G := G)).Cubic := by
  intro x
  constructor
  · rcases x with ⟨tag, x⟩
    cases tag <;>
      simp [nodeFun, Hypermap.edge_node_face, Hypermap.face_edge_node]
  · rcases x with ⟨tag, x⟩
    cases tag <;> intro h <;> cases h

theorem precubic :
    (hypermap (G := G)).Precubic :=
  (cubic (G := G)).precubic

theorem dart_card :
    Fintype.card (hypermap (G := G)).Dart = 6 * Fintype.card G.Dart := by
  change Fintype.card (CubeTag × G.Dart) = 6 * Fintype.card G.Dart
  simp [Fintype.card_prod, CubeTag.card]

theorem edgeOrbitCount_eq :
    (hypermap (G := G)).edgeOrbitCount = 3 * Fintype.card G.Dart := by
  have hplain :=
    Plain.card_dart_eq_two_mul_edgeOrbitCount
      (G := hypermap (G := G)) (plain (G := G))
  rw [dart_card (G := G)] at hplain
  omega

theorem nodeOrbitCount_eq :
    (hypermap (G := G)).nodeOrbitCount = 2 * Fintype.card G.Dart := by
  have hcubic :=
    Cubic.card_dart_eq_three_mul_nodeOrbitCount
      (G := hypermap (G := G)) (cubic (G := G))
  rw [dart_card (G := G)] at hcubic
  omega

theorem eulerLeft_eq_of_componentCount_eq
    (hcomp : (hypermap (G := G)).componentCount = G.componentCount) :
    (hypermap (G := G)).eulerLeft =
      2 * G.componentCount + 6 * Fintype.card G.Dart := by
  unfold Hypermap.eulerLeft
  rw [hcomp, dart_card (G := G)]

theorem eulerRight_eq :
    (hypermap (G := G)).eulerRight =
      5 * Fintype.card G.Dart + G.eulerRight := by
  unfold Hypermap.eulerRight
  rw [edgeOrbitCount_eq (G := G), nodeOrbitCount_eq (G := G),
    faceOrbitCount_eq (G := G)]
  omega

theorem genus_eq_of_componentCount_eq
    (hcomp : (hypermap (G := G)).componentCount = G.componentCount) :
    (hypermap (G := G)).genus = G.genus := by
  unfold Hypermap.genus
  rw [eulerLeft_eq_of_componentCount_eq (G := G) hcomp,
    eulerRight_eq (G := G)]
  unfold Hypermap.eulerLeft
  omega

theorem eulerPlanar_of_componentCount_eq
    (hcomp : (hypermap (G := G)).componentCount = G.componentCount)
    (hG : G.EulerPlanar) :
    (hypermap (G := G)).EulerPlanar := by
  unfold Hypermap.EulerPlanar at hG ⊢
  rw [genus_eq_of_componentCount_eq (G := G) hcomp]
  exact hG

theorem bridgeless_of_bridgeless
    (hG : G.Bridgeless) :
    (hypermap (G := G)).Bridgeless := by
  intro u hu
  rcases u with ⟨tag, x⟩
  cases tag
  · have hf := faceFamily_of_reachable (G := G) hu
    change faceFamily ((edgeFun (ctN, x)).1) = faceFamily (ctN) at hf
    simp [edgeFun, faceFamily] at hf
  · have hbase :
        PermReachable G.face x (G.edge x) := by
      simpa [hypermap, edgePerm, edgeFun] using
        main_faceReachable_base (G := G) hu (by rfl)
    exact hG x hbase
  · have hf := faceFamily_of_reachable (G := G) hu
    change faceFamily ((edgeFun (ctF, x)).1) = faceFamily (ctF) at hf
    simp [edgeFun, faceFamily] at hf
  · let y := G.node (G.face x)
    have hbase : PermReachable G.face x y := by
      simpa [hypermap, edgePerm, edgeFun, y] using
        main_faceReachable_base (G := G) hu (by rfl)
    have hyedge : G.edge y = x := by
      simp [y]
    exact hG y (by
      simpa [hyedge] using PermReachable.symm G.face hbase)
  · have hf := faceFamily_of_reachable (G := G) hu
    change faceFamily ((edgeFun (ctE, x)).1) = faceFamily (ctE) at hf
    simp [edgeFun, faceFamily] at hf
  · have hf := faceFamily_of_reachable (G := G) hu
    change faceFamily ((edgeFun (ctFE, x)).1) = faceFamily (ctFE) at hf
    simp [edgeFun, faceFamily] at hf

/-- Coq `cube_colorable`: a colouring of `cube G` pulls back to a colouring of
`G`. -/
theorem fourColorable_pullback
    (hcolor : (hypermap (G := G)).FourColorable) :
    G.FourColorable := by
  rcases hcolor with ⟨k, hk⟩
  refine ⟨fun x => k (ctNF, x), ?_⟩
  constructor
  · intro x hsame
    have hEdge := Hypermap.Coloring.edge_ne
      (G := hypermap (G := G)) hk (ctEN, x)
    apply hEdge
    calc
      k ((hypermap (G := G)).edge (ctEN, x)) = k (edgeFun (ctEN, x)) := rfl
      _ = k (ctNF, G.edge x) := rfl
      _ = k (ctNF, x) := hsame
      _ = k (ctF, x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctF, x)]
        rw [hypermap_face_ctF]
      _ = k (ctEN, x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctEN, x)]
        rw [hypermap_face_ctEN]
  · intro x
    calc
      k (ctNF, G.face x) = k (ctF, G.face x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctF, G.face x)]
        rw [hypermap_face_ctF]
      _ = k (ctEN, G.face x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctEN, G.face x)]
        rw [hypermap_face_ctEN]
      _ = k (ctN, G.face x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctN, G.face x)]
        rw [hypermap_face_ctN]
      _ = k (ctNF, x) := by
        rw [← Hypermap.Coloring.face_eq
          (G := hypermap (G := G)) hk (ctNF, x)]
        rw [hypermap_face_ctNF]

end Cube

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
