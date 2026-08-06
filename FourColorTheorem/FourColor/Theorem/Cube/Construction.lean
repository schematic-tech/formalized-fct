
import Schematic.Math.GraphTheory.Embedding.Coloring
import Schematic.Math.GraphTheory.Embedding.Counts
import Schematic.Math.GraphTheory.Embedding.Geometry
import FourColorTheorem.Tactic.Decide

/-!
Coq `cube.v` bridge layer.

The Coq theorem `four_color_hypermap` first replaces an arbitrary planar
bridgeless hypermap by `cube G`, a plain cubic hypermap whose colourings pull
back to colourings of `G`.  This file ports the finite permutation
construction and the easy structural/colour-transfer facts.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

universe u

/-- The six copies of each dart in Coq `cube.v`. -/
inductive CubeTag
  | ctN
  | ctEN
  | ctF
  | ctNF
  | ctE
  | ctFE
  deriving DecidableEq

namespace CubeTag

instance : Fintype CubeTag where
  elems := {ctN, ctEN, ctF, ctNF, ctE, ctFE}
  complete := by
    intro tag
    cases tag <;> simp

instance : BEq CubeTag where
  beq a b := decide (a = b)

instance : LawfulBEq CubeTag where
  eq_of_beq := by
    intro a b h
    exact of_decide_eq_true h
  rfl := by
    intro a
    exact decide_eq_true rfl

theorem card :
    Fintype.card CubeTag = 6 := by
  fct_decide

end CubeTag

namespace Hypermap

variable (G : Hypermap.{u})

abbrev CubeDart :=
  CubeTag × G.Dart

namespace Cube

variable {G}

open CubeTag

/-- Coq `cube_edge`. -/
def edgeFun : G.CubeDart → G.CubeDart
  | (ctEN, x) => (ctNF, G.edge x)
  | (ctF, x) => (ctE, G.node (G.face x))
  | (ctNF, x) => (ctEN, G.node (G.face x))
  | (ctE, x) => (ctF, G.edge x)
  | (ctFE, x) => (ctN, x)
  | (ctN, x) => (ctFE, x)

theorem edgeFun_edgeFun (x : G.CubeDart) :
    edgeFun (G := G) (edgeFun x) = x := by
  rcases x with ⟨tag, x⟩
  cases tag <;> simp [edgeFun, Hypermap.edge_node_face]

/-- Coq `cube_edge` as a permutation. -/
def edgePerm : Equiv.Perm G.CubeDart where
  toFun := edgeFun
  invFun := edgeFun
  left_inv := edgeFun_edgeFun
  right_inv := edgeFun_edgeFun

@[simp]
theorem edgePerm_apply (x : G.CubeDart) :
    edgePerm (G := G) x = edgeFun x :=
  rfl

/-- Coq `cube_node`. -/
def nodeFun : G.CubeDart → G.CubeDart
  | (ctN, x) => (ctEN, G.node x)
  | (ctEN, x) => (ctFE, x)
  | (ctF, x) => (ctNF, G.edge x)
  | (ctNF, x) => (ctE, G.node (G.face x))
  | (ctE, x) => (ctF, x)
  | (ctFE, x) => (ctN, G.face (G.edge x))

/-- Inverse of Coq `cube_node`. -/
def nodeInvFun : G.CubeDart → G.CubeDart
  | (ctN, x) => (ctFE, G.node x)
  | (ctEN, x) => (ctN, G.node.symm x)
  | (ctF, x) => (ctE, x)
  | (ctNF, x) => (ctF, G.edge.symm x)
  | (ctE, x) => (ctNF, G.edge x)
  | (ctFE, x) => (ctEN, x)

theorem nodeInvFun_nodeFun (x : G.CubeDart) :
    nodeInvFun (G := G) (nodeFun x) = x := by
  rcases x with ⟨tag, x⟩
  cases tag <;>
    simp [nodeFun, nodeInvFun, Hypermap.edge_node_face]

theorem nodeFun_nodeInvFun (x : G.CubeDart) :
    nodeFun (G := G) (nodeInvFun x) = x := by
  rcases x with ⟨tag, x⟩
  cases tag <;>
    simp [nodeFun, nodeInvFun, Hypermap.face_edge_node]

/-- Coq `cube_node` as a permutation. -/
def nodePerm : Equiv.Perm G.CubeDart where
  toFun := nodeFun
  invFun := nodeInvFun
  left_inv := nodeInvFun_nodeFun
  right_inv := nodeFun_nodeInvFun

@[simp]
theorem nodePerm_apply (x : G.CubeDart) :
    nodePerm (G := G) x = nodeFun x :=
  rfl

@[simp]
theorem nodePerm_symm_apply (x : G.CubeDart) :
    (nodePerm (G := G)).symm x = nodeInvFun x :=
  rfl

/-- The cubification hypermap.  Its face permutation is definitionally the one
forced by `edge` and `node`; the lemmas below identify the Coq face steps used
in colour transfer. -/
noncomputable def hypermap : Hypermap.{u} where
  Dart := G.CubeDart
  edge := edgePerm
  node := nodePerm
  face := (edgePerm (G := G)).symm.trans (nodePerm (G := G)).symm
  node_face_edge := by
    intro x
    change nodeFun (nodeInvFun (edgeFun (edgeFun x))) = x
    rw [edgeFun_edgeFun, nodeFun_nodeInvFun]

@[simp]
theorem hypermap_edge (x : G.CubeDart) :
    (hypermap (G := G)).edge x = edgeFun x :=
  rfl

@[simp]
theorem hypermap_node (x : G.CubeDart) :
    (hypermap (G := G)).node x = nodeFun x :=
  rfl

theorem hypermap_face_ctEN (x : G.Dart) :
    (hypermap (G := G)).face (ctEN, x) = (ctF, x) := by
  change nodeInvFun (edgeFun (ctEN, x)) = (ctF, x)
  simp [edgeFun, nodeInvFun]

theorem hypermap_face_ctF (x : G.Dart) :
    (hypermap (G := G)).face (ctF, x) = (ctNF, x) := by
  change nodeInvFun (edgeFun (ctF, x)) = (ctNF, x)
  simp [edgeFun, nodeInvFun, Hypermap.edge_node_face]

theorem hypermap_face_ctNF (x : G.Dart) :
    (hypermap (G := G)).face (ctNF, x) = (ctN, G.face x) := by
  change nodeInvFun (edgeFun (ctNF, x)) = (ctN, G.face x)
  simp [edgeFun, nodeInvFun]

theorem hypermap_face_ctN (x : G.Dart) :
    (hypermap (G := G)).face (ctN, x) = (ctEN, x) := by
  change nodeInvFun (edgeFun (ctN, x)) = (ctEN, x)
  simp [edgeFun, nodeInvFun]

theorem hypermap_face_ctE (x : G.Dart) :
    (hypermap (G := G)).face (ctE, x) = (ctE, G.edge x) := by
  change nodeInvFun (edgeFun (ctE, x)) = (ctE, G.edge x)
  simp [edgeFun, nodeInvFun]

theorem hypermap_face_ctFE (x : G.Dart) :
    (hypermap (G := G)).face (ctFE, x) = (ctFE, G.node x) := by
  change nodeInvFun (edgeFun (ctFE, x)) = (ctFE, G.node x)
  simp [edgeFun, nodeInvFun]

/-- The three kinds of face orbits in `cube G`: original faces, original edge
orbits, and original node orbits. -/
def faceFamily : CubeTag → Nat
  | ctE => 1
  | ctFE => 2
  | _ => 0

theorem faceFamily_face (x : G.CubeDart) :
    faceFamily (((hypermap (G := G)).face x).1) = faceFamily x.1 := by
  rcases x with ⟨tag, x⟩
  cases tag <;>
    simp [faceFamily, hypermap_face_ctN, hypermap_face_ctEN,
      hypermap_face_ctF, hypermap_face_ctNF, hypermap_face_ctE,
      hypermap_face_ctFE]

theorem faceFamily_face_symm (x : G.CubeDart) :
    faceFamily (((hypermap (G := G)).face.symm x).1) = faceFamily x.1 := by
  have h := faceFamily_face (G := G) ((hypermap (G := G)).face.symm x)
  simpa using h.symm

theorem faceFamily_of_link
    {x y : G.CubeDart}
    (hxy : PermLink (hypermap (G := G)).face x y) :
    faceFamily y.1 = faceFamily x.1 := by
  cases hxy
  ·
      exact faceFamily_face (G := G) x
  ·
      exact faceFamily_face_symm (G := G) x

theorem faceFamily_of_reachable
    {x y : G.CubeDart}
    (hxy : PermReachable (hypermap (G := G)).face x y) :
    faceFamily y.1 = faceFamily x.1 := by
  induction hxy with
  | refl =>
      rfl
  | tail hxb hbc ih =>
      exact (faceFamily_of_link (G := G) hbc).trans ih

end Cube

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
