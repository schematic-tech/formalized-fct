import FourColorTheorem.FourColor.Reducibility.ProgramMap.TailSeparation

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace PointedHypermap

/-- Inject an old dart from `cpmap cp₂` through the prefix `cp₁`, matching
Coq's `injcp cp₁ cp₂ : cpmap cp₂ → cpmap (catrev cp₁ cp₂)`. -/
noncomputable def injcp :
    (cp₁ cp₂ : CProg) →
      (cpmap cp₂).map.Dart →
        (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart
  | [], _cp₂, x => x
  | s :: cp₁, cp₂, x =>
      injcp cp₁ (s :: cp₂) (oldStep s (cpmap cp₂) x)

@[simp]
theorem injcp_nil (cp₂ : CProg) (x : (cpmap cp₂).map.Dart) :
    injcp [] cp₂ x = x :=
  rfl

@[simp]
theorem injcp_cons (s : CpStep) (cp₁ cp₂ : CProg)
    (x : (cpmap cp₂).map.Dart) :
    injcp (s :: cp₁) cp₂ x =
      injcp cp₁ (s :: cp₂) (oldStep s (cpmap cp₂) x) :=
  rfl

private theorem injcp_relation_of_relation
    (R : (P : PointedHypermap) → P.map.Dart → P.map.Dart → Prop)
    (hstep : ∀ (s : CpStep) (P : PointedHypermap) {x y},
      R P x y → R (step s P) (oldStep s P x) (oldStep s P y)) :
    ∀ (cp₁ cp₂ : CProg) {x y : (cpmap cp₂).map.Dart},
      R (cpmap cp₂) x y →
        R (cpmap (CProg.appendRev cp₁ cp₂))
          (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y)
  | [], _cp₂, _x, _y, hxy => hxy
  | s :: cp₁, cp₂, _x, _y, hxy =>
      injcp_relation_of_relation R hstep cp₁ (s :: cp₂)
        (hstep s (cpmap cp₂) hxy)

private theorem injcp_relation_iff_of_cubic
    (R : (P : PointedHypermap) → P.map.Dart → P.map.Dart → Prop)
    (hstep : ∀ (s : CpStep) (P : PointedHypermap),
      CProg.cubic [s] = true → ∀ x y,
        R (step s P) (oldStep s P x) (oldStep s P y) ↔ R P x y) :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ {x y : (cpmap cp₂).map.Dart},
        R (cpmap (CProg.appendRev cp₁ cp₂))
            (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
          R (cpmap cp₂) x y
  | [], _cp₂, _hcp, _x, _y => Iff.rfl
  | s :: cp₁, cp₂, hcp, x, y => by
      have htail := CProg.cubic_cons_tail hcp
      have hs := CProg.cubic_singleton_of_cons hcp
      exact Iff.trans
        (injcp_relation_iff_of_cubic R hstep cp₁ (s :: cp₂) htail)
        (hstep s (cpmap cp₂) hs x y)

theorem injcp_faceReachable_of_faceReachable :
    ∀ (cp₁ cp₂ : CProg) {x y : (cpmap cp₂).map.Dart},
      PermReachable (cpmap cp₂).map.face x y →
        PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.face
          (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) :=
  injcp_relation_of_relation
    (fun P => PermReachable P.map.face)
    oldStep_faceReachable_of_faceReachable

theorem injcp_faceReachable_iff_of_cubic :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ {x y : (cpmap cp₂).map.Dart},
        PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.face
          (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
        PermReachable (cpmap cp₂).map.face x y :=
  injcp_relation_iff_of_cubic
    (fun P => PermReachable P.map.face)
    (fun _s P hs x y =>
      oldStep_faceReachable_iff_of_cubicStep hs P (x := x) (y := y))

theorem injcp_ringAdj_of_ringAdj :
    ∀ (cp₁ cp₂ : CProg) {x y : (cpmap cp₂).map.Dart},
      (cpmap cp₂).map.RingAdj x y →
        (cpmap (CProg.appendRev cp₁ cp₂)).map.RingAdj
          (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) :=
  injcp_relation_of_relation
    (fun P => P.map.RingAdj)
    oldStep_ringAdj_of_ringAdj

theorem injcp_ringAdj_iff_of_cubic :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ {x y : (cpmap cp₂).map.Dart},
        (cpmap (CProg.appendRev cp₁ cp₂)).map.RingAdj
          (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
        (cpmap cp₂).map.RingAdj x y :=
  injcp_relation_iff_of_cubic
    (fun P => P.map.RingAdj)
    (fun _s P hs x y =>
      oldStep_ringAdj_iff_of_cubicStep hs P (x := x) (y := y))

private theorem injcp_unary_of_cubic
    (op : (P : PointedHypermap) → P.map.Dart → P.map.Dart)
    (hstep : ∀ (s : CpStep) (P : PointedHypermap),
      CProg.cubic [s] = true → ∀ x,
        oldStep s P (op P x) = op (step s P) (oldStep s P x)) :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ (x : (cpmap cp₂).map.Dart),
        injcp cp₁ cp₂ (op (cpmap cp₂) x) =
          op (cpmap (CProg.appendRev cp₁ cp₂)) (injcp cp₁ cp₂ x)
  | [], _cp₂, _hcp, _x => rfl
  | s :: cp₁, cp₂, hcp, x => by
      have htail := CProg.cubic_cons_tail hcp
      have hs := CProg.cubic_singleton_of_cons hcp
      calc
        injcp (s :: cp₁) cp₂ (op (cpmap cp₂) x) =
            injcp cp₁ (s :: cp₂)
              (oldStep s (cpmap cp₂) (op (cpmap cp₂) x)) := rfl
        _ = injcp cp₁ (s :: cp₂)
              (op (step s (cpmap cp₂)) (oldStep s (cpmap cp₂) x)) := by
            rw [hstep s (cpmap cp₂) hs x]
        _ = op (cpmap (CProg.appendRev cp₁ (s :: cp₂)))
              (injcp cp₁ (s :: cp₂) (oldStep s (cpmap cp₂) x)) := by
            simpa [cpmap_cons] using
              injcp_unary_of_cubic op hstep cp₁ (s :: cp₂) htail
                (oldStep s (cpmap cp₂) x)

theorem injcp_edge_of_cubic :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ (x : (cpmap cp₂).map.Dart),
        injcp cp₁ cp₂ ((cpmap cp₂).map.edge x) =
          (cpmap (CProg.appendRev cp₁ cp₂)).map.edge (injcp cp₁ cp₂ x) :=
  injcp_unary_of_cubic
    (fun P => P.map.edge)
    (fun _s P hs x => oldStep_edge_of_cubicStep hs P x)

theorem injcp_edge_symm_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (x : (cpmap cp₂).map.Dart) :
    injcp cp₁ cp₂ ((cpmap cp₂).map.edge.symm x) =
      (cpmap (CProg.appendRev cp₁ cp₂)).map.edge.symm
        (injcp cp₁ cp₂ x) := by
  apply (cpmap (CProg.appendRev cp₁ cp₂)).map.edge.injective
  calc
    (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
        (injcp cp₁ cp₂ ((cpmap cp₂).map.edge.symm x))
        = injcp cp₁ cp₂
            ((cpmap cp₂).map.edge ((cpmap cp₂).map.edge.symm x)) := by
          rw [← injcp_edge_of_cubic cp₁ cp₂ hcp
            ((cpmap cp₂).map.edge.symm x)]
    _ = injcp cp₁ cp₂ x := by simp
    _ = (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
        ((cpmap (CProg.appendRev cp₁ cp₂)).map.edge.symm
          (injcp cp₁ cp₂ x)) := by simp

theorem injcp_edgeReachable_of_edgeReachable
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart}
    (hxy : PermReachable (cpmap cp₂).map.edge x y) :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) := by
  induction hxy with
  | refl =>
      exact PermReachable.refl
        (cpmap (CProg.appendRev cp₁ cp₂)).map.edge (injcp cp₁ cp₂ x)
  | @tail b c hxb hbc ih =>
      refine Relation.ReflTransGen.trans ih ?_
      apply Relation.ReflTransGen.single
      cases hbc with
      | forward =>
          simpa [injcp_edge_of_cubic cp₁ cp₂ hcp b] using
            PermLink.forward
              (σ := (cpmap (CProg.appendRev cp₁ cp₂)).map.edge)
              (injcp cp₁ cp₂ b)
      | backward =>
          simpa [injcp_edge_symm_of_cubic cp₁ cp₂ hcp b] using
            PermLink.backward
              (σ := (cpmap (CProg.appendRev cp₁ cp₂)).map.edge)
              (injcp cp₁ cp₂ b)

theorem injcp_injective :
    ∀ (cp₁ cp₂ : CProg), Function.Injective (injcp cp₁ cp₂)
  | [], _cp₂ => by
      intro x y hxy
      exact hxy
  | s :: cp₁, cp₂ => by
      intro x y hxy
      have hstep :
          oldStep s (cpmap cp₂) x = oldStep s (cpmap cp₂) y :=
        injcp_injective cp₁ (s :: cp₂) hxy
      exact oldStep_injective s (cpmap cp₂) hstep

theorem injcp_not_onRing_of_cubic :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ {x : (cpmap cp₂).map.Dart},
        ¬ (cpmap cp₂).OnRing x →
          ¬ (cpmap (CProg.appendRev cp₁ cp₂)).OnRing
            (injcp cp₁ cp₂ x)
  | [], _cp₂, _hcp, _x, hx => hx
  | s :: cp₁, cp₂, hcp, _x, hx =>
      injcp_not_onRing_of_cubic cp₁ (s :: cp₂)
        (CProg.cubic_cons_tail hcp)
        (oldStep_not_onRing_of_cubicStep
          (CProg.cubic_singleton_of_cons hcp) (cpmap cp₂) hx)

theorem injcp_node_of_cubic_of_not_onRing :
    ∀ (cp₁ cp₂ : CProg), CProg.cubic cp₁ = true →
      ∀ {x : (cpmap cp₂).map.Dart},
        ¬ (cpmap cp₂).OnRing x →
          injcp cp₁ cp₂ ((cpmap cp₂).map.node x) =
            (cpmap (CProg.appendRev cp₁ cp₂)).map.node
              (injcp cp₁ cp₂ x)
  | [], _cp₂, _hcp, _x, _hx => rfl
  | s :: cp₁, cp₂, hcp, x, hx => by
      have htail : CProg.cubic cp₁ = true :=
        CProg.cubic_cons_tail hcp
      have hs : CProg.cubic [s] = true :=
        CProg.cubic_singleton_of_cons hcp
      have hstep :
          oldStep s (cpmap cp₂) ((cpmap cp₂).map.node x) =
            (step s (cpmap cp₂)).map.node
              (oldStep s (cpmap cp₂) x) :=
        oldStep_node_of_cubicStep_of_not_onRing hs (cpmap cp₂) hx
      have hnot :
          ¬ (cpmap (s :: cp₂)).OnRing
            (oldStep s (cpmap cp₂) x) :=
        oldStep_not_onRing_of_cubicStep hs (cpmap cp₂) hx
      calc
        injcp (s :: cp₁) cp₂ ((cpmap cp₂).map.node x)
            = injcp cp₁ (s :: cp₂)
                (oldStep s (cpmap cp₂) ((cpmap cp₂).map.node x)) := rfl
        _ = injcp cp₁ (s :: cp₂)
              ((step s (cpmap cp₂)).map.node
                (oldStep s (cpmap cp₂) x)) := by
              rw [hstep]
        _ = (cpmap (CProg.appendRev cp₁ (s :: cp₂))).map.node
              (injcp cp₁ (s :: cp₂)
                (oldStep s (cpmap cp₂) x)) := by
              simpa [cpmap_cons] using
                injcp_node_of_cubic_of_not_onRing cp₁ (s :: cp₂) htail
                  hnot

theorem injcp_nodeReachable_of_nodeReachable_of_cubic_of_not_onRing
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart}
    (hx : ¬ (cpmap cp₂).OnRing x)
    (hxy : PermReachable (cpmap cp₂).map.node x y) :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.node
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) := by
  induction hxy with
  | refl =>
      exact PermReachable.refl
        (cpmap (CProg.appendRev cp₁ cp₂)).map.node
        (injcp cp₁ cp₂ x)
  | @tail b c hxb hbc ih =>
      have hb :
          ¬ (cpmap cp₂).OnRing b :=
        not_onRing_of_nodeReachable (cpmap cp₂) hx hxb
      refine PermReachable.trans
        (cpmap (CProg.appendRev cp₁ cp₂)).map.node ih ?_
      cases hbc with
      | forward =>
          have hnode :=
            injcp_node_of_cubic_of_not_onRing cp₁ cp₂ hcp hb
          simpa [hnode] using
            PermReachable.forward
              (cpmap (CProg.appendRev cp₁ cp₂)).map.node
              (injcp cp₁ cp₂ b)
      | backward =>
          have hpre :
              ¬ (cpmap cp₂).OnRing ((cpmap cp₂).map.node.symm b) := by
            intro hring
            exact hb (PermReachable.trans (cpmap cp₂).map.node hring
              (by
                simpa using
                  PermReachable.forward (cpmap cp₂).map.node
                    ((cpmap cp₂).map.node.symm b)))
          have hnode :=
            injcp_node_of_cubic_of_not_onRing cp₁ cp₂ hcp hpre
          have hnode' :
              injcp cp₁ cp₂ b =
                (cpmap (CProg.appendRev cp₁ cp₂)).map.node
                  (injcp cp₁ cp₂ ((cpmap cp₂).map.node.symm b)) := by
            simpa using hnode
          simpa [hnode'] using
            PermReachable.backward
              (cpmap (CProg.appendRev cp₁ cp₂)).map.node
              (injcp cp₁ cp₂ b)

theorem injcp_nodeReachable_lift_of_cubic_of_not_onRing
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true) :
    ∀ {x : (cpmap cp₂).map.Dart}
      (_ : ¬ (cpmap cp₂).OnRing x)
      {z : (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart},
      PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.node
        (injcp cp₁ cp₂ x) z →
      ∃ y : (cpmap cp₂).map.Dart,
        z = injcp cp₁ cp₂ y ∧
          PermReachable (cpmap cp₂).map.node x y ∧
            ¬ (cpmap cp₂).OnRing y := by
  intro x hx z hxz
  induction hxz with
  | refl =>
      exact ⟨x, rfl, PermReachable.refl (cpmap cp₂).map.node x, hx⟩
  | @tail b c hxb hbc ih =>
      rcases ih with ⟨y, rfl, hxy, hy⟩
      cases hbc with
      | forward =>
          have hnode :=
            injcp_node_of_cubic_of_not_onRing cp₁ cp₂ hcp hy
          have hxy' :
              PermReachable (cpmap cp₂).map.node x
                ((cpmap cp₂).map.node y) :=
            PermReachable.trans (cpmap cp₂).map.node hxy
              (PermReachable.forward (cpmap cp₂).map.node y)
          refine ⟨(cpmap cp₂).map.node y, ?_, hxy', ?_⟩
          · exact hnode.symm
          · exact not_onRing_of_nodeReachable (cpmap cp₂) hx hxy'
      | backward =>
          have hpre :
              ¬ (cpmap cp₂).OnRing ((cpmap cp₂).map.node.symm y) := by
            intro hring
            exact hy (PermReachable.trans (cpmap cp₂).map.node hring
              (by
                simpa using
                  PermReachable.forward (cpmap cp₂).map.node
                    ((cpmap cp₂).map.node.symm y)))
          have hnode :=
            injcp_node_of_cubic_of_not_onRing cp₁ cp₂ hcp hpre
          have hnode' :
              injcp cp₁ cp₂ y =
                (cpmap (CProg.appendRev cp₁ cp₂)).map.node
                  (injcp cp₁ cp₂ ((cpmap cp₂).map.node.symm y)) := by
            simpa using hnode
          have hxy' :
              PermReachable (cpmap cp₂).map.node x
                ((cpmap cp₂).map.node.symm y) :=
            PermReachable.trans (cpmap cp₂).map.node hxy
              (PermReachable.backward (cpmap cp₂).map.node y)
          refine ⟨(cpmap cp₂).map.node.symm y, ?_, hxy', hpre⟩
          · simp [hnode']

theorem injcp_nodeReachable_iff_of_cubic_of_not_onRing
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart}
    (hx : ¬ (cpmap cp₂).OnRing x) :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.node
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
      PermReachable (cpmap cp₂).map.node x y := by
  constructor
  · intro hxy
    rcases injcp_nodeReachable_lift_of_cubic_of_not_onRing
        cp₁ cp₂ hcp hx hxy with
      ⟨z, hz, hxz, _hzNot⟩
    have hyz : y = z := injcp_injective cp₁ cp₂ hz
    subst z
    exact hxz
  · exact injcp_nodeReachable_of_nodeReachable_of_cubic_of_not_onRing
      cp₁ cp₂ hcp hx

/-- Coq `sub_cface_injcp`: construction-program injections preserve face
reachability. -/
theorem sub_cface_injcp
    (cp₁ cp₂ : CProg)
    {x y : (cpmap cp₂).map.Dart}
    (hxy : PermReachable (cpmap cp₂).map.face x y) :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.face
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) :=
  injcp_faceReachable_of_faceReachable cp₁ cp₂ hxy

/-- Coq `cface_injcp`: on cubic prefixes, construction-program injections
reflect and preserve face reachability. -/
theorem cface_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart} :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.face
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
      PermReachable (cpmap cp₂).map.face x y :=
  injcp_faceReachable_iff_of_cubic cp₁ cp₂ hcp

/-- Construction-program injections preserve finite face bands. -/
theorem injcp_faceBand_of_faceBand
    (cp₁ cp₂ : CProg)
    {r : List (cpmap cp₂).map.Dart} {u : (cpmap cp₂).map.Dart}
    (hu : (cpmap cp₂).map.FaceBand r u) :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
      (r.map (injcp cp₁ cp₂)) (injcp cp₁ cp₂ u) := by
  rcases hu with ⟨x, hx, hxu⟩
  exact ⟨injcp cp₁ cp₂ x, List.mem_map.mpr ⟨x, hx, rfl⟩,
    injcp_faceReachable_of_faceReachable cp₁ cp₂ hxu⟩

/-- On cubic prefixes, construction-program injections reflect and preserve
finite face bands. -/
theorem injcp_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {r : List (cpmap cp₂).map.Dart} {u : (cpmap cp₂).map.Dart} :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
      (r.map (injcp cp₁ cp₂)) (injcp cp₁ cp₂ u) ↔
      (cpmap cp₂).map.FaceBand r u := by
  constructor
  · rintro ⟨z, hz, hzu⟩
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (injcp_faceReachable_iff_of_cubic
      cp₁ cp₂ hcp).1 hzu⟩
  · exact injcp_faceBand_of_faceBand cp₁ cp₂

/-- Coq-style wrapper for `injcp_faceBand_of_faceBand`. -/
theorem sub_fband_injcp
    (cp₁ cp₂ : CProg)
    {r : List (cpmap cp₂).map.Dart} {u : (cpmap cp₂).map.Dart}
    (hu : (cpmap cp₂).map.FaceBand r u) :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
      (r.map (injcp cp₁ cp₂)) (injcp cp₁ cp₂ u) :=
  injcp_faceBand_of_faceBand cp₁ cp₂ hu

/-- Coq-style wrapper: on cubic prefixes, injected finite face bands are exact. -/
theorem fband_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {r : List (cpmap cp₂).map.Dart} {u : (cpmap cp₂).map.Dart} :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
      (r.map (injcp cp₁ cp₂)) (injcp cp₁ cp₂ u) ↔
      (cpmap cp₂).map.FaceBand r u :=
  injcp_faceBand_iff_of_cubic cp₁ cp₂ hcp

theorem not_fband_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {r : List (cpmap cp₂).map.Dart} {u : (cpmap cp₂).map.Dart} :
    ¬ (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
        (r.map (injcp cp₁ cp₂)) (injcp cp₁ cp₂ u) ↔
      ¬ (cpmap cp₂).map.FaceBand r u :=
  not_congr (fband_injcp cp₁ cp₂ hcp)

theorem injcp_selectMask_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (m : CfMask)
    {ring kernel : List (cpmap cp₂).map.Dart}
    {u : (cpmap cp₂).map.Dart} :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
      (CfMask.selectMask m (ring.map (injcp cp₁ cp₂))
        (kernel.map (injcp cp₁ cp₂)))
      (injcp cp₁ cp₂ u) ↔
      (cpmap cp₂).map.FaceBand (CfMask.selectMask m ring kernel) u := by
  rw [CfMask.selectMask_map]
  exact injcp_faceBand_iff_of_cubic cp₁ cp₂ hcp

theorem not_injcp_selectMask_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (m : CfMask)
    {ring kernel : List (cpmap cp₂).map.Dart}
    {u : (cpmap cp₂).map.Dart} :
    ¬ (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
        (CfMask.selectMask m (ring.map (injcp cp₁ cp₂))
          (kernel.map (injcp cp₁ cp₂)))
        (injcp cp₁ cp₂ u) ↔
      ¬ (cpmap cp₂).map.FaceBand (CfMask.selectMask m ring kernel) u :=
  not_congr (injcp_selectMask_faceBand_iff_of_cubic cp₁ cp₂ hcp m)

theorem injcp_exists_selectMask_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (m : CfMask)
    {sources ring kernel : List (cpmap cp₂).map.Dart} :
    (∃ z : (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart,
      z ∈ CfMask.selectMask m (ring.map (injcp cp₁ cp₂))
        (kernel.map (injcp cp₁ cp₂)) ∧
      (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
        (sources.map (injcp cp₁ cp₂)) z) ↔
      ∃ x : (cpmap cp₂).map.Dart,
        x ∈ CfMask.selectMask m ring kernel ∧
        (cpmap cp₂).map.FaceBand sources x := by
  rw [CfMask.selectMask_map]
  constructor
  · rintro ⟨z, hz, hband⟩
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (injcp_faceBand_iff_of_cubic
      cp₁ cp₂ hcp).1 hband⟩
  · rintro ⟨x, hx, hband⟩
    exact ⟨injcp cp₁ cp₂ x, List.mem_map.mpr ⟨x, hx, rfl⟩,
      (injcp_faceBand_iff_of_cubic cp₁ cp₂ hcp).2 hband⟩

theorem not_injcp_exists_selectMask_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (m : CfMask)
    {sources ring kernel : List (cpmap cp₂).map.Dart} :
    ¬ (∃ z : (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart,
      z ∈ CfMask.selectMask m (ring.map (injcp cp₁ cp₂))
        (kernel.map (injcp cp₁ cp₂)) ∧
      (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
        (sources.map (injcp cp₁ cp₂)) z) ↔
      ¬ ∃ x : (cpmap cp₂).map.Dart,
        x ∈ CfMask.selectMask m ring kernel ∧
        (cpmap cp₂).map.FaceBand sources x :=
  not_congr (injcp_exists_selectMask_faceBand_iff_of_cubic
    cp₁ cp₂ hcp m)

theorem injcp_forall_mem_not_faceBand_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {sources r : List (cpmap cp₂).map.Dart} :
    (∀ z : (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart,
      z ∈ r.map (injcp cp₁ cp₂) →
        ¬ (cpmap (CProg.appendRev cp₁ cp₂)).map.FaceBand
          (sources.map (injcp cp₁ cp₂)) z) ↔
      ∀ x : (cpmap cp₂).map.Dart,
        x ∈ r → ¬ (cpmap cp₂).map.FaceBand sources x := by
  constructor
  · intro h x hx hband
    exact h (injcp cp₁ cp₂ x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      ((injcp_faceBand_iff_of_cubic cp₁ cp₂ hcp).2 hband)
  · intro h z hz hband
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact h x hx ((injcp_faceBand_iff_of_cubic cp₁ cp₂ hcp).1 hband)

/-- Coq `sub_adj_injcp`: construction-program injections preserve the
face-adjacency predicate. -/
theorem sub_adj_injcp
    (cp₁ cp₂ : CProg)
    {x y : (cpmap cp₂).map.Dart}
    (hxy : (cpmap cp₂).map.RingAdj x y) :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.RingAdj
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) :=
  injcp_ringAdj_of_ringAdj cp₁ cp₂ hxy

/-- Coq `adj_injcp`: on cubic prefixes, construction-program injections
reflect and preserve the face-adjacency predicate. -/
theorem adj_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart} :
    (cpmap (CProg.appendRev cp₁ cp₂)).map.RingAdj
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
      (cpmap cp₂).map.RingAdj x y :=
  injcp_ringAdj_iff_of_cubic cp₁ cp₂ hcp

/-- Coq `edge_injcp`: on cubic prefixes, construction-program injections
commute with the edge involution. -/
theorem edge_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    (x : (cpmap cp₂).map.Dart) :
    injcp cp₁ cp₂ ((cpmap cp₂).map.edge x) =
      (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
        (injcp cp₁ cp₂ x) :=
  injcp_edge_of_cubic cp₁ cp₂ hcp x

/-- Coq `node_injcp`: off the source ring, construction-program injections
commute with the node permutation. -/
theorem node_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x : (cpmap cp₂).map.Dart}
    (hx : ¬ (cpmap cp₂).OnRing x) :
    injcp cp₁ cp₂ ((cpmap cp₂).map.node x) =
      (cpmap (CProg.appendRev cp₁ cp₂)).map.node
        (injcp cp₁ cp₂ x) :=
  injcp_node_of_cubic_of_not_onRing cp₁ cp₂ hcp hx

/-- Coq `cnode_injcp`: off the source ring, construction-program injections
reflect and preserve node reachability. -/
theorem cnode_injcp
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart}
    (hx : ¬ (cpmap cp₂).OnRing x) :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.node
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
      PermReachable (cpmap cp₂).map.node x y :=
  injcp_nodeReachable_iff_of_cubic_of_not_onRing cp₁ cp₂ hcp hx

theorem injcp_edgeReachable_lift_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true) :
    ∀ {x : (cpmap cp₂).map.Dart}
      {z : (cpmap (CProg.appendRev cp₁ cp₂)).map.Dart},
      PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
        (injcp cp₁ cp₂ x) z →
      ∃ y : (cpmap cp₂).map.Dart,
        z = injcp cp₁ cp₂ y ∧
          PermReachable (cpmap cp₂).map.edge x y := by
  intro x z hxz
  induction hxz with
  | refl =>
      exact ⟨x, rfl, PermReachable.refl (cpmap cp₂).map.edge x⟩
  | @tail b c hxb hbc ih =>
      rcases ih with ⟨y, rfl, hxy⟩
      cases hbc with
      | forward =>
          refine ⟨(cpmap cp₂).map.edge y, ?_, ?_⟩
          · exact (injcp_edge_of_cubic cp₁ cp₂ hcp y).symm
          · exact PermReachable.trans (cpmap cp₂).map.edge hxy
              (PermReachable.forward (cpmap cp₂).map.edge y)
      | backward =>
          refine ⟨(cpmap cp₂).map.edge.symm y, ?_, ?_⟩
          · exact (injcp_edge_symm_of_cubic cp₁ cp₂ hcp y).symm
          · exact PermReachable.trans (cpmap cp₂).map.edge hxy
              (PermReachable.backward (cpmap cp₂).map.edge y)

theorem injcp_edgeReachable_iff_of_cubic
    (cp₁ cp₂ : CProg)
    (hcp : CProg.cubic cp₁ = true)
    {x y : (cpmap cp₂).map.Dart} :
    PermReachable (cpmap (CProg.appendRev cp₁ cp₂)).map.edge
      (injcp cp₁ cp₂ x) (injcp cp₁ cp₂ y) ↔
      PermReachable (cpmap cp₂).map.edge x y := by
  constructor
  · intro hxy
    rcases injcp_edgeReachable_lift_of_cubic cp₁ cp₂ hcp hxy with
      ⟨z, hz, hxz⟩
    have hyz : y = z := injcp_injective cp₁ cp₂ hz
    subst z
    exact hxz
  · exact injcp_edgeReachable_of_edgeReachable cp₁ cp₂ hcp

end PointedHypermap
end FourColor
end Schematic.Math.GraphTheory
