import FourColorTheorem.FourColor.Reducibility.ProgramMap.Support

namespace Schematic.Math.GraphTheory.FourColor
/-- A hypermap together with the current ring head. -/
structure PointedHypermap where
  map : Hypermap
  point : map.Dart

namespace PointedHypermap

/-- The current pointer is a nontrivial ring head. -/
def ProperRingHead (P : PointedHypermap) : Prop :=
  P.map.ProperRingHead P.point

/-- The current pointer has at least three darts in its ring. -/
def LongRingHead (P : PointedHypermap) : Prop :=
  P.map.LongRingHead P.point

/-- The current semantic ring as a predicate: the node orbit of the pointer. -/
def OnRing (P : PointedHypermap) (x : P.map.Dart) : Prop :=
  PermReachable P.map.node P.point x

theorem onRing_point (P : PointedHypermap) :
    P.OnRing P.point :=
  PermReachable.refl P.map.node P.point

theorem onRing_node_point (P : PointedHypermap) :
    P.OnRing (P.map.node P.point) :=
  PermReachable.forward P.map.node P.point

theorem onRing_face_edge_point (P : PointedHypermap) :
    P.OnRing (P.map.face (P.map.edge P.point)) := by
  have h :
      PermReachable P.map.node (P.map.face (P.map.edge P.point))
        P.point := by
    simpa using
      (PermReachable.forward P.map.node (P.map.face (P.map.edge P.point)))
  exact PermReachable.symm P.map.node h

theorem not_onRing_of_nodeReachable
    (P : PointedHypermap) {x y : P.map.Dart}
    (hx : ¬ P.OnRing x)
    (hxy : PermReachable P.map.node x y) :
    ¬ P.OnRing y := by
  intro hy
  exact hx (PermReachable.trans P.map.node hy
    (PermReachable.symm P.map.node hxy))

theorem onRing_eq_point_or_node_point_of_period_two
    (P : PointedHypermap)
    (hperiod : P.map.node (P.map.node P.point) = P.point)
    {x : P.map.Dart}
    (hx : P.OnRing x) :
    x = P.point ∨ x = P.map.node P.point := by
  induction hx with
  | refl =>
      exact Or.inl rfl
  | @tail b c _hpb hbc ih =>
      rcases ih with rfl | rfl
      · cases hbc with
        | forward => exact Or.inr rfl
        | backward =>
            right
            apply P.map.node.injective
            simpa using hperiod.symm
      · cases hbc with
        | forward => exact Or.inl hperiod
        | backward => exact Or.inl (P.map.node.symm_apply_apply P.point)

/-- Plainness of the current pointed map. -/
def Plain (P : PointedHypermap) : Prop :=
  P.map.Plain

/-- Bridgelessness of the current pointed map. -/
def Bridgeless (P : PointedHypermap) : Prop :=
  P.map.Bridgeless

/-- Generated connectedness of the current pointed map. -/
def Connected (P : PointedHypermap) : Prop :=
  P.map.Connected

/-- Cubicity away from the current node-orbit perimeter.  This is the pointed
form of Coq's `quasicubic (rev (cpring P))`. -/
def Quasicubic (P : PointedHypermap) : Prop :=
  P.map.CubicOn (fun x => ¬ P.OnRing x)

/-- Geometry propagated by every construction program currently supported by
the certified interpreter. -/
structure SupportedGeometry (P : PointedHypermap) : Prop where
  plain : P.Plain
  connected : P.Connected

/-- Geometry propagated by every supported cubic program. -/
structure CubicGeometry (P : PointedHypermap) : Prop where
  proper : P.ProperRingHead
  plain : P.Plain
  connected : P.Connected

/-- Geometry propagated by supported configuration programs. -/
structure ConfigGeometry (P : PointedHypermap) : Prop extends CubicGeometry P where
  long : P.LongRingHead
  bridgeless : P.Bridgeless

theorem CubicGeometry.supported
    {P : PointedHypermap}
    (hP : P.CubicGeometry) :
    P.SupportedGeometry where
  plain := hP.plain
  connected := hP.connected

theorem ConfigGeometry.supported
    {P : PointedHypermap}
    (hP : P.ConfigGeometry) :
    P.SupportedGeometry :=
  hP.toCubicGeometry.supported

/-- Iterate a permutation forward a fixed number of times. -/
def iteratePerm {α : Type u} (σ : Equiv.Perm α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iteratePerm σ n (σ x)

@[simp]
theorem iteratePerm_zero {α : Type u} (σ : Equiv.Perm α) (x : α) :
    iteratePerm σ 0 x = x :=
  rfl

@[simp]
theorem iteratePerm_succ {α : Type u} (σ : Equiv.Perm α)
    (n : Nat) (x : α) :
    iteratePerm σ (n + 1) x = iteratePerm σ n (σ x) :=
  rfl

theorem permReachable_iteratePerm_symm {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (n : Nat) (x : α), PermReachable σ x (iteratePerm σ.symm n x)
  | 0, x => PermReachable.refl σ x
  | n + 1, x =>
      PermReachable.trans σ (PermReachable.backward σ x)
        (permReachable_iteratePerm_symm σ n (σ.symm x))

theorem permReachable_iteratePerm {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (n : Nat) (x : α), PermReachable σ x (iteratePerm σ n x)
  | 0, x => PermReachable.refl σ x
  | n + 1, x =>
      PermReachable.trans σ (PermReachable.forward σ x)
        (permReachable_iteratePerm σ n (σ x))

theorem iteratePerm_apply_comm {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (n : Nat) (x : α),
      σ (iteratePerm σ n x) = iteratePerm σ n (σ x)
  | 0, _x => rfl
  | n + 1, x => by
      change σ (iteratePerm σ n (σ x)) =
        iteratePerm σ n (σ (σ x))
      exact iteratePerm_apply_comm σ n (σ x)

theorem iteratePerm_add_right {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (m n : Nat) (x : α),
      iteratePerm σ (m + n) x =
        iteratePerm σ n (iteratePerm σ m x)
  | m, 0, _x => by
      simp
  | m, n + 1, x => by
      rw [Nat.add_succ]
      change iteratePerm σ (m + n) (σ x) =
        iteratePerm σ n (σ (iteratePerm σ m x))
      rw [iteratePerm_add_right σ m n (σ x)]
      rw [iteratePerm_apply_comm]

theorem iteratePerm_add_left {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (m n : Nat) (x : α),
      iteratePerm σ (m + n) x =
        iteratePerm σ m (iteratePerm σ n x)
  | m, n, x => by
      simpa [Nat.add_comm] using iteratePerm_add_right σ n m x

theorem iteratePerm_succ_right {α : Type u}
    (σ : Equiv.Perm α) (n : Nat) (x : α) :
    iteratePerm σ (n + 1) x = σ (iteratePerm σ n x) := by
  rw [iteratePerm_succ]
  exact (iteratePerm_apply_comm σ n x).symm

theorem iteratePerm_eq_iterate {α : Type u}
    (σ : Equiv.Perm α) (n : Nat) (x : α) :
    iteratePerm σ n x = (σ : α → α)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [iteratePerm_succ, Function.iterate_succ_apply, ih]

theorem iteratePerm_symm_iteratePerm_comm {α : Type u}
    (σ : Equiv.Perm α) (m n : Nat) (x : α) :
    iteratePerm σ.symm m (iteratePerm σ n x) =
      iteratePerm σ n (iteratePerm σ.symm m x) := by
  simp only [iteratePerm_eq_iterate]
  exact (Function.Commute.iterate_iterate (by
    intro y
    simp) m n) x

theorem iteratePerm_mod_eq_of_period {α : Type u}
    (σ : Equiv.Perm α) {x : α} {m n : Nat}
    (hperiod : iteratePerm σ n x = x) :
    iteratePerm σ (m % n) x = iteratePerm σ m x := by
  have hmul : ∀ k : Nat, iteratePerm σ (n * k) x = x := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        calc
          iteratePerm σ (n * (k + 1)) x =
              iteratePerm σ (n * k + n) x := by
                rw [Nat.mul_succ]
          _ = iteratePerm σ n (iteratePerm σ (n * k) x) := by
                rw [iteratePerm_add_right]
          _ = iteratePerm σ n x := by
                rw [ih]
          _ = x := hperiod
  have hmain :
      iteratePerm σ m x = iteratePerm σ (m % n) x := by
    calc
      iteratePerm σ m x =
          iteratePerm σ (m % n + n * (m / n)) x := by
            rw [Nat.mod_add_div]
      _ =
          iteratePerm σ (m % n)
            (iteratePerm σ (n * (m / n)) x) := by
            rw [iteratePerm_add_left]
      _ = iteratePerm σ (m % n) x := by
            rw [hmul]
  exact hmain.symm

theorem apply_iteratePerm_symm {α : Type u}
    (σ : Equiv.Perm α) :
    ∀ (n : Nat) (x : α),
      σ (iteratePerm σ.symm n x) =
        iteratePerm σ.symm n (σ x)
  | 0, _x => rfl
  | n + 1, x => by
      simp only [iteratePerm_succ]
      simpa using apply_iteratePerm_symm σ n (σ.symm x)

/-- The initial pointed configuration map. -/
def base : PointedHypermap where
  map := cpmap0
  point := true

@[simp]
theorem base_map :
    base.map = cpmap0 :=
  rfl

@[simp]
theorem base_point :
    base.point = true :=
  rfl

theorem base_properRingHead :
    base.ProperRingHead :=
  cpmap0_proper_true

theorem base_not_longRingHead :
    ¬ base.LongRingHead :=
  cpmap0_not_long_true

theorem base_plain :
    base.Plain :=
  cpmap0_plain

theorem base_bridgeless :
    base.Bridgeless :=
  cpmap0_bridgeless

theorem base_connected :
    base.Connected :=
  cpmap0_connected

theorem base_quasicubic :
    base.Quasicubic := by
  intro x hx
  exfalso
  apply hx
  cases x
  · exact PermReachable.forward cpmap0.node true
  · exact PermReachable.refl cpmap0.node true

/-- The order of the node orbit used by Coq's `ecpR`.  The representative
`node point` is the head of `cpring`, so this is the exact order exposed by a
proved ring cycle. -/
noncomputable def nodeOrder (P : PointedHypermap) : Nat :=
  Function.minimalPeriod
    (P.map.node.symm : P.map.Dart → P.map.Dart)
    (P.map.node P.point)

theorem nodeOrder_pos (P : PointedHypermap) : 0 < P.nodeOrder :=
  Function.minimalPeriod_pos_of_mem_periodicPts
    (P.map.node.symm.injective.mem_periodicPts (P.map.node P.point))

theorem nodeOrder_period (P : PointedHypermap) :
    iteratePerm P.map.node.symm P.nodeOrder (P.map.node P.point) =
      P.map.node P.point := by
  rw [iteratePerm_eq_iterate]
  exact Function.iterate_minimalPeriod

theorem nodeOrder_point_period (P : PointedHypermap) :
    iteratePerm P.map.node.symm P.nodeOrder P.point = P.point := by
  apply P.map.node.injective
  rw [apply_iteratePerm_symm]
  exact P.nodeOrder_period

theorem nodeOrder_forward_point_period (P : PointedHypermap) :
    iteratePerm P.map.node P.nodeOrder P.point = P.point := by
  have hinv := P.nodeOrder_point_period
  simp only [iteratePerm_eq_iterate] at hinv ⊢
  calc
    (P.map.node : P.map.Dart → P.map.Dart)^[P.nodeOrder] P.point =
        (P.map.node : P.map.Dart → P.map.Dart)^[P.nodeOrder]
          ((P.map.node.symm : P.map.Dart → P.map.Dart)^[P.nodeOrder]
            P.point) := by rw [hinv]
    _ = P.point :=
      (Function.LeftInverse.iterate P.map.node.apply_symm_apply
        P.nodeOrder) P.point

/-- Coq `ecpR n`: repoint by `node^(order node point - n)`.  In particular,
as in Coq, a rotation at least as large as the node-orbit order is the
identity rather than a modulo rotation. -/
noncomputable def rotate (n : Nat) (P : PointedHypermap) : PointedHypermap where
  map := P.map
  point := iteratePerm P.map.node (P.nodeOrder - n) P.point

@[simp]
theorem rotate_map (n : Nat) (P : PointedHypermap) :
    (P.rotate n).map = P.map :=
  rfl

@[simp]
theorem rotate_point (n : Nat) (P : PointedHypermap) :
    (P.rotate n).point =
      iteratePerm P.map.node (P.nodeOrder - n) P.point :=
  rfl

theorem rotate_one_point (P : PointedHypermap) :
    (P.rotate 1).point = P.map.node.symm P.point := by
  rw [rotate_point]
  apply P.map.node.injective
  rw [P.map.node.apply_symm_apply]
  have hpos := P.nodeOrder_pos
  have horder : P.nodeOrder = (P.nodeOrder - 1) + 1 := by
    omega
  rw [iteratePerm_apply_comm, ← iteratePerm_succ, ← horder]
  exact P.nodeOrder_forward_point_period

theorem rotate_onRing_iff (n : Nat) (P : PointedHypermap)
    {x : P.map.Dart} :
    (P.rotate n).OnRing x ↔ P.OnRing x := by
  change PermReachable P.map.node
      (iteratePerm P.map.node (P.nodeOrder - n) P.point) x ↔
    PermReachable P.map.node P.point x
  have hrot :
      PermReachable P.map.node P.point
        (iteratePerm P.map.node (P.nodeOrder - n) P.point) :=
    permReachable_iteratePerm P.map.node (P.nodeOrder - n) P.point
  constructor
  · intro h
    exact PermReachable.trans P.map.node hrot h
  · intro h
    exact PermReachable.trans P.map.node
      (PermReachable.symm P.map.node hrot) h

theorem rotate_quasicubic (n : Nat) (P : PointedHypermap)
    (hP : P.Quasicubic) :
    (P.rotate n).Quasicubic := by
  intro x hx
  exact hP x ((rotate_onRing_iff n P).not.mp hx)

theorem rotate_plain
    (n : Nat) (P : PointedHypermap)
    (hP : P.Plain) :
    (P.rotate n).Plain := by
  simpa [Plain, rotate] using hP

theorem rotate_bridgeless
    (n : Nat) (P : PointedHypermap)
    (hP : P.Bridgeless) :
    (P.rotate n).Bridgeless := by
  simpa [Bridgeless, rotate] using hP

theorem rotate_connected
    (n : Nat) (P : PointedHypermap)
    (hP : P.Connected) :
    (P.rotate n).Connected := by
  simpa [Connected, rotate] using hP

theorem rotate_eq_self_of_nodeOrder_le
    {n : Nat} (P : PointedHypermap) (h : P.nodeOrder ≤ n) :
    P.rotate n = P := by
  cases P
  simp [rotate, Nat.sub_eq_zero_of_le h]

theorem properRingHead_node_symm
    {G : Hypermap} {x : G.Dart}
    (hproper : G.ProperRingHead x) :
    G.ProperRingHead (G.node.symm x) := by
  unfold Hypermap.ProperRingHead at hproper ⊢
  intro h
  have hx : G.node.symm x = x := by
    simpa using h
  exact hproper (by
    simpa using congrArg G.node hx)

theorem longRingHead_node_symm
    {G : Hypermap} {x : G.Dart}
    (hlong : G.LongRingHead x) :
    G.LongRingHead (G.node.symm x) := by
  unfold Hypermap.LongRingHead at hlong ⊢
  have hnode : G.node.symm x ≠ G.node x := by
    intro h
    exact hlong (by
      rw [Hypermap.face_edge_eq_node_symm]
      exact h)
  intro hbad
  rw [Hypermap.face_edge_eq_node_symm] at hbad
  have hprev : G.node.symm (G.node.symm x) = x := by
    simpa using hbad
  have hnode_eq : G.node.symm x = G.node x := by
    simpa using congrArg G.node hprev
  exact hnode hnode_eq

theorem properRingHead_node
    {G : Hypermap} {x : G.Dart}
    (hproper : G.ProperRingHead x) :
    G.ProperRingHead (G.node x) := by
  unfold Hypermap.ProperRingHead at hproper ⊢
  intro h
  have hx : x = G.node x := by
    simpa using congrArg G.node.symm h
  exact hproper hx

theorem longRingHead_node
    {G : Hypermap} {x : G.Dart}
    (hlong : G.LongRingHead x) :
    G.LongRingHead (G.node x) := by
  unfold Hypermap.LongRingHead at hlong ⊢
  have hnode : G.node.symm x ≠ G.node x := by
    intro h
    exact hlong (by
      rw [Hypermap.face_edge_eq_node_symm]
      exact h)
  intro hbad
  rw [Hypermap.face_edge_eq_node_symm] at hbad
  have hnext : x = G.node (G.node x) := by
    simpa using hbad
  have hnode_eq : G.node.symm x = G.node x := by
    apply G.node.injective
    simpa using hnext
  exact hnode hnode_eq

theorem properRingHead_iterate_node_symm
    {G : Hypermap} {x : G.Dart} :
    ∀ n : Nat,
      G.ProperRingHead x →
        G.ProperRingHead (iteratePerm G.node.symm n x)
  | 0, hproper => hproper
  | n + 1, hproper =>
      properRingHead_iterate_node_symm n
        (properRingHead_node_symm hproper)

theorem longRingHead_iterate_node_symm
    {G : Hypermap} {x : G.Dart} :
    ∀ n : Nat,
      G.LongRingHead x →
        G.LongRingHead (iteratePerm G.node.symm n x)
  | 0, hlong => hlong
  | n + 1, hlong =>
      longRingHead_iterate_node_symm n
        (longRingHead_node_symm hlong)

theorem properRingHead_iterate_node
    {G : Hypermap} {x : G.Dart} :
    ∀ n : Nat,
      G.ProperRingHead x → G.ProperRingHead (iteratePerm G.node n x)
  | 0, hproper => hproper
  | n + 1, hproper =>
      properRingHead_iterate_node n (properRingHead_node hproper)

theorem longRingHead_iterate_node
    {G : Hypermap} {x : G.Dart} :
    ∀ n : Nat,
      G.LongRingHead x → G.LongRingHead (iteratePerm G.node n x)
  | 0, hlong => hlong
  | n + 1, hlong =>
      longRingHead_iterate_node n (longRingHead_node hlong)

theorem rotate_properRingHead
    (n : Nat) (P : PointedHypermap)
    (hP : P.ProperRingHead) :
    (P.rotate n).ProperRingHead :=
  properRingHead_iterate_node (G := P.map) (x := P.point)
    (P.nodeOrder - n) hP

theorem rotate_longRingHead
    (n : Nat) (P : PointedHypermap)
    (hP : P.LongRingHead) :
    (P.rotate n).LongRingHead :=
  longRingHead_iterate_node (G := P.map) (x := P.point)
    (P.nodeOrder - n) hP

/-- Coq `ecpR'`: rebase the current pointer to the forward node successor. -/
def reverseRotate (P : PointedHypermap) : PointedHypermap where
  map := P.map
  point := P.map.node P.point

@[simp]
theorem reverseRotate_map (P : PointedHypermap) :
    P.reverseRotate.map = P.map :=
  rfl

@[simp]
theorem reverseRotate_point (P : PointedHypermap) :
    P.reverseRotate.point = P.map.node P.point :=
  rfl

theorem reverseRotate_onRing_iff (P : PointedHypermap)
    {x : P.map.Dart} :
    P.reverseRotate.OnRing x ↔ P.OnRing x := by
  change PermReachable P.map.node (P.map.node P.point) x ↔
    PermReachable P.map.node P.point x
  constructor
  · intro h
    exact PermReachable.trans P.map.node
      (PermReachable.forward P.map.node P.point) h
  · intro h
    exact PermReachable.trans P.map.node
      (PermReachable.symm P.map.node
        (PermReachable.forward P.map.node P.point)) h

theorem reverseRotate_properRingHead
    (P : PointedHypermap)
    (hP : P.ProperRingHead) :
    P.reverseRotate.ProperRingHead :=
  properRingHead_node (G := P.map) (x := P.point) hP

theorem reverseRotate_longRingHead
    (P : PointedHypermap)
    (hP : P.LongRingHead) :
    P.reverseRotate.LongRingHead :=
  longRingHead_node (G := P.map) (x := P.point) hP

theorem reverseRotate_plain
    (P : PointedHypermap)
    (hP : P.Plain) :
    P.reverseRotate.Plain := by
  simpa [Plain, reverseRotate] using hP

theorem reverseRotate_bridgeless
    (P : PointedHypermap)
    (hP : P.Bridgeless) :
    P.reverseRotate.Bridgeless := by
  simpa [Bridgeless, reverseRotate] using hP

theorem reverseRotate_connected
    (P : PointedHypermap)
    (hP : P.Connected) :
    P.reverseRotate.Connected := by
  simpa [Connected, reverseRotate] using hP


end PointedHypermap

end Schematic.Math.GraphTheory.FourColor
