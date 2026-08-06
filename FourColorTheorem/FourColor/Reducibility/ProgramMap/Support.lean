import FourColorTheorem.FourColor.Configuration.Encoding
import FourColorTheorem.FourColor.PermutationIteration
import Schematic.Math.GraphTheory.Embedding.Counts
import Schematic.Math.GraphTheory.Embedding.DartExtension

namespace Schematic.Math.GraphTheory.FourColor
/-- Boolean negation as a permutation. -/
def boolFlip : Equiv.Perm Bool where
  toFun b := !b
  invFun b := !b
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- Coq `cpmap0`: the two-dart base map with edge/node negation and identity
face. -/
def cpmap0 : Hypermap where
  Dart := Bool
  edge := boolFlip
  node := boolFlip
  face := Equiv.refl Bool
  node_face_edge := by
    intro b
    cases b <;> rfl

theorem permReachable_refl_eq {α : Type u} {x y : α}
    (hxy : PermReachable (Equiv.refl α) x y) :
    x = y := by
  induction hxy with
  | refl => rfl
  | tail _ hyz ih =>
      cases hyz with
      | forward => simpa using ih
      | backward => simpa using ih

theorem permReachable_refl_iff {α : Type u} {x y : α} :
    PermReachable (Equiv.refl α) x y ↔ x = y := by
  constructor
  · exact permReachable_refl_eq
  · intro h
    subst h
    exact PermReachable.refl (Equiv.refl α) x

theorem cpmap0_faceReachable_iff {x y : cpmap0.Dart} :
    PermReachable cpmap0.face x y ↔ x = y := by
  simpa [cpmap0] using
    (permReachable_refl_iff (α := Bool) (x := x) (y := y))

@[simp]
theorem cpmap0_faceBand_iff {r : List cpmap0.Dart} {u : cpmap0.Dart} :
    cpmap0.FaceBand r u ↔ u ∈ r := by
  constructor
  · rintro ⟨x, hx, hxu⟩
    have hxu' : x = u := (cpmap0_faceReachable_iff (x := x) (y := u)).1 hxu
    subst hxu'
    exact hx
  · intro hu
    exact ⟨u, hu, PermReachable.refl cpmap0.face u⟩

@[simp]
theorem cpmap0_ringAdj_iff {x y : cpmap0.Dart} :
    cpmap0.RingAdj x y ↔ cpmap0.edge x = y := by
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have hxz' : x = z := (cpmap0_faceReachable_iff (x := x) (y := z)).1 hxz
    have hzy' : cpmap0.edge z = y :=
      (cpmap0_faceReachable_iff (x := cpmap0.edge z) (y := y)).1 hzy
    subst hxz'
    exact hzy'
  · intro hxy
    refine ⟨x, PermReachable.refl cpmap0.face x, ?_⟩
    rw [hxy]
    exact PermReachable.refl cpmap0.face y

theorem cpmap0_plain :
    cpmap0.Plain := by
  intro b
  cases b
  · constructor
    · change (!(!false)) = false
      rfl
    · intro h
      change (!false) = false at h
      cases h
  · constructor
    · change (!(!true)) = true
      rfl
    · intro h
      change (!true) = true at h
      cases h

theorem cpmap0_connected :
    cpmap0.Connected := by
  constructor
  · exact ⟨true⟩
  · intro x y
    cases x <;> cases y
    · exact cpmap0.reachable_refl false
    · convert cpmap0.reachable_edge false
    · convert cpmap0.reachable_edge true
    · exact cpmap0.reachable_refl true

theorem cpmap0_bridgeless :
    cpmap0.Bridgeless := by
  intro b hb
  have hEq : b = cpmap0.edge b :=
    permReachable_refl_eq (by simpa [cpmap0] using hb)
  cases b
  · change false = (!false) at hEq
    cases hEq
  · change true = (!true) at hEq
    cases hEq

/-- The two-dart initial construction map is Euler-planar. -/
theorem cpmap0_eulerPlanar :
    cpmap0.EulerPlanar := by
  apply cpmap0.eulerPlanar_of_plain_node_eq_edge_face_eq_refl cpmap0_plain
  · rfl
  · rfl

@[simp]
theorem cpmap0_edge_false :
    cpmap0.edge false = true :=
  rfl

@[simp]
theorem cpmap0_edge_true :
    cpmap0.edge true = false :=
  rfl

theorem cpmap0_proper_true :
    cpmap0.ProperRingHead true := by
  unfold Hypermap.ProperRingHead
  change true ≠ (!true)
  decide

theorem cpmap0_not_long_true :
    ¬ cpmap0.LongRingHead true := by
  unfold Hypermap.LongRingHead
  change ¬ (Equiv.refl Bool) (!true) ≠ (!true)
  simp

namespace CProg

/-- Construction programs whose semantic interpretation is executable in this
file.  This is larger than Coq's `cubic_prog` because it now includes `R'`,
but still excludes `K` and `A` until their remaining geometry interfaces are
ported. -/
def mapSupported : CProg → Bool
  | [] => true
  | CpStep.rotate _ :: cp => mapSupported cp
  | CpStep.reverseRotate :: cp => mapSupported cp
  | CpStep.y :: cp => mapSupported cp
  | CpStep.h :: cp => mapSupported cp
  | CpStep.u :: cp => mapSupported cp
  | _ => false

/-- Construction programs whose semantics preserve the plain/connected
geometry already proved in this file.  This extends `mapSupported` by admitting
`K`; it still excludes `A`, whose contraction geometry is a separate layer. -/
def plainConnectedSupported : CProg → Bool
  | [] => true
  | CpStep.rotate _ :: cp => plainConnectedSupported cp
  | CpStep.reverseRotate :: cp => plainConnectedSupported cp
  | CpStep.y :: cp => plainConnectedSupported cp
  | CpStep.h :: cp => plainConnectedSupported cp
  | CpStep.u :: cp => plainConnectedSupported cp
  | CpStep.k :: cp => plainConnectedSupported cp
  | CpStep.a :: _ => false

theorem mapSupported_implies_plainConnectedSupported
    {cp : CProg}
    (hcp : mapSupported cp = true) :
    plainConnectedSupported cp = true := by
  induction cp with
  | nil =>
      rfl
  | cons s cp ih =>
      cases s <;> simp [mapSupported, plainConnectedSupported] at hcp ⊢
      all_goals exact ih hcp

theorem plainConnectedSupported_eq_true_iff_not_mem_a :
    ∀ cp : CProg, plainConnectedSupported cp = true ↔ CpStep.a ∉ cp
  | [] => by
      simp [plainConnectedSupported]
  | s :: cp => by
      cases s <;> simp [plainConnectedSupported,
        plainConnectedSupported_eq_true_iff_not_mem_a cp]

theorem plainConnectedSupported_of_not_mem_a
    {cp : CProg}
    (hcp : CpStep.a ∉ cp) :
    plainConnectedSupported cp = true :=
  (plainConnectedSupported_eq_true_iff_not_mem_a cp).2 hcp

theorem not_mem_a_of_plainConnectedSupported
    {cp : CProg}
    (hcp : plainConnectedSupported cp = true) :
    CpStep.a ∉ cp :=
  (plainConnectedSupported_eq_true_iff_not_mem_a cp).1 hcp

theorem mapSupported_eq_true_iff_not_mem_k_and_not_mem_a :
    ∀ cp : CProg,
      mapSupported cp = true ↔ CpStep.k ∉ cp ∧ CpStep.a ∉ cp
  | [] => by
      simp [mapSupported]
  | s :: cp => by
      cases s <;> simp [mapSupported,
        mapSupported_eq_true_iff_not_mem_k_and_not_mem_a cp]

theorem cubic_implies_mapSupported
    {cp : CProg}
    (hcp : cubic cp = true) :
    mapSupported cp = true := by
  induction cp with
  | nil =>
      rfl
  | cons s cp ih =>
      cases s <;> simp [cubic, mapSupported] at hcp ⊢
      all_goals exact ih hcp

theorem config_implies_mapSupported
    {cp : CProg}
    (hcp : config cp = true) :
    mapSupported cp = true :=
  cubic_implies_mapSupported (config_implies_cubic hcp)

theorem cubic_implies_plainConnectedSupported
    {cp : CProg}
    (hcp : cubic cp = true) :
    plainConnectedSupported cp = true :=
  mapSupported_implies_plainConnectedSupported
    (cubic_implies_mapSupported hcp)

theorem config_implies_plainConnectedSupported
    {cp : CProg}
    (hcp : config cp = true) :
    plainConnectedSupported cp = true :=
  mapSupported_implies_plainConnectedSupported
    (config_implies_mapSupported hcp)

theorem cubic_cons_tail
    {s : CpStep} {cp : CProg}
    (hcp : cubic (s :: cp) = true) :
    cubic cp = true := by
  cases s <;> simp [cubic] at hcp ⊢
  all_goals exact hcp

theorem cubic_singleton_of_cons
    {s : CpStep} {cp : CProg}
    (hcp : cubic (s :: cp) = true) :
    cubic [s] = true := by
  cases s <;> simp [cubic] at hcp ⊢

/-- Reverse-append used by Coq's `catrev`: `appendRev cp₁ cp₂` is
`cp₁.reverse ++ cp₂`, but its recursive form matches the construction-program
injection proofs. -/
def appendRev : CProg → CProg → CProg
  | [], cp₂ => cp₂
  | s :: cp₁, cp₂ => appendRev cp₁ (s :: cp₂)

@[simp]
theorem appendRev_nil (cp : CProg) :
    appendRev [] cp = cp :=
  rfl

@[simp]
theorem appendRev_cons (s : CpStep) (cp₁ cp₂ : CProg) :
    appendRev (s :: cp₁) cp₂ = appendRev cp₁ (s :: cp₂) :=
  rfl

theorem appendRev_eq_reverse_append :
    ∀ cp₁ cp₂ : CProg, appendRev cp₁ cp₂ = cp₁.reverse ++ cp₂
  | [], cp₂ => by
      simp [appendRev]
  | s :: cp₁, cp₂ => by
      simp [appendRev, appendRev_eq_reverse_append cp₁ (s :: cp₂),
        List.append_assoc]

@[simp]
theorem appendRev_nil_right (cp : CProg) :
    appendRev cp [] = cp.reverse := by
  simp [appendRev_eq_reverse_append]

theorem cubic_appendRev :
    ∀ cp₁ cp₂ : CProg,
      cubic (appendRev cp₁ cp₂) = (cubic cp₁ && cubic cp₂)
  | [], cp₂ => by
      simp [appendRev, cubic]
  | s :: cp₁, cp₂ => by
      cases s with
      | rotate n =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.rotate n :: cp₂)
      | reverseRotate =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.reverseRotate :: cp₂)
      | y =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.y :: cp₂)
      | h =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.h :: cp₂)
      | u =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.u :: cp₂)
      | k =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.k :: cp₂)
      | a =>
          simpa [appendRev, cubic] using
            cubic_appendRev cp₁ (CpStep.a :: cp₂)

theorem cubic_appendRev_eq_true_iff {cp₁ cp₂ : CProg} :
    cubic (appendRev cp₁ cp₂) = true ↔
      cubic cp₁ = true ∧ cubic cp₂ = true := by
  rw [cubic_appendRev]
  cases cubic cp₁ <;> cases cubic cp₂ <;> simp

theorem mapSupported_appendRev :
    ∀ cp₁ cp₂ : CProg,
      mapSupported (appendRev cp₁ cp₂) =
        (mapSupported cp₁ && mapSupported cp₂)
  | [], cp₂ => by
      simp [appendRev, mapSupported]
  | s :: cp₁, cp₂ => by
      cases s with
      | rotate n =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.rotate n :: cp₂)
      | reverseRotate =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.reverseRotate :: cp₂)
      | y =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.y :: cp₂)
      | h =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.h :: cp₂)
      | u =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.u :: cp₂)
      | k =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.k :: cp₂)
      | a =>
          simpa [appendRev, mapSupported] using
            mapSupported_appendRev cp₁ (CpStep.a :: cp₂)

theorem mapSupported_appendRev_eq_true_iff {cp₁ cp₂ : CProg} :
    mapSupported (appendRev cp₁ cp₂) = true ↔
      mapSupported cp₁ = true ∧ mapSupported cp₂ = true := by
  rw [mapSupported_appendRev]
  cases mapSupported cp₁ <;> cases mapSupported cp₂ <;> simp

theorem plainConnectedSupported_appendRev :
    ∀ cp₁ cp₂ : CProg,
      plainConnectedSupported (appendRev cp₁ cp₂) =
        (plainConnectedSupported cp₁ && plainConnectedSupported cp₂)
  | [], cp₂ => by
      simp [appendRev, plainConnectedSupported]
  | s :: cp₁, cp₂ => by
      cases s with
      | rotate n =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.rotate n :: cp₂)
      | reverseRotate =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.reverseRotate :: cp₂)
      | y =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.y :: cp₂)
      | h =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.h :: cp₂)
      | u =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.u :: cp₂)
      | k =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.k :: cp₂)
      | a =>
          simpa [appendRev, plainConnectedSupported] using
            plainConnectedSupported_appendRev cp₁ (CpStep.a :: cp₂)

theorem plainConnectedSupported_appendRev_eq_true_iff
    {cp₁ cp₂ : CProg} :
    plainConnectedSupported (appendRev cp₁ cp₂) = true ↔
      plainConnectedSupported cp₁ = true ∧
        plainConnectedSupported cp₂ = true := by
  rw [plainConnectedSupported_appendRev]
  cases plainConnectedSupported cp₁ <;>
    cases plainConnectedSupported cp₂ <;> simp

theorem noReverse_appendRev :
    ∀ cp₁ cp₂ : CProg,
      noReverse (appendRev cp₁ cp₂) = (noReverse cp₁ && noReverse cp₂)
  | [], cp₂ => by
      simp [appendRev, noReverse]
  | s :: cp₁, cp₂ => by
      cases s with
      | rotate n =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.rotate n :: cp₂)
      | reverseRotate =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.reverseRotate :: cp₂)
      | y =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.y :: cp₂)
      | h =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.h :: cp₂)
      | u =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.u :: cp₂)
      | k =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.k :: cp₂)
      | a =>
          simpa [appendRev, noReverse] using
            noReverse_appendRev cp₁ (CpStep.a :: cp₂)

theorem noReverse_appendRev_eq_true_iff {cp₁ cp₂ : CProg} :
    noReverse (appendRev cp₁ cp₂) = true ↔
      noReverse cp₁ = true ∧ noReverse cp₂ = true := by
  rw [noReverse_appendRev]
  cases noReverse cp₁ <;> cases noReverse cp₂ <;> simp

end CProg

end Schematic.Math.GraphTheory.FourColor
