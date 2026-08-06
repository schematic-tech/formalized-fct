
import Schematic.Math.GraphTheory.Embedding.Coloring
import FourColorTheorem.FourColor.Hypermap.EulerInequality
import Schematic.Math.GraphTheory.Embedding.Geometry
import FourColorTheorem.FourColor.Coloring.RingTrace
import Mathlib.Data.List.Cycle

/-!
Semantic hypermap patches.

This ports the common interface from Gonthier's `patch.v`.  A patch presents
`G` as a disk map `Gd` and a remainder map `Gr`.  Their images cover `G` and
meet exactly on a boundary which is an edge cycle on the disk side and a node
cycle on the remainder side.  The interface is deliberately asymmetric,
matching the cut and sew constructions used by `snip.v` and `sew.v`.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

/-- A path obtained by repeatedly applying one function. -/
def FunctionPath {α : Type _} (f : α → α) (x : α) : List α → Prop
  | [] => True
  | y :: ys => f x = y ∧ FunctionPath f y ys

/-- A cyclic listing for `f`, including MathComp's vacuous empty cycle. -/
def FunctionCycle {α : Type _} (f : α → α) : List α → Prop
  | [] => True
  | x :: xs => FunctionPath f x xs ∧ f ((x :: xs).getLastD x) = x

theorem List.next_map_injective
    {α β : Type _} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (l : List α) (hn : l.Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).next (f x) (List.mem_map_of_mem hx) =
      f (l.next x hx) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiMap : i < (l.map f).length := by simpa using hi
  have hMap := List.next_getElem (l.map f) (hn.map hf) i hiMap
  have hSource := congrArg f (List.next_getElem l hn i hi)
  have hmod : (i + 1) % l.length < l.length :=
    Nat.mod_lt _ (Nat.zero_lt_of_lt hi)
  have hMap' :
      (l.map f).next (f l[i])
          (List.mem_map_of_mem (List.getElem_mem hi)) =
        f (l[(i + 1) % l.length]'(hmod)) := by
    simpa only [List.length_map, List.getElem_map] using hMap
  exact hMap'.trans hSource.symm

theorem List.prev_map_injective
    {α β : Type _} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (l : List α) (hn : l.Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).prev (f x) (List.mem_map_of_mem hx) =
      f (l.prev x hx) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiMap : i < (l.map f).length := by simpa using hi
  have hMap := List.prev_getElem (l.map f) (hn.map hf) i hiMap
  have hSource := congrArg f (List.prev_getElem l hn i hi)
  have hmod :
      (i + (l.length - 1)) % l.length < l.length :=
    Nat.mod_lt _ (Nat.zero_lt_of_lt hi)
  have hMap' :
      (l.map f).prev (f l[i])
          (List.mem_map_of_mem (List.getElem_mem hi)) =
        f (l[(i + (l.length - 1)) % l.length]'(hmod)) := by
    simpa only [List.length_map, List.getElem_map] using hMap
  exact hMap'.trans hSource.symm

namespace FunctionPath

theorem of_isChain
    {α : Type _} {f : α → α} {x : α} {xs : List α}
    (hc : List.IsChain (fun y z => f y = z) (x :: xs)) :
    FunctionPath f x xs := by
  induction xs generalizing x with
  | nil => simp [FunctionPath]
  | cons y ys ih =>
      cases hc with
      | cons_cons hxy htail => exact ⟨hxy, ih htail⟩

theorem isChain
    {α : Type _} {f : α → α} {x : α} {xs : List α}
    (hp : FunctionPath f x xs) :
    List.IsChain (fun y z => f y = z) (x :: xs) := by
  induction xs generalizing x with
  | nil => exact .singleton x
  | cons y ys ih =>
      rcases hp with ⟨hxy, hp⟩
      exact .cons_cons hxy (ih hp)

theorem map
    {α β : Type _} {f : α → α} {g : β → β} {e : α → β}
    {x : α} {xs : List α}
    (hp : FunctionPath f x xs)
    (hcomm : ∀ y ∈ x :: xs, g (e y) = e (f y)) :
    FunctionPath g (e x) (xs.map e) := by
  induction xs generalizing x with
  | nil => simp [FunctionPath]
  | cons y ys ih =>
      rcases hp with ⟨hxy, hp⟩
      refine ⟨?_, ih hp ?_⟩
      · rw [hcomm x (by simp), hxy]
      · intro z hz
        exact hcomm z (List.mem_cons_of_mem x hz)

theorem image_mem_or_eq_last
    {α : Type _} {f : α → α} {x y : α} {xs : List α}
    (hp : FunctionPath f x xs) (hy : y ∈ x :: xs) :
    f y ∈ x :: xs ∨ y = (x :: xs).getLastD x := by
  induction xs generalizing x with
  | nil =>
      simp at hy
      subst y
      exact Or.inr (by simp [List.getLastD])
  | cons z zs ih =>
      have hp' : f x = z ∧ FunctionPath f z zs := by
        simpa [FunctionPath] using hp
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Or.inl (by simp [hp'.1])
      · rcases ih hp'.2 hy with hmem | hlast
        · exact Or.inl (List.mem_cons_of_mem x hmem)
        · exact Or.inr (by simpa [List.getLastD] using hlast)

theorem permReachable_of_mem
    {α : Type _} {σ : Equiv.Perm α} {x y : α} {xs : List α}
    (hp : FunctionPath σ x xs) (hy : y ∈ x :: xs) :
    PermReachable σ x y := by
  induction xs generalizing x with
  | nil =>
      simp at hy
      subst y
      exact PermReachable.refl σ x
  | cons z zs ih =>
      rcases hp with ⟨hxz, hp⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Relation.ReflTransGen.refl
      · have hxzReach : PermReachable σ x z := by
          simpa [hxz] using PermReachable.forward σ x
        exact PermReachable.trans σ hxzReach (ih hp hy)

end FunctionPath

namespace FunctionCycle

/-- A duplicate-free list is a cycle for its cyclic successor function. -/
theorem of_eq_next
    {α : Type _} [DecidableEq α] {f : α → α} {r : List α}
    (hn : r.Nodup)
    (hnext : ∀ x : α, ∀ hx : x ∈ r, f x = r.next x hx) :
    FunctionCycle f r := by
  cases r with
  | nil => simp [FunctionCycle]
  | cons x xs =>
      have hchain :
          List.IsChain (fun y z => f y = z) (x :: xs) := by
        rw [List.isChain_iff_getElem]
        intro i hi
        have hi0 : i < (x :: xs).length := Nat.lt_of_succ_lt hi
        have himem : (x :: xs)[i] ∈ x :: xs := List.getElem_mem hi0
        have hcyclic := List.next_getElem (x :: xs) hn i hi0
        exact (hnext _ himem).trans (by
          convert hcyclic using 1
          exact getElem_congr rfl (Nat.mod_eq_of_lt hi).symm hi)
      constructor
      · exact FunctionPath.of_isChain hchain
      · have hlastMem : (x :: xs).getLastD x ∈ x :: xs := by
          simp [List.getLastD]
        calc
          f ((x :: xs).getLastD x) =
              (x :: xs).next ((x :: xs).getLastD x) hlastMem :=
            hnext _ hlastMem
          _ = x := by
            simpa [List.getLastD, List.head_eq_getElem] using
              List.next_getLast_eq_head (x :: xs)
                (List.cons_ne_nil x xs) hn

theorem isChain
    {α : Type _} {f : α → α} {r : List α}
    (hc : FunctionCycle f r) :
    List.IsChain (fun x y => f x = y) r := by
  cases r with
  | nil => exact .nil
  | cons x xs => exact hc.1.isChain

theorem map
    {α β : Type _} {f : α → α} {g : β → β} {e : α → β}
    {r : List α}
    (hc : FunctionCycle f r)
    (hcomm : ∀ x ∈ r, g (e x) = e (f x)) :
    FunctionCycle g (r.map e) := by
  cases r with
  | nil => simp [FunctionCycle]
  | cons x xs =>
      constructor
      · exact hc.1.map fun y hy => hcomm y hy
      · have hlast : (x :: xs).getLastD x ∈ x :: xs := by
          simp [List.getLastD]
        have map_getLast (y : α) (ys : List α) :
            ((y :: ys).map e).getLast (by simp) =
              e ((y :: ys).getLast (by simp)) := by
          induction ys generalizing y with
          | nil => simp
          | cons z zs ih =>
              simpa using ih z
        have hgetLast :
            ((x :: xs).map e).getLastD (e x) =
              e ((x :: xs).getLastD x) := by
          cases xs with
          | nil => simp [List.getLastD]
          | cons y ys => simpa [List.getLastD] using map_getLast y ys
        calc
          g ((x :: xs).map e |>.getLastD (e x)) =
              g (e ((x :: xs).getLastD x)) := congrArg g hgetLast
          _ = e (f ((x :: xs).getLastD x)) := hcomm _ hlast
          _ = e x := by rw [hc.2]

/-- On a duplicate-free function cycle, the cycling function is the list's
cyclic successor operation. -/
theorem eq_next
    {α : Type _} [DecidableEq α] {f : α → α} {r : List α}
    (hc : FunctionCycle f r) (hn : r.Nodup)
    (x : α) (hx : x ∈ r) :
    f x = r.next x hx := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem r hn i hi]
  by_cases hsucc : i + 1 < r.length
  · simp only [Nat.mod_eq_of_lt hsucc]
    exact (List.isChain_iff_getElem.mp hc.isChain) i hsucc
  · have hlast : i + 1 = r.length := by omega
    have hmod : (i + 1) % r.length = 0 := by rw [hlast, Nat.mod_self]
    simp only [hmod]
    cases r with
    | nil => simp at hi
    | cons y ys =>
        have hi' : i = ys.length := by simpa using hlast
        subst i
        simpa [List.getLastD, List.getLast_eq_getElem,
          List.head_eq_getElem] using hc.2

theorem image_mem
    {α : Type _} {f : α → α} {r : List α}
    (hc : FunctionCycle f r) {x : α} (hx : x ∈ r) :
    f x ∈ r := by
  cases r with
  | nil => simp at hx
  | cons y ys =>
      rcases FunctionPath.image_mem_or_eq_last hc.1 hx with hmem | hlast
      · exact hmem
      · rw [hlast, hc.2]
        simp

theorem image_mem_iff
    {α : Type _} [DecidableEq α] {f : α → α} {r : List α}
    (hc : FunctionCycle f r) (hinj : Function.Injective f) (x : α) :
    f x ∈ r ↔ x ∈ r := by
  let s : Finset α := r.toFinset
  have hsub : s.image f ⊆ s := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact List.mem_toFinset.mpr
      (hc.image_mem (List.mem_toFinset.mp hy))
  have hcard : (s.image f).card = s.card :=
    Finset.card_image_of_injective s hinj
  have heq : s.image f = s :=
    Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcard.symm)
  constructor
  · intro hfx
    have hmem : f x ∈ s.image f := by
      rw [heq]
      exact List.mem_toFinset.mpr hfx
    rcases Finset.mem_image.mp hmem with ⟨y, hy, hyx⟩
    have : y = x := hinj hyx
    simpa [this] using List.mem_toFinset.mp hy
  · exact hc.image_mem

theorem permReachable_of_mem_mem
    {α : Type _} {σ : Equiv.Perm α} {r : List α}
    (hc : FunctionCycle σ r) {x y : α}
    (hx : x ∈ r) (hy : y ∈ r) :
    PermReachable σ x y := by
  cases r with
  | nil => simp at hx
  | cons z zs =>
      have hzx : PermReachable σ z x := hc.1.permReachable_of_mem hx
      have hzy : PermReachable σ z y := hc.1.permReachable_of_mem hy
      exact PermReachable.trans σ (PermReachable.symm σ hzx) hzy

/-- The functions cycling a duplicate-free list in its two orientations are
mutual inverses on the listed elements. -/
theorem reverse_leftInverse
    {α : Type _} [DecidableEq α] {f g : α → α} {r : List α}
    (hf : FunctionCycle f r) (hg : FunctionCycle g r.reverse)
    (hn : r.Nodup) {x : α} (hx : x ∈ r) :
    g (f x) = x := by
  have hfx : f x ∈ r := hf.image_mem hx
  have hnext : r.next x hx ∈ r := List.next_mem r x hx
  have hsub :
      (⟨f x, hfx⟩ : {y // y ∈ r}) = ⟨r.next x hx, hnext⟩ :=
    Subtype.ext (hf.eq_next hn x hx)
  have hprev :
      r.prev (f x) hfx = r.prev (r.next x hx) hnext :=
    congrArg (fun y : {z // z ∈ r} => r.prev y.1 y.2) hsub
  calc
    g (f x) = r.reverse.next (f x) (List.mem_reverse.mpr hfx) :=
      hg.eq_next (List.nodup_reverse.mpr hn) _ _
    _ = r.prev (f x) hfx := List.next_reverse_eq_prev r hn _ _
    _ = r.prev (r.next x hx) hnext := hprev
    _ = x := List.prev_next r hn x hx

theorem reverse_rightInverse
    {α : Type _} [DecidableEq α] {f g : α → α} {r : List α}
    (hf : FunctionCycle f r) (hg : FunctionCycle g r.reverse)
    (hn : r.Nodup) {x : α} (hx : x ∈ r) :
    f (g x) = x := by
  have hx' : x ∈ r.reverse := List.mem_reverse.mpr hx
  have hf' : FunctionCycle f r.reverse.reverse := by simpa using hf
  exact hg.reverse_leftInverse hf' (List.nodup_reverse.mpr hn) hx'

end FunctionCycle
end FourColor

end Schematic.Math.GraphTheory
