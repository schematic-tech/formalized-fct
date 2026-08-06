import FourColorTheorem.FourColor.Configuration.Encoding.MaskSelection.Counting

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CfMask
/-- Generic `cpmask`-style selection from ring and kernel lists.  The semantic
`cpmask` will instantiate these lists with the concrete ring and kernel
transversals once those are available. -/
def selectMask {α : Type _} (m : CfMask) (ring kernel : List α) : List α :=
  select m.ring ring ++ select m.kernel kernel

/-- Coq-name alias for generic `cpmask` selection once concrete ring/kernel
lists are supplied. -/
abbrev cpmask {α : Type _} : CfMask → List α → List α → List α := selectMask

theorem selectMask_map {α β : Type _}
    (f : α → β) (m : CfMask) (ring kernel : List α) :
    selectMask m (ring.map f) (kernel.map f) =
      (selectMask m ring kernel).map f := by
  simp [selectMask, select_map, List.map_append]

theorem selectMask_cons_ring {α : Type _}
    (b : Bool) (mr ks : List Bool) (x : α)
    (ring kernel : List α) :
    selectMask (⟨b :: mr, ks⟩ : CfMask) (x :: ring) kernel =
      (if b then [x] else []) ++
        selectMask (⟨mr, ks⟩ : CfMask) ring kernel := by
  cases b <;> rfl

theorem selectMask_cons_cons_ring {α : Type _}
    (b0 b1 : Bool) (mr ks : List Bool) (x y : α)
    (ring kernel : List α) :
    selectMask (⟨b0 :: b1 :: mr, ks⟩ : CfMask) (x :: y :: ring) kernel =
      (if b0 then [x] else []) ++
        (if b1 then [y] else []) ++
          selectMask (⟨mr, ks⟩ : CfMask) ring kernel := by
  cases b0 <;> cases b1 <;> rfl

theorem selectMask_cons_kernel {α : Type _}
    (b : Bool) (mr ks : List Bool) (x : α)
    (ring kernel : List α) :
    selectMask (⟨mr, b :: ks⟩ : CfMask) ring (x :: kernel) =
      select mr ring ++ (if b then [x] else []) ++ select ks kernel := by
  cases b <;> simp [selectMask, select, List.append_assoc]

theorem selectMask_cons_ring_cons_kernel {α : Type _}
    (br bk : Bool) (mr ks : List Bool) (x y : α)
    (ring kernel : List α) :
    selectMask (⟨br :: mr, bk :: ks⟩ : CfMask) (x :: ring) (y :: kernel) =
      (if br then [x] else []) ++
        select mr ring ++ (if bk then [y] else []) ++ select ks kernel := by
  cases br <;> cases bk <;> simp [selectMask, select, List.append_assoc]

theorem mem_selectMask_map_iff_of_injective {α β : Type _}
    {f : α → β} (hf : Function.Injective f)
    (m : CfMask) (ring kernel : List α) {x : α} :
    f x ∈ selectMask m (ring.map f) (kernel.map f) ↔
      x ∈ selectMask m ring kernel := by
  rw [selectMask_map]
  exact List.mem_map_of_injective hf

theorem mem_two_prefixes_map_iff_of_injective {α β : Type _}
    {f : α → β} (hf : Function.Injective f) {x : α} {a b : β}
    (ha : f x ≠ a) (hb : f x ≠ b)
    (b0 b1 : Bool) (xs : List α) :
    f x ∈ (if b0 then [a] else []) ++ (if b1 then [b] else []) ++ xs.map f ↔
      x ∈ xs := by
  cases b0 <;> cases b1 <;>
    simp [ha, hb, List.mem_map_of_injective hf]

theorem mem_of_mem_selectMask {α : Type _}
    {m : CfMask} {ring kernel : List α} {x : α}
    (hx : x ∈ selectMask m ring kernel) :
    x ∈ ring ∨ x ∈ kernel := by
  rw [selectMask, List.mem_append] at hx
  rcases hx with hx | hx
  · exact Or.inl (mem_of_mem_select hx)
  · exact Or.inr (mem_of_mem_select hx)

theorem length_selectMask_le {α : Type _}
    (m : CfMask) (ring kernel : List α) :
    (selectMask m ring kernel).length ≤ ring.length + kernel.length := by
  unfold selectMask
  simp only [List.length_append]
  have hr := length_select_le m.ring ring
  have hk := length_select_le m.kernel kernel
  omega

theorem length_selectMask_eq_countTrue_of_lengths {α : Type _}
    (m : CfMask) {ring kernel : List α}
    (hr : ring.length = m.ring.length)
    (hk : kernel.length = m.kernel.length) :
    (selectMask m ring kernel).length =
      countTrue m.ring + countTrue m.kernel := by
  unfold selectMask
  simp [length_select_eq_countTrue_of_length m.ring ring hr,
    length_select_eq_countTrue_of_length m.kernel kernel hk]

theorem length_selectMask_eq_countTrue_of_proper {α : Type _}
    {cp : CProg} {m : CfMask} (hm : Proper cp m)
    {ring kernel : List α}
    (hr : ring.length = CProg.ringSize cp)
    (hk : kernel.length = CProg.kernelSize cp) :
    (selectMask m ring kernel).length =
      countTrue m.ring + countTrue m.kernel := by
  exact length_selectMask_eq_countTrue_of_lengths m
    (by rw [hr, hm.1])
    (by rw [hk, hm.2])

theorem mem_selectMask_rotateLeft_ring_iff_of_length {α : Type _}
    (n : Nat) {m : CfMask} {ring kernel : List α} {x : α}
    (hr : ring.length = m.ring.length) :
    x ∈ selectMask ⟨CProg.rotateLeft n m.ring, m.kernel⟩
        (CProg.rotateLeft n ring) kernel ↔
      x ∈ selectMask m ring kernel := by
  unfold selectMask
  rw [List.mem_append, List.mem_append]
  exact or_congr
    (mem_select_rotateLeft_iff_of_length (α := α) n hr)
    Iff.rfl

theorem mem_selectMask_rotateRight_ring_iff_of_length {α : Type _}
    (n : Nat) {m : CfMask} {ring kernel : List α} {x : α}
    (hr : ring.length = m.ring.length) :
    x ∈ selectMask ⟨CProg.rotateRight n m.ring, m.kernel⟩
        (CProg.rotateRight n ring) kernel ↔
      x ∈ selectMask m ring kernel := by
  unfold selectMask
  rw [List.mem_append, List.mem_append]
  exact or_congr
    (mem_select_rotateRight_iff_of_length (α := α) n hr)
    Iff.rfl

theorem mem_selectMask_rotateRight_ring_rotateLeft_values_iff_of_length
    {α : Type _}
    (n : Nat) {m : CfMask} {ring kernel : List α} {x : α}
    (hr : ring.length = m.ring.length) :
    x ∈ selectMask ⟨CProg.rotateRight n m.ring, m.kernel⟩
        ring kernel ↔
      x ∈ selectMask m (CProg.rotateLeft n ring) kernel := by
  unfold selectMask
  rw [List.mem_append, List.mem_append]
  exact or_congr
    (mem_select_rotateRight_mask_rotateLeft_values_iff_of_length
      (α := α) n hr)
    Iff.rfl

theorem selectMask_ring_of_kernelSingleton {α : Type _}
    (cp : CProg) (i : Nat) (ring : List α) :
    select (kernelSingleton cp i).ring ring = [] := by
  simp [kernelSingleton, select_replicate_false]

/-- The generic `cfmask1`/kernel-singleton mask never selects a ring entry. -/
theorem cpmask1_no_ring {α : Type _}
    (cp : CProg) (i : Nat) (ring kernel : List α) :
    cpmask (cfmask1 cp i) ring kernel =
      select (cfmask1 cp i).kernel kernel := by
  simp [cpmask, selectMask, cfmask1, selectMask_ring_of_kernelSingleton]

/-- The singleton kernel mask selects exactly the indexed kernel entry when the
provided kernel list has the program's kernel size. -/
theorem cpmask1_kernel_getElem? {α : Type _}
    (cp : CProg) (i : Nat) (kernel : List α)
    (hkernel : kernel.length = CProg.kernelSize cp) :
    select (cfmask1 cp i).kernel kernel =
      match kernel[i]? with
      | some x => [x]
      | none => [] := by
  simpa [cfmask1, kernelSingleton, hkernel] using
    select_kernelIndex_getElem? kernel i

/-- Coq `cpmask1` specialized to explicit ring/kernel lists. -/
theorem cpmask1_getElem?_of_kernel_length {α : Type _}
    (cp : CProg) (i : Nat) (ring kernel : List α)
    (hkernel : kernel.length = CProg.kernelSize cp) :
    cpmask (cfmask1 cp i) ring kernel =
      match kernel[i]? with
      | some x => [x]
      | none => [] := by
  rw [cpmask1_no_ring]
  exact cpmask1_kernel_getElem? cp i kernel hkernel

end CfMask

end FourColor

end Schematic.Math.GraphTheory
