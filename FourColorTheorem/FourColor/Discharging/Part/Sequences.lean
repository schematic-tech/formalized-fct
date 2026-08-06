import FourColorTheorem.FourColor.Discharging.Part.Ranges

/-! Sequence operations on discharging parts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Part

/-- Number of subparts, i.e. the constrained hub arity. -/
def size : Part → Nat
  | Pnil => 0
  | Pcons _ _ p => size p + 1
  | Pcons6 _ _ p => size p + 1
  | Pcons7 _ _ _ p => size p + 1
  | Pcons8 _ _ _ _ p => size p + 1

@[simp]
theorem size_eq_zero {p : Part} :
    size p = 0 ↔ p = Pnil := by
  cases p <;> simp [size]

@[simp]
theorem size_pos_iff_ne_pnil {p : Part} :
    0 < size p ↔ p ≠ Pnil := by
  cases p <;> simp [size]

@[simp]
theorem size_pconsN : ∀ n : Nat, size (pconsN n) = n
  | 0 => rfl
  | n + 1 => by simp [pconsN, size, size_pconsN n]

/-- Drop the first `n` subparts. -/
def drop : Nat → Part → Part
  | n + 1, Pcons _ _ p => drop n p
  | n + 1, Pcons6 _ _ p => drop n p
  | n + 1, Pcons7 _ _ _ p => drop n p
  | n + 1, Pcons8 _ _ _ _ p => drop n p
  | _, p => p

/-- Keep the first `n` subparts. -/
def take : Nat → Part → Part
  | n + 1, Pcons s h p => Pcons s h (take n p)
  | n + 1, Pcons6 h f1 p => Pcons6 h f1 (take n p)
  | n + 1, Pcons7 h f1 f2 p => Pcons7 h f1 f2 (take n p)
  | n + 1, Pcons8 h f1 f2 f3 p => Pcons8 h f1 f2 f3 (take n p)
  | _, _ => Pnil

/-- Concatenate two parts. -/
def append : Part → Part → Part
  | Pcons s h p, q => Pcons s h (append p q)
  | Pcons6 h f1 p, q => Pcons6 h f1 (append p q)
  | Pcons7 h f1 f2 p, q => Pcons7 h f1 f2 (append p q)
  | Pcons8 h f1 f2 f3 p, q => Pcons8 h f1 f2 f3 (append p q)
  | Pnil, q => q

/-- Rotate a part by `n` subparts. -/
def rotate (n : Nat) (p : Part) : Part :=
  append (drop n p) (take n p)

@[simp]
theorem size_append (p q : Part) :
    size (append p q) = size p + size q := by
  induction p with
  | Pnil => simp [append, size]
  | Pcons _ _ p ih =>
      simp [append, size, ih]
      omega
  | Pcons6 _ _ p ih =>
      simp [append, size, ih]
      omega
  | Pcons7 _ _ _ p ih =>
      simp [append, size, ih]
      omega
  | Pcons8 _ _ _ _ p ih =>
      simp [append, size, ih]
      omega

@[simp]
theorem size_drop (n : Nat) (p : Part) :
    size (drop n p) = size p - n := by
  induction n generalizing p with
  | zero =>
      cases p <;> simp [drop]
  | succ n ih =>
      cases p <;> simp [drop, size, ih]

theorem append_take_drop (n : Nat) (p : Part) :
    append (take n p) (drop n p) = p := by
  induction n generalizing p with
  | zero =>
      cases p <;> rfl
  | succ n ih =>
      cases p <;> simp [take, drop, append, ih]

@[simp]
theorem drop_size_append (p q : Part) :
    drop (size p) (append p q) = q := by
  induction p with
  | Pnil =>
      rfl
  | Pcons _ _ p ih =>
      simpa [size, append, drop] using ih
  | Pcons6 _ _ p ih =>
      simpa [size, append, drop] using ih
  | Pcons7 _ _ _ p ih =>
      simpa [size, append, drop] using ih
  | Pcons8 _ _ _ _ p ih =>
      simpa [size, append, drop] using ih

@[simp]
theorem take_size_append (p q : Part) :
    take (size p) (append p q) = p := by
  induction p with
  | Pnil =>
      rfl
  | Pcons _ _ p ih =>
      simp [size, append, take, ih]
  | Pcons6 _ _ p ih =>
      simp [size, append, take, ih]
  | Pcons7 _ _ _ p ih =>
      simp [size, append, take, ih]
  | Pcons8 _ _ _ _ p ih =>
      simp [size, append, take, ih]

theorem size_take_add_size_drop (n : Nat) (p : Part) :
    size (take n p) + size (drop n p) = size p := by
  have h := congrArg size (append_take_drop n p)
  simpa [size_append] using h

theorem size_take_of_le {n : Nat} {p : Part}
    (h : n ≤ size p) :
    size (take n p) = n := by
  have hsum := size_take_add_size_drop n p
  simp [size_drop] at hsum
  omega

@[simp]
theorem append_pnil (p : Part) :
    append p Pnil = p := by
  induction p with
  | Pnil => rfl
  | Pcons _ _ p ih => simp [append, ih]
  | Pcons6 _ _ p ih => simp [append, ih]
  | Pcons7 _ _ _ p ih => simp [append, ih]
  | Pcons8 _ _ _ _ p ih => simp [append, ih]

@[simp]
theorem append_assoc (p q r : Part) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | Pnil =>
      rfl
  | Pcons _ _ p ih =>
      simp [append, ih]
  | Pcons6 _ _ p ih =>
      simp [append, ih]
  | Pcons7 _ _ _ p ih =>
      simp [append, ih]
  | Pcons8 _ _ _ _ p ih =>
      simp [append, ih]

@[simp]
theorem size_rotate (n : Nat) (p : Part) :
    size (rotate n p) = size p := by
  rw [rotate, size_append]
  have h := size_take_add_size_drop n p
  omega

@[simp]
theorem rotate_zero (p : Part) :
    rotate 0 p = p := by
  simp [rotate, drop, take]

theorem drop_eq_pnil_of_size_le :
    ∀ (n : Nat) (p : Part), size p ≤ n → drop n p = Pnil := by
  intro n
  induction n with
  | zero =>
      intro p h
      cases p <;> simp [size, drop] at h ⊢
  | succ n ih =>
      intro p h
      cases p <;> simp [size, drop] at h ⊢
      · exact ih _ (by omega)
      · exact ih _ (by omega)
      · exact ih _ (by omega)
      · exact ih _ (by omega)

theorem take_eq_self_of_size_le (n : Nat) (p : Part)
    (h : size p ≤ n) :
    take n p = p := by
  have hcat := append_take_drop n p
  rw [drop_eq_pnil_of_size_le n p h] at hcat
  simpa using hcat

theorem rotate_eq_self_of_size_le (n : Nat) (p : Part)
    (h : size p ≤ n) :
    rotate n p = p := by
  rw [rotate, drop_eq_pnil_of_size_le n p h,
    take_eq_self_of_size_le n p h]
  rfl

theorem rotate_size_sub_rotate (n : Nat) (p : Part) :
    rotate (size p - n) (rotate n p) = p := by
  have hsizeDrop : size (drop n p) = size p - n := by
    simp
  rw [rotate]
  rw [rotate]
  rw [show drop (size p - n) (append (drop n p) (take n p)) = take n p by
    simpa [hsizeDrop] using drop_size_append (drop n p) (take n p)]
  rw [show take (size p - n) (append (drop n p) (take n p)) = drop n p by
    simpa [hsizeDrop] using take_size_append (drop n p) (take n p)]
  exact append_take_drop n p

/-- Reverse-append, used by zipped part operations. -/
def reverseAppend : Part → Part → Part
  | Pnil, q => q
  | Pcons s h p, q => reverseAppend p (Pcons s h q)
  | Pcons6 h f1 p, q => reverseAppend p (Pcons6 h f1 q)
  | Pcons7 h f1 f2 p, q => reverseAppend p (Pcons7 h f1 f2 q)
  | Pcons8 h f1 f2 f3 p, q => reverseAppend p (Pcons8 h f1 f2 f3 q)

/-- Reverse the subpart order. -/
def reverse (p : Part) : Part :=
  reverseAppend p Pnil

theorem reverseAppend_eq_append_reverse (p q : Part) :
    reverseAppend p q = append (reverse p) q := by
  induction p generalizing q with
  | Pnil =>
      rfl
  | Pcons s h p ih =>
      calc
        reverseAppend (Pcons s h p) q =
            reverseAppend p (Pcons s h q) := rfl
        _ = append (reverse p) (Pcons s h q) := ih _
        _ = append (append (reverse p) (Pcons s h Pnil)) q := by
          simp [append_assoc, append]
        _ = append (reverse (Pcons s h p)) q := by
          have hrev :
              reverse (Pcons s h p) =
                append (reverse p) (Pcons s h Pnil) := ih _
          rw [hrev]
  | Pcons6 h f1 p ih =>
      calc
        reverseAppend (Pcons6 h f1 p) q =
            reverseAppend p (Pcons6 h f1 q) := rfl
        _ = append (reverse p) (Pcons6 h f1 q) := ih _
        _ = append (append (reverse p) (Pcons6 h f1 Pnil)) q := by
          simp [append_assoc, append]
        _ = append (reverse (Pcons6 h f1 p)) q := by
          have hrev :
              reverse (Pcons6 h f1 p) =
                append (reverse p) (Pcons6 h f1 Pnil) := ih _
          rw [hrev]
  | Pcons7 h f1 f2 p ih =>
      calc
        reverseAppend (Pcons7 h f1 f2 p) q =
            reverseAppend p (Pcons7 h f1 f2 q) := rfl
        _ = append (reverse p) (Pcons7 h f1 f2 q) := ih _
        _ = append (append (reverse p) (Pcons7 h f1 f2 Pnil)) q := by
          simp [append_assoc, append]
        _ = append (reverse (Pcons7 h f1 f2 p)) q := by
          have hrev :
              reverse (Pcons7 h f1 f2 p) =
                append (reverse p) (Pcons7 h f1 f2 Pnil) := ih _
          rw [hrev]
  | Pcons8 h f1 f2 f3 p ih =>
      calc
        reverseAppend (Pcons8 h f1 f2 f3 p) q =
            reverseAppend p (Pcons8 h f1 f2 f3 q) := rfl
        _ = append (reverse p) (Pcons8 h f1 f2 f3 q) := ih _
        _ = append (append (reverse p) (Pcons8 h f1 f2 f3 Pnil)) q := by
          simp [append_assoc, append]
        _ = append (reverse (Pcons8 h f1 f2 f3 p)) q := by
          have hrev :
              reverse (Pcons8 h f1 f2 f3 p) =
                append (reverse p) (Pcons8 h f1 f2 f3 Pnil) := ih _
          rw [hrev]

theorem reverseAppend_append (p q r : Part) :
    reverseAppend (append p q) r = reverseAppend q (reverseAppend p r) := by
  induction p generalizing q r with
  | Pnil =>
      rfl
  | Pcons s h p ih =>
      simpa [append, reverseAppend] using ih q (Pcons s h r)
  | Pcons6 h f1 p ih =>
      simpa [append, reverseAppend] using ih q (Pcons6 h f1 r)
  | Pcons7 h f1 f2 p ih =>
      simpa [append, reverseAppend] using ih q (Pcons7 h f1 f2 r)
  | Pcons8 h f1 f2 f3 p ih =>
      simpa [append, reverseAppend] using ih q (Pcons8 h f1 f2 f3 r)

theorem reverse_append (p q : Part) :
    reverse (append p q) = reverseAppend q (reverse p) := by
  simp [reverse, reverseAppend_append]

@[simp]
theorem reverse_reverse (p : Part) :
    reverse (reverse p) = p := by
  induction p with
  | Pnil =>
      rfl
  | Pcons s h p ih =>
      change reverse (reverseAppend p (Pcons s h Pnil)) = Pcons s h p
      rw [reverseAppend_eq_append_reverse, reverse_append]
      simp [reverseAppend, ih]
  | Pcons6 h f1 p ih =>
      change reverse (reverseAppend p (Pcons6 h f1 Pnil)) = Pcons6 h f1 p
      rw [reverseAppend_eq_append_reverse, reverse_append]
      simp [reverseAppend, ih]
  | Pcons7 h f1 f2 p ih =>
      change reverse (reverseAppend p (Pcons7 h f1 f2 Pnil)) = Pcons7 h f1 f2 p
      rw [reverseAppend_eq_append_reverse, reverse_append]
      simp [reverseAppend, ih]
  | Pcons8 h f1 f2 f3 p ih =>
      change reverse (reverseAppend p (Pcons8 h f1 f2 f3 Pnil)) =
        Pcons8 h f1 f2 f3 p
      rw [reverseAppend_eq_append_reverse, reverse_append]
      simp [reverseAppend, ih]

@[simp]
theorem reverseAppend_reverse (p q : Part) :
    reverseAppend (reverse p) q = append p q := by
  rw [reverseAppend_eq_append_reverse, reverse_reverse]

@[simp]
theorem size_reverseAppend (p q : Part) :
    size (reverseAppend p q) = size p + size q := by
  induction p generalizing q with
  | Pnil => simp [reverseAppend, size]
  | Pcons _ _ p ih =>
      simp [reverseAppend, size, ih]
      omega
  | Pcons6 _ _ p ih =>
      simp [reverseAppend, size, ih]
      omega
  | Pcons7 _ _ _ p ih =>
      simp [reverseAppend, size, ih]
      omega
  | Pcons8 _ _ _ _ p ih =>
      simp [reverseAppend, size, ih]
      omega

@[simp]
theorem size_reverse (p : Part) :
    size (reverse p) = size p := by
  rw [reverse, size_reverseAppend]
  simp [size]

end Part

end FourColor

end Schematic.Math.GraphTheory
