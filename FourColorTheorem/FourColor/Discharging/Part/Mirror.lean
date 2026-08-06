import FourColorTheorem.FourColor.Discharging.Part.Sequences

/-! Accessors and mirror symmetry for discharging parts. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PRange

namespace Part

/-- First spoke range, defaulting to the free range on empty parts. -/
def getSpoke : Part → PRange
  | Pcons s _ _ => s
  | Pcons6 _ _ _ => Pr66
  | Pcons7 _ _ _ _ => Pr77
  | Pcons8 _ _ _ _ _ => Pr88
  | Pnil => Pr59

/-- First hat range, with caller-provided default on empty parts. -/
def nextHat (h0 : PRange) : Part → PRange
  | Pnil => h0
  | Pcons _ h _ => h
  | Pcons6 h _ _ => h
  | Pcons7 h _ _ _ => h
  | Pcons8 h _ _ _ _ => h

/-- First hat range, defaulting to the free range. -/
def getHat (p : Part) : PRange :=
  nextHat Pr59 p

@[simp]
theorem nextHat_getHat (p : Part) :
    nextHat (getHat p) p = getHat p := by
  cases p <;> rfl

@[simp]
theorem nextHat_append (h0 : PRange) (p q : Part) :
    nextHat h0 (append p q) = nextHat (nextHat h0 q) p := by
  cases p <;> rfl

def getFan1r : Part → PRange
  | Pcons6 _ f1 _ => f1
  | Pcons7 _ f1 _ _ => f1
  | Pcons8 _ f1 _ _ _ => f1
  | _ => Pr59

def getFan2r : Part → PRange
  | Pcons7 _ _ f2 _ => f2
  | Pcons8 _ _ f2 _ _ => f2
  | _ => Pr59

def getFan3r : Part → PRange
  | Pcons8 _ _ _ f3 _ => f3
  | _ => Pr59

def getFan1l : Part → PRange
  | Pcons6 _ f1 _ => f1
  | Pcons7 _ _ f2 _ => f2
  | Pcons8 _ _ _ f3 _ => f3
  | _ => Pr59

def getFan2l : Part → PRange
  | Pcons7 _ f1 _ _ => f1
  | Pcons8 _ _ f2 _ _ => f2
  | _ => Pr59

def getFan3l : Part → PRange
  | Pcons8 _ f1 _ _ _ => f1
  | _ => Pr59

/-- Mirror image of a part, accumulated in reverse order. -/
def mirrorRec (h0 : PRange) : Part → Part → Part
  | rp, Pnil => rp
  | rp, Pcons s _ p => mirrorRec h0 (Pcons s (nextHat h0 p) rp) p
  | rp, Pcons6 _ f1 p => mirrorRec h0 (Pcons6 (nextHat h0 p) f1 rp) p
  | rp, Pcons7 _ f1 f2 p => mirrorRec h0 (Pcons7 (nextHat h0 p) f2 f1 rp) p
  | rp, Pcons8 _ f1 f2 f3 p =>
      mirrorRec h0 (Pcons8 (nextHat h0 p) f3 f2 f1 rp) p

/-- Mirror image of a part by reflection across the first spoke. -/
def mirror (p : Part) : Part :=
  mirrorRec (getHat p) Pnil p

theorem mirrorRec_append
    (h0 : PRange) (rp p q : Part) :
    mirrorRec h0 rp (append p q) =
      mirrorRec h0 (mirrorRec (nextHat h0 q) rp p) q := by
  induction p generalizing rp with
  | Pnil =>
      rfl
  | Pcons s _ p ih =>
      simp [append, mirrorRec]
      exact ih (Pcons s (nextHat (nextHat h0 q) p) rp)
  | Pcons6 _ f1 p ih =>
      simp [append, mirrorRec]
      exact ih (Pcons6 (nextHat (nextHat h0 q) p) f1 rp)
  | Pcons7 _ f1 f2 p ih =>
      simp [append, mirrorRec]
      exact ih (Pcons7 (nextHat (nextHat h0 q) p) f2 f1 rp)
  | Pcons8 _ f1 f2 f3 p ih =>
      simp [append, mirrorRec]
      exact ih (Pcons8 (nextHat (nextHat h0 q) p) f3 f2 f1 rp)

theorem mirrorRec_eq_append
    (h0 : PRange) (rp p : Part) :
    mirrorRec h0 rp p = append (mirrorRec h0 Pnil p) rp := by
  induction p generalizing rp with
  | Pnil =>
      rfl
  | Pcons s _ p ih =>
      simp [mirrorRec]
      rw [ih (Pcons s (nextHat h0 p) rp)]
      rw [ih (Pcons s (nextHat h0 p) Pnil)]
      change
        append (mirrorRec h0 Pnil p)
            (append (Pcons s (nextHat h0 p) Pnil) rp) =
          append (append (mirrorRec h0 Pnil p)
            (Pcons s (nextHat h0 p) Pnil)) rp
      exact (append_assoc (mirrorRec h0 Pnil p)
        (Pcons s (nextHat h0 p) Pnil) rp).symm
  | Pcons6 _ f1 p ih =>
      simp [mirrorRec]
      rw [ih (Pcons6 (nextHat h0 p) f1 rp)]
      rw [ih (Pcons6 (nextHat h0 p) f1 Pnil)]
      change
        append (mirrorRec h0 Pnil p)
            (append (Pcons6 (nextHat h0 p) f1 Pnil) rp) =
          append (append (mirrorRec h0 Pnil p)
            (Pcons6 (nextHat h0 p) f1 Pnil)) rp
      exact (append_assoc (mirrorRec h0 Pnil p)
        (Pcons6 (nextHat h0 p) f1 Pnil) rp).symm
  | Pcons7 _ f1 f2 p ih =>
      simp [mirrorRec]
      rw [ih (Pcons7 (nextHat h0 p) f2 f1 rp)]
      rw [ih (Pcons7 (nextHat h0 p) f2 f1 Pnil)]
      change
        append (mirrorRec h0 Pnil p)
            (append (Pcons7 (nextHat h0 p) f2 f1 Pnil) rp) =
          append (append (mirrorRec h0 Pnil p)
            (Pcons7 (nextHat h0 p) f2 f1 Pnil)) rp
      exact (append_assoc (mirrorRec h0 Pnil p)
        (Pcons7 (nextHat h0 p) f2 f1 Pnil) rp).symm
  | Pcons8 _ f1 f2 f3 p ih =>
      simp [mirrorRec]
      rw [ih (Pcons8 (nextHat h0 p) f3 f2 f1 rp)]
      rw [ih (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil)]
      change
        append (mirrorRec h0 Pnil p)
            (append (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) rp) =
          append (append (mirrorRec h0 Pnil p)
            (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil)) rp
      exact (append_assoc (mirrorRec h0 Pnil p)
        (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) rp).symm

@[simp]
theorem size_mirrorRec (h0 : PRange) (rp p : Part) :
    size (mirrorRec h0 rp p) = size rp + size p := by
  induction p generalizing rp with
  | Pnil =>
      simp [mirrorRec, size]
  | Pcons _ _ p ih =>
      simp [mirrorRec, size, ih]
      omega
  | Pcons6 _ _ p ih =>
      simp [mirrorRec, size, ih]
      omega
  | Pcons7 _ _ _ p ih =>
      simp [mirrorRec, size, ih]
      omega
  | Pcons8 _ _ _ _ p ih =>
      simp [mirrorRec, size, ih]
      omega

@[simp]
theorem size_mirror (p : Part) :
    size (mirror p) = size p := by
  rw [mirror, size_mirrorRec]
  simp [size]

theorem getHat_mirrorRec_of_ne_pnil
    (h0 : PRange) (rp p : Part)
    (hp : p ≠ Pnil) :
    getHat (mirrorRec h0 rp p) = h0 := by
  induction p generalizing rp with
  | Pnil =>
      exact False.elim (hp rfl)
  | Pcons s _ p ih =>
      by_cases htail : p = Pnil
      · subst p
        rfl
      · simpa [mirrorRec] using
          ih (Pcons s (nextHat h0 p) rp) htail
  | Pcons6 _ f1 p ih =>
      by_cases htail : p = Pnil
      · subst p
        rfl
      · simpa [mirrorRec] using
          ih (Pcons6 (nextHat h0 p) f1 rp) htail
  | Pcons7 _ f1 f2 p ih =>
      by_cases htail : p = Pnil
      · subst p
        rfl
      · simpa [mirrorRec] using
          ih (Pcons7 (nextHat h0 p) f2 f1 rp) htail
  | Pcons8 _ f1 f2 f3 p ih =>
      by_cases htail : p = Pnil
      · subst p
        rfl
      · simpa [mirrorRec] using
          ih (Pcons8 (nextHat h0 p) f3 f2 f1 rp) htail

@[simp]
theorem getHat_mirror (p : Part) :
    getHat (mirror p) = getHat p := by
  by_cases hp : p = Pnil
  · subst p
    rfl
  · exact getHat_mirrorRec_of_ne_pnil (getHat p) Pnil p hp

theorem mirrorRec_involutive_core
    (h0 : PRange) (p : Part) :
    mirrorRec (nextHat h0 p) Pnil (mirrorRec h0 Pnil p) = p := by
  induction p with
  | Pnil =>
      rfl
  | Pcons s _ p ih =>
      change mirrorRec _ Pnil
          (mirrorRec h0 (Pcons s (nextHat h0 p) Pnil) p) =
        Pcons s _ p
      rw [mirrorRec_eq_append
        (h0 := h0) (rp := Pcons s (nextHat h0 p) Pnil) (p := p)]
      rw [mirrorRec_append]
      change mirrorRec _
          (mirrorRec (nextHat h0 p) Pnil (mirrorRec h0 Pnil p))
          (Pcons s (nextHat h0 p) Pnil) =
        Pcons s _ p
      rw [ih]
      rfl
  | Pcons6 _ f1 p ih =>
      change mirrorRec _ Pnil
          (mirrorRec h0 (Pcons6 (nextHat h0 p) f1 Pnil) p) =
        Pcons6 _ f1 p
      rw [mirrorRec_eq_append
        (h0 := h0) (rp := Pcons6 (nextHat h0 p) f1 Pnil) (p := p)]
      rw [mirrorRec_append]
      change mirrorRec _
          (mirrorRec (nextHat h0 p) Pnil (mirrorRec h0 Pnil p))
          (Pcons6 (nextHat h0 p) f1 Pnil) =
        Pcons6 _ f1 p
      rw [ih]
      rfl
  | Pcons7 _ f1 f2 p ih =>
      change mirrorRec _ Pnil
          (mirrorRec h0 (Pcons7 (nextHat h0 p) f2 f1 Pnil) p) =
        Pcons7 _ f1 f2 p
      rw [mirrorRec_eq_append
        (h0 := h0) (rp := Pcons7 (nextHat h0 p) f2 f1 Pnil) (p := p)]
      rw [mirrorRec_append]
      change mirrorRec _
          (mirrorRec (nextHat h0 p) Pnil (mirrorRec h0 Pnil p))
          (Pcons7 (nextHat h0 p) f2 f1 Pnil) =
        Pcons7 _ f1 f2 p
      rw [ih]
      rfl
  | Pcons8 _ f1 f2 f3 p ih =>
      change mirrorRec _ Pnil
          (mirrorRec h0 (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) p) =
        Pcons8 _ f1 f2 f3 p
      rw [mirrorRec_eq_append
        (h0 := h0) (rp := Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) (p := p)]
      rw [mirrorRec_append]
      change mirrorRec _
          (mirrorRec (nextHat h0 p) Pnil (mirrorRec h0 Pnil p))
          (Pcons8 (nextHat h0 p) f3 f2 f1 Pnil) =
        Pcons8 _ f1 f2 f3 p
      rw [ih]
      rfl

@[simp]
theorem mirror_mirror (p : Part) :
    mirror (mirror p) = p := by
  rw [mirror]
  rw [getHat_mirror]
  change mirrorRec (getHat p) Pnil (mirrorRec (getHat p) Pnil p) = p
  nth_rewrite 1 [← nextHat_getHat p]
  exact mirrorRec_involutive_core (getHat p) p

theorem mirror_injective :
    Function.Injective mirror := by
  intro p q hpq
  calc
    p = mirror (mirror p) := (mirror_mirror p).symm
    _ = mirror (mirror q) := by rw [hpq]
    _ = q := mirror_mirror q

@[simp]
theorem mirror_eq_mirror_iff {p q : Part} :
    mirror p = mirror q ↔ p = q :=
  ⟨fun h => mirror_injective h, fun h => by rw [h]⟩

@[simp]
theorem nextHat_pconsN_Pr59 (n : Nat) :
    nextHat Pr59 (pconsN n) = Pr59 := by
  cases n <;> rfl

theorem mirrorRec_pconsN (m n : Nat) :
    mirrorRec Pr59 (pconsN m) (pconsN n) = pconsN (m + n) := by
  induction n generalizing m with
  | zero =>
      simp [pconsN, mirrorRec]
  | succ n ih =>
      rw [pconsN, mirrorRec, nextHat_pconsN_Pr59 n]
      change mirrorRec Pr59 (pconsN (m + 1)) (pconsN n) =
        pconsN (m + (n + 1))
      rw [ih (m + 1)]
      rw [show (m + 1) + n = m + (n + 1) by omega]

@[simp]
theorem getHat_pconsN (n : Nat) :
    getHat (pconsN n) = Pr59 := by
  cases n <;> rfl

@[simp]
theorem mirror_pconsN (n : Nat) :
    mirror (pconsN n) = pconsN n := by
  simpa [mirror, pconsN] using mirrorRec_pconsN 0 n

end Part

end FourColor

end Schematic.Math.GraphTheory
