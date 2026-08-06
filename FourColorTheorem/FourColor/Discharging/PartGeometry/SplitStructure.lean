import FourColorTheorem.FourColor.Discharging.PartGeometry.Foundations

namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}

theorem contains_of_splitRange_of_goodRSplit
    (k : Nat) (lo : Bool) (r : PRange) {n : Nat}
    (hgood : goodRSplit k r = true)
    (h : splitRange k lo r n = true) :
    r n = true :=
  ((splitRange_eq_true_iff_of_goodRSplit k lo r hgood).mp h).1

theorem splitCondition_of_splitRange_of_goodRSplit
    (k : Nat) (lo : Bool) (r : PRange) {n : Nat}
    (hgood : goodRSplit k r = true)
    (h : splitRange k lo r n = true) :
    splitCondition k lo n = true :=
  ((splitRange_eq_true_iff_of_goodRSplit k lo r hgood).mp h).2

theorem splitRange_of_splitCondition_of_contains_of_goodRSplit
    (k : Nat) (lo : Bool) (r : PRange) {n : Nat}
    (hgood : goodRSplit k r = true)
    (hcond : splitCondition k lo n = true)
    (hr : r n = true) :
    splitRange k lo r n = true :=
  (splitRange_eq_true_iff_of_goodRSplit k lo r hgood).mpr ⟨hr, hcond⟩

@[simp]
theorem split_succ_pcons
    (i : SubpartLoc) (j k : Nat) (lo : Bool)
    (s h : PRange) (p : Part) :
    split i (j + 1) k lo (Pcons s h p) =
      Pcons s h (split i j k lo p) := by
  cases i <;> cases hdrop : drop j p <;>
    simp [split, take, drop, append, hdrop] <;>
    first
    | rfl
    | rename_i sp _ _
      cases sp <;> rfl

@[simp]
theorem split_succ_pcons6
    (i : SubpartLoc) (j k : Nat) (lo : Bool)
    (h f1 : PRange) (p : Part) :
    split i (j + 1) k lo (Pcons6 h f1 p) =
      Pcons6 h f1 (split i j k lo p) := by
  cases i <;> cases hdrop : drop j p <;>
    simp [split, take, drop, append, hdrop] <;>
    first
    | rfl
    | rename_i sp _ _
      cases sp <;> rfl

@[simp]
theorem split_succ_pcons7
    (i : SubpartLoc) (j k : Nat) (lo : Bool)
    (h f1 f2 : PRange) (p : Part) :
    split i (j + 1) k lo (Pcons7 h f1 f2 p) =
      Pcons7 h f1 f2 (split i j k lo p) := by
  cases i <;> cases hdrop : drop j p <;>
    simp [split, take, drop, append, hdrop] <;>
    first
    | rfl
    | rename_i sp _ _
      cases sp <;> rfl

@[simp]
theorem split_succ_pcons8
    (i : SubpartLoc) (j k : Nat) (lo : Bool)
    (h f1 f2 f3 : PRange) (p : Part) :
    split i (j + 1) k lo (Pcons8 h f1 f2 f3 p) =
      Pcons8 h f1 f2 f3 (split i j k lo p) := by
  cases i <;> cases hdrop : drop j p <;>
    simp [split, take, drop, append, hdrop] <;>
    first
    | rfl
    | rename_i sp _ _
      cases sp <;> rfl

@[simp]
theorem goodSplit_succ_pcons
    (i : SubpartLoc) (j k : Nat) (s h : PRange) (p : Part) :
    goodSplit i (j + 1) k (Pcons s h p) = goodSplit i j k p := by
  simp [goodSplit, drop]

@[simp]
theorem goodSplit_succ_pcons6
    (i : SubpartLoc) (j k : Nat) (h f1 : PRange) (p : Part) :
    goodSplit i (j + 1) k (Pcons6 h f1 p) = goodSplit i j k p := by
  simp [goodSplit, drop]

@[simp]
theorem goodSplit_succ_pcons7
    (i : SubpartLoc) (j k : Nat) (h f1 f2 : PRange) (p : Part) :
    goodSplit i (j + 1) k (Pcons7 h f1 f2 p) = goodSplit i j k p := by
  simp [goodSplit, drop]

@[simp]
theorem goodSplit_succ_pcons8
    (i : SubpartLoc) (j k : Nat) (h f1 f2 f3 : PRange) (p : Part) :
    goodSplit i (j + 1) k (Pcons8 h f1 f2 f3 p) =
      goodSplit i j k p := by
  simp [goodSplit, drop]

@[simp]
theorem size_split
    (i : SubpartLoc) (j k : Nat) (lo : Bool) (p : Part) :
    size (split i j k lo p) = size p := by
  induction j generalizing p with
  | zero =>
      cases i <;> cases p <;>
        simp [split, take, drop, append, size] <;>
        first
        | rfl
        | rename_i sp _ _
          cases sp <;> simp [size]
  | succ j ih =>
      cases p with
      | Pnil =>
          cases i <;> simp [split, drop, size]
      | Pcons s h p =>
          simp [size, ih]
      | Pcons6 h f1 p =>
          simp [size, ih]
      | Pcons7 h f1 f2 p =>
          simp [size, ih]
      | Pcons8 h f1 f2 f3 p =>
          simp [size, ih]

theorem PartUpdate.fitp_splitRange_low_or_high
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (r : PRange) (p : Part) (x : G.Dart)
    (hfit : fitp G x (pc r p) = true) :
    fitp G x (pc (splitRange k true r) p) = true ∨
      fitp G x (pc (splitRange k false r) p) = true := by
  rcases (hupdate r p).2 G x hfit with ⟨hr, hreplace⟩
  rcases contains_splitRange_low_or_high k r hr with hlo | hhi
  · exact Or.inl (hreplace _ hlo)
  · exact Or.inr (hreplace _ hhi)

theorem PartUpdate.exactFitp_splitRange_low_or_high
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (r : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (pc r p) = true) :
    exactFitp G x (pc (splitRange k true r) p) = true ∨
      exactFitp G x (pc (splitRange k false r) p) = true := by
  have hfit' := hfit
  simp [exactFitp] at hfit'
  rcases hupdate.fitp_splitRange_low_or_high
      (G := G) k r p x hfit'.2 with hlo | hhi
  · left
    simp [exactFitp]
    exact ⟨hfit'.1.trans ((hupdate r p).1.trans
      (hupdate (splitRange k true r) p).1.symm), hlo⟩
  · right
    simp [exactFitp]
    exact ⟨hfit'.1.trans ((hupdate r p).1.trans
      (hupdate (splitRange k false r) p).1.symm), hhi⟩

theorem PartUpdate.exactFitp_splitRange_or_complement
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hfit : exactFitp G x (pc r p) = true) :
    exactFitp G x (pc (splitRange k lo r) p) = true ∨
      exactFitp G x (pc (splitRange k (!lo) r) p) = true := by
  cases lo <;> simpa [or_comm] using
    hupdate.exactFitp_splitRange_low_or_high (G := G) k r p x hfit

theorem PartUpdate.fitp_of_fitp_splitRange_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hfit : fitp G x (pc (splitRange k lo r) p) = true) :
    fitp G x (pc r p) = true := by
  rcases (hupdate (splitRange k lo r) p).2 G x hfit with
    ⟨hsplit, hreplace⟩
  exact hreplace r
    (contains_of_splitRange_of_goodRSplit k lo r hgood hsplit)

theorem PartUpdate.exactFitp_of_exactFitp_splitRange_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hfit : exactFitp G x (pc (splitRange k lo r) p) = true) :
    exactFitp G x (pc r p) = true := by
  have hfit' := hfit
  simp [exactFitp] at hfit'
  simp [exactFitp]
  exact ⟨hfit'.1.trans ((hupdate (splitRange k lo r) p).1.trans
      (hupdate r p).1.symm),
    hupdate.fitp_of_fitp_splitRange_of_goodRSplit
      (G := G) k lo r p x hgood hfit'.2⟩

theorem PartUpdate.splitCondition_of_fitp_splitRange_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hfit : fitp G x (pc (splitRange k lo r) p) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move i G x)) = true := by
  rcases (hupdate (splitRange k lo r) p).2 G x hfit with
    ⟨hsplit, _⟩
  exact splitCondition_of_splitRange_of_goodRSplit
    k lo r hgood hsplit

theorem PartUpdate.splitCondition_of_exactFitp_splitRange_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hfit : exactFitp G x (pc (splitRange k lo r) p) = true) :
    splitCondition k lo (G.arity (SubpartLoc.move i G x)) = true := by
  have hfit' := hfit
  simp [exactFitp] at hfit'
  exact hupdate.splitCondition_of_fitp_splitRange_of_goodRSplit
    (G := G) k lo r p x hgood hfit'.2

theorem PartUpdate.fitp_splitRange_of_splitCondition_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hcond : splitCondition k lo
      (G.arity (SubpartLoc.move i G x)) = true)
    (hfit : fitp G x (pc r p) = true) :
    fitp G x (pc (splitRange k lo r) p) = true := by
  rcases (hupdate r p).2 G x hfit with ⟨hr, hreplace⟩
  exact hreplace (splitRange k lo r)
    (splitRange_of_splitCondition_of_contains_of_goodRSplit
      k lo r hgood hcond hr)

theorem PartUpdate.exactFitp_splitRange_of_splitCondition_of_goodRSplit
    {pc : PRange → Part → Part} {i : SubpartLoc}
    (hupdate : PartUpdate.{u} pc i)
    (k : Nat) (lo : Bool) (r : PRange) (p : Part) (x : G.Dart)
    (hgood : goodRSplit k r = true)
    (hcond : splitCondition k lo
      (G.arity (SubpartLoc.move i G x)) = true)
    (hfit : exactFitp G x (pc r p) = true) :
    exactFitp G x (pc (splitRange k lo r) p) = true := by
  have hfit' := hfit
  simp [exactFitp] at hfit'
  simp [exactFitp]
  exact ⟨hfit'.1.trans ((hupdate r p).1.trans
      (hupdate (splitRange k lo r) p).1.symm),
    hupdate.fitp_splitRange_of_splitCondition_of_goodRSplit
      (G := G) k lo r p x hgood hcond hfit'.2⟩

end

end Part

end FourColor

end Schematic.Math.GraphTheory
