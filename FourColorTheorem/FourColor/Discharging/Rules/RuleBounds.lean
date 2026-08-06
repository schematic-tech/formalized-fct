import FourColorTheorem.FourColor.Discharging.Rules.GlobalScore

/-! Final hub-size form of the discharging bound. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Discharge

/-- The initial charge term `10 * (6 - nhub)` from Coq `dboundK`. -/
def dboundK (nhub : Nat) : Int :=
  match nhub - 5 with
  | 0 => 10
  | n + 1 => -Int.ofNat (n * 10)

theorem dboundK_eq_of_ge_five {nhub : Nat}
    (hnhub : 5 ≤ nhub) :
    dboundK nhub = (60 : Int) - 10 * (nhub : Int) := by
  rcases Nat.exists_eq_add_of_le hnhub with ⟨d, rfl⟩
  cases d with
  | zero =>
      simp [dboundK]
  | succ d =>
      simp [dboundK]
      omega

theorem dscore_eq_dboundK_add_faceScoreSum_of_arity_ge_five
    (G : Hypermap) (x : G.Dart)
    (hx : 5 ≤ G.arity x) :
    G.dscore x = dboundK (G.arity x) + G.faceScoreSum x := by
  rw [dboundK_eq_of_ge_five hx]
  simp [Hypermap.dscore]

end Discharge

end FourColor

end Schematic.Math.GraphTheory
