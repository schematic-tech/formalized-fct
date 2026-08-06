import FourColorTheorem.FourColor.Discharging.PartGeometry.SplitSemantics.Condition
namespace Schematic.Math.GraphTheory




namespace FourColor

universe u

namespace Part

noncomputable section

variable {G : Hypermap.{u}}
theorem not_both_fitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hlo : fitp G x (split i j k true p) = true)
    (hhi : fitp G x (split i j k false p) = true) :
    False := by
  have hloCondition := splitCondition_of_fitp_split_of_goodSplit
    (G := G) i j k true p x hgood hlo
  have hhiCondition := splitCondition_of_fitp_split_of_goodSplit
    (G := G) i j k false p x hgood hhi
  simp [splitCondition] at hloCondition hhiCondition
  omega

theorem not_both_exactFitp_split_of_goodSplit
    (i : SubpartLoc) (j k : Nat) (p : Part) (x : G.Dart)
    (hgood : goodSplit i j k p = true)
    (hlo : exactFitp G x (split i j k true p) = true)
    (hhi : exactFitp G x (split i j k false p) = true) :
    False := by
  apply not_both_fitp_split_of_goodSplit
    (G := G) i j k p x hgood
  · have hlo' := hlo
    simp [exactFitp] at hlo'
    exact hlo'.2
  · have hhi' := hhi
    simp [exactFitp] at hhi'
    exact hhi'.2

end

end Part

end FourColor

end Schematic.Math.GraphTheory
