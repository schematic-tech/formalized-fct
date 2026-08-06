import FourColorTheorem.FourColor.Reducibility.Jobs.Job000to020
import FourColorTheorem.FourColor.Reducibility.Jobs.Job020to040
import FourColorTheorem.FourColor.Reducibility.Jobs.Job040to060
import FourColorTheorem.FourColor.Reducibility.Jobs.Job060to080
import FourColorTheorem.FourColor.Reducibility.Jobs.Job080to100
import FourColorTheorem.FourColor.Reducibility.Jobs.Job100to106
import FourColorTheorem.FourColor.Reducibility.Jobs.Job106to120
import FourColorTheorem.FourColor.Reducibility.Jobs.Job120to140
import FourColorTheorem.FourColor.Reducibility.Jobs.Job140to164

namespace Schematic.Math.GraphTheory.FourColor.Config




theorem red000to040 : CheckedInRange 0 40 theConfigs :=
  catCheckedRange red000to020 red020to040

theorem red000to060 : CheckedInRange 0 60 theConfigs :=
  catCheckedRange red000to040 red040to060

theorem red060to100 : CheckedInRange 60 100 theConfigs :=
  catCheckedRange red060to080 red080to100

theorem red060to106 : CheckedInRange 60 106 theConfigs :=
  catCheckedRange red060to100 red100to106

theorem red000to106 : CheckedInRange 0 106 theConfigs :=
  catCheckedRange red000to060 red060to106

theorem red106to140 : CheckedInRange 106 140 theConfigs :=
  catCheckedRange red106to120 red120to140

theorem red106to164 : CheckedInRange 106 164 theConfigs :=
  catCheckedRange red106to140 red140to164

theorem red000to164 : CheckedInRange 0 164 theConfigs :=
  catCheckedRange red000to106 red106to164

end Schematic.Math.GraphTheory.FourColor.Config
