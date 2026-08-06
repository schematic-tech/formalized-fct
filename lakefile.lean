import Lake
open Lake DSL

package FourColorTheorem where
  moreLeanArgs :=
    if get_config? nativeDecide == some "true" then
      #["-D", "weak.fct.nativeDecide=true"]
    else
      #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "9d44f295b1de1c2a2c91bcb7dae8d5b0b15839c4"
require SchematicMath from git
  "git@github.com:schematic-rs/math.git" @
    "fa493430f626140dd5043753d465bf8c9cfa15ab"

@[default_target]
lean_lib FourColorTheorem where
  roots := #[`FourColorTheorem]
