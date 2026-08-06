import Lean.Elab.Tactic.Decide
import FourColorTheorem.Tactic.DecideOptions

/-!
Project-local decision tactic for executable certificates.

`fct_decide` uses kernel reduction by default. Set `fct.nativeDecide` to use
Lean's native evaluator for the large generated certificates.
-/

open Lean Elab Tactic

elab "fct_decide" : tactic => do
  if fct.nativeDecide.get (← getOptions) then
    evalTactic (← `(tactic| native_decide))
  else
    evalTactic (← `(tactic|
      set_option maxRecDepth 100000 in
      set_option maxHeartbeats 0 in
      decide +kernel))
