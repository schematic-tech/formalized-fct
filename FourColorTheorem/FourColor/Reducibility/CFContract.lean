import FourColorTheorem.FourColor.Reducibility.CFContract.Complete

/-!
Semantic interpretation of configuration contracts.

This ports `cfcontract.v`. In particular, `cpContractDarts` is Coq's
`ctrenum`: the reverse construction-order transversal of all kernel edges.
The executable contract mask selects a finite contract from this list.
-/
