import Lean

/-! Configuration for executable Four Color Theorem certificate checks. -/

register_option fct.nativeDecide : Bool := {
  defValue := false
  descr := "use native evaluation for Four Color Theorem certificate checks"
}
